/*  Title:      Tools/jEdit/src/scala_console.scala
    Author:     Makarius

Scala instance of Console plugin.
*/

package isabelle.jedit


import isabelle._

import console.{Console, ConsolePane, Shell, Output}

import org.gjt.sp.jedit.{jEdit, JARClassLoader}
import org.gjt.sp.jedit.MiscUtilities

import java.io.{File => JFile, FileFilter, OutputStream, Writer, PrintWriter}

import scala.tools.nsc.{GenericRunnerSettings, NewLinePrintWriter, ConsoleWriter}
import scala.tools.nsc.interpreter.IMain
import scala.collection.mutable


class Scala_Console extends Shell("Scala")
{
  /* reconstructed jEdit/plugin classpath */

  private def reconstruct_classpath(): String =
  {
    def find_jars(start: String): List[String] =
      if (start != null)
        File.find_files(new JFile(start), file => file.getName.endsWith(".jar")).
          map(_.getAbsolutePath)
      else Nil

    val initial_class_path =
      Library.space_explode(JFile.pathSeparatorChar, System.getProperty("java.class.path", ""))

    val path =
      initial_class_path :::
      find_jars(jEdit.getSettingsDirectory) :::
      find_jars(jEdit.getJEditHome)
    path.mkString(JFile.pathSeparator)
  }


  /* global state -- owned by GUI thread */

  @volatile private var interpreters = Map.empty[Console, Interpreter]

  @volatile private var global_console: Console = null
  @volatile private var global_out: Output = null
  @volatile private var global_err: Output = null

  private val console_stream = new OutputStream
  {
    val buf = new StringBuilder
    override def flush()
    {
      val s = buf.synchronized { val s = buf.toString; buf.clear; s }
      val str = UTF8.decode_permissive(s)
      GUI_Thread.later {
        if (global_out == null) System.out.print(str)
        else global_out.writeAttrs(null, str)
      }
      Thread.sleep(10)  // FIXME adhoc delay to avoid loosing output
    }
    override def close() { flush () }
    def write(byte: Int) {
      val c = byte.toChar
      buf.synchronized { buf.append(c) }
      if (c == '\n') flush()
    }
  }

  private val console_writer = new Writer
  {
    def flush() {}
    def close() {}

    def write(cbuf: Array[Char], off: Int, len: Int)
    {
      if (len > 0) write(new String(cbuf.slice(off, off + len)))
    }

    override def write(str: String)
    {
      if (global_out == null) System.out.println(str)
      else global_out.print(null, str)
    }
  }

  private def with_console[A](console: Console, out: Output, err: Output)(e: => A): A =
  {
    global_console = console
    global_out = out
    global_err = if (err == null) out else err
    try {
      scala.Console.withErr(console_stream) {
        scala.Console.withOut(console_stream) { e }
      }
    }
    finally {
      console_stream.flush
      global_console = null
      global_out = null
      global_err = null
    }
  }

  private def report_error(str: String)
  {
    if (global_console == null || global_err == null) System.err.println(str)
    else GUI_Thread.later { global_err.print(global_console.getErrorColor, str) }
  }


  /* interpreter thread */

  private abstract class Request
  private case class Start(console: Console) extends Request
  private case class Execute(console: Console, out: Output, err: Output, command: String)
    extends Request

  private class Interpreter
  {
    private val running = Synchronized[Option[Thread]](None)
    def interrupt { running.change(opt => { opt.foreach(_.interrupt); opt }) }

    private val settings = new GenericRunnerSettings(report_error)
    settings.classpath.value = reconstruct_classpath()

    private val interp = new IMain(settings, new PrintWriter(console_writer, true))
    {
      override def parentClassLoader = new JARClassLoader
    }
    interp.setContextClassLoader

    val thread: Consumer_Thread[Request] = Consumer_Thread.fork("Scala_Console")
    {
      case Start(console) =>
        interp.bind("view", "org.gjt.sp.jedit.View", console.getView)
        interp.bind("console", "console.Console", console)
        interp.interpret("import isabelle._; import isabelle.jedit._")
        true

      case Execute(console, out, err, command) =>
        with_console(console, out, err) {
          try {
            running.change(_ => Some(Thread.currentThread()))
            interp.interpret(command)
          }
          finally {
            running.change(_ => None)
            Thread.interrupted
          }
          GUI_Thread.later {
            if (err != null) err.commandDone()
            out.commandDone()
          }
          true
        }
    }
  }


  /* jEdit console methods */

  override def openConsole(console: Console)
  {
    val interp = new Interpreter
    interp.thread.send(Start(console))
    interpreters += (console -> interp)
  }

  override def closeConsole(console: Console)
  {
    interpreters.get(console) match {
      case Some(interp) =>
        interp.interrupt
        interp.thread.shutdown
        interpreters -= console
      case None =>
    }
  }

  override def printInfoMessage(out: Output)
  {
    out.print(null,
     "This shell evaluates Isabelle/Scala expressions.\n\n" +
     "The contents of package isabelle and isabelle.jedit are imported.\n" +
     "The following special toplevel bindings are provided:\n" +
     "  view    -- current jEdit/Swing view (e.g. view.getBuffer, view.getTextArea)\n" +
     "  console -- jEdit Console plugin\n" +
     "  PIDE    -- Isabelle/PIDE plugin (e.g. PIDE.session, PIDE.snapshot, PIDE.rendering)\n")
  }

  override def printPrompt(console: Console, out: Output)
  {
    out.writeAttrs(ConsolePane.colorAttributes(console.getInfoColor), "scala>")
    out.writeAttrs(ConsolePane.colorAttributes(console.getPlainColor), " ")
  }

  override def execute(console: Console, input: String, out: Output, err: Output, command: String)
  {
    interpreters(console).thread.send(Execute(console, out, err, command))
  }

  override def stop(console: Console)
  {
    interpreters.get(console).foreach(_.interrupt)
  }
}
