/*  Title:      Tools/jEdit/src/session_build.scala
    Author:     Makarius

Session build management.
*/

package isabelle.jedit


import isabelle._

import java.awt.event.{WindowEvent, WindowAdapter}
import javax.swing.{WindowConstants, JDialog}

import scala.swing.{ScrollPane, Button, CheckBox, FlowPanel,
  BorderPanel, TextArea, Component, Label}
import scala.swing.event.ButtonClicked

import org.gjt.sp.jedit.View


object Session_Build
{
  def session_build(view: View)
  {
    GUI_Thread.require {}

    try {
      if (JEdit_Sessions.session_build_mode() == "none" ||
          JEdit_Sessions.session_build(no_build = true) == 0) JEdit_Sessions.session_start()
      else new Dialog(view)
    }
    catch {
      case exn: Throwable =>
        GUI.dialog(view, "Isabelle", GUI.scrollable_text(Exn.message(exn)))
    }
  }

  private class Dialog(view: View) extends JDialog(view)
  {
    /* text */

    private val text = new TextArea {
      editable = false
      columns = 65
      rows = 24
    }
    text.font = GUI.copy_font((new Label).font)

    private val scroll_text = new ScrollPane(text)


    /* progress */

    @volatile private var is_stopped = false

    private val progress = new Progress {
      override def echo(txt: String): Unit =
        GUI_Thread.later {
          text.append(txt + "\n")
          val vertical = scroll_text.peer.getVerticalScrollBar
          vertical.setValue(vertical.getMaximum)
        }

      override def theory(session: String, theory: String): Unit =
        echo(session + ": theory " + theory)

      override def stopped: Boolean = is_stopped
    }


    /* layout panel with dynamic actions */

    private val action_panel = new FlowPanel(FlowPanel.Alignment.Center)()
    private val layout_panel = new BorderPanel
    layout_panel.layout(scroll_text) = BorderPanel.Position.Center
    layout_panel.layout(action_panel) = BorderPanel.Position.South

    setContentPane(layout_panel.peer)

    private def set_actions(cs: Component*)
    {
      action_panel.contents.clear
      action_panel.contents ++= cs
      layout_panel.revalidate
      layout_panel.repaint
    }


    /* return code and exit */

    private var _return_code: Option[Int] = None

    private def return_code(rc: Int): Unit =
      GUI_Thread.later {
        _return_code = Some(rc)
        delay_exit.invoke
      }

    private val delay_exit =
      GUI_Thread.delay_first(Time.seconds(1.0))
      {
        if (can_auto_close) conclude()
        else {
          val button = new Button("Close") { reactions += { case ButtonClicked(_) => conclude() } }
          set_actions(button)
          button.peer.getRootPane.setDefaultButton(button.peer)
        }
      }

    private def conclude()
    {
      setVisible(false)
      dispose()
    }


    /* close */

    setDefaultCloseOperation(WindowConstants.DO_NOTHING_ON_CLOSE)

    addWindowListener(new WindowAdapter {
      override def windowClosing(e: WindowEvent) {
        if (_return_code.isDefined) conclude()
        else stopping()
      }
    })

    private def stopping()
    {
      is_stopped = true
      set_actions(new Label("Stopping ..."))
    }

    private val stop_button = new Button("Stop") {
      reactions += { case ButtonClicked(_) => stopping() }
    }

    private var do_auto_close = true
    private def can_auto_close: Boolean = do_auto_close && _return_code == Some(0)

    private val auto_close = new CheckBox("Auto close") {
      reactions += {
        case ButtonClicked(_) => do_auto_close = this.selected
        if (can_auto_close) conclude()
      }
    }
    auto_close.selected = do_auto_close
    auto_close.tooltip = "Automatically close dialog when finished"

    set_actions(stop_button, auto_close)


    /* main */

    setTitle("Isabelle build (" +
      Isabelle_System.getenv("ML_IDENTIFIER") + " / " +
      "jdk-" + Platform.jvm_version + "_" + Platform.jvm_platform + ")")

    pack()
    setLocationRelativeTo(view)
    setVisible(true)

    Standard_Thread.fork("session_build") {
      progress.echo("Build started for Isabelle/" + JEdit_Sessions.session_name() + " ...")

      val (out, rc) =
        try { ("", JEdit_Sessions.session_build(progress = progress)) }
        catch {
          case exn: Throwable =>
            (Output.error_text(Exn.message(exn)) + "\n", Exn.return_code(exn, 2))
        }

      progress.echo(out + (if (rc == 0) "OK\n" else "Return code: " + rc + "\n"))

      if (rc == 0) JEdit_Sessions.session_start()
      else progress.echo("Session build failed -- prover process remains inactive!")

      return_code(rc)
    }
  }
}
