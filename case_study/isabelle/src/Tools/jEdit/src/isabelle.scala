/*  Title:      Tools/jEdit/src/isabelle.scala
    Author:     Makarius

Global configuration and convenience operations for Isabelle/jEdit.
*/

package isabelle.jedit


import isabelle._

import java.awt.Frame

import scala.swing.CheckBox
import scala.swing.event.ButtonClicked

import org.gjt.sp.jedit.{jEdit, View, Buffer}
import org.gjt.sp.jedit.buffer.JEditBuffer
import org.gjt.sp.jedit.textarea.{JEditTextArea, TextArea, StructureMatcher, Selection}
import org.gjt.sp.jedit.syntax.TokenMarker
import org.gjt.sp.jedit.indent.IndentRule
import org.gjt.sp.jedit.gui.{DockableWindowManager, CompleteWord}
import org.jedit.options.CombinedOptions


object Isabelle
{
  /* editor modes */

  val modes =
    List(
      "isabelle",         // theory source
      "isabelle-ml",      // ML source
      "isabelle-news",    // NEWS
      "isabelle-options", // etc/options
      "isabelle-output",  // pretty text area output
      "isabelle-root",    // session ROOT
      "sml")              // Standard ML (not Isabelle/ML)

  private lazy val ml_syntax: Outer_Syntax =
    Outer_Syntax.init().no_tokens.
      set_language_context(Completion.Language_Context.ML_outer)

  private lazy val sml_syntax: Outer_Syntax =
    Outer_Syntax.init().no_tokens.
      set_language_context(Completion.Language_Context.SML_outer)

  private lazy val news_syntax: Outer_Syntax =
    Outer_Syntax.init().no_tokens

  def mode_syntax(mode: String): Option[Outer_Syntax] =
    mode match {
      case "isabelle" => Some(PIDE.resources.base_syntax)
      case "isabelle-options" => Some(Options.options_syntax)
      case "isabelle-root" => Some(Sessions.root_syntax)
      case "isabelle-ml" => Some(ml_syntax)
      case "isabelle-news" => Some(news_syntax)
      case "isabelle-output" => None
      case "sml" => Some(sml_syntax)
      case _ => None
    }

  def buffer_syntax(buffer: JEditBuffer): Option[Outer_Syntax] =
    if (buffer == null) None
    else
      (JEdit_Lib.buffer_mode(buffer), PIDE.document_model(buffer)) match {
        case ("isabelle", Some(model)) =>
          Some(PIDE.session.recent_syntax(model.node_name))
        case (mode, _) => mode_syntax(mode)
      }


  /* token markers */

  private val mode_markers: Map[String, TokenMarker] =
    Map(modes.map(mode => (mode, new Token_Markup.Marker(mode, None))): _*) +
      ("bibtex" -> new Bibtex_JEdit.Token_Marker)

  def mode_token_marker(mode: String): Option[TokenMarker] = mode_markers.get(mode)

  def buffer_token_marker(buffer: Buffer): Option[TokenMarker] =
  {
    val mode = JEdit_Lib.buffer_mode(buffer)
    if (mode == "isabelle") Some(new Token_Markup.Marker(mode, Some(buffer)))
    else mode_token_marker(mode)
  }


  /* text structure */

  def indent_rule(mode: String): Option[IndentRule] =
    mode match {
      case "isabelle" | "isabelle-options" | "isabelle-root" =>
        Some(Text_Structure.Indent_Rule)
      case _ => None
    }

  def structure_matchers(mode: String): List[StructureMatcher] =
    if (mode == "isabelle") List(Text_Structure.Matcher) else Nil


  /* dockable windows */

  private def wm(view: View): DockableWindowManager = view.getDockableWindowManager

  def debugger_dockable(view: View): Option[Debugger_Dockable] =
    wm(view).getDockableWindow("isabelle-debugger") match {
      case dockable: Debugger_Dockable => Some(dockable)
      case _ => None
    }

  def documentation_dockable(view: View): Option[Documentation_Dockable] =
    wm(view).getDockableWindow("isabelle-documentation") match {
      case dockable: Documentation_Dockable => Some(dockable)
      case _ => None
    }

  def monitor_dockable(view: View): Option[Monitor_Dockable] =
    wm(view).getDockableWindow("isabelle-monitor") match {
      case dockable: Monitor_Dockable => Some(dockable)
      case _ => None
    }

  def output_dockable(view: View): Option[Output_Dockable] =
    wm(view).getDockableWindow("isabelle-output") match {
      case dockable: Output_Dockable => Some(dockable)
      case _ => None
    }

  def protocol_dockable(view: View): Option[Protocol_Dockable] =
    wm(view).getDockableWindow("isabelle-protocol") match {
      case dockable: Protocol_Dockable => Some(dockable)
      case _ => None
    }

  def query_dockable(view: View): Option[Query_Dockable] =
    wm(view).getDockableWindow("isabelle-query") match {
      case dockable: Query_Dockable => Some(dockable)
      case _ => None
    }

  def raw_output_dockable(view: View): Option[Raw_Output_Dockable] =
    wm(view).getDockableWindow("isabelle-raw-output") match {
      case dockable: Raw_Output_Dockable => Some(dockable)
      case _ => None
    }

  def simplifier_trace_dockable(view: View): Option[Simplifier_Trace_Dockable] =
    wm(view).getDockableWindow("isabelle-simplifier-trace") match {
      case dockable: Simplifier_Trace_Dockable => Some(dockable)
      case _ => None
    }

  def sledgehammer_dockable(view: View): Option[Sledgehammer_Dockable] =
    wm(view).getDockableWindow("isabelle-sledgehammer") match {
      case dockable: Sledgehammer_Dockable => Some(dockable)
      case _ => None
    }

  def state_dockable(view: View): Option[State_Dockable] =
    wm(view).getDockableWindow("isabelle-state") match {
      case dockable: State_Dockable => Some(dockable)
      case _ => None
    }

  def symbols_dockable(view: View): Option[Symbols_Dockable] =
    wm(view).getDockableWindow("isabelle-symbols") match {
      case dockable: Symbols_Dockable => Some(dockable)
      case _ => None
    }

  def syslog_dockable(view: View): Option[Syslog_Dockable] =
    wm(view).getDockableWindow("isabelle-syslog") match {
      case dockable: Syslog_Dockable => Some(dockable)
      case _ => None
    }

  def theories_dockable(view: View): Option[Theories_Dockable] =
    wm(view).getDockableWindow("isabelle-theories") match {
      case dockable: Theories_Dockable => Some(dockable)
      case _ => None
    }

  def timing_dockable(view: View): Option[Timing_Dockable] =
    wm(view).getDockableWindow("isabelle-timing") match {
      case dockable: Timing_Dockable => Some(dockable)
      case _ => None
    }


  /* continuous checking */

  private val CONTINUOUS_CHECKING = "editor_continuous_checking"

  def continuous_checking: Boolean = PIDE.options.bool(CONTINUOUS_CHECKING)
  def continuous_checking_=(b: Boolean): Unit =
    GUI_Thread.require {
      if (continuous_checking != b) {
        PIDE.options.bool(CONTINUOUS_CHECKING) = b
        PIDE.session.update_options(PIDE.options.value)
      }
    }

  def set_continuous_checking() { continuous_checking = true }
  def reset_continuous_checking() { continuous_checking = false }
  def toggle_continuous_checking() { continuous_checking = !continuous_checking }

  class Continuous_Checking extends CheckBox("Continuous checking")
  {
    tooltip = "Continuous checking of proof document (visible and required parts)"
    reactions += { case ButtonClicked(_) => continuous_checking = selected }
    def load() { selected = continuous_checking }
    load()
  }


  /* update state */

  def update_state(view: View): Unit =
    state_dockable(view).foreach(_.update_request())


  /* ML statistics */

  class ML_Stats extends
    JEdit_Options.Check_Box("ML_statistics", "ML statistics", "Enable ML runtime system statistics")

  /* skip proofs */

  private val SKIP_PROOFS = "skip_proofs"

  def skip_proofs: Boolean = PIDE.options.bool(SKIP_PROOFS)

  def skip_proofs_=(b: Boolean)
  {
    GUI_Thread.require()

    if (skip_proofs != b) {
      PIDE.options.bool(SKIP_PROOFS) = b
      PIDE.options_changed()
      PIDE.session.update_options(PIDE.options.value)
      PIDE.editor.flush()
    }
  }

  def set_skip_proofs() { skip_proofs = true }
  def reset_skip_proofs() { skip_proofs = false }
  def toggle_skip_proofs() { skip_proofs = !skip_proofs }

  class Skip_Proofs extends CheckBox("Skip proofs")
  {
    tooltip = "Avoid checking proofs where possible"
    reactions += { case ButtonClicked(_) => skip_proofs = selected }
    def load() { selected = skip_proofs }
    load()
  }

/* defer proofs */

  private val DEFER_PROOFS = "defer_proofs"

  def defer_proofs: Boolean = PIDE.options.bool(DEFER_PROOFS)

  def defer_proofs_=(b: Boolean)
  {
    GUI_Thread.require()

    if (defer_proofs != b) {
      PIDE.options.bool(DEFER_PROOFS) = b
      PIDE.options_changed()
      PIDE.session.update_options(PIDE.options.value)
      PIDE.editor.flush()
    }
  }

  def set_defer_proofs() { defer_proofs = true }
  def reset_defer_proofs() { defer_proofs = false }
  def toggle_defer_proofs() { defer_proofs = !defer_proofs }

  class Defer_Proofs extends CheckBox("Defer proofs")
  {
    tooltip = "Defer proof checking"
    reactions += { case ButtonClicked(_) => defer_proofs = selected }
    def load() { selected = defer_proofs }
    load()
  }

/* quick print */

  private val QUICK_PRINT = "quick_print"

  def quick_print: Boolean = PIDE.options.bool(QUICK_PRINT)

  def quick_print_=(b: Boolean)
  {
    GUI_Thread.require()

    if (quick_print != b) {
      PIDE.options.bool(QUICK_PRINT) = b
      PIDE.options_changed()
      PIDE.session.update_options(PIDE.options.value)
      PIDE.editor.flush()
    }
  }

  def set_quick_print() { quick_print = true }
  def reset_quick_print() { quick_print = false }
  def toggle_quick_print() { quick_print = !quick_print }

  class Quick_Print extends CheckBox("Quick Print")
  {
    tooltip = "Skip typed print translations"
    reactions += { case ButtonClicked(_) => quick_print = selected }
    def load() { selected = quick_print }
    load()
  }


  /* required document nodes */

  private def node_required_update(view: View, toggle: Boolean = false, set: Boolean = false)
  {
    GUI_Thread.require {}
    PIDE.document_model(view.getBuffer) match {
      case Some(model) =>
        model.node_required = (if (toggle) !model.node_required else set)
      case None =>
    }
  }

  def set_node_required(view: View) { node_required_update(view, set = true) }
  def reset_node_required(view: View) { node_required_update(view, set = false) }
  def toggle_node_required(view: View) { node_required_update(view, toggle = true) }


  /* font size */

  def reset_font_size() {
    Font_Info.main_change.reset(PIDE.options.int("jedit_reset_font_size").toFloat)
  }
  def increase_font_size() { Font_Info.main_change.step(1) }
  def decrease_font_size() { Font_Info.main_change.step(-1) }


  /* structured edits */

  def newline(text_area: TextArea)
  {
    if (!text_area.isEditable()) text_area.getToolkit().beep()
    else {
      val buffer = text_area.getBuffer
      def nl { text_area.userInput('\n') }

      if (indent_rule(JEdit_Lib.buffer_mode(buffer)).isDefined &&
          buffer.getStringProperty("autoIndent") == "full" &&
          PIDE.options.bool("jedit_indent_newline"))
      {
        Isabelle.buffer_syntax(buffer) match {
          case Some(syntax) if buffer.isInstanceOf[Buffer] =>
            val keywords = syntax.keywords

            val caret = text_area.getCaretPosition
            val line = text_area.getCaretLine
            val line_range = JEdit_Lib.line_range(buffer, line)

            def line_content(start: Text.Offset, stop: Text.Offset, context: Scan.Line_Context)
              : (List[Token], Scan.Line_Context) =
            {
              val text = JEdit_Lib.try_get_text(buffer, Text.Range(start, stop)).getOrElse("")
              val (toks, context1) = Token.explode_line(keywords, text, context)
              val toks1 = toks.filterNot(_.is_space)
              (toks1, context1)
            }

            val context0 = Token_Markup.Line_Context.prev(buffer, line).get_context
            val (tokens1, context1) = line_content(line_range.start, caret, context0)
            val (tokens2, _) = line_content(caret, line_range.stop, context1)

            if (tokens1.nonEmpty && keywords.is_indent_command(tokens1.head))
              buffer.indentLine(line, true)

            if (tokens2.isEmpty || keywords.is_indent_command(tokens2.head))
              JEdit_Lib.buffer_edit(buffer) {
                text_area.setSelectedText("\n")
                if (!buffer.indentLine(line + 1, true)) text_area.goToStartOfWhiteSpace(false)
              }
            else nl
          case _ => nl
        }
      }
      else nl
    }
  }

  def insert_line_padding(text_area: JEditTextArea, text: String)
  {
    val buffer = text_area.getBuffer
    JEdit_Lib.buffer_edit(buffer) {
      val text1 =
        if (text_area.getSelectionCount == 0) {
          def pad(range: Text.Range): String =
            if (JEdit_Lib.try_get_text(buffer, range) == Some("\n")) "" else "\n"

          val caret = JEdit_Lib.caret_range(text_area)
          val before_caret = JEdit_Lib.point_range(buffer, caret.start - 1)
          pad(before_caret) + text + pad(caret)
        }
        else text
      text_area.setSelectedText(text1)
    }
  }

  def edit_command(
    snapshot: Document.Snapshot,
    text_area: TextArea,
    padding: Boolean,
    id: Document_ID.Generic,
    text: String)
  {
    val buffer = text_area.getBuffer
    if (!snapshot.is_outdated && text != "") {
      (snapshot.state.find_command(snapshot.version, id), PIDE.document_model(buffer)) match {
        case (Some((node, command)), Some(model)) if command.node_name == model.node_name =>
          node.command_start(command) match {
            case Some(start) =>
              JEdit_Lib.buffer_edit(buffer) {
                val range = command.proper_range + start
                JEdit_Lib.buffer_edit(buffer) {
                  if (padding) {
                    text_area.moveCaretPosition(start + range.length)
                    val start_line = text_area.getCaretLine + 1
                    text_area.setSelectedText("\n" + text)
                    val end_line = text_area.getCaretLine
                    buffer.indentLines(start_line, end_line)
                  }
                  else {
                    buffer.remove(start, range.length)
                    text_area.moveCaretPosition(start)
                    text_area.setSelectedText(text)
                  }
                }
              }
            case None =>
          }
        case _ =>
      }
    }
  }


  /* selection */

  def select_entity(text_area: JEditTextArea)
  {
    for {
      doc_view <- PIDE.document_view(text_area)
      rendering = doc_view.get_rendering()
    } {
      val caret_range = JEdit_Lib.caret_range(text_area)
      val buffer_range = JEdit_Lib.buffer_range(text_area.getBuffer)
      val active_focus = rendering.caret_focus_ranges(caret_range, buffer_range)
      if (active_focus.nonEmpty) {
        text_area.selectNone()
        for (r <- active_focus)
          text_area.addToSelection(new Selection.Range(r.start, r.stop))
      }
    }
  }


  /* completion */

  def complete(view: View, word_only: Boolean)
  {
    Completion_Popup.Text_Area.action(view.getTextArea, word_only)
  }


  /* control styles */

  def control_sub(text_area: JEditTextArea)
  { Token_Markup.edit_control_style(text_area, Symbol.sub) }

  def control_sup(text_area: JEditTextArea)
  { Token_Markup.edit_control_style(text_area, Symbol.sup) }

  def control_bold(text_area: JEditTextArea)
  { Token_Markup.edit_control_style(text_area, Symbol.bold) }

  def control_emph(text_area: JEditTextArea)
  { Token_Markup.edit_control_style(text_area, Symbol.emph) }

  def control_reset(text_area: JEditTextArea)
  { Token_Markup.edit_control_style(text_area, "") }


  /* block styles */

  private def enclose_input(text_area: JEditTextArea, s1: String, s2: String)
  {
    s1.foreach(text_area.userInput(_))
    s2.foreach(text_area.userInput(_))
    s2.foreach(_ => text_area.goToPrevCharacter(false))
  }

  def input_bsub(text_area: JEditTextArea)
  { enclose_input(text_area, Symbol.bsub_decoded, Symbol.esub_decoded) }

  def input_bsup(text_area: JEditTextArea)
  { enclose_input(text_area, Symbol.bsup_decoded, Symbol.esup_decoded) }


  /* spell-checker dictionary */

  def update_dictionary(text_area: JEditTextArea, include: Boolean, permanent: Boolean)
  {
    for {
      spell_checker <- PIDE.spell_checker.get
      doc_view <- PIDE.document_view(text_area)
      rendering = doc_view.get_rendering()
      range = JEdit_Lib.caret_range(text_area)
      Text.Info(_, word) <- Spell_Checker.current_word(text_area, rendering, range)
    } {
      spell_checker.update(word, include, permanent)
      JEdit_Lib.jedit_views().foreach(_.repaint())
    }
  }

  def reset_dictionary()
  {
    for (spell_checker <- PIDE.spell_checker.get)
    {
      spell_checker.reset()
      JEdit_Lib.jedit_views().foreach(_.repaint())
    }
  }


  /* debugger */

  def toggle_breakpoint(text_area: JEditTextArea): Unit =
    if (Debugger.is_active()) {
      for {
        (command, serial) <- Debugger_Dockable.get_breakpoint(text_area, text_area.getCaretPosition)
      } Debugger_Dockable.toggle_breakpoint(command, serial)
    }


  /* plugin options */

  def plugin_options(frame: Frame)
  {
    GUI_Thread.require {}
    jEdit.setProperty("Plugin Options.last", "isabelle-general")
    new CombinedOptions(frame, 1)
  }
}
