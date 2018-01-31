/*  Title:      Tools/jEdit/src/symbols_dockable.scala
    Author:     Fabian Immler

Dockable window for Symbol Palette.
*/

package isabelle.jedit


import isabelle._

import scala.swing.event.{SelectionChanged, ValueChanged}
import scala.swing.{Component, Action, Button, TabbedPane, TextField, BorderPanel,
  Label, ScrollPane}

import org.gjt.sp.jedit.{EditBus, EBComponent, EBMessage, View}


class Symbols_Dockable(view: View, position: String) extends Dockable(view, position)
{
  private def font_size: Int =
    Font_Info.main_size(PIDE.options.real("jedit_font_scale")).round


  /* abbrevs */

  private val abbrevs_panel = new Abbrevs_Panel

  private val abbrevs_refresh_delay =
    GUI_Thread.delay_last(PIDE.options.seconds("editor_update_delay")) { abbrevs_panel.refresh }

  private class Abbrev_Component(txt: String, abbrs: List[String]) extends Button
  {
    def update_font { font = GUI.font(size = font_size) }
    update_font

    text = "<html>" + HTML.output(Symbol.decode(txt)) + "</html>"
    action =
      Action(text) {
        val text_area = view.getTextArea
        val (s1, s2) =
          Completion.split_template(Isabelle_Encoding.maybe_decode(text_area.getBuffer, txt))
        text_area.setSelectedText(s1 + s2)
        text_area.moveCaretPosition(text_area.getCaretPosition - s2.length)
        text_area.requestFocus
      }
    tooltip = GUI.tooltip_lines(cat_lines(txt :: abbrs.map(a => "abbrev: " + a)))
  }

  private class Abbrevs_Panel extends Wrap_Panel
  {
    private var abbrevs: Thy_Header.Abbrevs = Nil

    def refresh: Unit = GUI_Thread.require {
      val abbrevs1 = Isabelle.buffer_syntax(view.getBuffer).getOrElse(Outer_Syntax.empty).abbrevs

      if (abbrevs != abbrevs1) {
        abbrevs = abbrevs1

        val entries: List[(String, List[String])] =
          Multi_Map(
            (for {
              (abbr, txt0) <- abbrevs
              txt = Symbol.encode(txt0)
              if !Symbol.iterator(txt).
                forall(s => s.length == 1 && s(0) != Completion.caret_indicator)
            } yield (txt, abbr)): _*).iterator_list.toList

        contents.clear
        for ((txt, abbrs) <- entries.sortBy(_._1))
          contents += new Abbrev_Component(txt, abbrs.filterNot(_ == "").sorted)

        revalidate
        repaint
      }
    }

    refresh
  }


  /* symbols */

  private class Symbol_Component(val symbol: String, is_control: Boolean) extends Button
  {
    def update_font
    {
      font =
        Symbol.fonts.get(symbol) match {
          case None => GUI.font(size = font_size)
          case Some(font_family) => GUI.font(family = font_family, size = font_size)
        }
    }
    update_font

    action =
      Action(Symbol.decode(symbol)) {
        val text_area = view.getTextArea
        if (is_control && HTML.control.isDefinedAt(symbol))
          Token_Markup.edit_control_style(text_area, symbol)
        else
          text_area.setSelectedText(Isabelle_Encoding.maybe_decode(text_area.getBuffer, symbol))
        text_area.requestFocus
      }
    tooltip =
      GUI.tooltip_lines(
        cat_lines(symbol :: Symbol.abbrevs.get_list(symbol).map(a => "abbrev: " + a)))
  }

  private class Reset_Component extends Button
  {
    action = Action("Reset") {
      val text_area = view.getTextArea
      Token_Markup.edit_control_style(text_area, "")
      text_area.requestFocus
    }
    tooltip = "Reset control symbols within text"
  }


  /* search */

  private class Search_Panel extends BorderPanel {
    val search_field = new TextField(10)
    val results_panel = new Wrap_Panel
    layout(search_field) = BorderPanel.Position.North
    layout(new ScrollPane(results_panel)) = BorderPanel.Position.Center

    val search_space =
      (for (sym <- Symbol.names.keysIterator) yield (sym, Word.lowercase(sym))).toList
    val search_delay =
      GUI_Thread.delay_last(PIDE.options.seconds("editor_input_delay")) {
        val search_words = Word.explode(Word.lowercase(search_field.text))
        val search_limit = PIDE.options.int("jedit_symbols_search_limit") max 0
        val results =
          for ((sym, s) <- search_space; if search_words.forall(s.contains(_))) yield sym

        results_panel.contents.clear
        for (sym <- results.take(search_limit))
          results_panel.contents += new Symbol_Component(sym, false)
        if (results.length > search_limit)
          results_panel.contents +=
            new Label("...") { tooltip = "(" + (results.length - search_limit) + " more)" }
        revalidate
        repaint
      }
      search_field.reactions += { case ValueChanged(_) => search_delay.invoke() }
  }


  /* tabs */

  private val group_tabs: TabbedPane = new TabbedPane {
    pages += new TabbedPane.Page("abbrevs", abbrevs_panel)

    pages ++=
      Symbol.groups.map({ case (group, symbols) =>
        new TabbedPane.Page(group,
          new ScrollPane(new Wrap_Panel {
            val control = group == "control"
            contents ++= symbols.map(new Symbol_Component(_, control))
            if (control) contents += new Reset_Component
          }), null)
      })

    val search_panel = new Search_Panel
    val search_page = new TabbedPane.Page("search", search_panel, "Search Symbols")
    pages += search_page

    listenTo(selection)
    reactions += {
      case SelectionChanged(_) if selection.page == search_page =>
        search_panel.search_field.requestFocus
    }

    for (page <- pages)
      page.title = Word.implode(Word.explode('_', page.title).map(Word.perhaps_capitalize(_)))
  }
  set_content(group_tabs)



  /* main */

  private val edit_bus_handler: EBComponent =
    new EBComponent { def handleMessage(msg: EBMessage) { abbrevs_refresh_delay.invoke() } }

  private val main =
    Session.Consumer[Any](getClass.getName) {
      case _: Session.Global_Options =>
        GUI_Thread.later {
          val comp = group_tabs.peer
          GUI.traverse_components(comp,
            {
              case c0: javax.swing.JComponent =>
                Component.wrap(c0) match {
                  case c: Abbrev_Component => c.update_font
                  case c: Symbol_Component => c.update_font
                  case _ =>
                }
              case _ =>
            })
          comp.revalidate
          comp.repaint()
        }
      case _: Session.Commands_Changed => abbrevs_refresh_delay.invoke()
    }

  override def init()
  {
    EditBus.addToBus(edit_bus_handler)
    PIDE.session.global_options += main
    PIDE.session.commands_changed += main
  }

  override def exit()
  {
    EditBus.removeFromBus(edit_bus_handler)
    PIDE.session.global_options -= main
    PIDE.session.commands_changed -= main
  }
}
