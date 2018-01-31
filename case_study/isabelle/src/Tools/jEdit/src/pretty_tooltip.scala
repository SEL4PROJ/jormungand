/*  Title:      Tools/jEdit/src/pretty_tooltip.scala
    Author:     Makarius

Tooltip based on Pretty_Text_Area.
*/

package isabelle.jedit


import isabelle._

import java.awt.{Color, Point, BorderLayout, Dimension}
import java.awt.event.{FocusAdapter, FocusEvent}
import javax.swing.{JPanel, JComponent, SwingUtilities, JLayeredPane}
import javax.swing.border.LineBorder

import scala.swing.{FlowPanel, Label}
import scala.swing.event.MouseClicked

import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.textarea.TextArea


object Pretty_Tooltip
{
  /* tooltip hierarchy */

  // owned by GUI thread
  private var stack: List[Pretty_Tooltip] = Nil

  private def hierarchy(tip: Pretty_Tooltip): Option[(List[Pretty_Tooltip], List[Pretty_Tooltip])] =
  {
    GUI_Thread.require {}

    if (stack.contains(tip)) Some(stack.span(_ != tip))
    else None
  }

  private def descendant(parent: JComponent): Option[Pretty_Tooltip] =
    GUI_Thread.require { stack.find(tip => tip.original_parent == parent) }

  def apply(
    view: View,
    parent: JComponent,
    location: Point,
    rendering: Rendering,
    results: Command.Results,
    info: Text.Info[XML.Body])
  {
    GUI_Thread.require {}

    stack match {
      case top :: _ if top.results == results && top.info == info =>
      case _ =>
        GUI.layered_pane(parent) match {
          case None =>
          case Some(layered) =>
            val (old, rest) =
              GUI.ancestors(parent).collectFirst({ case x: Pretty_Tooltip => x }) match {
                case Some(tip) => hierarchy(tip).getOrElse((stack, Nil))
                case None => (stack, Nil)
              }
            old.foreach(_.hide_popup)

            val loc = SwingUtilities.convertPoint(parent, location, layered)
            val tip = new Pretty_Tooltip(view, layered, parent, loc, rendering, results, info)
            stack = tip :: rest
            tip.show_popup
        }
    }
  }


  /* pending event and active state */  // owned by GUI thread

  private var pending: Option[() => Unit] = None
  private var active = true

  private val pending_delay =
    GUI_Thread.delay_last(PIDE.options.seconds("jedit_tooltip_delay")) {
      pending match {
        case Some(body) => pending = None; body()
        case None =>
      }
    }

  def invoke(body: () => Unit): Unit =
    GUI_Thread.require {
      if (active) {
        pending = Some(body)
        pending_delay.invoke()
      }
    }

  def revoke(): Unit =
    GUI_Thread.require {
      pending = None
      pending_delay.revoke()
    }

  private lazy val reactivate_delay =
    GUI_Thread.delay_last(PIDE.options.seconds("jedit_tooltip_delay")) {
      active = true
    }

  private def deactivate(): Unit =
    GUI_Thread.require {
      revoke()
      active = false
      reactivate_delay.invoke()
    }


  /* dismiss */

  private lazy val focus_delay = GUI_Thread.delay_last(PIDE.options.seconds("editor_input_delay"))
  {
    dismiss_unfocused()
  }

  def dismiss_unfocused()
  {
    stack.span(tip => !tip.pretty_text_area.isFocusOwner) match {
      case (Nil, _) =>
      case (unfocused, rest) =>
        deactivate()
        unfocused.foreach(_.hide_popup)
        stack = rest
    }
  }

  def dismiss(tip: Pretty_Tooltip)
  {
    deactivate()
    hierarchy(tip) match {
      case Some((old, _ :: rest)) =>
        rest match {
          case top :: _ => top.request_focus
          case Nil => JEdit_Lib.request_focus_view()
        }
        old.foreach(_.hide_popup)
        tip.hide_popup
        stack = rest
      case _ =>
    }
  }

  def dismiss_descendant(parent: JComponent): Unit =
    descendant(parent).foreach(dismiss(_))

  def dismissed_all(): Boolean =
  {
    deactivate()
    if (stack.isEmpty) false
    else {
      JEdit_Lib.request_focus_view()
      stack.foreach(_.hide_popup)
      stack = Nil
      true
    }
  }
}


class Pretty_Tooltip private(
  view: View,
  layered: JLayeredPane,
  val original_parent: JComponent,
  location: Point,
  rendering: Rendering,
  private val results: Command.Results,
  private val info: Text.Info[XML.Body]) extends JPanel(new BorderLayout)
{
  tip =>

  GUI_Thread.require {}


  /* controls */

  private val close = new Label {
    icon = rendering.tooltip_close_icon
    tooltip = "Close tooltip window"
    listenTo(mouse.clicks)
    reactions += { case _: MouseClicked => Pretty_Tooltip.dismiss(tip) }
  }

  private val detach = new Label {
    icon = rendering.tooltip_detach_icon
    tooltip = "Detach tooltip window"
    listenTo(mouse.clicks)
    reactions += {
      case _: MouseClicked =>
        Info_Dockable(view, rendering.snapshot, results, info.info)
        Pretty_Tooltip.dismiss(tip)
    }
  }

  private val controls = new FlowPanel(FlowPanel.Alignment.Left)(close, detach) {
    background = rendering.tooltip_color
  }


  /* text area */

  val pretty_text_area =
    new Pretty_Text_Area(view, () => Pretty_Tooltip.dismiss(tip), true) {
      override def get_background() = Some(rendering.tooltip_color)
    }

  pretty_text_area.addFocusListener(new FocusAdapter {
    override def focusGained(e: FocusEvent)
    {
      tip_border(true)
      Pretty_Tooltip.focus_delay.invoke()
    }
    override def focusLost(e: FocusEvent)
    {
      tip_border(false)
      Pretty_Tooltip.focus_delay.invoke()
    }
  })

  pretty_text_area.resize(Font_Info.main(PIDE.options.real("jedit_popup_font_scale")))


  /* main content */

  def tip_border(has_focus: Boolean)
  {
    tip.setBorder(new LineBorder(if (has_focus) Color.BLACK else Color.GRAY))
    tip.repaint()
  }
  tip_border(true)

  override def getFocusTraversalKeysEnabled = false
  tip.setBackground(rendering.tooltip_color)
  tip.add(controls.peer, BorderLayout.NORTH)
  tip.add(pretty_text_area)


  /* popup */

  private val popup =
  {
    val screen = JEdit_Lib.screen_location(layered, location)
    val size =
    {
      val bounds = Rendering.popup_bounds

      val w_max = layered.getWidth min (screen.bounds.width * bounds).toInt
      val h_max = layered.getHeight min (screen.bounds.height * bounds).toInt

      val painter = pretty_text_area.getPainter
      val geometry = JEdit_Lib.window_geometry(tip, painter)
      val metric = JEdit_Lib.pretty_metric(painter)

      val margin =
        ((rendering.tooltip_margin * metric.average) min
          ((w_max - geometry.deco_width) / metric.unit).toInt) max 20

      val formatted = Pretty.formatted(info.info, margin, metric)
      val lines =
        XML.traverse_text(formatted)(0)(
          (n: Int, s: String) => n + s.iterator.filter(_ == '\n').length)

      val h = painter.getLineHeight * (lines + 1) + geometry.deco_height
      val margin1 =
        if (h <= h_max)
          (0.0 /: split_lines(XML.content(formatted)))({ case (m, line) => m max metric(line) })
        else margin
      val w = (metric.unit * (margin1 + metric.average)).round.toInt + geometry.deco_width

      new Dimension(w min w_max, h min h_max)
    }
    new Popup(layered, tip, screen.relative(layered, size), size)
  }

  private def show_popup
  {
    popup.show
    pretty_text_area.requestFocus
    pretty_text_area.update(rendering.snapshot, results, info.info)
  }

  private def hide_popup: Unit = popup.hide

  private def request_focus: Unit = pretty_text_area.requestFocus
}

