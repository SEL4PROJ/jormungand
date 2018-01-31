/***************************************************************************
  Title:      GraphBrowser/Vertex.java
  Author:     Stefan Berghofer, TU Muenchen
  Options:    :tabSize=4:

  This class contains attributes and methods common to all kinds of
  vertices (e.g. coordinates, successors, predecessors).
***************************************************************************/

package GraphBrowser;

import java.util.*;
import java.awt.*;
import java.io.*;

abstract class Vertex {
	Vector children=new Vector(10,10);
	Vector parents=new Vector(10,10);
	int degree=0;
	int number=-1;
	double weight=0;
	int x,y;
	Graph gra;

	public abstract Object clone();

	public void setGraph(Graph g) { gra=g; }

	public int countChildren() { return children.size(); }

	/** getInflate returns a vector of vertices which get **/
	/** inflated again if the user clicks on this vertex  **/

	public void setInflate(Vector v) {}

	public Vector getInflate() { return null; }

	/** getUp returns a vector of vertices which get inflated   **/
	/** again, if the user clicks on this vertex's upward arrow **/

	public Vector getUp() { return null; }

	public void setUp(Vector v) {}

	/** getUp returns a vector of vertices which get inflated     **/
	/** again, if the user clicks on this vertex's downward arrow **/

	public Vector getDown() { return null; }

	public void setDown(Vector v) {}

	/** internal number, for decoding / encoding etc. **/

	public int getNumber() { return number; }

	public void setNumber(int n) { number=n; }

	public String getLabel() {return "";}

	public void setLabel(String s) {}

	/** unique identifier **/

	public String getID() {return "";}

	public void setID(String s) {}

	public Box getLabelSize(Graphics g) {
		AbstractFontMetrics fm = g == null ? 
      (AbstractFontMetrics) new DefaultFontMetrics(12) : 
      (AbstractFontMetrics) new AWTFontMetrics(g.getFontMetrics(g.getFont()));
		
		return new Box(Math.max(fm.stringWidth("[. . . .]"),
                            fm.stringWidth(getLabel())),
                   fm.getAscent()+fm.getDescent());
	}
		
	public String getPath() { return "";}

	public void setPath(String p) {}

	public String getDir() { return ""; }

	public void setDir(String d) {}

	public void setWeight(double w) {weight=w;}

	public double getWeight() {return weight;}

	public void setDegree(int d) { degree=d; }

	public int getDegree() { return degree; }

	public boolean isDummy() { return false; }

	public Enumeration getChildren() {
		return ((Vector)(children.clone())).elements();
	}

	public void addChild(Vertex v) {
		children.addElement(v);
		v.parents.addElement(this);
	}

	public void removeChild(Vertex v) {
		children.removeElement(v);
		v.parents.removeElement(this);
	}

	public boolean isChild(Vertex v) {
		return children.indexOf(v)>=0;
	}

	public boolean isParent(Vertex v) {
		return parents.indexOf(v)>=0;
	}

	public Enumeration getParents() {
		return ((Vector)(parents.clone())).elements();
	}

	public void addParent(Vertex v) {
		parents.addElement(v);
		v.children.addElement(this);
	}

	public void removeParent(Vertex v) {
		parents.removeElement(v);
		v.children.removeElement(this);
	}

	/********************************************************************/
	/*                   get all predecessor vertices                   */
	/********************************************************************/

	public Vector getPreds() {
	    Vector preds=new Vector(10,10);
	    Vector todo=(Vector)(parents.clone());
	    Vertex vx1,vx2;
	    Enumeration e;

	    while (!todo.isEmpty()) {
		vx1=(Vertex)(todo.lastElement());
		todo.removeElementAt(todo.size()-1);
		preds.addElement(vx1);
		e=vx1.parents.elements();
		while (e.hasMoreElements()) {
		    vx2=(Vertex)(e.nextElement());
		    if (preds.indexOf(vx2)<0 && todo.indexOf(vx2)<0)
			todo.addElement(vx2);
		}
	    }

	    return preds;
	}

	/********************************************************************/
	/*                     get all successor vertices                   */
	/********************************************************************/

	public Vector getSuccs() {
	    Vector succs=new Vector(10,10);
	    Vector todo=(Vector)(children.clone());
	    Vertex vx1,vx2;
	    Enumeration e;

	    while (!todo.isEmpty()) {
		vx1=(Vertex)(todo.lastElement());
		todo.removeElementAt(todo.size()-1);
		succs.addElement(vx1);
		e=vx1.children.elements();
		while (e.hasMoreElements()) {
		    vx2=(Vertex)(e.nextElement());
		    if (succs.indexOf(vx2)<0 && todo.indexOf(vx2)<0)
			todo.addElement(vx2);
		}
	    }

	    return succs;
	}

	public int box_width() { return getLabelSize(gra.gfx).width+8; }

	public int box_width2() { return box_width()/2; }

	public void setX(int x) {this.x=x;}

	public void setY(int y) {this.y=y;}

	public int getX() {return x;}

	public int getY() {return y;}

	public abstract int leftX();

	public abstract int rightX();

	public abstract void draw(Graphics g);

	public void drawButtons(Graphics g) {}

	public void drawBox(Graphics g,Color boxColor) {}

	public void removeButtons(Graphics g) {}

	public boolean contains(int x,int y) { return false; }

	public boolean leftButton(int x,int y) { return false; }

	public boolean rightButton(int x,int y) { return false; }

	public void PS(PrintWriter p) {}
}
