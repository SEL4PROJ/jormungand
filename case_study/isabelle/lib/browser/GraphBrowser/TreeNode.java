/***************************************************************************
  Title:      GraphBrowser/TreeNode.java
  Author:     Stefan Berghofer, TU Muenchen
  Options:    :tabSize=4:

  This class contains methods for storing and manipulating directory
  trees (e.g. collapsing / uncollapsing directory branches).
***************************************************************************/

package GraphBrowser;

import java.awt.*;
import java.util.*;


public class TreeNode
{
	int starty,endy,number;
	String name,path;

	Vector leaves=new Vector(10,10);
	boolean unfold=false;

	public void insertNode(String n,String d,String p,int num,boolean u) {
		if (d.length()==0) {
			leaves.addElement(new TreeNode(n,p,num));
			unfold=unfold||u;
		} else {
			unfold=unfold||u;
			String str1,str2;
			if (d.indexOf('/')<0) {
				str1=d;str2="";
			} else {
				str1=d.substring(0,d.indexOf('/'));
				str2=d.substring(d.indexOf('/')+1);
			}

			Enumeration e1=leaves.elements();
			TreeNode nd=null;

			while (e1.hasMoreElements()) {
				TreeNode nd2=(TreeNode)(e1.nextElement());
				if (nd2.name.equals(str1)) {
					nd=nd2;break;
				}
			}
			if (nd==null) {
				nd=new TreeNode(str1,"",-1);
				leaves.addElement(nd);
			}
			nd.insertNode(n,str2,p,num,u);
		}
	}

	public TreeNode(String n,String p,int num) {
		name=n;
		path=p;
		number=num;
	}

	public TreeNode(String n,String p,int num,boolean u) {
		this(n,p,num);
		unfold=u;
	}	

	public int getNumber() { return number; }

	public TreeNode lookup(int y)
	{
		if (y>=starty && y<endy) return this;
		else
		if (unfold)
			for (int i=0;i<leaves.size();i++)
			{
				TreeNode t=((TreeNode)leaves.elementAt(i)).lookup(y);
				if (t!=null) return t;
			}
		return null;
	}

	public boolean select()
	{
		if (!leaves.isEmpty()) {
			if (unfold) collapse();
			else unfold=true;
			return true;
		}
		return false; 
	}

	public void collapse()
	{
		unfold=false;
		/*
		for(int i=0;i<leaves.size();i++)
			((Tree)leaves.elementAt(i)).collapse();
		*/
	}

	void collapsedNodes(Vector v) {
		if (number>=0) v.addElement(new Integer(number));
		Enumeration e1=leaves.elements();
		while (e1.hasMoreElements())
			((TreeNode)(e1.nextElement())).collapsedNodes(v);
	}

	public void collapsedDirectories(Vector v) {
		if (!unfold) {
			Vector v2=new Vector(10,10);
			v.addElement(new Directory(this,name,v2));
			collapsedNodes(v2);
		} else {
			Enumeration e1=leaves.elements();
			while (e1.hasMoreElements()) {
				TreeNode tn=(TreeNode)(e1.nextElement());
				if (!tn.leaves.isEmpty())
					tn.collapsedDirectories(v);
			}
		}
	}

	public Dimension draw(Graphics g,int x,int y,TreeNode t)
	{
		FontMetrics fm=g.getFontMetrics(g.getFont());
		int h=fm.getHeight();
		int e=(int) (h / 10) + 1;
		int down_x[]={x + e, x + h - e, x + (int)(h / 2)};
		int down_y[]={y + e, y + e, y + (int)(3 * h / 4) - e};
		int right_x[]={x + e, x + (int)(3 * h / 4) - e, x + e};
		int right_y[]={y + e, y + (int)(h / 2), y + h - e};
		int dx=0;

		if (unfold)
		{
			g.setColor(Color.green);
			g.fillPolygon(down_x,down_y,3);
			g.setColor(Color.black);
			g.drawString(name,x+h+4,y+fm.getAscent());
			starty=y;endy=y+h;
			dx=Math.max(dx,x+h+4+fm.stringWidth(name));
			y+=h+5;
			for(int i=0;i<leaves.size();i++)
			{
				Dimension d=((TreeNode)leaves.elementAt(i)).draw(g,x+h+4,y,t);
				y=d.height;
				dx=Math.max(dx,d.width);
			}
		}
		else
		{
			g.setColor(leaves.isEmpty() ? Color.blue : Color.red);
			g.fillPolygon(right_x,right_y,3);
			if (this==t && leaves.isEmpty())
			{
				g.setColor(Color.white);
				g.fillRect(x+h+4,y,fm.stringWidth(name),h);
			}
			g.setColor(Color.black);
			g.drawString(name,x+h+4,y+fm.getAscent());
			starty=y;endy=y+h;
			dx=Math.max(dx,x+h+4+fm.stringWidth(name));
			y+=h+5;
		}
		return new Dimension(dx,y);
	}
}


