(*<*)
theory simp imports Main begin
(*>*)

subsection{*Simplification Rules*}

text{*\index{simplification rules}
To facilitate simplification,  
the attribute @{text"[simp]"}\index{*simp (attribute)}
declares theorems to be simplification rules, which the simplifier
will use automatically.  In addition, \isacommand{datatype} and
\isacommand{primrec} declarations (and a few others) 
implicitly declare some simplification rules.  
Explicit definitions are \emph{not} declared as 
simplification rules automatically!

Nearly any theorem can become a simplification
rule. The simplifier will try to transform it into an equation.  
For example, the theorem
@{prop"~P"} is turned into @{prop"P = False"}. The details
are explained in \S\ref{sec:SimpHow}.

The simplification attribute of theorems can be turned on and off:%
\index{*simp del (attribute)}
\begin{quote}
\isacommand{declare} \textit{theorem-name}@{text"[simp]"}\\
\isacommand{declare} \textit{theorem-name}@{text"[simp del]"}
\end{quote}
Only equations that really simplify, like \isa{rev\
{\isacharparenleft}rev\ xs{\isacharparenright}\ {\isacharequal}\ xs} and
\isa{xs\ {\isacharat}\ {\isacharbrackleft}{\isacharbrackright}\
{\isacharequal}\ xs}, should be declared as default simplification rules. 
More specific ones should only be used selectively and should
not be made default.  Distributivity laws, for example, alter
the structure of terms and can produce an exponential blow-up instead of
simplification.  A default simplification rule may
need to be disabled in certain proofs.  Frequent changes in the simplification
status of a theorem may indicate an unwise use of defaults.
\begin{warn}
  Simplification can run forever, for example if both $f(x) = g(x)$ and
  $g(x) = f(x)$ are simplification rules. It is the user's responsibility not
  to include simplification rules that can lead to nontermination, either on
  their own or in combination with other simplification rules.
\end{warn}
\begin{warn}
  It is inadvisable to toggle the simplification attribute of a
  theorem from a parent theory $A$ in a child theory $B$ for good.
  The reason is that if some theory $C$ is based both on $B$ and (via a
  different path) on $A$, it is not defined what the simplification attribute
  of that theorem will be in $C$: it could be either.
\end{warn}
*} 

subsection{*The {\tt\slshape simp}  Method*}

text{*\index{*simp (method)|bold}
The general format of the simplification method is
\begin{quote}
@{text simp} \textit{list of modifiers}
\end{quote}
where the list of \emph{modifiers} fine tunes the behaviour and may
be empty. Specific modifiers are discussed below.  Most if not all of the
proofs seen so far could have been performed
with @{text simp} instead of \isa{auto}, except that @{text simp} attacks
only the first subgoal and may thus need to be repeated --- use
\methdx{simp_all} to simplify all subgoals.
If nothing changes, @{text simp} fails.
*}

subsection{*Adding and Deleting Simplification Rules*}

text{*
\index{simplification rules!adding and deleting}%
If a certain theorem is merely needed in a few proofs by simplification,
we do not need to make it a global simplification rule. Instead we can modify
the set of simplification rules used in a simplification step by adding rules
to it and/or deleting rules from it. The two modifiers for this are
\begin{quote}
@{text"add:"} \textit{list of theorem names}\index{*add (modifier)}\\
@{text"del:"} \textit{list of theorem names}\index{*del (modifier)}
\end{quote}
Or you can use a specific list of theorems and omit all others:
\begin{quote}
@{text"only:"} \textit{list of theorem names}\index{*only (modifier)}
\end{quote}
In this example, we invoke the simplifier, adding two distributive
laws:
\begin{quote}
\isacommand{apply}@{text"(simp add: mod_mult_distrib add_mult_distrib)"}
\end{quote}
*}

subsection{*Assumptions*}

text{*\index{simplification!with/of assumptions}
By default, assumptions are part of the simplification process: they are used
as simplification rules and are simplified themselves. For example:
*}

lemma "\<lbrakk> xs @ zs = ys @ xs; [] @ xs = [] @ [] \<rbrakk> \<Longrightarrow> ys = zs"
apply simp
done

text{*\noindent
The second assumption simplifies to @{term"xs = []"}, which in turn
simplifies the first assumption to @{term"zs = ys"}, thus reducing the
conclusion to @{term"ys = ys"} and hence to @{term"True"}.

In some cases, using the assumptions can lead to nontermination:
*}

lemma "\<forall>x. f x = g (f (g x)) \<Longrightarrow> f [] = f [] @ []"

txt{*\noindent
An unmodified application of @{text"simp"} loops.  The culprit is the
simplification rule @{term"f x = g (f (g x))"}, which is extracted from
the assumption.  (Isabelle notices certain simple forms of
nontermination but not this one.)  The problem can be circumvented by
telling the simplifier to ignore the assumptions:
*}

apply(simp (no_asm))
done

text{*\noindent
Three modifiers influence the treatment of assumptions:
\begin{description}
\item[@{text"(no_asm)"}]\index{*no_asm (modifier)}
 means that assumptions are completely ignored.
\item[@{text"(no_asm_simp)"}]\index{*no_asm_simp (modifier)}
 means that the assumptions are not simplified but
  are used in the simplification of the conclusion.
\item[@{text"(no_asm_use)"}]\index{*no_asm_use (modifier)}
 means that the assumptions are simplified but are not
  used in the simplification of each other or the conclusion.
\end{description}
Only one of the modifiers is allowed, and it must precede all
other modifiers.
%\begin{warn}
%Assumptions are simplified in a left-to-right fashion. If an
%assumption can help in simplifying one to the left of it, this may get
%overlooked. In such cases you have to rotate the assumptions explicitly:
%\isacommand{apply}@ {text"("}\methdx{rotate_tac}~$n$@ {text")"}
%causes a cyclic shift by $n$ positions from right to left, if $n$ is
%positive, and from left to right, if $n$ is negative.
%Beware that such rotations make proofs quite brittle.
%\end{warn}
*}

subsection{*Rewriting with Definitions*}

text{*\label{sec:Simp-with-Defs}\index{simplification!with definitions}
Constant definitions (\S\ref{sec:ConstDefinitions}) can be used as
simplification rules, but by default they are not: the simplifier does not
expand them automatically.  Definitions are intended for introducing abstract
concepts and not merely as abbreviations.  Of course, we need to expand
the definition initially, but once we have proved enough abstract properties
of the new constant, we can forget its original definition.  This style makes
proofs more robust: if the definition has to be changed,
only the proofs of the abstract properties will be affected.

For example, given *}

definition xor :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
"xor A B \<equiv> (A \<and> \<not>B) \<or> (\<not>A \<and> B)"

text{*\noindent
we may want to prove
*}

lemma "xor A (\<not>A)"

txt{*\noindent
Typically, we begin by unfolding some definitions:
\indexbold{definitions!unfolding}
*}

apply(simp only: xor_def)

txt{*\noindent
In this particular case, the resulting goal
@{subgoals[display,indent=0]}
can be proved by simplification. Thus we could have proved the lemma outright by
*}(*<*)oops lemma "xor A (\<not>A)"(*>*)
apply(simp add: xor_def)
(*<*)done(*>*)
text{*\noindent
Of course we can also unfold definitions in the middle of a proof.

\begin{warn}
  If you have defined $f\,x\,y~\isasymequiv~t$ then you can only unfold
  occurrences of $f$ with at least two arguments. This may be helpful for unfolding
  $f$ selectively, but it may also get in the way. Defining
  $f$~\isasymequiv~\isasymlambda$x\,y.\;t$ allows to unfold all occurrences of $f$.
\end{warn}

There is also the special method \isa{unfold}\index{*unfold (method)|bold}
which merely unfolds
one or several definitions, as in \isacommand{apply}\isa{(unfold xor_def)}.
This is can be useful in situations where \isa{simp} does too much.
Warning: \isa{unfold} acts on all subgoals!
*}

subsection{*Simplifying {\tt\slshape let}-Expressions*}

text{*\index{simplification!of \isa{let}-expressions}\index{*let expressions}%
Proving a goal containing \isa{let}-expressions almost invariably requires the
@{text"let"}-con\-structs to be expanded at some point. Since
@{text"let"}\ldots\isa{=}\ldots@{text"in"}{\ldots} is just syntactic sugar for
the predefined constant @{term"Let"}, expanding @{text"let"}-constructs
means rewriting with \tdx{Let_def}: *}

lemma "(let xs = [] in xs@ys@xs) = ys"
apply(simp add: Let_def)
done

text{*
If, in a particular context, there is no danger of a combinatorial explosion
of nested @{text"let"}s, you could even simplify with @{thm[source]Let_def} by
default:
*}
declare Let_def [simp]

subsection{*Conditional Simplification Rules*}

text{*
\index{conditional simplification rules}%
So far all examples of rewrite rules were equations. The simplifier also
accepts \emph{conditional} equations, for example
*}

lemma hd_Cons_tl[simp]: "xs \<noteq> []  \<Longrightarrow>  hd xs # tl xs = xs"
apply(case_tac xs, simp, simp)
done

text{*\noindent
Note the use of ``\ttindexboldpos{,}{$Isar}'' to string together a
sequence of methods. Assuming that the simplification rule
@{term"(rev xs = []) = (xs = [])"}
is present as well,
the lemma below is proved by plain simplification:
*}

lemma "xs \<noteq> [] \<Longrightarrow> hd(rev xs) # tl(rev xs) = rev xs"
(*<*)
by(simp)
(*>*)
text{*\noindent
The conditional equation @{thm[source]hd_Cons_tl} above
can simplify @{term"hd(rev xs) # tl(rev xs)"} to @{term"rev xs"}
because the corresponding precondition @{term"rev xs ~= []"}
simplifies to @{term"xs ~= []"}, which is exactly the local
assumption of the subgoal.
*}


subsection{*Automatic Case Splits*}

text{*\label{sec:AutoCaseSplits}\indexbold{case splits}%
Goals containing @{text"if"}-expressions\index{*if expressions!splitting of}
are usually proved by case
distinction on the boolean condition.  Here is an example:
*}

lemma "\<forall>xs. if xs = [] then rev xs = [] else rev xs \<noteq> []"

txt{*\noindent
The goal can be split by a special method, \methdx{split}:
*}

apply(split if_split)

txt{*\noindent
@{subgoals[display,indent=0]}
where \tdx{if_split} is a theorem that expresses splitting of
@{text"if"}s. Because
splitting the @{text"if"}s is usually the right proof strategy, the
simplifier does it automatically.  Try \isacommand{apply}@{text"(simp)"}
on the initial goal above.

This splitting idea generalizes from @{text"if"} to \sdx{case}.
Let us simplify a case analysis over lists:\index{*list.split (theorem)}
*}(*<*)by simp(*>*)
lemma "(case xs of [] \<Rightarrow> zs | y#ys \<Rightarrow> y#(ys@zs)) = xs@zs"
apply(split list.split)
 
txt{*
@{subgoals[display,indent=0]}
The simplifier does not split
@{text"case"}-expressions, as it does @{text"if"}-expressions, 
because with recursive datatypes it could lead to nontermination.
Instead, the simplifier has a modifier
@{text split}\index{*split (modifier)} 
for adding splitting rules explicitly.  The
lemma above can be proved in one step by
*}
(*<*)oops
lemma "(case xs of [] \<Rightarrow> zs | y#ys \<Rightarrow> y#(ys@zs)) = xs@zs"
(*>*)
apply(simp split: list.split)
(*<*)done(*>*)
text{*\noindent
whereas \isacommand{apply}@{text"(simp)"} alone will not succeed.

Every datatype $t$ comes with a theorem
$t$@{text".split"} which can be declared to be a \bfindex{split rule} either
locally as above, or by giving it the \attrdx{split} attribute globally:
*}

declare list.split [split]

text{*\noindent
The @{text"split"} attribute can be removed with the @{text"del"} modifier,
either locally
*}
(*<*)
lemma "dummy=dummy"
(*>*)
apply(simp split del: if_split)
(*<*)
oops
(*>*)
text{*\noindent
or globally:
*}
declare list.split [split del]

text{*
Polished proofs typically perform splitting within @{text simp} rather than 
invoking the @{text split} method.  However, if a goal contains
several @{text "if"} and @{text case} expressions, 
the @{text split} method can be
helpful in selectively exploring the effects of splitting.

The split rules shown above are intended to affect only the subgoal's
conclusion.  If you want to split an @{text"if"} or @{text"case"}-expression
in the assumptions, you have to apply \tdx{if_split_asm} or
$t$@{text".split_asm"}: *}

lemma "if xs = [] then ys \<noteq> [] else ys = [] \<Longrightarrow> xs @ ys \<noteq> []"
apply(split if_split_asm)

txt{*\noindent
Unlike splitting the conclusion, this step creates two
separate subgoals, which here can be solved by @{text"simp_all"}:
@{subgoals[display,indent=0]}
If you need to split both in the assumptions and the conclusion,
use $t$@{text".splits"} which subsumes $t$@{text".split"} and
$t$@{text".split_asm"}. Analogously, there is @{thm[source]if_splits}.

\begin{warn}
  The simplifier merely simplifies the condition of an 
  \isa{if}\index{*if expressions!simplification of} but not the
  \isa{then} or \isa{else} parts. The latter are simplified only after the
  condition reduces to \isa{True} or \isa{False}, or after splitting. The
  same is true for \sdx{case}-expressions: only the selector is
  simplified at first, until either the expression reduces to one of the
  cases or it is split.
\end{warn}
*}
(*<*)
by(simp_all)
(*>*)

subsection{*Tracing*}
text{*\indexbold{tracing the simplifier}
Using the simplifier effectively may take a bit of experimentation.  Set the
Proof General flag \pgmenu{Isabelle} $>$ \pgmenu{Settings} $>$ \pgmenu{Trace Simplifier} to get a better idea of what is going on:
*}

lemma "rev [a] = []"
apply(simp)
(*<*)oops(*>*)

text{*\noindent
produces the following trace in Proof General's \pgmenu{Trace} buffer:

\begin{ttbox}\makeatother
[1]Applying instance of rewrite rule "List.rev.simps_2":
rev (?x1 # ?xs1) \(\equiv\) rev ?xs1 @ [?x1]

[1]Rewriting:
rev [a] \(\equiv\) rev [] @ [a]

[1]Applying instance of rewrite rule "List.rev.simps_1":
rev [] \(\equiv\) []

[1]Rewriting:
rev [] \(\equiv\) []

[1]Applying instance of rewrite rule "List.op @.append_Nil":
[] @ ?y \(\equiv\) ?y

[1]Rewriting:
[] @ [a] \(\equiv\) [a]

[1]Applying instance of rewrite rule
?x2 # ?t1 = ?t1 \(\equiv\) False

[1]Rewriting:
[a] = [] \(\equiv\) False
\end{ttbox}
The trace lists each rule being applied, both in its general form and
the instance being used. The \texttt{[}$i$\texttt{]} in front (where
above $i$ is always \texttt{1}) indicates that we are inside the $i$th
invocation of the simplifier. Each attempt to apply a
conditional rule shows the rule followed by the trace of the
(recursive!) simplification of the conditions, the latter prefixed by
\texttt{[}$i+1$\texttt{]} instead of \texttt{[}$i$\texttt{]}.
Another source of recursive invocations of the simplifier are
proofs of arithmetic formulae. By default, recursive invocations are not shown,
you must increase the trace depth via \pgmenu{Isabelle} $>$ \pgmenu{Settings} $>$ \pgmenu{Trace Simplifier Depth}.

Many other hints about the simplifier's actions may appear.

In more complicated cases, the trace can be very lengthy.  Thus it is
advisable to reset the \pgmenu{Trace Simplifier} flag after having
obtained the desired trace.
Since this is easily forgotten (and may have the unpleasant effect of
swamping the interface with trace information), here is how you can switch
the trace on locally in a proof: *}

(*<*)lemma "x=x"
(*>*)
using [[simp_trace=true]]
apply simp
(*<*)oops(*>*)

text{* \noindent
Within the current proof, all simplifications in subsequent proof steps
will be traced, but the text reminds you to remove the \isa{using} clause
after it has done its job. *}

subsection{*Finding Theorems\label{sec:find}*}

text{*\indexbold{finding theorems}\indexbold{searching theorems}
Isabelle's large database of proved theorems 
offers a powerful search engine. Its chief limitation is
its restriction to the theories currently loaded.

\begin{pgnote}
The search engine is started by clicking on Proof General's \pgmenu{Find} icon.
You specify your search textually in the input buffer at the bottom
of the window.
\end{pgnote}

The simplest form of search finds theorems containing specified
patterns.  A pattern can be any term (even
a single identifier).  It may contain ``\texttt{\_}'', a wildcard standing
for any term. Here are some
examples:
\begin{ttbox}
length
"_ # _ = _ # _"
"_ + _"
"_ * (_ - (_::nat))"
\end{ttbox}
Specifying types, as shown in the last example, 
constrains searches involving overloaded operators.

\begin{warn}
Always use ``\texttt{\_}'' rather than variable names: searching for
\texttt{"x + y"} will usually not find any matching theorems
because they would need to contain \texttt{x} and~\texttt{y} literally.
When searching for infix operators, do not just type in the symbol,
such as~\texttt{+}, but a proper term such as \texttt{"_ + _"}.
This remark applies to more complicated syntaxes, too.
\end{warn}

If you are looking for rewrite rules (possibly conditional) that could
simplify some term, prefix the pattern with \texttt{simp:}.
\begin{ttbox}
simp: "_ * (_ + _)"
\end{ttbox}
This finds \emph{all} equations---not just those with a \isa{simp} attribute---whose conclusion has the form
@{text[display]"_ * (_ + _) = \<dots>"}
It only finds equations that can simplify the given pattern
at the root, not somewhere inside: for example, equations of the form
@{text"_ + _ = \<dots>"} do not match.

You may also search for theorems by name---you merely
need to specify a substring. For example, you could search for all
commutativity theorems like this:
\begin{ttbox}
name: comm
\end{ttbox}
This retrieves all theorems whose name contains \texttt{comm}.

Search criteria can also be negated by prefixing them with ``\texttt{-}''.
For example,
\begin{ttbox}
-name: List
\end{ttbox}
finds theorems whose name does not contain \texttt{List}. You can use this
to exclude particular theories from the search: the long name of
a theorem contains the name of the theory it comes from.

Finallly, different search criteria can be combined arbitrarily. 
The effect is conjuctive: Find returns the theorems that satisfy all of
the criteria. For example,
\begin{ttbox}
"_ + _"  -"_ - _"  -simp: "_ * (_ + _)"  name: assoc
\end{ttbox}
looks for theorems containing plus but not minus, and which do not simplify
\mbox{@{text"_ * (_ + _)"}} at the root, and whose name contains \texttt{assoc}.

Further search criteria are explained in \S\ref{sec:find2}.

\begin{pgnote}
Proof General keeps a history of all your search expressions.
If you click on \pgmenu{Find}, you can use the arrow keys to scroll
through previous searches and just modify them. This saves you having
to type in lengthy expressions again and again.
\end{pgnote}
*}
(*<*)
end
(*>*)
