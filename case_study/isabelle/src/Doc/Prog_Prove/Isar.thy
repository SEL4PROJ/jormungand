(*<*)
theory Isar
imports LaTeXsugar
begin
declare [[quick_and_dirty]]
(*>*)
text{*
Apply-scripts are unreadable and hard to maintain. The language of choice
for larger proofs is \concept{Isar}. The two key features of Isar are:
\begin{itemize}
\item It is structured, not linear.
\item It is readable without its being run because
you need to state what you are proving at any given point.
\end{itemize}
Whereas apply-scripts are like assembly language programs, Isar proofs
are like structured programs with comments. A typical Isar proof looks like this:
*}text{*
\begin{tabular}{@ {}l}
\isacom{proof}\\
\quad\isacom{assume} @{text"\""}$\mathit{formula}_0$@{text"\""}\\
\quad\isacom{have} @{text"\""}$\mathit{formula}_1$@{text"\""} \quad\isacom{by} @{text simp}\\
\quad\vdots\\
\quad\isacom{have} @{text"\""}$\mathit{formula}_n$@{text"\""} \quad\isacom{by} @{text blast}\\
\quad\isacom{show} @{text"\""}$\mathit{formula}_{n+1}$@{text"\""} \quad\isacom{by} @{text \<dots>}\\
\isacom{qed}
\end{tabular}
*}text{*
It proves $\mathit{formula}_0 \Longrightarrow \mathit{formula}_{n+1}$
(provided each proof step succeeds).
The intermediate \isacom{have} statements are merely stepping stones
on the way towards the \isacom{show} statement that proves the actual
goal. In more detail, this is the Isar core syntax:
\medskip

\begin{tabular}{@ {}lcl@ {}}
\textit{proof} &=& \indexed{\isacom{by}}{by} \textit{method}\\
      &$\mid$& \indexed{\isacom{proof}}{proof} [\textit{method}] \ \textit{step}$^*$ \ \indexed{\isacom{qed}}{qed}
\end{tabular}
\medskip

\begin{tabular}{@ {}lcl@ {}}
\textit{step} &=& \indexed{\isacom{fix}}{fix} \textit{variables} \\
      &$\mid$& \indexed{\isacom{assume}}{assume} \textit{proposition} \\
      &$\mid$& [\indexed{\isacom{from}}{from} \textit{fact}$^+$] (\indexed{\isacom{have}}{have} $\mid$ \indexed{\isacom{show}}{show}) \ \textit{proposition} \ \textit{proof}
\end{tabular}
\medskip

\begin{tabular}{@ {}lcl@ {}}
\textit{proposition} &=& [\textit{name}:] @{text"\""}\textit{formula}@{text"\""}
\end{tabular}
\medskip

\begin{tabular}{@ {}lcl@ {}}
\textit{fact} &=& \textit{name} \ $\mid$ \ \dots
\end{tabular}
\medskip

\noindent A proof can either be an atomic \isacom{by} with a single proof
method which must finish off the statement being proved, for example @{text
auto},  or it can be a \isacom{proof}--\isacom{qed} block of multiple
steps. Such a block can optionally begin with a proof method that indicates
how to start off the proof, e.g., \mbox{@{text"(induction xs)"}}.

A step either assumes a proposition or states a proposition
together with its proof. The optional \isacom{from} clause
indicates which facts are to be used in the proof.
Intermediate propositions are stated with \isacom{have}, the overall goal
is stated with \isacom{show}. A step can also introduce new local variables with
\isacom{fix}. Logically, \isacom{fix} introduces @{text"\<And>"}-quantified
variables, \isacom{assume} introduces the assumption of an implication
(@{text"\<Longrightarrow>"}) and \isacom{have}/\isacom{show} introduce the conclusion.

Propositions are optionally named formulas. These names can be referred to in
later \isacom{from} clauses. In the simplest case, a fact is such a name.
But facts can also be composed with @{text OF} and @{text of} as shown in
\autoref{sec:forward-proof} --- hence the \dots\ in the above grammar.  Note
that assumptions, intermediate \isacom{have} statements and global lemmas all
have the same status and are thus collectively referred to as
\conceptidx{facts}{fact}.

Fact names can stand for whole lists of facts. For example, if @{text f} is
defined by command \isacom{fun}, @{text"f.simps"} refers to the whole list of
recursion equations defining @{text f}. Individual facts can be selected by
writing @{text"f.simps(2)"}, whole sublists by writing @{text"f.simps(2-4)"}.


\section{Isar by Example}

We show a number of proofs of Cantor's theorem that a function from a set to
its powerset cannot be surjective, illustrating various features of Isar. The
constant @{const surj} is predefined.
*}

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume 0: "surj f"
  from 0 have 1: "\<forall>A. \<exists>a. A = f a" by(simp add: surj_def)
  from 1 have 2: "\<exists>a. {x. x \<notin> f x} = f a" by blast
  from 2 show "False" by blast
qed

text{*
The \isacom{proof} command lacks an explicit method by which to perform
the proof. In such cases Isabelle tries to use some standard introduction
rule, in the above case for @{text"\<not>"}:
\[
\inferrule{
\mbox{@{thm (prem 1) notI}}}
{\mbox{@{thm (concl) notI}}}
\]
In order to prove @{prop"~ P"}, assume @{text P} and show @{text False}.
Thus we may assume @{prop"surj f"}. The proof shows that names of propositions
may be (single!) digits --- meaningful names are hard to invent and are often
not necessary. Both \isacom{have} steps are obvious. The second one introduces
the diagonal set @{term"{x. x \<notin> f x}"}, the key idea in the proof.
If you wonder why @{text 2} directly implies @{text False}: from @{text 2}
it follows that @{prop"a \<notin> f a \<longleftrightarrow> a \<in> f a"}.

\subsection{\indexed{@{text this}}{this}, \indexed{\isacom{then}}{then}, \indexed{\isacom{hence}}{hence} and \indexed{\isacom{thus}}{thus}}

Labels should be avoided. They interrupt the flow of the reader who has to
scan the context for the point where the label was introduced. Ideally, the
proof is a linear flow, where the output of one step becomes the input of the
next step, piping the previously proved fact into the next proof, like
in a UNIX pipe. In such cases the predefined name @{text this} can be used
to refer to the proposition proved in the previous step. This allows us to
eliminate all labels from our proof (we suppress the \isacom{lemma} statement):
*}
(*<*)
lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
(*>*)
proof
  assume "surj f"
  from this have "\<exists>a. {x. x \<notin> f x} = f a" by(auto simp: surj_def)
  from this show "False" by blast
qed

text{* We have also taken the opportunity to compress the two \isacom{have}
steps into one.

To compact the text further, Isar has a few convenient abbreviations:
\medskip

\begin{tabular}{r@ {\quad=\quad}l}
\isacom{then} & \isacom{from} @{text this}\\
\isacom{thus} & \isacom{then} \isacom{show}\\
\isacom{hence} & \isacom{then} \isacom{have}
\end{tabular}
\medskip

\noindent
With the help of these abbreviations the proof becomes
*}
(*<*)
lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
(*>*)
proof
  assume "surj f"
  hence "\<exists>a. {x. x \<notin> f x} = f a" by(auto simp: surj_def)
  thus "False" by blast
qed
text{*

There are two further linguistic variations:
\medskip

\begin{tabular}{r@ {\quad=\quad}l}
(\isacom{have}$\mid$\isacom{show}) \ \textit{prop} \ \indexed{\isacom{using}}{using} \ \textit{facts}
&
\isacom{from} \ \textit{facts} \ (\isacom{have}$\mid$\isacom{show}) \ \textit{prop}\\
\indexed{\isacom{with}}{with} \ \textit{facts} & \isacom{from} \ \textit{facts} \isa{this}
\end{tabular}
\medskip

\noindent The \isacom{using} idiom de-emphasizes the used facts by moving them
behind the proposition.

\subsection{Structured Lemma Statements: \indexed{\isacom{fixes}}{fixes}, \indexed{\isacom{assumes}}{assumes}, \indexed{\isacom{shows}}{shows}}
\index{lemma@\isacom{lemma}}
Lemmas can also be stated in a more structured fashion. To demonstrate this
feature with Cantor's theorem, we rephrase @{prop"\<not> surj f"}
a little:
*}

lemma
  fixes f :: "'a \<Rightarrow> 'a set"
  assumes s: "surj f"
  shows "False"

txt{* The optional \isacom{fixes} part allows you to state the types of
variables up front rather than by decorating one of their occurrences in the
formula with a type constraint. The key advantage of the structured format is
the \isacom{assumes} part that allows you to name each assumption; multiple
assumptions can be separated by \isacom{and}. The
\isacom{shows} part gives the goal. The actual theorem that will come out of
the proof is @{prop"surj f \<Longrightarrow> False"}, but during the proof the assumption
@{prop"surj f"} is available under the name @{text s} like any other fact.
*}

proof -
  have "\<exists> a. {x. x \<notin> f x} = f a" using s
    by(auto simp: surj_def)
  thus "False" by blast
qed

text{*
\begin{warn}
Note the hyphen after the \isacom{proof} command.
It is the null method that does nothing to the goal. Leaving it out would be asking
Isabelle to try some suitable introduction rule on the goal @{const False} --- but
there is no such rule and \isacom{proof} would fail.
\end{warn}
In the \isacom{have} step the assumption @{prop"surj f"} is now
referenced by its name @{text s}. The duplication of @{prop"surj f"} in the
above proofs (once in the statement of the lemma, once in its proof) has been
eliminated.

Stating a lemma with \isacom{assumes}-\isacom{shows} implicitly introduces the
name \indexed{@{text assms}}{assms} that stands for the list of all assumptions. You can refer
to individual assumptions by @{text"assms(1)"}, @{text"assms(2)"}, etc.,
thus obviating the need to name them individually.

\section{Proof Patterns}

We show a number of important basic proof patterns. Many of them arise from
the rules of natural deduction that are applied by \isacom{proof} by
default. The patterns are phrased in terms of \isacom{show} but work for
\isacom{have} and \isacom{lemma}, too.

We start with two forms of \concept{case analysis}:
starting from a formula @{text P} we have the two cases @{text P} and
@{prop"~P"}, and starting from a fact @{prop"P \<or> Q"}
we have the two cases @{text P} and @{text Q}:
*}text_raw{*
\begin{tabular}{@ {}ll@ {}}
\begin{minipage}[t]{.4\textwidth}
\isa{%
*}
(*<*)lemma "R" proof-(*>*)
show "R"
proof cases
  assume "P"
  text_raw{*\\\mbox{}\quad$\vdots$\\\mbox{}\hspace{-1.4ex}*}
  show "R" (*<*)sorry(*>*)text_raw{*\ $\dots$\\*}
next
  assume "\<not> P"
  text_raw{*\\\mbox{}\quad$\vdots$\\\mbox{}\hspace{-1.4ex}*}
  show "R" (*<*)sorry(*>*)text_raw{*\ $\dots$\\*}
qed(*<*)oops(*>*)
text_raw {* }
\end{minipage}\index{cases@@{text cases}}
&
\begin{minipage}[t]{.4\textwidth}
\isa{%
*}
(*<*)lemma "R" proof-(*>*)
have "P \<or> Q" (*<*)sorry(*>*)text_raw{*\ $\dots$\\*}
then show "R"
proof
  assume "P"
  text_raw{*\\\mbox{}\quad$\vdots$\\\mbox{}\hspace{-1.4ex}*}
  show "R" (*<*)sorry(*>*)text_raw{*\ $\dots$\\*}
next
  assume "Q"
  text_raw{*\\\mbox{}\quad$\vdots$\\\mbox{}\hspace{-1.4ex}*}
  show "R" (*<*)sorry(*>*)text_raw{*\ $\dots$\\*}
qed(*<*)oops(*>*)

text_raw {* }
\end{minipage}
\end{tabular}
\medskip
\begin{isamarkuptext}%
How to prove a logical equivalence:
\end{isamarkuptext}%
\isa{%
*}
(*<*)lemma "P\<longleftrightarrow>Q" proof-(*>*)
show "P \<longleftrightarrow> Q"
proof
  assume "P"
  text_raw{*\\\mbox{}\quad$\vdots$\\\mbox{}\hspace{-1.4ex}*}
  show "Q" (*<*)sorry(*>*) text_raw{*\ $\dots$\\*}
next
  assume "Q"
  text_raw{*\\\mbox{}\quad$\vdots$\\\mbox{}\hspace{-1.4ex}*}
  show "P" (*<*)sorry(*>*) text_raw{*\ $\dots$\\*}
qed(*<*)qed(*>*)
text_raw {* }
\medskip
\begin{isamarkuptext}%
Proofs by contradiction (@{thm[source] ccontr} stands for ``classical contradiction''):
\end{isamarkuptext}%
\begin{tabular}{@ {}ll@ {}}
\begin{minipage}[t]{.4\textwidth}
\isa{%
*}
(*<*)lemma "\<not> P" proof-(*>*)
show "\<not> P"
proof
  assume "P"
  text_raw{*\\\mbox{}\quad$\vdots$\\\mbox{}\hspace{-1.4ex}*}
  show "False" (*<*)sorry(*>*)text_raw{*\ $\dots$\\*}
qed(*<*)oops(*>*)

text_raw {* }
\end{minipage}
&
\begin{minipage}[t]{.4\textwidth}
\isa{%
*}
(*<*)lemma "P" proof-(*>*)
show "P"
proof (rule ccontr)
  assume "\<not>P"
  text_raw{*\\\mbox{}\quad$\vdots$\\\mbox{}\hspace{-1.4ex}*}
  show "False" (*<*)sorry(*>*)text_raw{*\ $\dots$\\*}
qed(*<*)oops(*>*)

text_raw {* }
\end{minipage}
\end{tabular}
\medskip
\begin{isamarkuptext}%
How to prove quantified formulas:
\end{isamarkuptext}%
\begin{tabular}{@ {}ll@ {}}
\begin{minipage}[t]{.4\textwidth}
\isa{%
*}
(*<*)lemma "ALL x. P x" proof-(*>*)
show "\<forall>x. P(x)"
proof
  fix x
  text_raw{*\\\mbox{}\quad$\vdots$\\\mbox{}\hspace{-1.4ex}*}
  show "P(x)" (*<*)sorry(*>*)text_raw{*\ $\dots$\\*}
qed(*<*)oops(*>*)

text_raw {* }
\end{minipage}
&
\begin{minipage}[t]{.4\textwidth}
\isa{%
*}
(*<*)lemma "EX x. P(x)" proof-(*>*)
show "\<exists>x. P(x)"
proof
  text_raw{*\\\mbox{}\quad$\vdots$\\\mbox{}\hspace{-1.4ex}*}
  show "P(witness)" (*<*)sorry(*>*)text_raw{*\ $\dots$\\*}
qed
(*<*)oops(*>*)

text_raw {* }
\end{minipage}
\end{tabular}
\medskip
\begin{isamarkuptext}%
In the proof of \noquotes{@{prop[source]"\<forall>x. P(x)"}},
the step \indexed{\isacom{fix}}{fix}~@{text x} introduces a locally fixed variable @{text x}
into the subproof, the proverbial ``arbitrary but fixed value''.
Instead of @{text x} we could have chosen any name in the subproof.
In the proof of \noquotes{@{prop[source]"\<exists>x. P(x)"}},
@{text witness} is some arbitrary
term for which we can prove that it satisfies @{text P}.

How to reason forward from \noquotes{@{prop[source] "\<exists>x. P(x)"}}:
\end{isamarkuptext}%
*}
(*<*)lemma True proof- assume 1: "EX x. P x"(*>*)
have "\<exists>x. P(x)" (*<*)by(rule 1)(*>*)text_raw{*\ $\dots$\\*}
then obtain x where p: "P(x)" by blast
(*<*)oops(*>*)
text{*
After the \indexed{\isacom{obtain}}{obtain} step, @{text x} (we could have chosen any name)
is a fixed local
variable, and @{text p} is the name of the fact
\noquotes{@{prop[source] "P(x)"}}.
This pattern works for one or more @{text x}.
As an example of the \isacom{obtain} command, here is the proof of
Cantor's theorem in more detail:
*}

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  hence  "\<exists>a. {x. x \<notin> f x} = f a" by(auto simp: surj_def)
  then obtain a where  "{x. x \<notin> f x} = f a"  by blast
  hence  "a \<notin> f a \<longleftrightarrow> a \<in> f a"  by blast
  thus "False" by blast
qed

text_raw{*
\begin{isamarkuptext}%

Finally, how to prove set equality and subset relationship:
\end{isamarkuptext}%
\begin{tabular}{@ {}ll@ {}}
\begin{minipage}[t]{.4\textwidth}
\isa{%
*}
(*<*)lemma "A = (B::'a set)" proof-(*>*)
show "A = B"
proof
  show "A \<subseteq> B" (*<*)sorry(*>*)text_raw{*\ $\dots$\\*}
next
  show "B \<subseteq> A" (*<*)sorry(*>*)text_raw{*\ $\dots$\\*}
qed(*<*)qed(*>*)

text_raw {* }
\end{minipage}
&
\begin{minipage}[t]{.4\textwidth}
\isa{%
*}
(*<*)lemma "A <= (B::'a set)" proof-(*>*)
show "A \<subseteq> B"
proof
  fix x
  assume "x \<in> A"
  text_raw{*\\\mbox{}\quad$\vdots$\\\mbox{}\hspace{-1.4ex}*}
  show "x \<in> B" (*<*)sorry(*>*)text_raw{*\ $\dots$\\*}
qed(*<*)qed(*>*)

text_raw {* }
\end{minipage}
\end{tabular}
\begin{isamarkuptext}%
\section{Streamlining Proofs}

\subsection{Pattern Matching and Quotations}

In the proof patterns shown above, formulas are often duplicated.
This can make the text harder to read, write and maintain. Pattern matching
is an abbreviation mechanism to avoid such duplication. Writing
\begin{quote}
\isacom{show} \ \textit{formula} @{text"("}\indexed{\isacom{is}}{is} \textit{pattern}@{text")"}
\end{quote}
matches the pattern against the formula, thus instantiating the unknowns in
the pattern for later use. As an example, consider the proof pattern for
@{text"\<longleftrightarrow>"}:
\end{isamarkuptext}%
*}
(*<*)lemma "formula\<^sub>1 \<longleftrightarrow> formula\<^sub>2" proof-(*>*)
show "formula\<^sub>1 \<longleftrightarrow> formula\<^sub>2" (is "?L \<longleftrightarrow> ?R")
proof
  assume "?L"
  text_raw{*\\\mbox{}\quad$\vdots$\\\mbox{}\hspace{-1.4ex}*}
  show "?R" (*<*)sorry(*>*) text_raw{*\ $\dots$\\*}
next
  assume "?R"
  text_raw{*\\\mbox{}\quad$\vdots$\\\mbox{}\hspace{-1.4ex}*}
  show "?L" (*<*)sorry(*>*) text_raw{*\ $\dots$\\*}
qed(*<*)qed(*>*)

text{* Instead of duplicating @{text"formula\<^sub>i"} in the text, we introduce
the two abbreviations @{text"?L"} and @{text"?R"} by pattern matching.
Pattern matching works wherever a formula is stated, in particular
with \isacom{have} and \isacom{lemma}.

The unknown \indexed{@{text"?thesis"}}{thesis} is implicitly matched against any goal stated by
\isacom{lemma} or \isacom{show}. Here is a typical example: *}

lemma "formula"
proof -
  text_raw{*\\\mbox{}\quad$\vdots$\\\mbox{}\hspace{-1.4ex}*}
  show ?thesis (*<*)sorry(*>*) text_raw{*\ $\dots$\\*}
qed

text{* 
Unknowns can also be instantiated with \indexed{\isacom{let}}{let} commands
\begin{quote}
\isacom{let} @{text"?t"} = @{text"\""}\textit{some-big-term}@{text"\""}
\end{quote}
Later proof steps can refer to @{text"?t"}:
\begin{quote}
\isacom{have} @{text"\""}\dots @{text"?t"} \dots@{text"\""}
\end{quote}
\begin{warn}
Names of facts are introduced with @{text"name:"} and refer to proved
theorems. Unknowns @{text"?X"} refer to terms or formulas.
\end{warn}

Although abbreviations shorten the text, the reader needs to remember what
they stand for. Similarly for names of facts. Names like @{text 1}, @{text 2}
and @{text 3} are not helpful and should only be used in short proofs. For
longer proofs, descriptive names are better. But look at this example:
\begin{quote}
\isacom{have} \ @{text"x_gr_0: \"x > 0\""}\\
$\vdots$\\
\isacom{from} @{text "x_gr_0"} \dots
\end{quote}
The name is longer than the fact it stands for! Short facts do not need names;
one can refer to them easily by quoting them:
\begin{quote}
\isacom{have} \ @{text"\"x > 0\""}\\
$\vdots$\\
\isacom{from} @{text "`x>0`"} \dots\index{$IMP053@@{text"`...`"}}
\end{quote}
Note that the quotes around @{text"x>0"} are \conceptnoidx{back quotes}.
They refer to the fact not by name but by value.

\subsection{\indexed{\isacom{moreover}}{moreover}}
\index{ultimately@\isacom{ultimately}}

Sometimes one needs a number of facts to enable some deduction. Of course
one can name these facts individually, as shown on the right,
but one can also combine them with \isacom{moreover}, as shown on the left:
*}text_raw{*
\begin{tabular}{@ {}ll@ {}}
\begin{minipage}[t]{.4\textwidth}
\isa{%
*}
(*<*)lemma "P" proof-(*>*)
have "P\<^sub>1" (*<*)sorry(*>*)text_raw{*\ $\dots$\\*}
moreover have "P\<^sub>2" (*<*)sorry(*>*)text_raw{*\ $\dots$\\*}
moreover
text_raw{*\\$\vdots$\\\hspace{-1.4ex}*}(*<*)have "True" ..(*>*)
moreover have "P\<^sub>n" (*<*)sorry(*>*)text_raw{*\ $\dots$\\*}
ultimately have "P"  (*<*)sorry(*>*)text_raw{*\ $\dots$\\*}
(*<*)oops(*>*)

text_raw {* }
\end{minipage}
&
\qquad
\begin{minipage}[t]{.4\textwidth}
\isa{%
*}
(*<*)lemma "P" proof-(*>*)
have lab\<^sub>1: "P\<^sub>1" (*<*)sorry(*>*)text_raw{*\ $\dots$\\*}
have lab\<^sub>2: "P\<^sub>2" (*<*)sorry(*>*)text_raw{*\ $\dots$*}
text_raw{*\\$\vdots$\\\hspace{-1.4ex}*}
have lab\<^sub>n: "P\<^sub>n" (*<*)sorry(*>*)text_raw{*\ $\dots$\\*}
from lab\<^sub>1 lab\<^sub>2 text_raw{*\ $\dots$\\*}
have "P"  (*<*)sorry(*>*)text_raw{*\ $\dots$\\*}
(*<*)oops(*>*)

text_raw {* }
\end{minipage}
\end{tabular}
\begin{isamarkuptext}%
The \isacom{moreover} version is no shorter but expresses the structure more
clearly and avoids new names.

\subsection{Raw Proof Blocks}

Sometimes one would like to prove some lemma locally within a proof,
a lemma that shares the current context of assumptions but that
has its own assumptions and is generalized over its locally fixed
variables at the end. This is what a \concept{raw proof block} does:
\begin{quote}\index{$IMP053@@{text"{ ... }"} (proof block)}
@{text"{"} \isacom{fix} @{text"x\<^sub>1 \<dots> x\<^sub>n"}\\
\mbox{}\ \ \ \isacom{assume} @{text"A\<^sub>1 \<dots> A\<^sub>m"}\\
\mbox{}\ \ \ $\vdots$\\
\mbox{}\ \ \ \isacom{have} @{text"B"}\\
@{text"}"}
\end{quote}
proves @{text"\<lbrakk> A\<^sub>1; \<dots> ; A\<^sub>m \<rbrakk> \<Longrightarrow> B"}
where all @{text"x\<^sub>i"} have been replaced by unknowns @{text"?x\<^sub>i"}.
\begin{warn}
The conclusion of a raw proof block is \emph{not} indicated by \isacom{show}
but is simply the final \isacom{have}.
\end{warn}

As an example we prove a simple fact about divisibility on integers.
The definition of @{text "dvd"} is @{thm dvd_def}.
\end{isamarkuptext}%
*}

lemma fixes a b :: int assumes "b dvd (a+b)" shows "b dvd a"
proof -
  { fix k assume k: "a+b = b*k"
    have "\<exists>k'. a = b*k'"
    proof
      show "a = b*(k - 1)" using k by(simp add: algebra_simps)
    qed }
  then show ?thesis using assms by(auto simp add: dvd_def)
qed

text{* Note that the result of a raw proof block has no name. In this example
it was directly piped (via \isacom{then}) into the final proof, but it can
also be named for later reference: you simply follow the block directly by a
\isacom{note} command:
\begin{quote}
\indexed{\isacom{note}}{note} \ @{text"name = this"}
\end{quote}
This introduces a new name @{text name} that refers to @{text this},
the fact just proved, in this case the preceding block. In general,
\isacom{note} introduces a new name for one or more facts.

\subsection*{Exercises}

\exercise
Give a readable, structured proof of the following lemma:
*}
lemma assumes T: "\<forall>x y. T x y \<or> T y x"
  and A: "\<forall>x y. A x y \<and> A y x \<longrightarrow> x = y"
  and TA: "\<forall>x y. T x y \<longrightarrow> A x y" and "A x y"
  shows "T x y"
(*<*)oops(*>*)
text{*
\endexercise

\exercise
Give a readable, structured proof of the following lemma:
*}
lemma "(\<exists>ys zs. xs = ys @ zs \<and> length ys = length zs)
      \<or> (\<exists>ys zs. xs = ys @ zs \<and> length ys = length zs + 1)"
(*<*)oops(*>*)
text{*
Hint: There are predefined functions @{const_typ take} and @{const_typ drop}
such that @{text"take k [x\<^sub>1,\<dots>] = [x\<^sub>1,\<dots>,x\<^sub>k]"} and
@{text"drop k [x\<^sub>1,\<dots>] = [x\<^bsub>k+1\<^esub>,\<dots>]"}. Let sledgehammer find and apply
the relevant @{const take} and @{const drop} lemmas for you.
\endexercise


\section{Case Analysis and Induction}

\subsection{Datatype Case Analysis}
\index{case analysis|(}

We have seen case analysis on formulas. Now we want to distinguish
which form some term takes: is it @{text 0} or of the form @{term"Suc n"},
is it @{term"[]"} or of the form @{term"x#xs"}, etc. Here is a typical example
proof by case analysis on the form of @{text xs}:
*}

lemma "length(tl xs) = length xs - 1"
proof (cases xs)
  assume "xs = []"
  thus ?thesis by simp
next
  fix y ys assume "xs = y#ys"
  thus ?thesis by simp
qed

text{*\index{cases@@{text"cases"}|(}Function @{text tl} (''tail'') is defined by @{thm list.sel(2)} and
@{thm list.sel(3)}. Note that the result type of @{const length} is @{typ nat}
and @{prop"0 - 1 = (0::nat)"}.

This proof pattern works for any term @{text t} whose type is a datatype.
The goal has to be proved for each constructor @{text C}:
\begin{quote}
\isacom{fix} \ @{text"x\<^sub>1 \<dots> x\<^sub>n"} \isacom{assume} @{text"\"t = C x\<^sub>1 \<dots> x\<^sub>n\""}
\end{quote}\index{case@\isacom{case}|(}
Each case can be written in a more compact form by means of the \isacom{case}
command:
\begin{quote}
\isacom{case} @{text "(C x\<^sub>1 \<dots> x\<^sub>n)"}
\end{quote}
This is equivalent to the explicit \isacom{fix}-\isacom{assume} line
but also gives the assumption @{text"\"t = C x\<^sub>1 \<dots> x\<^sub>n\""} a name: @{text C},
like the constructor.
Here is the \isacom{case} version of the proof above:
*}
(*<*)lemma "length(tl xs) = length xs - 1"(*>*)
proof (cases xs)
  case Nil
  thus ?thesis by simp
next
  case (Cons y ys)
  thus ?thesis by simp
qed

text{* Remember that @{text Nil} and @{text Cons} are the alphanumeric names
for @{text"[]"} and @{text"#"}. The names of the assumptions
are not used because they are directly piped (via \isacom{thus})
into the proof of the claim.
\index{case analysis|)}

\subsection{Structural Induction}
\index{induction|(}
\index{structural induction|(}

We illustrate structural induction with an example based on natural numbers:
the sum (@{text"\<Sum>"}) of the first @{text n} natural numbers
(@{text"{0..n::nat}"}) is equal to \mbox{@{term"n*(n+1) div 2::nat"}}.
Never mind the details, just focus on the pattern:
*}

lemma "\<Sum>{0..n::nat} = n*(n+1) div 2"
proof (induction n)
  show "\<Sum>{0..0::nat} = 0*(0+1) div 2" by simp
next
  fix n assume "\<Sum>{0..n::nat} = n*(n+1) div 2"
  thus "\<Sum>{0..Suc n} = Suc n*(Suc n+1) div 2" by simp
qed

text{* Except for the rewrite steps, everything is explicitly given. This
makes the proof easily readable, but the duplication means it is tedious to
write and maintain. Here is how pattern
matching can completely avoid any duplication: *}

lemma "\<Sum>{0..n::nat} = n*(n+1) div 2" (is "?P n")
proof (induction n)
  show "?P 0" by simp
next
  fix n assume "?P n"
  thus "?P(Suc n)" by simp
qed

text{* The first line introduces an abbreviation @{text"?P n"} for the goal.
Pattern matching @{text"?P n"} with the goal instantiates @{text"?P"} to the
function @{term"\<lambda>n. \<Sum>{0..n::nat} = n*(n+1) div 2"}.  Now the proposition to
be proved in the base case can be written as @{text"?P 0"}, the induction
hypothesis as @{text"?P n"}, and the conclusion of the induction step as
@{text"?P(Suc n)"}.

Induction also provides the \isacom{case} idiom that abbreviates
the \isacom{fix}-\isacom{assume} step. The above proof becomes
*}
(*<*)lemma "\<Sum>{0..n::nat} = n*(n+1) div 2"(*>*)
proof (induction n)
  case 0
  show ?case by simp
next
  case (Suc n)
  thus ?case by simp
qed

text{*
The unknown @{text"?case"}\index{case?@@{text"?case"}|(} is set in each case to the required
claim, i.e., @{text"?P 0"} and \mbox{@{text"?P(Suc n)"}} in the above proof,
without requiring the user to define a @{text "?P"}. The general
pattern for induction over @{typ nat} is shown on the left-hand side:
*}text_raw{*
\begin{tabular}{@ {}ll@ {}}
\begin{minipage}[t]{.4\textwidth}
\isa{%
*}
(*<*)lemma "P(n::nat)" proof -(*>*)
show "P(n)"
proof (induction n)
  case 0
  text_raw{*\\\mbox{}\ \ $\vdots$\\\mbox{}\hspace{-1ex}*}
  show ?case (*<*)sorry(*>*) text_raw{*\ $\dots$\\*}
next
  case (Suc n)
  text_raw{*\\\mbox{}\ \ $\vdots$\\\mbox{}\hspace{-1ex}*}
  show ?case (*<*)sorry(*>*) text_raw{*\ $\dots$\\*}
qed(*<*)qed(*>*)

text_raw {* }
\end{minipage}
&
\begin{minipage}[t]{.4\textwidth}
~\\
~\\
\isacom{let} @{text"?case = \"P(0)\""}\\
~\\
~\\
~\\[1ex]
\isacom{fix} @{text n} \isacom{assume} @{text"Suc: \"P(n)\""}\\
\isacom{let} @{text"?case = \"P(Suc n)\""}\\
\end{minipage}
\end{tabular}
\medskip
*}
text{*
On the right side you can see what the \isacom{case} command
on the left stands for.

In case the goal is an implication, induction does one more thing: the
proposition to be proved in each case is not the whole implication but only
its conclusion; the premises of the implication are immediately made
assumptions of that case. That is, if in the above proof we replace
\isacom{show}~@{text"\"P(n)\""} by
\mbox{\isacom{show}~@{text"\"A(n) \<Longrightarrow> P(n)\""}}
then \isacom{case}~@{text 0} stands for
\begin{quote}
\isacom{assume} \ @{text"0: \"A(0)\""}\\
\isacom{let} @{text"?case = \"P(0)\""}
\end{quote}
and \isacom{case}~@{text"(Suc n)"} stands for
\begin{quote}
\isacom{fix} @{text n}\\
\isacom{assume} @{text"Suc:"}
  \begin{tabular}[t]{l}@{text"\"A(n) \<Longrightarrow> P(n)\""}\\@{text"\"A(Suc n)\""}\end{tabular}\\
\isacom{let} @{text"?case = \"P(Suc n)\""}
\end{quote}
The list of assumptions @{text Suc} is actually subdivided
into @{text"Suc.IH"}, the induction hypotheses (here @{text"A(n) \<Longrightarrow> P(n)"}),
and @{text"Suc.prems"}, the premises of the goal being proved
(here @{text"A(Suc n)"}).

Induction works for any datatype.
Proving a goal @{text"\<lbrakk> A\<^sub>1(x); \<dots>; A\<^sub>k(x) \<rbrakk> \<Longrightarrow> P(x)"}
by induction on @{text x} generates a proof obligation for each constructor
@{text C} of the datatype. The command \isacom{case}~@{text"(C x\<^sub>1 \<dots> x\<^sub>n)"}
performs the following steps:
\begin{enumerate}
\item \isacom{fix} @{text"x\<^sub>1 \<dots> x\<^sub>n"}
\item \isacom{assume} the induction hypotheses (calling them @{text C.IH}\index{IH@@{text".IH"}})
 and the premises \mbox{@{text"A\<^sub>i(C x\<^sub>1 \<dots> x\<^sub>n)"}} (calling them @{text"C.prems"}\index{prems@@{text".prems"}})
 and calling the whole list @{text C}
\item \isacom{let} @{text"?case = \"P(C x\<^sub>1 \<dots> x\<^sub>n)\""}
\end{enumerate}
\index{structural induction|)}

\subsection{Rule Induction}
\index{rule induction|(}

Recall the inductive and recursive definitions of even numbers in
\autoref{sec:inductive-defs}:
*}

inductive ev :: "nat \<Rightarrow> bool" where
ev0: "ev 0" |
evSS: "ev n \<Longrightarrow> ev(Suc(Suc n))"

fun evn :: "nat \<Rightarrow> bool" where
"evn 0 = True" |
"evn (Suc 0) = False" |
"evn (Suc(Suc n)) = evn n"

text{* We recast the proof of @{prop"ev n \<Longrightarrow> evn n"} in Isar. The
left column shows the actual proof text, the right column shows
the implicit effect of the two \isacom{case} commands:*}text_raw{*
\begin{tabular}{@ {}l@ {\qquad}l@ {}}
\begin{minipage}[t]{.5\textwidth}
\isa{%
*}

lemma "ev n \<Longrightarrow> evn n"
proof(induction rule: ev.induct)
  case ev0
  show ?case by simp
next
  case evSS



  thus ?case by simp
qed

text_raw {* }
\end{minipage}
&
\begin{minipage}[t]{.5\textwidth}
~\\
~\\
\isacom{let} @{text"?case = \"evn 0\""}\\
~\\
~\\
\isacom{fix} @{text n}\\
\isacom{assume} @{text"evSS:"}
  \begin{tabular}[t]{l} @{text"\"ev n\""}\\@{text"\"evn n\""}\end{tabular}\\
\isacom{let} @{text"?case = \"evn(Suc(Suc n))\""}\\
\end{minipage}
\end{tabular}
\medskip
*}
text{*
The proof resembles structural induction, but the induction rule is given
explicitly and the names of the cases are the names of the rules in the
inductive definition.
Let us examine the two assumptions named @{thm[source]evSS}:
@{prop "ev n"} is the premise of rule @{thm[source]evSS}, which we may assume
because we are in the case where that rule was used; @{prop"evn n"}
is the induction hypothesis.
\begin{warn}
Because each \isacom{case} command introduces a list of assumptions
named like the case name, which is the name of a rule of the inductive
definition, those rules now need to be accessed with a qualified name, here
@{thm[source] ev.ev0} and @{thm[source] ev.evSS}.
\end{warn}

In the case @{thm[source]evSS} of the proof above we have pretended that the
system fixes a variable @{text n}.  But unless the user provides the name
@{text n}, the system will just invent its own name that cannot be referred
to.  In the above proof, we do not need to refer to it, hence we do not give
it a specific name. In case one needs to refer to it one writes
\begin{quote}
\isacom{case} @{text"(evSS m)"}
\end{quote}
like \isacom{case}~@{text"(Suc n)"} in earlier structural inductions.
The name @{text m} is an arbitrary choice. As a result,
case @{thm[source] evSS} is derived from a renamed version of
rule @{thm[source] evSS}: @{text"ev m \<Longrightarrow> ev(Suc(Suc m))"}.
Here is an example with a (contrived) intermediate step that refers to @{text m}:
*}

lemma "ev n \<Longrightarrow> evn n"
proof(induction rule: ev.induct)
  case ev0 show ?case by simp
next
  case (evSS m)
  have "evn(Suc(Suc m)) = evn m" by simp
  thus ?case using `evn m` by blast
qed

text{*
\indent
In general, let @{text I} be a (for simplicity unary) inductively defined
predicate and let the rules in the definition of @{text I}
be called @{text "rule\<^sub>1"}, \dots, @{text "rule\<^sub>n"}. A proof by rule
induction follows this pattern:\index{inductionrule@@{text"induction ... rule:"}}
*}

(*<*)
inductive I where rule\<^sub>1: "I()" |  rule\<^sub>2: "I()" |  rule\<^sub>n: "I()"
lemma "I x \<Longrightarrow> P x" proof-(*>*)
show "I x \<Longrightarrow> P x"
proof(induction rule: I.induct)
  case rule\<^sub>1
  text_raw{*\\[-.4ex]\mbox{}\ \ $\vdots$\\[-.4ex]\mbox{}\hspace{-1ex}*}
  show ?case (*<*)sorry(*>*)text_raw{*\ $\dots$\\*}
next
  text_raw{*\\[-.4ex]$\vdots$\\[-.4ex]\mbox{}\hspace{-1ex}*}
(*<*)
  case rule\<^sub>2
  show ?case sorry
(*>*)
next
  case rule\<^sub>n
  text_raw{*\\[-.4ex]\mbox{}\ \ $\vdots$\\[-.4ex]\mbox{}\hspace{-1ex}*}
  show ?case (*<*)sorry(*>*)text_raw{*\ $\dots$\\*}
qed(*<*)qed(*>*)

text{*
One can provide explicit variable names by writing
\isacom{case}~@{text"(rule\<^sub>i x\<^sub>1 \<dots> x\<^sub>k)"}, thus renaming the first @{text k}
free variables in rule @{text i} to @{text"x\<^sub>1 \<dots> x\<^sub>k"},
going through rule @{text i} from left to right.

\subsection{Assumption Naming}
\label{sec:assm-naming}

In any induction, \isacom{case}~@{text name} sets up a list of assumptions
also called @{text name}, which is subdivided into three parts:
\begin{description}
\item[@{text name.IH}]\index{IH@@{text".IH"}} contains the induction hypotheses.
\item[@{text name.hyps}]\index{hyps@@{text".hyps"}} contains all the other hypotheses of this case in the
induction rule. For rule inductions these are the hypotheses of rule
@{text name}, for structural inductions these are empty.
\item[@{text name.prems}]\index{prems@@{text".prems"}} contains the (suitably instantiated) premises
of the statement being proved, i.e., the @{text A\<^sub>i} when
proving @{text"\<lbrakk> A\<^sub>1; \<dots>; A\<^sub>n \<rbrakk> \<Longrightarrow> A"}.
\end{description}
\begin{warn}
Proof method @{text induct} differs from @{text induction}
only in this naming policy: @{text induct} does not distinguish
@{text IH} from @{text hyps} but subsumes @{text IH} under @{text hyps}.
\end{warn}

More complicated inductive proofs than the ones we have seen so far
often need to refer to specific assumptions --- just @{text name} or even
@{text name.prems} and @{text name.IH} can be too unspecific.
This is where the indexing of fact lists comes in handy, e.g.,
@{text"name.IH(2)"} or @{text"name.prems(1-2)"}.

\subsection{Rule Inversion}
\label{sec:rule-inversion}
\index{rule inversion|(}

Rule inversion is case analysis of which rule could have been used to
derive some fact. The name \conceptnoidx{rule inversion} emphasizes that we are
reasoning backwards: by which rules could some given fact have been proved?
For the inductive definition of @{const ev}, rule inversion can be summarized
like this:
@{prop[display]"ev n \<Longrightarrow> n = 0 \<or> (EX k. n = Suc(Suc k) \<and> ev k)"}
The realisation in Isabelle is a case analysis.
A simple example is the proof that @{prop"ev n \<Longrightarrow> ev (n - 2)"}. We
already went through the details informally in \autoref{sec:Logic:even}. This
is the Isar proof:
*}
(*<*)
notepad
begin fix n
(*>*)
  assume "ev n"
  from this have "ev(n - 2)"
  proof cases
    case ev0 thus "ev(n - 2)" by (simp add: ev.ev0)
  next
    case (evSS k) thus "ev(n - 2)" by (simp add: ev.evSS)
  qed
(*<*)
end
(*>*)

text{* The key point here is that a case analysis over some inductively
defined predicate is triggered by piping the given fact
(here: \isacom{from}~@{text this}) into a proof by @{text cases}.
Let us examine the assumptions available in each case. In case @{text ev0}
we have @{text"n = 0"} and in case @{text evSS} we have @{prop"n = Suc(Suc k)"}
and @{prop"ev k"}. In each case the assumptions are available under the name
of the case; there is no fine-grained naming schema like there is for induction.

Sometimes some rules could not have been used to derive the given fact
because constructors clash. As an extreme example consider
rule inversion applied to @{prop"ev(Suc 0)"}: neither rule @{text ev0} nor
rule @{text evSS} can yield @{prop"ev(Suc 0)"} because @{text"Suc 0"} unifies
neither with @{text 0} nor with @{term"Suc(Suc n)"}. Impossible cases do not
have to be proved. Hence we can prove anything from @{prop"ev(Suc 0)"}:
*}
(*<*)
notepad begin fix P
(*>*)
  assume "ev(Suc 0)" then have P by cases
(*<*)
end
(*>*)

text{* That is, @{prop"ev(Suc 0)"} is simply not provable: *}

lemma "\<not> ev(Suc 0)"
proof
  assume "ev(Suc 0)" then show False by cases
qed

text{* Normally not all cases will be impossible. As a simple exercise,
prove that \mbox{@{prop"\<not> ev(Suc(Suc(Suc 0)))"}.}

\subsection{Advanced Rule Induction}
\label{sec:advanced-rule-induction}

So far, rule induction was always applied to goals of the form @{text"I x y z \<Longrightarrow> \<dots>"}
where @{text I} is some inductively defined predicate and @{text x}, @{text y}, @{text z}
are variables. In some rare situations one needs to deal with an assumption where
not all arguments @{text r}, @{text s}, @{text t} are variables:
\begin{isabelle}
\isacom{lemma} @{text"\"I r s t \<Longrightarrow> \<dots>\""}
\end{isabelle}
Applying the standard form of
rule induction in such a situation will lead to strange and typically unprovable goals.
We can easily reduce this situation to the standard one by introducing
new variables @{text x}, @{text y}, @{text z} and reformulating the goal like this:
\begin{isabelle}
\isacom{lemma} @{text"\"I x y z \<Longrightarrow> x = r \<Longrightarrow> y = s \<Longrightarrow> z = t \<Longrightarrow> \<dots>\""}
\end{isabelle}
Standard rule induction will work fine now, provided the free variables in
@{text r}, @{text s}, @{text t} are generalized via @{text"arbitrary"}.

However, induction can do the above transformation for us, behind the curtains, so we never
need to see the expanded version of the lemma. This is what we need to write:
\begin{isabelle}
\isacom{lemma} @{text"\"I r s t \<Longrightarrow> \<dots>\""}\isanewline
\isacom{proof}@{text"(induction \"r\" \"s\" \"t\" arbitrary: \<dots> rule: I.induct)"}\index{inductionrule@@{text"induction ... rule:"}}\index{arbitrary@@{text"arbitrary:"}}
\end{isabelle}
Like for rule inversion, cases that are impossible because of constructor clashes
will not show up at all. Here is a concrete example: *}

lemma "ev (Suc m) \<Longrightarrow> \<not> ev m"
proof(induction "Suc m" arbitrary: m rule: ev.induct)
  fix n assume IH: "\<And>m. n = Suc m \<Longrightarrow> \<not> ev m"
  show "\<not> ev (Suc n)"
  proof --"contradiction"
    assume "ev(Suc n)"
    thus False
    proof cases --"rule inversion"
      fix k assume "n = Suc k" "ev k"
      thus False using IH by auto
    qed
  qed
qed

text{*
Remarks:
\begin{itemize}
\item 
Instead of the \isacom{case} and @{text ?case} magic we have spelled all formulas out.
This is merely for greater clarity.
\item
We only need to deal with one case because the @{thm[source] ev0} case is impossible.
\item
The form of the @{text IH} shows us that internally the lemma was expanded as explained
above: \noquotes{@{prop[source]"ev x \<Longrightarrow> x = Suc m \<Longrightarrow> \<not> ev m"}}.
\item
The goal @{prop"\<not> ev (Suc n)"} may surprise. The expanded version of the lemma
would suggest that we have a \isacom{fix} @{text m} \isacom{assume} @{prop"Suc(Suc n) = Suc m"}
and need to show @{prop"\<not> ev m"}. What happened is that Isabelle immediately
simplified @{prop"Suc(Suc n) = Suc m"} to @{prop"Suc n = m"} and could then eliminate
@{text m}. Beware of such nice surprises with this advanced form of induction.
\end{itemize}
\begin{warn}
This advanced form of induction does not support the @{text IH}
naming schema explained in \autoref{sec:assm-naming}:
the induction hypotheses are instead found under the name @{text hyps},
as they are for the simpler
@{text induct} method.
\end{warn}
\index{induction|)}
\index{cases@@{text"cases"}|)}
\index{case@\isacom{case}|)}
\index{case?@@{text"?case"}|)}
\index{rule induction|)}
\index{rule inversion|)}

\subsection*{Exercises}


\exercise
Give a structured proof by rule inversion:
*}

lemma assumes a: "ev(Suc(Suc n))" shows "ev n"
(*<*)oops(*>*)

text{*
\endexercise

\begin{exercise}
Give a structured proof of @{prop "\<not> ev(Suc(Suc(Suc 0)))"}
by rule inversions. If there are no cases to be proved you can close
a proof immediately with \isacom{qed}.
\end{exercise}

\begin{exercise}
Recall predicate @{text star} from \autoref{sec:star} and @{text iter}
from Exercise~\ref{exe:iter}. Prove @{prop "iter r n x y \<Longrightarrow> star r x y"}
in a structured style; do not just sledgehammer each case of the
required induction.
\end{exercise}

\begin{exercise}
Define a recursive function @{text "elems ::"} @{typ"'a list \<Rightarrow> 'a set"}
and prove @{prop "x : elems xs \<Longrightarrow> \<exists>ys zs. xs = ys @ x # zs \<and> x \<notin> elems ys"}.
\end{exercise}

\begin{exercise}
Extend Exercise~\ref{exe:cfg} with a function that checks if some
\mbox{@{text "alpha list"}} is a balanced
string of parentheses. More precisely, define a \mbox{recursive} function
@{text "balanced :: nat \<Rightarrow> alpha list \<Rightarrow> bool"} such that @{term"balanced n w"}
is true iff (informally) @{text"S (a\<^sup>n @ w)"}. Formally, prove that
@{prop "balanced n w \<longleftrightarrow> S (replicate n a @ w)"} where
@{const replicate} @{text"::"} @{typ"nat \<Rightarrow> 'a \<Rightarrow> 'a list"} is predefined
and @{term"replicate n x"} yields the list @{text"[x, \<dots>, x]"} of length @{text n}.
\end{exercise}
*}

(*<*)
end
(*>*)
