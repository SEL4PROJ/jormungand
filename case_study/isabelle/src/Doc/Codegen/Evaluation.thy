theory Evaluation
imports Setup
begin (*<*)

ML \<open>
  Isabelle_System.mkdirs (File.tmp_path (Path.basic "examples"))
\<close> (*>*)

section \<open>Evaluation \label{sec:evaluation}\<close>

text \<open>
  Recalling \secref{sec:principle}, code generation turns a system of
  equations into a program with the \emph{same} equational semantics.
  As a consequence, this program can be used as a \emph{rewrite
  engine} for terms: rewriting a term @{term "t"} using a program to a
  term @{term "t'"} yields the theorems @{prop "t \<equiv> t'"}.  This
  application of code generation in the following is referred to as
  \emph{evaluation}.
\<close>


subsection \<open>Evaluation techniques\<close>

text \<open>
  The existing infrastructure provides a rich palette of evaluation
  techniques, each comprising different aspects:

  \begin{description}

    \item[Expressiveness.]  Depending on how good symbolic computation
      is supported, the class of terms which can be evaluated may be
      bigger or smaller.

    \item[Efficiency.]  The more machine-near the technique, the
      faster it is.

    \item[Trustability.]  Techniques which a huge (and also probably
      more configurable infrastructure) are more fragile and less
      trustable.

  \end{description}
\<close>


subsubsection \<open>The simplifier (@{text simp})\<close>

text \<open>
  The simplest way for evaluation is just using the simplifier with
  the original code equations of the underlying program.  This gives
  fully symbolic evaluation and highest trustablity, with the usual
  performance of the simplifier.  Note that for operations on abstract
  datatypes (cf.~\secref{sec:invariant}), the original theorems as
  given by the users are used, not the modified ones.
\<close>


subsubsection \<open>Normalization by evaluation (@{text nbe})\<close>

text \<open>
  Normalization by evaluation @{cite "Aehlig-Haftmann-Nipkow:2008:nbe"}
  provides a comparably fast partially symbolic evaluation which
  permits also normalization of functions and uninterpreted symbols;
  the stack of code to be trusted is considerable.
\<close>


subsubsection \<open>Evaluation in ML (@{text code})\<close>

text \<open>
  Highest performance can be achieved by evaluation in ML, at the cost
  of being restricted to ground results and a layered stack of code to
  be trusted, including code generator configurations by the user.

  Evaluation is carried out in a target language \emph{Eval} which
  inherits from \emph{SML} but for convenience uses parts of the
  Isabelle runtime environment.  The soundness of computation carried
  out there depends crucially on the correctness of the code
  generator setup; this is one of the reasons why you should not use
  adaptation (see \secref{sec:adaptation}) frivolously.
\<close>


subsection \<open>Aspects of evaluation\<close>

text \<open>
  Each of the techniques can be combined with different aspects.  The
  most important distinction is between dynamic and static evaluation.
  Dynamic evaluation takes the code generator configuration \qt{as it
  is} at the point where evaluation is issued.  Best example is the
  @{command_def value} command which allows ad-hoc evaluation of
  terms:
\<close>

value %quote "42 / (12 :: rat)"

text \<open>
  \noindent @{command value} tries first to evaluate using ML, falling
  back to normalization by evaluation if this fails.

  A particular technique may be specified in square brackets, e.g.
\<close>

value %quote [nbe] "42 / (12 :: rat)"

text \<open>
  To employ dynamic evaluation in the document generation, there is also
  a @{text value} antiquotation with the same evaluation techniques 
  as @{command value}.

  Static evaluation freezes the code generator configuration at a
  certain point and uses this context whenever evaluation is issued
  later on.  This is particularly appropriate for proof procedures
  which use evaluation, since then the behaviour of evaluation is not
  changed or even compromised later on by actions of the user.

  As a technical complication, terms after evaluation in ML must be
  turned into Isabelle's internal term representation again.  Since
  this is also configurable, it is never fully trusted.  For this
  reason, evaluation in ML comes with further aspects:

  \begin{description}

    \item[Plain evaluation.]  A term is normalized using the provided
      term reconstruction from ML to Isabelle; for applications which
      do not need to be fully trusted.

    \item[Property conversion.]  Evaluates propositions; since these
      are monomorphic, the term reconstruction is fixed once and for all
      and therefore trustable.

    \item[Conversion.]  Evaluates an arbitrary term @{term "t"} first
      by plain evaluation and certifies the result @{term "t'"} by
      checking the equation @{term "t \<equiv> t'"} using property
      conversion.

  \end{description}

  \noindent The picture is further complicated by the roles of
  exceptions.  Here three cases have to be distinguished:

  \begin{itemize}

    \item Evaluation of @{term t} terminates with a result @{term
      "t'"}.

    \item Evaluation of @{term t} terminates which an exception
      indicating a pattern match failure or a non-implemented
      function.  As sketched in \secref{sec:partiality}, this can be
      interpreted as partiality.
     
    \item Evaluation raises any other kind of exception.
     
  \end{itemize}

  \noindent For conversions, the first case yields the equation @{term
  "t = t'"}, the second defaults to reflexivity @{term "t = t"}.
  Exceptions of the third kind are propagated to the user.

  By default return values of plain evaluation are optional, yielding
  @{text "SOME t'"} in the first case, @{text "NONE"} in the
  second, and propagating the exception in the third case.  A strict
  variant of plain evaluation either yields @{text "t'"} or propagates
  any exception, a liberal variant captures any exception in a result
  of type @{text "Exn.result"}.
  
  For property conversion (which coincides with conversion except for
  evaluation in ML), methods are provided which solve a given goal by
  evaluation.
\<close>


subsection \<open>Schematic overview\<close>

text \<open>
  \newcommand{\ttsize}{\fontsize{5.8pt}{8pt}\selectfont}
  \fontsize{9pt}{12pt}\selectfont
  \begin{tabular}{ll||c|c|c}
    & & @{text simp} & @{text nbe} & @{text code} \tabularnewline \hline \hline
    \multirow{5}{1ex}{\rotatebox{90}{dynamic}}
      & interactive evaluation 
      & @{command value} @{text "[simp]"} & @{command value} @{text "[nbe]"} & @{command value} @{text "[code]"}
      \tabularnewline
    & plain evaluation & & & \ttsize@{ML "Code_Evaluation.dynamic_value"} \tabularnewline \cline{2-5}
    & evaluation method & @{method code_simp} & @{method normalization} & @{method eval} \tabularnewline
    & property conversion & & & \ttsize@{ML "Code_Runtime.dynamic_holds_conv"} \tabularnewline \cline{2-5}
    & conversion & \ttsize@{ML "Code_Simp.dynamic_conv"} & \ttsize@{ML "Nbe.dynamic_conv"}
      & \ttsize@{ML "Code_Evaluation.dynamic_conv"} \tabularnewline \hline \hline
    \multirow{3}{1ex}{\rotatebox{90}{static}}
    & plain evaluation & & & \ttsize@{ML "Code_Evaluation.static_value"} \tabularnewline \cline{2-5}
    & property conversion & &
      & \ttsize@{ML "Code_Runtime.static_holds_conv"} \tabularnewline \cline{2-5}
    & conversion & \ttsize@{ML "Code_Simp.static_conv"}
      & \ttsize@{ML "Nbe.static_conv"}
      & \ttsize@{ML "Code_Evaluation.static_conv"}
  \end{tabular}
\<close>

text \<open>
  \noindent Note that @{ML Code_Evaluation.static_value} and
  @{ML Code_Evaluation.static_conv} require certain code equations to
  reconstruct Isabelle terms from results and certify results.  This is
  achieved as follows:

  \<^enum> Identify which result types are expected.

  \<^enum> Define an auxiliary operation which for each possible result type @{text \<tau>}
    contains a term @{const Code_Evaluation.TERM_OF} of type @{text "\<tau> itself"}
    (for @{ML Code_Evaluation.static_value}) or
    a term @{const Code_Evaluation.TERM_OF_EQUAL} of type @{text "\<tau> itself"}
    (for @{ML Code_Evaluation.static_conv}) respectively.

  \<^enum> Include that auxiliary operation into the set of constants when generating
    the static conversion.
\<close>


subsection \<open>Preprocessing HOL terms into evaluable shape\<close>

text \<open>
  When integrating decision procedures developed inside HOL into HOL itself,
  it is necessary to somehow get from the Isabelle/ML representation to
  the representation used by the decision procedure itself (``reification'').
  One option is to hardcode it using code antiquotations (see \secref{sec:code_antiq}).
  Another option is to use pre-existing infrastructure in HOL:
  @{ML "Reification.conv"} and @{ML "Reification.tac"}

  A simplistic example:
\<close>

datatype %quote form_ord = T | F | Less nat nat
  | And form_ord form_ord | Or form_ord form_ord | Neg form_ord

primrec %quote interp :: "form_ord \<Rightarrow> 'a::order list \<Rightarrow> bool"
where
  "interp T vs \<longleftrightarrow> True"
| "interp F vs \<longleftrightarrow> False"
| "interp (Less i j) vs \<longleftrightarrow> vs ! i < vs ! j"
| "interp (And f1 f2) vs \<longleftrightarrow> interp f1 vs \<and> interp f2 vs"
| "interp (Or f1 f2) vs \<longleftrightarrow> interp f1 vs \<or> interp f2 vs"
| "interp (Neg f) vs \<longleftrightarrow> \<not> interp f vs"

text \<open>
  The datatype @{type form_ord} represents formulae whose semantics is given by
  @{const interp}.  Note that values are represented by variable indices (@{typ nat})
  whose concrete values are given in list @{term vs}.
\<close>

ML (*<*) \<open>\<close>
schematic_goal "thm": fixes x y z :: "'a::order" shows "x < y \<and> x < z \<equiv> ?P"
ML_prf 
(*>*) \<open>val thm =
  Reification.conv @{context} @{thms interp.simps} @{cterm "x < y \<and> x < z"}\<close> (*<*)
by (tactic \<open>ALLGOALS (resolve_tac @{context} [thm])\<close>)
(*>*) 

text \<open>
  By virtue of @{fact interp.simps}, @{ML "Reification.conv"} provides a conversion
  which, for this concrete example, yields @{thm thm [no_vars]}.  Note that the argument
  to @{const interp} does not contain any free variables and can thus be evaluated
  using evaluation.

  A less meager example can be found in the AFP, session @{text "Regular-Sets"},
  theory @{text Regexp_Method}.
\<close>


subsection \<open>Intimate connection between logic and system runtime\<close>

text \<open>
  The toolbox of static evaluation conversions forms a reasonable base
  to interweave generated code and system tools.  However in some
  situations more direct interaction is desirable.
\<close>


subsubsection \<open>Static embedding of generated code into system runtime -- the @{text code} antiquotation \label{sec:code_antiq}\<close>

text \<open>
  The @{text code} antiquotation allows to include constants from
  generated code directly into ML system code, as in the following toy
  example:
\<close>

datatype %quote form = T | F | And form form | Or form form (*<*)

(*>*) ML %quotett \<open>
  fun eval_form @{code T} = true
    | eval_form @{code F} = false
    | eval_form (@{code And} (p, q)) =
        eval_form p andalso eval_form q
    | eval_form (@{code Or} (p, q)) =
        eval_form p orelse eval_form q;
\<close>

text \<open>
  \noindent @{text code} takes as argument the name of a constant;
  after the whole ML is read, the necessary code is generated
  transparently and the corresponding constant names are inserted.
  This technique also allows to use pattern matching on constructors
  stemming from compiled datatypes.  Note that the @{text code}
  antiquotation may not refer to constants which carry adaptations;
  here you have to refer to the corresponding adapted code directly.

  For a less simplistic example, theory @{text Approximation} in
  the @{text Decision_Procs} session is a good reference.
\<close>


subsubsection \<open>Static embedding of generated code into system runtime -- @{text code_reflect}\<close>

text \<open>
  The @{text code} antiquoation is lightweight, but the generated code
  is only accessible while the ML section is processed.  Sometimes this
  is not appropriate, especially if the generated code contains datatype
  declarations which are shared with other parts of the system.  In these
  cases, @{command_def code_reflect} can be used:
\<close>

code_reflect %quote Sum_Type
  datatypes sum = Inl | Inr
  functions "Sum_Type.sum.projl" "Sum_Type.sum.projr"

text \<open>
  \noindent @{command_def code_reflect} takes a structure name and
  references to datatypes and functions; for these code is compiled
  into the named ML structure and the \emph{Eval} target is modified
  in a way that future code generation will reference these
  precompiled versions of the given datatypes and functions.  This
  also allows to refer to the referenced datatypes and functions from
  arbitrary ML code as well.

  A typical example for @{command code_reflect} can be found in the
  @{theory Predicate} theory.
\<close>


subsubsection \<open>Separate compilation -- @{text code_reflect}\<close>

text \<open>
  For technical reasons it is sometimes necessary to separate
  generation and compilation of code which is supposed to be used in
  the system runtime.  For this @{command code_reflect} with an
  optional \<^theory_text>\<open>file\<close> argument can be used:
\<close>

code_reflect %quote Rat
  datatypes rat
  functions Fract
    "(plus :: rat \<Rightarrow> rat \<Rightarrow> rat)" "(minus :: rat \<Rightarrow> rat \<Rightarrow> rat)"
    "(times :: rat \<Rightarrow> rat \<Rightarrow> rat)" "(divide :: rat \<Rightarrow> rat \<Rightarrow> rat)"
  file "$ISABELLE_TMP/examples/rat.ML"

text \<open>
  \noindent This merely generates the referenced code to the given
  file which can be included into the system runtime later on.
\<close>

end

