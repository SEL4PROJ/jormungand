theory Further
imports Setup
begin

section \<open>Further issues \label{sec:further}\<close>

subsection \<open>Specialities of the @{text Scala} target language \label{sec:scala}\<close>

text \<open>
  @{text Scala} deviates from languages of the ML family in a couple
  of aspects; those which affect code generation mainly have to do with
  @{text Scala}'s type system:

  \begin{itemize}

    \item @{text Scala} prefers tupled syntax over curried syntax.

    \item @{text Scala} sacrifices Hindely-Milner type inference for a
      much more rich type system with subtyping etc.  For this reason
      type arguments sometimes have to be given explicitly in square
      brackets (mimicking System F syntax).

    \item In contrast to @{text Haskell} where most specialities of
      the type system are implemented using \emph{type classes},
      @{text Scala} provides a sophisticated system of \emph{implicit
      arguments}.

  \end{itemize}

  \noindent Concerning currying, the @{text Scala} serializer counts
  arguments in code equations to determine how many arguments
  shall be tupled; remaining arguments and abstractions in terms
  rather than function definitions are always curried.

  The second aspect affects user-defined adaptations with @{command
  code_printing}.  For regular terms, the @{text Scala} serializer prints
  all type arguments explicitly.  For user-defined term adaptations
  this is only possible for adaptations which take no arguments: here
  the type arguments are just appended.  Otherwise they are ignored;
  hence user-defined adaptations for polymorphic constants have to be
  designed very carefully to avoid ambiguity.
\<close>


subsection \<open>Modules namespace\<close>

text \<open>
  When invoking the @{command export_code} command it is possible to
  leave out the @{keyword "module_name"} part; then code is
  distributed over different modules, where the module name space
  roughly is induced by the Isabelle theory name space.

  Then sometimes the awkward situation occurs that dependencies
  between definitions introduce cyclic dependencies between modules,
  which in the @{text Haskell} world leaves you to the mercy of the
  @{text Haskell} implementation you are using, while for @{text
  SML}/@{text OCaml} code generation is not possible.

  A solution is to declare module names explicitly.  Let use assume
  the three cyclically dependent modules are named \emph{A}, \emph{B}
  and \emph{C}.  Then, by stating
\<close>

code_identifier %quote
  code_module A \<rightharpoonup> (SML) ABC
| code_module B \<rightharpoonup> (SML) ABC
| code_module C \<rightharpoonup> (SML) ABC

text \<open>
  \noindent we explicitly map all those modules on \emph{ABC},
  resulting in an ad-hoc merge of this three modules at serialisation
  time.
\<close>

subsection \<open>Locales and interpretation\<close>

text \<open>
  A technical issue comes to surface when generating code from
  specifications stemming from locale interpretation into global
  theories.

  Let us assume a locale specifying a power operation on arbitrary
  types:
\<close>

locale %quote power =
  fixes power :: "'a \<Rightarrow> 'b \<Rightarrow> 'b"
  assumes power_commute: "power x \<circ> power y = power y \<circ> power x"
begin

text \<open>
  \noindent Inside that locale we can lift @{text power} to exponent
  lists by means of a specification relative to that locale:
\<close>

primrec %quote powers :: "'a list \<Rightarrow> 'b \<Rightarrow> 'b" where
  "powers [] = id"
| "powers (x # xs) = power x \<circ> powers xs"

lemma %quote powers_append:
  "powers (xs @ ys) = powers xs \<circ> powers ys"
  by (induct xs) simp_all

lemma %quote powers_power:
  "powers xs \<circ> power x = power x \<circ> powers xs"
  by (induct xs)
    (simp_all del: o_apply id_apply add: comp_assoc,
      simp del: o_apply add: o_assoc power_commute)

lemma %quote powers_rev:
  "powers (rev xs) = powers xs"
    by (induct xs) (simp_all add: powers_append powers_power)

end %quote

text \<open>
  After an interpretation of this locale (say, @{command_def
  global_interpretation} @{text "fun_power:"} @{term [source] "power (\<lambda>n (f
  :: 'a \<Rightarrow> 'a). f ^^ n)"}), one could naively expect to have a constant @{text
  "fun_power.powers :: nat list \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a"} for which code
  can be generated.  But this not the case: internally, the term
  @{text "fun_power.powers"} is an abbreviation for the foundational
  term @{term [source] "power.powers (\<lambda>n (f :: 'a \<Rightarrow> 'a). f ^^ n)"}
  (see @{cite "isabelle-locale"} for the details behind).

  Fortunately, a succint solution is available: a dedicated
  rewrite definition:
\<close>

global_interpretation %quote fun_power: power "(\<lambda>n (f :: 'a \<Rightarrow> 'a). f ^^ n)"
  defines funpows = fun_power.powers
  by unfold_locales
    (simp_all add: fun_eq_iff funpow_mult mult.commute)

text \<open>
  \noindent This amends the interpretation morphisms such that
  occurrences of the foundational term @{term [source] "power.powers (\<lambda>n (f :: 'a \<Rightarrow> 'a). f ^^ n)"}
  are folded to a newly defined constant @{const funpows}.

  After this setup procedure, code generation can continue as usual:
\<close>

text %quotetypewriter \<open>
  @{code_stmts funpows (consts) Nat.funpow funpows (Haskell)}
\<close>


subsection \<open>Parallel computation\<close>

text \<open>
  Theory @{text Parallel} in \<^dir>\<open>~~/src/HOL/Library\<close> contains
  operations to exploit parallelism inside the Isabelle/ML
  runtime engine.
\<close>

subsection \<open>Imperative data structures\<close>

text \<open>
  If you consider imperative data structures as inevitable for a
  specific application, you should consider \emph{Imperative
  Functional Programming with Isabelle/HOL}
  @{cite "bulwahn-et-al:2008:imperative"}; the framework described there
  is available in session @{text Imperative_HOL}, together with a
  short primer document.
\<close>


subsection \<open>ML system interfaces \label{sec:ml}\<close>

text \<open>
  Since the code generator framework not only aims to provide a nice
  Isar interface but also to form a base for code-generation-based
  applications, here a short description of the most fundamental ML
  interfaces.
\<close>

subsubsection \<open>Managing executable content\<close>

text %mlref \<open>
  \begin{mldecls}
  @{index_ML Code.read_const: "theory -> string -> string"} \\
  @{index_ML Code.add_eqn: "Code.kind * bool -> thm -> theory -> theory"} \\
  @{index_ML Code.del_eqn: "thm -> theory -> theory"} \\
  @{index_ML Code_Preproc.map_pre: "(Proof.context -> Proof.context) -> theory -> theory"} \\
  @{index_ML Code_Preproc.map_post: "(Proof.context -> Proof.context) -> theory -> theory"} \\
  @{index_ML Code_Preproc.add_functrans: "
    string * (Proof.context -> (thm * bool) list -> (thm * bool) list option)
      -> theory -> theory"} \\
  @{index_ML Code_Preproc.del_functrans: "string -> theory -> theory"} \\
  @{index_ML Code.add_datatype: "(string * typ) list -> theory -> theory"} \\
  @{index_ML Code.get_type: "theory -> string
    -> ((string * sort) list * (string * ((string * sort) list * typ list)) list) * bool"} \\
  @{index_ML Code.get_type_of_constr_or_abstr: "theory -> string -> (string * bool) option"}
  \end{mldecls}

  \begin{description}

  \item @{ML Code.read_const}~@{text thy}~@{text s}
     reads a constant as a concrete term expression @{text s}.

  \item @{ML Code.add_eqn}~@{text "(kind, default)"}~@{text "thm"}~@{text "thy"} adds code equation
     @{text "thm"} to executable content.

  \item @{ML Code.del_eqn}~@{text "thm"}~@{text "thy"} removes code equation
     @{text "thm"} from executable content, if present.

  \item @{ML Code_Preproc.map_pre}~@{text "f"}~@{text "thy"} changes
     the preprocessor simpset.

  \item @{ML Code_Preproc.add_functrans}~@{text "(name, f)"}~@{text "thy"} adds
     function transformer @{text f} (named @{text name}) to executable content;
     @{text f} is a transformer of the code equations belonging
     to a certain function definition, depending on the
     current theory context.  Returning @{text NONE} indicates that no
     transformation took place;  otherwise, the whole process will be iterated
     with the new code equations.

  \item @{ML Code_Preproc.del_functrans}~@{text "name"}~@{text "thy"} removes
     function transformer named @{text name} from executable content.

  \item @{ML Code.add_datatype}~@{text cs}~@{text thy} adds
     a datatype to executable content, with generation
     set @{text cs}.

  \item @{ML Code.get_type_of_constr_or_abstr}~@{text "thy"}~@{text "const"}
     returns type constructor corresponding to
     constructor @{text const}; returns @{text NONE}
     if @{text const} is no constructor.

  \end{description}
\<close>


subsubsection \<open>Data depending on the theory's executable content\<close>

text \<open>
  Implementing code generator applications on top of the framework set
  out so far usually not only involves using those primitive
  interfaces but also storing code-dependent data and various other
  things.

  Due to incrementality of code generation, changes in the theory's
  executable content have to be propagated in a certain fashion.
  Additionally, such changes may occur not only during theory
  extension but also during theory merge, which is a little bit nasty
  from an implementation point of view.  The framework provides a
  solution to this technical challenge by providing a functorial data
  slot @{ML_functor Code_Data}; on instantiation of this functor, the
  following types and operations are required:

  \medskip
  \begin{tabular}{l}
  @{text "type T"} \\
  @{text "val empty: T"} \\
  \end{tabular}

  \begin{description}

  \item @{text T} the type of data to store.

  \item @{text empty} initial (empty) data.

  \end{description}

  \noindent An instance of @{ML_functor Code_Data} provides the
  following interface:

  \medskip
  \begin{tabular}{l}
  @{text "change: theory \<rightarrow> (T \<rightarrow> T) \<rightarrow> T"} \\
  @{text "change_yield: theory \<rightarrow> (T \<rightarrow> 'a * T) \<rightarrow> 'a * T"}
  \end{tabular}

  \begin{description}

  \item @{text change} update of current data (cached!) by giving a
    continuation.

  \item @{text change_yield} update with side result.

  \end{description}
\<close>

end
