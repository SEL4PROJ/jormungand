(*:maxLineLen=78:*)

theory Syntax
imports Base
begin

chapter \<open>Concrete syntax and type-checking\<close>

text \<open>
  Pure \<open>\<lambda>\<close>-calculus as introduced in \chref{ch:logic} is an adequate
  foundation for logical languages --- in the tradition of \<^emph>\<open>higher-order
  abstract syntax\<close> --- but end-users require additional means for reading and
  printing of terms and types. This important add-on outside the logical core
  is called \<^emph>\<open>inner syntax\<close> in Isabelle jargon, as opposed to the \<^emph>\<open>outer
  syntax\<close> of the theory and proof language @{cite "isabelle-isar-ref"}.

  For example, according to @{cite church40} quantifiers are represented as
  higher-order constants \<open>All :: ('a \<Rightarrow> bool) \<Rightarrow> bool\<close> such that \<open>All (\<lambda>x::'a. B
  x)\<close> faithfully represents the idea that is displayed in Isabelle as \<open>\<forall>x::'a.
  B x\<close> via @{keyword "binder"} notation. Moreover, type-inference in the style
  of Hindley-Milner @{cite hindleymilner} (and extensions) enables users to
  write \<open>\<forall>x. B x\<close> concisely, when the type \<open>'a\<close> is already clear from the
  context.\<^footnote>\<open>Type-inference taken to the extreme can easily confuse users.
  Beginners often stumble over unexpectedly general types inferred by the
  system.\<close>

  \<^medskip>
  The main inner syntax operations are \<^emph>\<open>read\<close> for parsing together with
  type-checking, and \<^emph>\<open>pretty\<close> for formatted output. See also
  \secref{sec:read-print}.

  Furthermore, the input and output syntax layers are sub-divided into
  separate phases for \<^emph>\<open>concrete syntax\<close> versus \<^emph>\<open>abstract syntax\<close>, see also
  \secref{sec:parse-unparse} and \secref{sec:term-check}, respectively. This
  results in the following decomposition of the main operations:

    \<^item> \<open>read = parse; check\<close>

    \<^item> \<open>pretty = uncheck; unparse\<close>

  For example, some specification package might thus intercept syntax
  processing at a well-defined stage after \<open>parse\<close>, to a augment the resulting
  pre-term before full type-reconstruction is performed by \<open>check\<close>. Note that
  the formal status of bound variables, versus free variables, versus
  constants must not be changed between these phases.

  \<^medskip>
  In general, \<open>check\<close> and \<open>uncheck\<close> operate simultaneously on a list of terms.
  This is particular important for type-checking, to reconstruct types for
  several terms of the same context and scope. In contrast, \<open>parse\<close> and
  \<open>unparse\<close> operate separately on single terms.

  There are analogous operations to read and print types, with the same
  sub-division into phases.
\<close>


section \<open>Reading and pretty printing \label{sec:read-print}\<close>

text \<open>
  Read and print operations are roughly dual to each other, such that for the
  user \<open>s' = pretty (read s)\<close> looks similar to the original source text \<open>s\<close>,
  but the details depend on many side-conditions. There are also explicit
  options to control the removal of type information in the output. The
  default configuration routinely looses information, so \<open>t' = read (pretty
  t)\<close> might fail, or produce a differently typed term, or a completely
  different term in the face of syntactic overloading.
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{index_ML Syntax.read_typs: "Proof.context -> string list -> typ list"} \\
  @{index_ML Syntax.read_terms: "Proof.context -> string list -> term list"} \\
  @{index_ML Syntax.read_props: "Proof.context -> string list -> term list"} \\[0.5ex]
  @{index_ML Syntax.read_typ: "Proof.context -> string -> typ"} \\
  @{index_ML Syntax.read_term: "Proof.context -> string -> term"} \\
  @{index_ML Syntax.read_prop: "Proof.context -> string -> term"} \\[0.5ex]
  @{index_ML Syntax.pretty_typ: "Proof.context -> typ -> Pretty.T"} \\
  @{index_ML Syntax.pretty_term: "Proof.context -> term -> Pretty.T"} \\
  @{index_ML Syntax.string_of_typ: "Proof.context -> typ -> string"} \\
  @{index_ML Syntax.string_of_term: "Proof.context -> term -> string"} \\
  \end{mldecls}

  \<^descr> @{ML Syntax.read_typs}~\<open>ctxt strs\<close> parses and checks a simultaneous list
  of source strings as types of the logic.

  \<^descr> @{ML Syntax.read_terms}~\<open>ctxt strs\<close> parses and checks a simultaneous list
  of source strings as terms of the logic. Type-reconstruction puts all parsed
  terms into the same scope: types of free variables ultimately need to
  coincide.

  If particular type-constraints are required for some of the arguments, the
  read operations needs to be split into its parse and check phases. Then it
  is possible to use @{ML Type.constraint} on the intermediate pre-terms
  (\secref{sec:term-check}).

  \<^descr> @{ML Syntax.read_props}~\<open>ctxt strs\<close> parses and checks a simultaneous list
  of source strings as terms of the logic, with an implicit type-constraint
  for each argument to enforce type @{typ prop}; this also affects the inner
  syntax for parsing. The remaining type-reconstruction works as for @{ML
  Syntax.read_terms}.

  \<^descr> @{ML Syntax.read_typ}, @{ML Syntax.read_term}, @{ML Syntax.read_prop} are
  like the simultaneous versions, but operate on a single argument only. This
  convenient shorthand is adequate in situations where a single item in its
  own scope is processed. Do not use @{ML "map o Syntax.read_term"} where @{ML
  Syntax.read_terms} is actually intended!

  \<^descr> @{ML Syntax.pretty_typ}~\<open>ctxt T\<close> and @{ML Syntax.pretty_term}~\<open>ctxt t\<close>
  uncheck and pretty-print the given type or term, respectively. Although the
  uncheck phase acts on a simultaneous list as well, this is rarely used in
  practice, so only the singleton case is provided as combined pretty
  operation. There is no distinction of term vs.\ proposition.

  \<^descr> @{ML Syntax.string_of_typ} and @{ML Syntax.string_of_term} are convenient
  compositions of @{ML Syntax.pretty_typ} and @{ML Syntax.pretty_term} with
  @{ML Pretty.string_of} for output. The result may be concatenated with other
  strings, as long as there is no further formatting and line-breaking
  involved.


  @{ML Syntax.read_term}, @{ML Syntax.read_prop}, and @{ML
  Syntax.string_of_term} are the most important operations in practice.

  \<^medskip>
  Note that the string values that are passed in and out are annotated by the
  system, to carry further markup that is relevant for the Prover IDE @{cite
  "isabelle-jedit"}. User code should neither compose its own input strings,
  nor try to analyze the output strings. Conceptually this is an abstract
  datatype, encoded as concrete string for historical reasons.

  The standard way to provide the required position markup for input works via
  the outer syntax parser wrapper @{ML Parse.inner_syntax}, which is already
  part of @{ML Parse.typ}, @{ML Parse.term}, @{ML Parse.prop}. So a string
  obtained from one of the latter may be directly passed to the corresponding
  read operation: this yields PIDE markup of the input and precise positions
  for warning and error messages.
\<close>


section \<open>Parsing and unparsing \label{sec:parse-unparse}\<close>

text \<open>
  Parsing and unparsing converts between actual source text and a certain
  \<^emph>\<open>pre-term\<close> format, where all bindings and scopes are already resolved
  faithfully. Thus the names of free variables or constants are determined in
  the sense of the logical context, but type information might be still
  missing. Pre-terms support an explicit language of \<^emph>\<open>type constraints\<close> that
  may be augmented by user code to guide the later \<^emph>\<open>check\<close> phase.

  Actual parsing is based on traditional lexical analysis and Earley parsing
  for arbitrary context-free grammars. The user can specify the grammar
  declaratively via mixfix annotations. Moreover, there are \<^emph>\<open>syntax
  translations\<close> that can be augmented by the user, either declaratively via
  @{command translations} or programmatically via @{command
  parse_translation}, @{command print_translation} @{cite
  "isabelle-isar-ref"}. The final scope-resolution is performed by the system,
  according to name spaces for types, term variables and constants determined
  by the context.
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{index_ML Syntax.parse_typ: "Proof.context -> string -> typ"} \\
  @{index_ML Syntax.parse_term: "Proof.context -> string -> term"} \\
  @{index_ML Syntax.parse_prop: "Proof.context -> string -> term"} \\[0.5ex]
  @{index_ML Syntax.unparse_typ: "Proof.context -> typ -> Pretty.T"} \\
  @{index_ML Syntax.unparse_term: "Proof.context -> term -> Pretty.T"} \\
  \end{mldecls}

  \<^descr> @{ML Syntax.parse_typ}~\<open>ctxt str\<close> parses a source string as pre-type that
  is ready to be used with subsequent check operations.

  \<^descr> @{ML Syntax.parse_term}~\<open>ctxt str\<close> parses a source string as pre-term that
  is ready to be used with subsequent check operations.

  \<^descr> @{ML Syntax.parse_prop}~\<open>ctxt str\<close> parses a source string as pre-term that
  is ready to be used with subsequent check operations. The inner syntax
  category is @{typ prop} and a suitable type-constraint is included to ensure
  that this information is observed in subsequent type reconstruction.

  \<^descr> @{ML Syntax.unparse_typ}~\<open>ctxt T\<close> unparses a type after uncheck
  operations, to turn it into a pretty tree.

  \<^descr> @{ML Syntax.unparse_term}~\<open>ctxt T\<close> unparses a term after uncheck
  operations, to turn it into a pretty tree. There is no distinction for
  propositions here.


  These operations always operate on a single item; use the combinator @{ML
  map} to apply them to a list.
\<close>


section \<open>Checking and unchecking \label{sec:term-check}\<close>

text \<open>
  These operations define the transition from pre-terms and fully-annotated
  terms in the sense of the logical core (\chref{ch:logic}).

  The \<^emph>\<open>check\<close> phase is meant to subsume a variety of mechanisms in the manner
  of ``type-inference'' or ``type-reconstruction'' or ``type-improvement'',
  not just type-checking in the narrow sense. The \<^emph>\<open>uncheck\<close> phase is roughly
  dual, it prunes type-information before pretty printing.

  A typical add-on for the check/uncheck syntax layer is the @{command
  abbreviation} mechanism @{cite "isabelle-isar-ref"}. Here the user specifies
  syntactic definitions that are managed by the system as polymorphic \<open>let\<close>
  bindings. These are expanded during the \<open>check\<close> phase, and contracted during
  the \<open>uncheck\<close> phase, without affecting the type-assignment of the given
  terms.

  \<^medskip>
  The precise meaning of type checking depends on the context --- additional
  check/uncheck modules might be defined in user space.

  For example, the @{command class} command defines a context where \<open>check\<close>
  treats certain type instances of overloaded constants according to the
  ``dictionary construction'' of its logical foundation. This involves ``type
  improvement'' (specialization of slightly too general types) and replacement
  by certain locale parameters. See also @{cite "Haftmann-Wenzel:2009"}.
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{index_ML Syntax.check_typs: "Proof.context -> typ list -> typ list"} \\
  @{index_ML Syntax.check_terms: "Proof.context -> term list -> term list"} \\
  @{index_ML Syntax.check_props: "Proof.context -> term list -> term list"} \\[0.5ex]
  @{index_ML Syntax.uncheck_typs: "Proof.context -> typ list -> typ list"} \\
  @{index_ML Syntax.uncheck_terms: "Proof.context -> term list -> term list"} \\
  \end{mldecls}

  \<^descr> @{ML Syntax.check_typs}~\<open>ctxt Ts\<close> checks a simultaneous list of pre-types
  as types of the logic. Typically, this involves normalization of type
  synonyms.

  \<^descr> @{ML Syntax.check_terms}~\<open>ctxt ts\<close> checks a simultaneous list of pre-terms
  as terms of the logic. Typically, this involves type-inference and
  normalization term abbreviations. The types within the given terms are
  treated in the same way as for @{ML Syntax.check_typs}.

  Applications sometimes need to check several types and terms together. The
  standard approach uses @{ML Logic.mk_type} to embed the language of types
  into that of terms; all arguments are appended into one list of terms that
  is checked; afterwards the type arguments are recovered with @{ML
  Logic.dest_type}.

  \<^descr> @{ML Syntax.check_props}~\<open>ctxt ts\<close> checks a simultaneous list of pre-terms
  as terms of the logic, such that all terms are constrained by type @{typ
  prop}. The remaining check operation works as @{ML Syntax.check_terms}
  above.

  \<^descr> @{ML Syntax.uncheck_typs}~\<open>ctxt Ts\<close> unchecks a simultaneous list of types
  of the logic, in preparation of pretty printing.

  \<^descr> @{ML Syntax.uncheck_terms}~\<open>ctxt ts\<close> unchecks a simultaneous list of terms
  of the logic, in preparation of pretty printing. There is no distinction for
  propositions here.


  These operations always operate simultaneously on a list; use the combinator
  @{ML singleton} to apply them to a single item.
\<close>

end
