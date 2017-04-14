(*<*)
theory Paper
imports Paper_Defs
begin
(*>*)
text \<open>
\section{Notation} \label{sec:notation}
This section introduces the Isabelle/HOL~\cite{Nipkow_PW:Isabelle}
notation used in this paper, where different from standard mathematical notation.

We denote the space of total functions by @{text "\<Rightarrow>"}, and
write type variables as @{typ 'a}, @{typ 'b}, etc.
The notation @{text "t::\<tau>"} means that term @{term t} has type @{text \<tau>}.
The @{text option} type

\begin{center}
  @{datatype option} 
\end{center}

\noindent
adjoins a new element @{const None} to a type @{typ 'a}. We use @{typ "'a option"} to model partial
functions, writing @{term "Some a"} instead of @{term [source] "Some a"} and
@{typ [source] "'a \<rightharpoonup> 'b"} instead of @{typ "'a \<Rightarrow> 'b option"}.

Assertions in separation logic typically are functions from the state to bool, \ie
@{typ "'s => bool"}. We lift the standard logical connectives @{text "\<and>"},
@{text "\<or>"}, @{text "\<not>"}, and @{text "\<longrightarrow>"} point-wise to the function space in the spirit
of standard separation logic. For instance
\begin{center}
  @{thm pred_impl_def}
\end{center}

For modelling the example programs in this paper, we use a deterministic state monad.
Since we will be interested in distinguishing failed executions, we add a failure flag in
the style of other monadic Hoare logic frameworks~\cite{Cock_KS_08cp}. This
means, a program execution has the type \mbox{@{typ "'s => 'r \<times> 's \<times> bool"}},
\ie a function that takes a state and returns a result, a new state, and a flag indicating whether 
the execution failed or not. Sequential composition, as usual, is denoted by @{text "\<bind>"}.

\isastartskip
@{thm [display,indent=5] bind_def}
\isaendskip

\noindent We use @{text "do"}-notation for sequential composition in larger computations, \eg
\begin{center}
@{term [mode=no_break] "do { x \<leftarrow> f; g x; h x } :: ('s,'a) det_monad"}
\end{center}
\<close>

text \<open>
\section{Hoare Logic and Separation Logic}\label{sec:HLandSL}

\emph{Hoare logic} or \emph{Floyd-Hoare logic}~\cite{Hoare_69,Floyd_67}
is the standard logic for program analysis, based on the eponymous \emph{Hoare triple}:
@{term "\<lbrace>P\<rbrace> m \<lbrace>Q\<rbrace>"} (originally written \mbox{@{text "P {m} Q"}} by Hoare~\cite{Hoare_69}). 

Initially, Hoare logic considered \emph{partial correctness} only~\cite{Hoare_69}, ignoring
termination. In our monadic context, where we identify termination and failed execution, this
translates to
\begin{center}
@{thm valid_def}
\end{center}
If the precondition @{term P} holds before the execution of @{term m},
\emph{and} @{term m} terminates successfully (@{term "f'"} is false)
then the postcondition @{term Q} holds afterwards.
Successful termination needs to be proven separately.
If @{term m} fails to  terminate successfully under @{term P}, \ie by non-termination
or other program failure, then any postconditions forms a valid Hoare triple.

\emph{Total correctness} combines termination with correctness.
\begin{center}
   @{thm validNF_def}
\end{center}

For total correctness, whenever @{term P} holds, @{term m} \emph{will} terminate successfully,
and the result satisfies @{term Q}. If @{term P} causes the program to fail, then no
such triple exists.

\begin{example}
  Assume the function @{term "delete_ptr p"}, which clears the 
  allocated memory pointed to by @{term p}, and fails if @{term p} does not exist.
  
  The Hoare triple @{thm delete_ptr_valid_simple} describes the situation where the heap consists 
  of pointer @{term p} only, pointing to some value in the memory, and otherwise the heap is 
  empty.\footnote{We will explain the heap model in detail later in this section.}
  After the program @{term "delete_ptr p"} terminates (which it will) the heap is empty, 
  which is denoted by @{term \<box>}. 

  However, this specification is limiting since it only
  allows one particular heap configuration as precondition. Consider two further scenarios,
  namely heap configurations where @{term p} does not exist (\eg the empty heap),
  and heap configurations with additional memory.
  
  In the first scenario, since  @{term "delete_ptr p"} fails if the referenced pointer
  does not exist, the Hoare triple @{term "\<lbrace>\<box>\<rbrace> free p \<lbrace>Q\<rbrace>"} would be true under partial
  correctness for any @{term Q}, and false under total correctness.

  In the second scenario, with additional memory, this additional memory remains
  unchanged during the execution of @{term "delete_ptr p"}. This is the case separation logic
  deals with.
\end{example}

\emph{Separation logic (SL)}~(\eg \cite{Reynolds_09}) extends Hoare logic by assertions to
express separation between memory regions, which allows reasoning about mutable data structures.
It is built around \emph{separating conjunction}, denoted by 
@{text "*"}. It asserts that the heap can be split into two disjoint parts where its 
two arguments hold.

An indispensable ingredient of SL is the \emph{frame rule}
\begin{center}
 @{term [mode=Rule]"\<lbrace>P\<rbrace> m \<lbrace>\<lambda>_. Q\<rbrace>  \<Longrightarrow> \<lbrace>P \<and>* R\<rbrace> m \<lbrace>\<lambda>_. Q \<and>* R\<rbrace>"}
\end{center}
The rule assumes that no variable occurring free in @{term R} is modified by @{term m}.
It states that a program @{term m} which executes correctly in a small state satisfying 
its precondition @{term P}, with postcondition @{term Q}, can also execute in any larger state 
(satisfying \mbox{@{term "P \<and>* R"})} and that the execution will not affect the additional part of the 
state---the side conditions enforce this.

SL can be built upon separation algebras, which are commutative partial 
monoids~\cite{CalcagnoEtAl_07}. The algebra offers a binary operation @{text "+"} and a neutral 
element @{text "0"}, such that whenever @{term "x + y"} is defined, @{text "+"} is commutative and 
associative, and \mbox{@{text "x + 0 = x"}}.
Our framework is built upon an existing Isabelle framework~\cite{Klein_KB_12cp,Separation_Algebra-AFP}, 
which uses a total function @{text "+"} in combination with another operation @{text "##"}, 
representing the aforementioned disjointness.

Using these operations, separating conjunction is defined as
\vspace{-0.45mm}

\begin{center}
@{thm conj_semantics}
\vspace{-0.45mm}
\end{center}
which implies the associativity and commutativity of @{text "*"}.

The standard model of SL, and of a separation algebra, uses heaps. The term 
@{text "(p \<^latex>\<open>\\!\<close>\<mapsto> \<^latex>\<open>\\!\<close>v) h"}
indicates that the pointer @{term p} on heap @{term h} is allocated and points to value~@{term v}.
% Since the pointer may not be allocated, the Isabelle formalisation uses the option type.
The term @{term "p \<mapsto> -"} indicates an arbitrary value of the pointer. 

A heap is a partial function from addresses (pointers) to values.
The operation @{term "h\<^sub>1 ## h\<^sub>2"} checks whether the domains of @{term "h\<^sub>1"}
and @{term "h\<^sub>2"} are disjoint. When \mbox{@{term "h\<^sub>1 ## h\<^sub>2"}} evaluates to true, 
\mbox{@{term "h\<^sub>1 + h\<^sub>2"}} `merges' the heap. The formal definitions are straightforward 
and omitted here.

The operations @{text "##"} and @{text "+"} define a partial order, which 
formalises subheaps:
\vspace{-0.45mm}

\begin{center}
@{thm subheap_pretty}
\vspace{-0.45mm}
\end{center}

SL often leads to simple proofs of pointer manipulation for data structures.
Classical examples of such data structures are simply and doubly-linked lists, trees, as well as 
directed acyclic graphs (DAGs)~\cite{Reynolds_02,HoborVillard_13}.

\emph{Separating implication} @{term "P \<longrightarrow>* Q"}, also called \emph{magic wand}, is another basic 
operator of SL. When applied to a heap @{term h} it asserts that extending @{term h} by a 
disjoint heap satisfying @{term P} will guarantee that @{term Q} holds on the combined heap:
\mbox{@{thm sep_impl_def_rename}}. Ishtiaq and O'Hearn introduced \wand for reasoning in the 
presence of sharing~\cite{IshtiaqOHearn_01}.

It is known (\eg \cite{DangEtAl_11}) that @{text "*"} and @{text "\<longrightarrow>*"} are lower and upper 
adjoints of a Galois connection (\eg \cite{Birkhoff_67}).
This abstract relationship implies many useful rules such as, 
currying\label{wand_curry} @{thm conj_impl_curry_prettyprint},
decurrying @{thm conj_impl_decurry_prettyprint}, and
modus ponens @{thm conj_impl_inference}.
As we will see, \wand is useful for backward reasoning.

The literature on SL uses another `basic' operator of SL, \emph{septraction}~\cite{VafeiadisParkinson_07}:
\vspace{-0.45mm}

\begin{center}
 @{thm septration_semantics}
\vspace{-0.45mm}
\end{center}
It is the dual of \wand, \ie @{thm (lhs) septraction_def} @{text "="} @{thm (rhs) septraction_def},
and denotes that the heap can be extended with a state satisfying @{term P}, so that
the extended state satisfies @{term Q}.
Septraction plays an important role in combining SL with rely-guarantee 
reasoning~\cite{VafeiadisParkinson_07}, and when looking at shared data structures 
such as DAGs~\cite{HoborVillard_13}. 
\pagebreak[3]
\<close>

text \<open>
\section{Separating Coimplication}\label{sec:snake}
While separating conjunction, separating implication, and septraction, as well as their relationships
to each other are well studied and understood, one operation of SL is missing.

We define \emph{\snake}, denoted by @{text " \<leadsto>*"}, as
\begin{center}
  @{thm snake_semantics}
\end{center}
It states that whenever there is a subheap @{term "h\<^sub>1"} 
satisfying @{term P} then the remaining heap satisfies @{term Q}.
To the best of our knowledge, we are the first to define this operator and explore 
its properties. It is the dual of separating conjunction, \ie
\begin{center}
  @{thm snake_dual [folded eq'_def]}
\end{center}
\noindent
In the latter form (doubly negated conjunction) it \emph{does} appear in the literature: the 
\emph{dangling operator} of Vafeiadis and Parkinson~\cite{VafeiadisParkinson_07} uses subterms of the form 
@{term "not ((p \<mapsto> -) \<and>* sep_true')"}, which equals @{term "(p \<mapsto> -) \<leadsto>* sep_false'"}, and
the \emph{substraction operator} by Calcagno et al.~\cite{CalcagnoEtAl_11}, used for comparing 
bi-abduction solutions, uses terms of the form @{term "P \<leadsto>* sep_empty"}.
These occurrences indicate that \snake is an important, unexplored aspect of SL. 
As we will show, it is also the crucial ingredient to set up forward reasoning for SL.

Since \snake forms a Galois connection with septraction, many useful theorems follow 
from abstract algebraic reasoning. For example, similar to the rules stated above for @{text "*"} 
and @{text "\<longrightarrow>*"}, we get rules for currying, decurrying and cancellation:

\begin{center}
  @{thm [mode=Rule] sep_snake_curry_prettyprint} \mbox{\small(\sc curry)}
  \quad
  @{thm [mode=Rule] sep_snake_decurry_prettyprint} \mbox{\small(\sc decurry)}
  \quad
  @{thm [mode=XRule] sep_snake_inf} \mbox{\hypertarget{snake_inf}{\small(\sc canc)}}
\end{center}
It is also straightforward to show that \snake is isotone in one, and antitone in the other
argument, \ie
\begin{center}
  @{thm [mode=Rule] snake_impl1} \qquad
  @{thm [mode=Rule] snake_impl2}
\end{center}

\begin{figure}[t]
\centering
\scalebox{0.75}{
\begin{tikzpicture} [align=center,node distance=14mm and 28mm] 
  \node[point] (conj) {@{term "P \<and>* Q"}};
  \node[point, right=of conj] (impl) {@{term "P \<longrightarrow>* Q"}};
  \node[point, below=of conj] (snake) {@{term "P \<leadsto>* Q"}};
  \node[point, right=of snake] (sept) {@{term "P -* Q"}};
  
  \draw[pil, bend right=15]
    (conj)    edge[<->] node[auto]{dual}    (snake)  
    (snake)   edge[<->] node[auto]{Galois} (sept)
    (sept)    edge[<->] node[auto]{dual}    (impl)
    (impl)    edge[<->] node[auto]{Galois} (conj)
  ;
\end{tikzpicture}
\vspace{-1mm}
}
\caption{Relationship between operators of separation logic \label{fig_sl_ops}}
\vspace{-1mm}
\end{figure}

\Snake is not only interesting because it completes the set of `nicely' connected operators for SL (see 
\autoref{fig_sl_ops}), 
it is also useful to characterise specific heap configurations. 
For example, @{term "(P \<leadsto>* sep_false') h"}
states that @{term P} is not satisfied by any subheap of @{term "h"}
\begin{center}
  @{thm p_snake_false_subheap[folded eq'_def]}
\end{center}
\pagebreak[3]

\noindent From this we immediately derive @{thm  sep_snake_dne'} and @{thm sep_coimpl_dne'}.


While properties concerning @{text "\<leadsto>*"} and @{text "-*"} mostly follow from the Galois connection, 
other relationships need to be derived `manually'. Using the fact that \snake
satisfies contraposition, \ie @{thm sep_coimpl_contrapos[folded eq'_def]}, we can derive rules  
of modus ponens and modus tollens:
\vspace{-0.95mm}

\begin{center}
  @{thm [mode=XRule] conj_snake_mp}
  \qquad
  @{thm [mode=XRule] conj_snake_mt}
\vspace{-0.95mm}
\end{center}

SL considers different classes of assertions~\cite{Reynolds_09}. 
For examples, a \emph{precise assertion} characterises an unambiguous heap portion, \ie
\begin{center}
  @{thm precise_pretty_print}
\end{center}
While it is known that precision can be characterised by a distributivity axiom~\cite{DangEtAl_11}, \ie 
@{thm precise_distribute [folded eq'_def]}, 
separating co\-implication yields a nicer characterisation:
\vspace{-0.95mm}

\begin{center}
  @{thm precise_characterise_var [folded eq'_def]}
\vspace{-0.95mm}
\end{center}

\noindent On the one hand this equivalence eliminates one of the @{text "\<forall>"}-quantifiers, which simplifies 
reasoning; on the other hand it directly relates separating conjunction with coimplication, stating 
that if @{term "P"} and @{term "Q"} hold on a heap, and one pulls out an arbitrary subheap satisfying 
@{term P}, the remaining heap must satisfy @{term Q}. Obviously, this relationship between 
@{text "*"} and @{text "\<leadsto>*"} does not hold in general since \snake may pull out the 
`wrong' subheap satisfying @{term P}.

As a consequence, using \hyperlink{snake_inf}{(\sc canc)}, we immediately get 
\vspace{-0.95mm}
\begin{equation}\label{eq:prec_canc}
  @{thm [mode=Rule,mode=paren] septraction_precise_conj'}
\vspace{-0.95mm}
\end{equation}

\noindent We can also connect \wand and coimplication directly:
\vspace{-0.95mm}

\begin{center}
 	@{thm [mode=XRule] some_name}
\vspace{-0.95mm}
\end{center}

\noindent Our Isabelle files~\cite{BannisterHoefnerKlein_17} contain many more properties of \snake.
The most important usage of \snake, however, is its application for forward reasoning, as we will 
demonstrate in \autoref{sec:forward}.

\begin{example}
With \snake we can fully specify \mbox{@{text "delete_ptr p"}} in a way that matches intuition:
\vspace{-0.95mm}

\begin{center}
   @{thm delete_ptr_sp}
\vspace{-0.95mm}
\end{center}

\noindent This rule states that the precondition should satisfy @{term R}, when the pointer is
deleted, and the pointer existed in the first place.
\end{example}
\<close>

text \<open>
\vspace{-2.9mm}
\section{Walking Backwards}\label{sec:backward}
\emph{Backward reasoning}~\cite{Dijkstra_76} or \emph{reasoning in weakest-precondition style}
proceeds backwards from a given postcondition @{term Q} and a given program @{term m} by 
determining the \emph{weakest} precondition @{text "wp(m,Q)"} such that 
@{text "\<lbrace>wp(m,Q)\<rbrace> m \<lbrace>Q\<rbrace>"} is a
\pagebreak[3]
 valid Hoare triple. Backward reasoning is well established 
for formal programming languages. For example the weakest precondition
@{text "wp(m\<^sub>1;m\<^sub>2,Q)"} for a sequential program equals @{text "wp(m\<^sub>1,wp(m\<^sub>2,Q))"}---more equations
are nicely summarised in~\cite{Dijkstra_76,GordonCollavizza_10}.

Using these well-established equations, backward reasoning in Hoare logic is more or 
less straightforward. In SL, however, it comes at a price, because specifications usually have 
the form @{term "\<lbrace>P \<and>* R\<rbrace> m \<lbrace>\<lambda>_. Q \<and>* R\<rbrace> "}. Whenever either a precondition or a postcondition is 
given, one needs to \emph{calculate the frame} @{term R}, which may be challenging since @{term R} 
can be arbitrarily complex.

\begin{example}
Suppose we have a program
\begin{isatab}
  @{thm [mode=no_break] copy_ptr_def}
\end{isatab}

\noindent which copies the value at pointer @{term p}
to the pointer @{term p'}. Its natural specification is 
\begin{equation}\label{spe:copy_ptr}
  @{thm copy_ptr_valid}
\end{equation}
\noindent If the program @{term  copy_ptr} is part of a larger program being ana\-lysed, 
the postcondition will be more complicated than just
{@{text "\<lbrace>p \<^latex>\<open>\\!\<close> \<mapsto> \<^latex>\<open>\\!\<close>x * p' \<^latex>\<open>\\!\<close>\<mapsto> \<^latex>\<open>\\!\<close>x * R\<rbrace>"}}.
Let us assume it is 
@{text "\<lbrace>p' \<^latex>\<open>\\!\<close>\<mapsto> \<^latex>\<open>\\!\<close>v * a \<^latex>\<open>\\!\<close>\<mapsto> \<^latex>\<open>\\!\\_\<close> * p \<mapsto> v * R'\<rbrace>"}. 
To determine the precondition, using (\ref{spe:copy_ptr}), the postcondition needs to be 
in the format (@{term "DUMMY \<and>* R"}); 
%Hence 
one has
to calculate the frame @{term R}---in our example @{term "a \<mapsto> - \<and>* R'"}---which 
is not always straightforward.
\end{example}

There is a well-known solution to this problem in SL \cite{Reynolds_09},
which follows immediately from the Galois connection mentioned in 
\autoref{sec:HLandSL}.
\begin{equation}\label{sep_wp_simple}
  @{thm sep_wp_simple' [where f=m]}
\end{equation}
Transforming specifications into the latter form has the advantage that 
 no frame calculation is needed, and the rule can be applied to \emph{any} postcondition. 
Applying such rules can easily be mechanised.

% The second is that said tool does not need to understand how to massage SL conjuncts into the 
%appropriate form to do so. The resulting proof obligation can be solved by a dedicated solver, 
%allowing for a neat separation of concerns. 

\begin{example}
Using equivalence (\ref{sep_wp_simple}), the specification for @{term copy_ptr} (\ref {spe:copy_ptr}) 
becomes
\begin{center}
 @{thm copy_ptr_wp'}
\end{center}
\end{example}
\noindent When performing a backward analysis it is important to simplify generated preconditions.
The shape of the right hand side of (\ref{sep_wp_simple}) 
shows that any automatic simplifier has to deal with interleavings of @{text "*"} and 
@{text "\<longrightarrow>*"}. The difficulty of managing \wand means that many solvers do not provide 
support for it.~This in turn slowed its widespread use~\cite{Berdine_05,LeePark_14}. 
\emph{Automatic} solvers for separating implication exist for formulas over a \emph{restricted} 
set of predicates~\cite{HouGoreTiu_15}; the problem for \emph{arbitrary} pre- and postconditions
is undecidable~\cite{CalcagnoEtAl_01}.
Since we aim at a reasoning framework for \emph{arbitrary} conditions 
we cannot use such solvers~in~general. 

Instead, we developed an interactive semi-solver.
Our framework builds on top of an existing library~\cite{Separation_Algebra-AFP}, which is
based on separation algebras (see \autoref{sec:HLandSL}).
This brings the advantage that we can easily apply abstract rules of SL, such as 
\mbox{@{thm conj_impl_inference}}, which is indispensable for simplifying such preconditions.
Moreover, the developed theories and tactics are independent of the concrete heap model, 
which allows us to apply the tool to a wide range of problem domains. 

Our set of semi-solvers for Isabelle/HOL can
be combined with other standard proof tactics, such as @{method clarsimp}, @{method metis}, etc. 
\begin{itemize}
 \item The tactic @{method wp}~\cite{Cock_KS_08cp} implements weakest-precondition 
reasoning through the combination of user-provided Hoare triples in combination with a set of rules 
for structured decomposition of postconditions. We extended this tactic to allow the addition 
of theorems for transforming Hoare triples into weakest-precondition format,
as presented in (\ref{sep_wp_simple}).

  \item We extended the tactic @{method sep_cancel}~\cite{Separation_Algebra-AFP}, 
which aims at solving formulas by means of the cancellation rule
\vspace{-1.2ex}%compensate half-empty line 
\begin{center}
 @{thm [mode=Rule] sep_cancellation}
\end{center}
It now offers support for \wand, and, when feasible, applies the currying rule presented in 
\autoref{sec:HLandSL}, eliminating \wand.

It is worth mentioning that applying (\ref{sep_wp_simple})
introduces an ordering in how a goal needs to be resolved by our tactics: 
the calculated (weakest) preconditions have the form  @{term "(P \<and>* (Q \<longrightarrow>* R))" }, 
where @{term P}  is the pre- and @{term Q} the postcondition. Therefore the currying rule can only be
 applied \emph{after} @{term P} has been eliminated.
\end{itemize}

By default, the tactic @{method sep_cancel}
only cancels identical conjuncts;
however, additional rules can be added, a typical example is @{thm maps_to_maps_to_ex'}\,.
It also resolves \wand in assumptions through the
modus-ponens rule.
%, though this appears fairly infrequently in our proofs.

Although these tactics are simple, they are sufficient to resolve
every use of the weakest-precondition transformation we employed in the verification of seL4 system 
initialisation~\cite{Boyton_ABFGGKLS_13cp} (about $15,000$ lines of proof script),
that is, the general undecidability of \wand is usually not a problem in practice.

To illustrate backward reasoning in SL, we conclude this section with a few detailed examples.
When applying weakest-precondition reasoning in the area of system verification, such 
as the aforementioned seL4 system initialisation, complicated programs are built from four basic  
operations, which manipulate the heap: 
@{term new_ptr} allocates memory for a pointer, 
@{term delete_ptr} removes a pointer from the heap, 
@{term set_ptr} assigns a value to a pointer, and 
@{term get_ptr} reads a value, respectively.
The specifications of these operations are the following:
\begin{center}
@{thm new_ptr_valid}\\
@{thm delete_ptr_valid}\\ 
@{thm set_ptr_valid} \\
@{thm get_ptr_valid''}
\end{center}
\noindent
%
In general the postcondition @{term R} is a predicate that takes two parameters: the return value
@{term rv} of the function (\eg for @{const get_ptr}),
and the state @{term s} after termination. When there is no return value (\eg for @{const set_ptr}),
we omit the first parameter.

Using (\ref{sep_wp_simple}), or the tactic @{method wp}, we transform these specifications into 
\begin{center}
@{thm new_ptr_wp_pretty}\\
@{thm set_ptr_wp}\\
@{thm get_ptr_wp_ex}
\end{center}
The rule for @{term delete_ptr} already has the appropriate form. 

From these basic operations we can build more complex programs and perform backwards reasoning.
Let us look at the example @{term "swap_ptr p p'"}:
\isastartskip
@{thm [display,indent=5] swap_ptr_def}
\isaendskip
We use the specifications of the basic operators to prove
\vspace{-.5mm}
\begin{center}
  {@{thm swap_ptr_valid}}
\vspace{-.5mm}
\end{center}

\noindent With the equation @{text "wp(m\<^sub>1;m\<^sub>2,Q) = wp(m\<^sub>1,wp(m\<^sub>2,Q))"}, and starting from the postcondition, 
our framework automatically derives
the following precondition~@{text "pre"}:\!
\isastartskip
@{thm [display] (xconcl) swap_ptr_wp_problem_ximp}
\vspace{-.7mm}
\isaendskip

The goal is to prove that the given precondition of @{thm (xprem 1) swap_ptr_wp_problem_ximp}
implies @{text "pre"}. Before we can apply our machinery, the existential quantifiers need to be 
instantiated. In the example at hand, the instantiation is trivial, and the rest is automatically 
resolved by the tactic @{method sep_cancel}.
\pagebreak[3]

Although resolving existential quantifiers cannot be automated in general, in practice the situation 
is often easier. The reason is that the predicates involved in pre- and postconditions are often precise 
assertions, which means they characterise unambiguous heaps. This means that instantiation of 
existential quantifiers can often be solved by simple name matching, 
which can be passed to Isabelle/HOL without any input from the user.
\<close>  
  
text \<open>
\section{Walking Forwards}\label{sec:forward}
\emph{Forward reasoning} uses 
strongest postconditions~\cite{Floyd_67}, rather than weakest preconditions. 
It proceeds forwards from a given precondition @{term P} and a given program @{term m} by 
calculating the strongest postcondition @{text "sp(m,P)"}.
To enable forward reasoning for SL it is desirable to transform a Hoare triple of the form 
\mbox{@{term "\<lbrace>P \<and>* R\<rbrace> m \<lbrace>\<lambda>_.Q \<and>* R\<rbrace>"}} into a Hoare triple of the form @{term "\<lbrace>R\<rbrace>m\<lbrace>post\<rbrace>"},
similar to Equation~(\ref{sep_wp_simple}).

Hobor and Villard~\cite{HoborVillard_13} present the rule \hypertarget{rule:fmramify}{{\sc FWRamify}}:
\begin{center}
 @{thm [mode=Rule] bad_strongest_post' [where f=m]}
\end{center}
\pagebreak[3]

\noindent This rule is a `complification' of @{thm bad_strongest_post_simple'' [where f=m]}, which states that 
a terminating program @{term m}, which is specified by @{term "P \<and>* F"} and  @{term "Q \<and>* F"},
will end up in a state satisfying @{term "Q \<and>* (P -* R)"} \emph{if} @{term R} contains a subheap
satisfying @{term P}, which is characterised by @{thm (prem 2) bad_strongest_post' [where f=m]}.

This rule has the severe limitation that the condition @{thm (prem 2) bad_strongest_post'},
is as hard to check as reasoning via ordinary weakening of the precondition.
Moreover, it requires calculating the result of removing @{term P} from the precondition twice, 
once as part of the frame calculation, and once as resolution of septraction.

Using \snake we derive an equivalence similar to~(\ref{sep_wp_simple}):
\begin{equation}\label{sep_sp_simple}
  @{thm sep_sp_simple}
\end{equation}

It is based on a type of reverse modus ponens, @{thm [mode=paren] sep_antimp}, 
which follows immediately from the above-mentioned Galois connection.

We do not believe that it is possible to find a general rule to transform Hoare triples 
@{term "\<lbrace>P \<and>* Q\<rbrace> m \<lbrace>\<lambda>_. Q \<and>* R\<rbrace>"} into strongest-postcondition form, without introducing additional 
proof burden, as it happens in \hyperlink{rule:fmramify}{{\sc FWRamify}}. However, as discussed in \autoref{sec:snake}, 
the term @{term "P \<leadsto>* Q"} states that @{term Q} holds, whenever @{term P} is removed from the 
heap---removal is only feasible if @{term P} exists.

In practice this means that specifications of the form 
\mbox{@{term "\<lbrace>P \<and>* Q\<rbrace> m \<lbrace>\<lambda>_. Q \<and>* R\<rbrace>"}}
can almost always be rewritten into the form  @{term "\<lbrace>P \<leadsto>* Q\<rbrace> m \<lbrace>\<lambda>_. Q \<and>* R\<rbrace>"}.

\begin{example}
Using the specifications of the heap operations, and Rule (\ref{sep_sp_simple}) yields
\begin{center}
  @{thm new_ptr_sp}\\
  @{thm delete_ptr_sp}\\
  @{thm set_ptr_sp}\\
  @{thm get_ptr_sp}
\end{center}

The precondition of @{text "set_ptr"} assumes the hypothetical case that if we had the required 
resource (@{term "p \<mapsto> -"}), we would have a predicate @{term R} corresponding to the rest of the heap.
In the postcondition, the resource \emph{does} exist and is assigned to the correct value 
@{term v}.
\end{example}

Similarly to backward reasoning, forward reasoning in larger programs generates lengthy 
postconditions that need to be simplified automatically. 
To understand the format of the generated postconditions, we 
look at the program \mbox{@{term "swap_ptr p p'"}}, which involves all four heap operations.
For the given precondition 
@{text "\<lbrace>p \<^latex>\<open>\\!\<close> \<mapsto> \<^latex>\<open>\\!\<close>v * p' \<^latex>\<open>\\!\<close> \<mapsto> \<^latex>\<open>\\!\<close>v' * R\<rbrace>"}
we automatically generate the postcondition~@{text "post"}:

\isastartskip
@{thm [display] (xprem 1) swap_ptr_sp_problem_ximp}
\isaendskip

To prove correctness of @{term "swap_ptr"}, @{text "post"} has to imply
\mbox{@{thm (xconcl) swap_ptr_sp_problem_ximp}}.
\pagebreak[3]

The generated postcondition has a regular pattern: 
as one moves from the innermost 
sub-formula to the outermost, required resources are progressively septracted, 
and resources set or generated 
are added by separating conjunction.

Simplifying such formulas can be automated.
First, we push existential quantifiers to the outside of the formula.
Secondly, we simplify matching septractions~and conjunctions by the rule 
\begin{center}
@{thm [mode=Rule,mode=paren] septract_maps_to [where s=h]}
\end{center}
\noindent Thirdly, we move the generated equalities between values to the outer layers 
of the formula---as far as possible, which often makes it possible to re-apply the simplification 
rule.
 
This process is repeated until all the septractions are resolved, upon which the rest of the proof
is handled by the tactic @{method sep_cancel}.

We implemented this tactic, called @{method septract_cancel}, using the Eisbach
method language~\cite{Matichuk_MW_16}.
The tactic is able to prove @{term swap_ptr} fully automatically.
 
Another example we applied forward reasoning to is in-place list reversal.
\isastartskip
@{thm [display,indent=5,margin=95] list_rev_def}
\isaendskip
\noindent For the example, the predicate @{term list} that relates pointers to abstract lists
is defined in the standard, relational recursive way~\cite{Mehta_Nipkow_03}.
We used @{method septract_cancel} to verify the Hoare triple 
\begin{center}
@{thm list_rev_valid_sp}
\end{center}
To achieve the goal we had to interact with our Isabelle framework:
(a) We added the invariant that the list pointed to by the previous pointer is already reversed.
(b) We do not yet have a tactic for performing strongest-postcondition calculation---the equivalent 
  of tactic @{method wp}---we applied  these rules manually.
\<close>

text \<open>
\section{Unified Correctness}

In the previous section on strongest-postcondition reasoning we restricted ourselves to \emph{partial} 
correctness, allowing us to take advantage of \snake. 
This comes at the cost of requiring a separate termination/non-failure proof.
In order to combine forward reasoning with non-termination proofs, the use of total Hoare logic is 
tempting. For total correctness, however, there does not always exist a strongest postcondition.

\begin{example}
Previously, we used the term @{term "p \<mapsto> v \<and>* (p \<mapsto> - -* R)"} as postcondition for 
 @{term set_ptr}. When @{term "R"} \pagebreak[3] does not contain @{term "p \<mapsto> -"} the postcondition 
yields a contradiction, and evaluates to @{term "False"}. 
This is fine under partial correctness, because it only expresses that @{term set_ptr}
does not terminate successfully when the pointer does not exist.
However, there is no postcondition one can write for this precondition to make
the corresponding total correctness triple true.
\end{example}

In this section we extend the work presented in the previous sections to address this problem.
Our approach uses neither partial correctness, nor total correctness, 
but \emph{unified correctness}:

\isastartskip
@{thm [display,indent=5] validU_def}
\isaendskip

As before, @{term P} is the precondition and @{term Q} the postcondition of a program @{term m},
but they now additionally take the (non-)failure state of @{term m} as parameter.
Unified correctness states that @{term Q} holds after executing @{term m} on
 \emph{any} state described by @{term P}, 
allowing even failed executions to have a proper description by @{term Q}.
%
This means, unified correctness 
allows pre- and postconditions that can make statements about the presence or absence of failure.  
Partial correctness corresponds to predicates @{term "Q (s,f)"} that are of the form
@{term "f \<Longrightarrow> Q"}, whereas total correctness can be encoded with predicates of the
form @{term "Q \<and> f"}. Unified correctness allows arbitrary expressions with @{term f}.



%\chC{We write specifications that cover both cases with a conservative extension of SL, where missing resources are described by a 
%paraconsistency rule rather than inconsistency.}
%\comP{I suggest to skip since sentence entirely (does not add much).}

When writing SL predicates, we want formulas to produce `dead values' rather than 
inconsistencies in case of failure, since the latter yield contradictions and evaluate to 
@{term False}. 
That is, while the impossible situation \mbox{@{term "p \<mapsto> - -* sep_false'"}} should evaluate to 
@{term False}, the execution of \mbox{@{term "p \<mapsto> - -* \<box>"}}, which refers to a world where a 
program consumed a non-existing resource, should result in failure.


To express failure in specifications we extend the heap model of \autoref{sec:HLandSL} 
by an additional Boolean flag @{text "nf"}, indicating non-failure---@{term "True"} means successfull termination,
@{term "False"} indicates failure. 
Formally, we define
\begin{center}
  @{thm plus_prod_pretty}\\
  @{thm sep_disj_prod_pretty}
\end{center}
In this definition the operations @{text "+"} and @{text "##"} occurring on the right hand side 
are the operations of the original heap model. The neutral element of @{text "+"} is 
@{term "(sep_empty, True)"}. 

Based on this new model, we can set up a `new' separation logic.%
\footnote{We overload symbols here.}
%\begin{center}
%@{thm sep_con_renamed}\\
%@{thm sept_renamed}
%\end{center}
\begin{center}
  \begin{tabular}{rl}
    @{text "P * Q \<equiv>"}& @{text "\<lambda>h. \<exists>h\<^sub>1 h\<^sub>2. P h\<^sub>1 \<and> Q h\<^sub>2 \<and>"}\\
    &\ \ \ \ \ @{text "(if nf h\<^sub>1 \<and> nf h\<^sub>2 then h\<^sub>2 + h\<^sub>1 = h \<and> h\<^sub>1 ## h\<^sub>2"}\\
    &\ \ \ \ \ \ @{text "else nf h \<longrightarrow> (nf h\<^sub>1 \<longrightarrow> h\<^sub>1 ## h) \<and> (nf h\<^sub>2 \<longrightarrow>  h ## h\<^sub>2))"}\\
    %
    @{text "P -* Q \<equiv>"}& @{text "\<lambda>h. \<exists>h\<^sub>1 h\<^sub>2. P h\<^sub>1 \<and> Q h\<^sub>2 \<and>"}\\
    &\ \ \ \ \ @{text "(if nf h\<^sub>1 \<and> nf h then h\<^sub>1 + h = h\<^sub>2 \<and> h\<^sub>1 ## h"}\\ 
    &\ \ \ \ \ \ @{text "else nf h\<^sub>2 \<longrightarrow> (nf h\<^sub>1  \<longrightarrow> h\<^sub>1 ## h\<^sub>2) \<and> (nf h \<longrightarrow> h ## h\<^sub>2))"}
  \end{tabular}
\end{center}

Both separating conjunction and septraction behave exactly as the original ones when both flags 
within a single formula indicate non-failure and (sub)heaps are as expected.
However, there is the possibility that both flags indicate non-failure, yet 
septraction still fails. This is covered by the second (@{text else}) case, which states that 
this can only occur if the septracted and the septracting heaps are disjoint.
The relationship between these two operators is the same as in the original model. Hence 
we can define \wand and coimplication as  @{thm sep_imp_def[folded eq'_def]} and
@{thm sep_snake_def[folded eq'_def]}, respectively.
As before, the operations @{text "*"} and @{text "\<longrightarrow>*"}, as well as  @{text "-*"} and @{text "\<leadsto>*"}
form Galois connections (cf.~\autoref{fig_sl_ops}). All rules 
presented in this paper hold for the new operations as well. 

Unfortunately, separating conjunction @{text "*"} is \emph{not} associative any longer. 
However, it is associative in case of non-failure (all flags being @{term True}) or
`total' failure (all flags @{term False}). As we will show this is not a big 
disadvantage w.r.t.\ automation.

The intuition behind this model is that the heap describes the state after 
execution correctly in case of non-failure. 

When @{term nf} is false, the program failed to terminate successfully,
and the heap configuration may be unpredictable. 
Hence, one could say that the introduced flag indicates a `non-corrupt' heap.

The above definitions are carefully chosen to imply the following three behaviours, which we 
assume to be `natural'. In the listing all predicates are in terms of the new model.
In particular, @{thm maps_to_renamed} and  @{thm maps_to_ex_renamed}:

\begin{description}
\item[Collapsing.] Consumption from a failed state causes failure, \ie  septracting a non-failure state from a failed 
one cannot recover the state into a non-failure state: @{thm sep_collapsing'}.

\item[Consuming.] If a resource exists and a program consumes it, the program cannot fail due to 
this resource: @{thm sept_success_prettier'}. This implication is closely related to 
the cancellation rule~(\ref{eq:prec_canc}).

\item[Paraconsistent.] If a program tries to consume a resource that does not  exist, 
the resulting state is different from @{term False}, and has the failure flag set.
In the simplest case this means @{thm sept_paraconsistent''}.
\end{description}

Using the new operators, we are able to prove rules for the basic heap operations for unified 
correctness.
\begin{center}
@{thm Unified_Correctness.set_ptr_sp}\\
@{thm Unified_Correctness.delete_ptr_sp} \\
@{thm Unified_Correctness.get_ptr_sp}
\end{center} 

As mentioned above, separating conjunction is not associative. 
Looking at the model at hand this is natural behaviour: consider @{text "P * (Q * R)"}, where @{term Q} and 
 @{term R} have true flags, and @{term P}'s flag evaluates to false. 
This asserts that the heaps of @{term Q} and @{term R} are disjoint, but we do not know 
whether the heap of  @{term P} is disjoint to \mbox{@{term "(Q \<and>& R)"}}. 
Therefore, when rearranging into @{text "(P * Q) * R"}, it is not guaranteed that 
 the heaps of @{term P} and  @{term Q}  are disjoint.

Non-associativity makes automation more complicated, but not completely impossible, as associativity 
still holds when all conjuncts succeed, and a single failed conjunct indicates failure of a program. 
\pagebreak[3]
Moreover, using the rule of \emph{collapsing}, a single flag 
indicating failure can  immediately 
evaluate an entire term to failed (without using any associativity). 
In terms of program verification, where non-failure should be proven next to correctness, 
 such failure is an indication the program contains defects.
\<close>
(*<*)
end
(*>*)
