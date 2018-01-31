(*<*)
theory ABexpr imports Main begin
(*>*)

text{*
\index{datatypes!mutually recursive}%
Sometimes it is necessary to define two datatypes that depend on each
other. This is called \textbf{mutual recursion}. As an example consider a
language of arithmetic and boolean expressions where
\begin{itemize}
\item arithmetic expressions contain boolean expressions because there are
  conditional expressions like ``if $m<n$ then $n-m$ else $m-n$'',
  and
\item boolean expressions contain arithmetic expressions because of
  comparisons like ``$m<n$''.
\end{itemize}
In Isabelle this becomes
*}

datatype 'a aexp = IF   "'a bexp" "'a aexp" "'a aexp"
                 | Sum  "'a aexp" "'a aexp"
                 | Diff "'a aexp" "'a aexp"
                 | Var 'a
                 | Num nat
and      'a bexp = Less "'a aexp" "'a aexp"
                 | And  "'a bexp" "'a bexp"
                 | Neg  "'a bexp"

text{*\noindent
Type @{text"aexp"} is similar to @{text"expr"} in \S\ref{sec:ExprCompiler},
except that we have added an @{text IF} constructor,
fixed the values to be of type @{typ"nat"} and declared the two binary
operations @{text Sum} and @{term"Diff"}.  Boolean
expressions can be arithmetic comparisons, conjunctions and negations.
The semantics is given by two evaluation functions:
*}

primrec evala :: "'a aexp \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> nat" and
         evalb :: "'a bexp \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> bool" where
"evala (IF b a1 a2) env =
   (if evalb b env then evala a1 env else evala a2 env)" |
"evala (Sum a1 a2) env = evala a1 env + evala a2 env" |
"evala (Diff a1 a2) env = evala a1 env - evala a2 env" |
"evala (Var v) env = env v" |
"evala (Num n) env = n" |

"evalb (Less a1 a2) env = (evala a1 env < evala a2 env)" |
"evalb (And b1 b2) env = (evalb b1 env \<and> evalb b2 env)" |
"evalb (Neg b) env = (\<not> evalb b env)"

text{*\noindent

Both take an expression and an environment (a mapping from variables
@{typ"'a"} to values @{typ"nat"}) and return its arithmetic/boolean
value. Since the datatypes are mutually recursive, so are functions
that operate on them. Hence they need to be defined in a single
\isacommand{primrec} section. Notice the \isakeyword{and} separating
the declarations of @{const evala} and @{const evalb}. Their defining
equations need not be split into two groups;
the empty line is purely for readability.

In the same fashion we also define two functions that perform substitution:
*}

primrec substa :: "('a \<Rightarrow> 'b aexp) \<Rightarrow> 'a aexp \<Rightarrow> 'b aexp" and
         substb :: "('a \<Rightarrow> 'b aexp) \<Rightarrow> 'a bexp \<Rightarrow> 'b bexp" where
"substa s (IF b a1 a2) =
   IF (substb s b) (substa s a1) (substa s a2)" |
"substa s (Sum a1 a2) = Sum (substa s a1) (substa s a2)" |
"substa s (Diff a1 a2) = Diff (substa s a1) (substa s a2)" |
"substa s (Var v) = s v" |
"substa s (Num n) = Num n" |

"substb s (Less a1 a2) = Less (substa s a1) (substa s a2)" |
"substb s (And b1 b2) = And (substb s b1) (substb s b2)" |
"substb s (Neg b) = Neg (substb s b)"

text{*\noindent
Their first argument is a function mapping variables to expressions, the
substitution. It is applied to all variables in the second argument. As a
result, the type of variables in the expression may change from @{typ"'a"}
to @{typ"'b"}. Note that there are only arithmetic and no boolean variables.

Now we can prove a fundamental theorem about the interaction between
evaluation and substitution: applying a substitution $s$ to an expression $a$
and evaluating the result in an environment $env$ yields the same result as
evaluation $a$ in the environment that maps every variable $x$ to the value
of $s(x)$ under $env$. If you try to prove this separately for arithmetic or
boolean expressions (by induction), you find that you always need the other
theorem in the induction step. Therefore you need to state and prove both
theorems simultaneously:
*}

lemma "evala (substa s a) env = evala a (\<lambda>x. evala (s x) env) \<and>
        evalb (substb s b) env = evalb b (\<lambda>x. evala (s x) env)"
apply(induct_tac a and b)

txt{*\noindent The resulting 8 goals (one for each constructor) are proved in one fell swoop:
*}

apply simp_all
(*<*)done(*>*)

text{*
In general, given $n$ mutually recursive datatypes $\tau@1$, \dots, $\tau@n$,
an inductive proof expects a goal of the form
\[ P@1(x@1)\ \land \dots \land P@n(x@n) \]
where each variable $x@i$ is of type $\tau@i$. Induction is started by
\begin{isabelle}
\isacommand{apply}@{text"(induct_tac"} $x@1$ \isacommand{and} \dots\ \isacommand{and} $x@n$@{text ")"}
\end{isabelle}

\begin{exercise}
  Define a function @{text"norma"} of type @{typ"'a aexp => 'a aexp"} that
  replaces @{term"IF"}s with complex boolean conditions by nested
  @{term"IF"}s; it should eliminate the constructors
  @{term"And"} and @{term"Neg"}, leaving only @{term"Less"}.
  Prove that @{text"norma"}
  preserves the value of an expression and that the result of @{text"norma"}
  is really normal, i.e.\ no more @{term"And"}s and @{term"Neg"}s occur in
  it.  ({\em Hint:} proceed as in \S\ref{sec:boolex} and read the discussion
  of type annotations following lemma @{text subst_id} below).
\end{exercise}
*}
(*<*)
primrec norma :: "'a aexp \<Rightarrow> 'a aexp" and
        normb :: "'a bexp \<Rightarrow> 'a aexp \<Rightarrow> 'a aexp \<Rightarrow> 'a aexp" where
"norma (IF b t e)   = (normb b (norma t) (norma e))" |
"norma (Sum a1 a2)  = Sum (norma a1) (norma a2)" |
"norma (Diff a1 a2) = Diff (norma a1) (norma a2)" |
"norma (Var v)      = Var v" |
"norma (Num n)      = Num n" |
            
"normb (Less a1 a2) t e = IF (Less (norma a1) (norma a2)) t e" |
"normb (And b1 b2)  t e = normb b1 (normb b2 t e) e" |
"normb (Neg b)      t e = normb b e t"

lemma " evala (norma a) env = evala a env 
      \<and> (\<forall> t e. evala (normb b t e) env = evala (IF b t e) env)"
apply (induct_tac a and b)
apply (simp_all)
done

primrec normala :: "'a aexp \<Rightarrow> bool" and
        normalb :: "'a bexp \<Rightarrow> bool" where
"normala (IF b t e)   = (normalb b \<and> normala t \<and> normala e)" |
"normala (Sum a1 a2)  = (normala a1 \<and> normala a2)" |
"normala (Diff a1 a2) = (normala a1 \<and> normala a2)" |
"normala (Var v)      = True" |
"normala (Num n)      = True" |

"normalb (Less a1 a2) = (normala a1 \<and> normala a2)" |
"normalb (And b1 b2)  = False" |
"normalb (Neg b)      = False"

lemma "normala (norma (a::'a aexp)) \<and>
       (\<forall> (t::'a aexp) e. (normala t \<and> normala e) \<longrightarrow> normala (normb b t e))"
apply (induct_tac a and b)
apply (auto)
done

end
(*>*)
