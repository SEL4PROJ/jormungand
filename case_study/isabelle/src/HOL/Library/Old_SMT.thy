(*  Title:      HOL/Library/Old_SMT.thy
    Author:     Sascha Boehme, TU Muenchen
*)

section \<open>Old Version of Bindings to Satisfiability Modulo Theories (SMT) solvers\<close>

theory Old_SMT
imports "../Real" "../Word/Word"
keywords "old_smt_status" :: diag
begin

ML_file "Old_SMT/old_smt_utils.ML"
ML_file "Old_SMT/old_smt_failure.ML"
ML_file "Old_SMT/old_smt_config.ML"


subsection \<open>Triggers for quantifier instantiation\<close>

text \<open>
Some SMT solvers support patterns as a quantifier instantiation
heuristics.  Patterns may either be positive terms (tagged by "pat")
triggering quantifier instantiations -- when the solver finds a
term matching a positive pattern, it instantiates the corresponding
quantifier accordingly -- or negative terms (tagged by "nopat")
inhibiting quantifier instantiations.  A list of patterns
of the same kind is called a multipattern, and all patterns in a
multipattern are considered conjunctively for quantifier instantiation.
A list of multipatterns is called a trigger, and their multipatterns
act disjunctively during quantifier instantiation.  Each multipattern
should mention at least all quantified variables of the preceding
quantifier block.
\<close>

typedecl pattern

consts
  pat :: "'a \<Rightarrow> pattern"
  nopat :: "'a \<Rightarrow> pattern"

definition trigger :: "pattern list list \<Rightarrow> bool \<Rightarrow> bool" where "trigger _ P = P"


subsection \<open>Quantifier weights\<close>

text \<open>
Weight annotations to quantifiers influence the priority of quantifier
instantiations.  They should be handled with care for solvers, which support
them, because incorrect choices of weights might render a problem unsolvable.
\<close>

definition weight :: "int \<Rightarrow> bool \<Rightarrow> bool" where "weight _ P = P"

text \<open>
Weights must be non-negative.  The value \<open>0\<close> is equivalent to providing
no weight at all.

Weights should only be used at quantifiers and only inside triggers (if the
quantifier has triggers).  Valid usages of weights are as follows:

\begin{itemize}
\item
@{term "\<forall>x. trigger [[pat (P x)]] (weight 2 (P x))"}
\item
@{term "\<forall>x. weight 3 (P x)"}
\end{itemize}
\<close>


subsection \<open>Higher-order encoding\<close>

text \<open>
Application is made explicit for constants occurring with varying
numbers of arguments.  This is achieved by the introduction of the
following constant.
\<close>

definition fun_app where "fun_app f = f"

text \<open>
Some solvers support a theory of arrays which can be used to encode
higher-order functions.  The following set of lemmas specifies the
properties of such (extensional) arrays.
\<close>

lemmas array_rules = ext fun_upd_apply fun_upd_same fun_upd_other
  fun_upd_upd fun_app_def


subsection \<open>First-order logic\<close>

text \<open>
Some SMT solvers only accept problems in first-order logic, i.e.,
where formulas and terms are syntactically separated. When
translating higher-order into first-order problems, all
uninterpreted constants (those not built-in in the target solver)
are treated as function symbols in the first-order sense.  Their
occurrences as head symbols in atoms (i.e., as predicate symbols) are
turned into terms by logically equating such atoms with @{term True}.
For technical reasons, @{term True} and @{term False} occurring inside
terms are replaced by the following constants.
\<close>

definition term_true where "term_true = True"
definition term_false where "term_false = False"


subsection \<open>Integer division and modulo for Z3\<close>

definition z3div :: "int \<Rightarrow> int \<Rightarrow> int" where
  "z3div k l = (if 0 \<le> l then k div l else -(k div (-l)))"

definition z3mod :: "int \<Rightarrow> int \<Rightarrow> int" where
  "z3mod k l = (if 0 \<le> l then k mod l else k mod (-l))"


subsection \<open>Setup\<close>

ML_file "Old_SMT/old_smt_builtin.ML"
ML_file "Old_SMT/old_smt_datatypes.ML"
ML_file "Old_SMT/old_smt_normalize.ML"
ML_file "Old_SMT/old_smt_translate.ML"
ML_file "Old_SMT/old_smt_solver.ML"
ML_file "Old_SMT/old_smtlib_interface.ML"
ML_file "Old_SMT/old_z3_interface.ML"
ML_file "Old_SMT/old_z3_proof_parser.ML"
ML_file "Old_SMT/old_z3_proof_tools.ML"
ML_file "Old_SMT/old_z3_proof_literals.ML"
ML_file "Old_SMT/old_z3_proof_methods.ML"
named_theorems old_z3_simp "simplification rules for Z3 proof reconstruction"
ML_file "Old_SMT/old_z3_proof_reconstruction.ML"
ML_file "Old_SMT/old_z3_model.ML"
ML_file "Old_SMT/old_smt_setup_solvers.ML"

setup \<open>
  Old_SMT_Config.setup #>
  Old_SMT_Normalize.setup #>
  Old_SMTLIB_Interface.setup #>
  Old_Z3_Interface.setup #>
  Old_SMT_Setup_Solvers.setup
\<close>

method_setup old_smt = \<open>
  Scan.optional Attrib.thms [] >>
    (fn thms => fn ctxt =>
      (legacy_feature "Proof method \"old_smt\" will be discontinued soon -- use \"smt\" instead";
       METHOD (fn facts => HEADGOAL (Old_SMT_Solver.smt_tac ctxt (thms @ facts)))))
\<close> "apply an SMT solver to the current goal"


subsection \<open>Configuration\<close>

text \<open>
The current configuration can be printed by the command
\<open>old_smt_status\<close>, which shows the values of most options.
\<close>



subsection \<open>General configuration options\<close>

text \<open>
The option \<open>old_smt_solver\<close> can be used to change the target SMT
solver.  The possible values can be obtained from the \<open>old_smt_status\<close>
command.

Due to licensing restrictions, Yices and Z3 are not installed/enabled
by default.  Z3 is free for non-commercial applications and can be enabled
by setting the \<open>OLD_Z3_NON_COMMERCIAL\<close> environment variable to
\<open>yes\<close>.
\<close>

declare [[ old_smt_solver = z3 ]]

text \<open>
Since SMT solvers are potentially non-terminating, there is a timeout
(given in seconds) to restrict their runtime.  A value greater than
120 (seconds) is in most cases not advisable.
\<close>

declare [[ old_smt_timeout = 20 ]]

text \<open>
SMT solvers apply randomized heuristics.  In case a problem is not
solvable by an SMT solver, changing the following option might help.
\<close>

declare [[ old_smt_random_seed = 1 ]]

text \<open>
In general, the binding to SMT solvers runs as an oracle, i.e, the SMT
solvers are fully trusted without additional checks.  The following
option can cause the SMT solver to run in proof-producing mode, giving
a checkable certificate.  This is currently only implemented for Z3.
\<close>

declare [[ old_smt_oracle = false ]]

text \<open>
Each SMT solver provides several commandline options to tweak its
behaviour.  They can be passed to the solver by setting the following
options.
\<close>

declare [[ old_cvc3_options = "" ]]
declare [[ old_yices_options = "" ]]
declare [[ old_z3_options = "" ]]

text \<open>
Enable the following option to use built-in support for datatypes and
records.  Currently, this is only implemented for Z3 running in oracle
mode.
\<close>

declare [[ old_smt_datatypes = false ]]

text \<open>
The SMT method provides an inference mechanism to detect simple triggers
in quantified formulas, which might increase the number of problems
solvable by SMT solvers (note: triggers guide quantifier instantiations
in the SMT solver).  To turn it on, set the following option.
\<close>

declare [[ old_smt_infer_triggers = false ]]

text \<open>
The SMT method monomorphizes the given facts, that is, it tries to
instantiate all schematic type variables with fixed types occurring
in the problem.  This is a (possibly nonterminating) fixed-point
construction whose cycles are limited by the following option.
\<close>

declare [[ monomorph_max_rounds = 5 ]]

text \<open>
In addition, the number of generated monomorphic instances is limited
by the following option.
\<close>

declare [[ monomorph_max_new_instances = 500 ]]



subsection \<open>Certificates\<close>

text \<open>
By setting the option \<open>old_smt_certificates\<close> to the name of a file,
all following applications of an SMT solver a cached in that file.
Any further application of the same SMT solver (using the very same
configuration) re-uses the cached certificate instead of invoking the
solver.  An empty string disables caching certificates.

The filename should be given as an explicit path.  It is good
practice to use the name of the current theory (with ending
\<open>.certs\<close> instead of \<open>.thy\<close>) as the certificates file.
Certificate files should be used at most once in a certain theory context,
to avoid race conditions with other concurrent accesses.
\<close>

declare [[ old_smt_certificates = "" ]]

text \<open>
The option \<open>old_smt_read_only_certificates\<close> controls whether only
stored certificates are should be used or invocation of an SMT solver
is allowed.  When set to \<open>true\<close>, no SMT solver will ever be
invoked and only the existing certificates found in the configured
cache are used;  when set to \<open>false\<close> and there is no cached
certificate for some proposition, then the configured SMT solver is
invoked.
\<close>

declare [[ old_smt_read_only_certificates = false ]]



subsection \<open>Tracing\<close>

text \<open>
The SMT method, when applied, traces important information.  To
make it entirely silent, set the following option to \<open>false\<close>.
\<close>

declare [[ old_smt_verbose = true ]]

text \<open>
For tracing the generated problem file given to the SMT solver as
well as the returned result of the solver, the option
\<open>old_smt_trace\<close> should be set to \<open>true\<close>.
\<close>

declare [[ old_smt_trace = false ]]

text \<open>
From the set of assumptions given to the SMT solver, those assumptions
used in the proof are traced when the following option is set to
@{term true}.  This only works for Z3 when it runs in non-oracle mode
(see options \<open>old_smt_solver\<close> and \<open>old_smt_oracle\<close> above).
\<close>

declare [[ old_smt_trace_used_facts = false ]]



subsection \<open>Schematic rules for Z3 proof reconstruction\<close>

text \<open>
Several prof rules of Z3 are not very well documented.  There are two
lemma groups which can turn failing Z3 proof reconstruction attempts
into succeeding ones: the facts in \<open>z3_rule\<close> are tried prior to
any implemented reconstruction procedure for all uncertain Z3 proof
rules;  the facts in \<open>z3_simp\<close> are only fed to invocations of
the simplifier when reconstructing theory-specific proof steps.
\<close>

lemmas [old_z3_rule] =
  refl eq_commute conj_commute disj_commute simp_thms nnf_simps
  ring_distribs field_simps times_divide_eq_right times_divide_eq_left
  if_True if_False not_not

lemma [old_z3_rule]:
  "(P \<and> Q) = (\<not>(\<not>P \<or> \<not>Q))"
  "(P \<and> Q) = (\<not>(\<not>Q \<or> \<not>P))"
  "(\<not>P \<and> Q) = (\<not>(P \<or> \<not>Q))"
  "(\<not>P \<and> Q) = (\<not>(\<not>Q \<or> P))"
  "(P \<and> \<not>Q) = (\<not>(\<not>P \<or> Q))"
  "(P \<and> \<not>Q) = (\<not>(Q \<or> \<not>P))"
  "(\<not>P \<and> \<not>Q) = (\<not>(P \<or> Q))"
  "(\<not>P \<and> \<not>Q) = (\<not>(Q \<or> P))"
  by auto

lemma [old_z3_rule]:
  "(P \<longrightarrow> Q) = (Q \<or> \<not>P)"
  "(\<not>P \<longrightarrow> Q) = (P \<or> Q)"
  "(\<not>P \<longrightarrow> Q) = (Q \<or> P)"
  "(True \<longrightarrow> P) = P"
  "(P \<longrightarrow> True) = True"
  "(False \<longrightarrow> P) = True"
  "(P \<longrightarrow> P) = True"
  by auto

lemma [old_z3_rule]:
  "((P = Q) \<longrightarrow> R) = (R | (Q = (\<not>P)))"
  by auto

lemma [old_z3_rule]:
  "(\<not>True) = False"
  "(\<not>False) = True"
  "(x = x) = True"
  "(P = True) = P"
  "(True = P) = P"
  "(P = False) = (\<not>P)"
  "(False = P) = (\<not>P)"
  "((\<not>P) = P) = False"
  "(P = (\<not>P)) = False"
  "((\<not>P) = (\<not>Q)) = (P = Q)"
  "\<not>(P = (\<not>Q)) = (P = Q)"
  "\<not>((\<not>P) = Q) = (P = Q)"
  "(P \<noteq> Q) = (Q = (\<not>P))"
  "(P = Q) = ((\<not>P \<or> Q) \<and> (P \<or> \<not>Q))"
  "(P \<noteq> Q) = ((\<not>P \<or> \<not>Q) \<and> (P \<or> Q))"
  by auto

lemma [old_z3_rule]:
  "(if P then P else \<not>P) = True"
  "(if \<not>P then \<not>P else P) = True"
  "(if P then True else False) = P"
  "(if P then False else True) = (\<not>P)"
  "(if P then Q else True) = ((\<not>P) \<or> Q)"
  "(if P then Q else True) = (Q \<or> (\<not>P))"
  "(if P then Q else \<not>Q) = (P = Q)"
  "(if P then Q else \<not>Q) = (Q = P)"
  "(if P then \<not>Q else Q) = (P = (\<not>Q))"
  "(if P then \<not>Q else Q) = ((\<not>Q) = P)"
  "(if \<not>P then x else y) = (if P then y else x)"
  "(if P then (if Q then x else y) else x) = (if P \<and> (\<not>Q) then y else x)"
  "(if P then (if Q then x else y) else x) = (if (\<not>Q) \<and> P then y else x)"
  "(if P then (if Q then x else y) else y) = (if P \<and> Q then x else y)"
  "(if P then (if Q then x else y) else y) = (if Q \<and> P then x else y)"
  "(if P then x else if P then y else z) = (if P then x else z)"
  "(if P then x else if Q then x else y) = (if P \<or> Q then x else y)"
  "(if P then x else if Q then x else y) = (if Q \<or> P then x else y)"
  "(if P then x = y else x = z) = (x = (if P then y else z))"
  "(if P then x = y else y = z) = (y = (if P then x else z))"
  "(if P then x = y else z = y) = (y = (if P then x else z))"
  by auto

lemma [old_z3_rule]:
  "0 + (x::int) = x"
  "x + 0 = x"
  "x + x = 2 * x"
  "0 * x = 0"
  "1 * x = x"
  "x + y = y + x"
  by auto

lemma [old_z3_rule]:  (* for def-axiom *)
  "P = Q \<or> P \<or> Q"
  "P = Q \<or> \<not>P \<or> \<not>Q"
  "(\<not>P) = Q \<or> \<not>P \<or> Q"
  "(\<not>P) = Q \<or> P \<or> \<not>Q"
  "P = (\<not>Q) \<or> \<not>P \<or> Q"
  "P = (\<not>Q) \<or> P \<or> \<not>Q"
  "P \<noteq> Q \<or> P \<or> \<not>Q"
  "P \<noteq> Q \<or> \<not>P \<or> Q"
  "P \<noteq> (\<not>Q) \<or> P \<or> Q"
  "(\<not>P) \<noteq> Q \<or> P \<or> Q"
  "P \<or> Q \<or> P \<noteq> (\<not>Q)"
  "P \<or> Q \<or> (\<not>P) \<noteq> Q"
  "P \<or> \<not>Q \<or> P \<noteq> Q"
  "\<not>P \<or> Q \<or> P \<noteq> Q"
  "P \<or> y = (if P then x else y)"
  "P \<or> (if P then x else y) = y"
  "\<not>P \<or> x = (if P then x else y)"
  "\<not>P \<or>  (if P then x else y) = x"
  "P \<or> R \<or> \<not>(if P then Q else R)"
  "\<not>P \<or> Q \<or> \<not>(if P then Q else R)"
  "\<not>(if P then Q else R) \<or> \<not>P \<or> Q"
  "\<not>(if P then Q else R) \<or> P \<or> R"
  "(if P then Q else R) \<or> \<not>P \<or> \<not>Q"
  "(if P then Q else R) \<or> P \<or> \<not>R"
  "(if P then \<not>Q else R) \<or> \<not>P \<or> Q"
  "(if P then Q else \<not>R) \<or> P \<or> R"
  by auto

ML_file "Old_SMT/old_smt_real.ML"
ML_file "Old_SMT/old_smt_word.ML"

hide_type (open) pattern
hide_const fun_app term_true term_false z3div z3mod
hide_const (open) trigger pat nopat weight

end
