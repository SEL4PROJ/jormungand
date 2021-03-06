theory IMP_3
imports "~~/src/HOL/Library/Predicate_Compile_Quickcheck"
begin

subsection \<open>IMP\<close>

text \<open>
  In this example, the state is one integer variable and the commands are Skip, Ass, Seq, IF, and While.
\<close>

type_synonym var = unit
type_synonym state = int

datatype com =
  Skip |
  Ass var "int" |
  Seq com com |
  IF "state list" com com |
  While "state list" com

inductive exec :: "com => state => state => bool" where
  "exec Skip s s" |
  "exec (Ass x e) s e" |
  "exec c1 s1 s2 ==> exec c2 s2 s3 ==> exec (Seq c1 c2) s1 s3" |
  "s \<in> set b ==> exec c1 s t ==> exec (IF b c1 c2) s t" |
  "s \<notin> set b ==> exec c2 s t ==> exec (IF b c1 c2) s t" |
  "s \<notin> set b ==> exec (While b c) s s" |
  "s1 \<in> set b ==> exec c s1 s2 ==> exec (While b c) s2 s3 ==> exec (While b c) s1 s3"

lemma
  "exec c s s' ==> exec (Seq c c) s s'"
  quickcheck[tester = smart_exhaustive, size=2, iterations=100, quiet = false, expect = counterexample]
oops


end
