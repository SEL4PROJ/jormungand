(*  Title:      HOL/Decision_Procs/Cooper.thy
    Author:     Amine Chaieb
*)

theory Cooper
imports
  Complex_Main
  "~~/src/HOL/Library/Code_Target_Numeral"
  "~~/src/HOL/Library/Old_Recdef"
begin

(* Periodicity of dvd *)

(*********************************************************************************)
(****                            SHADOW SYNTAX AND SEMANTICS                  ****)
(*********************************************************************************)

datatype num = C int | Bound nat | CN nat int num | Neg num | Add num num| Sub num num
  | Mul int num

primrec num_size :: "num \<Rightarrow> nat" \<comment> \<open>A size for num to make inductive proofs simpler\<close>
where
  "num_size (C c) = 1"
| "num_size (Bound n) = 1"
| "num_size (Neg a) = 1 + num_size a"
| "num_size (Add a b) = 1 + num_size a + num_size b"
| "num_size (Sub a b) = 3 + num_size a + num_size b"
| "num_size (CN n c a) = 4 + num_size a"
| "num_size (Mul c a) = 1 + num_size a"

primrec Inum :: "int list \<Rightarrow> num \<Rightarrow> int"
where
  "Inum bs (C c) = c"
| "Inum bs (Bound n) = bs!n"
| "Inum bs (CN n c a) = c * (bs!n) + (Inum bs a)"
| "Inum bs (Neg a) = -(Inum bs a)"
| "Inum bs (Add a b) = Inum bs a + Inum bs b"
| "Inum bs (Sub a b) = Inum bs a - Inum bs b"
| "Inum bs (Mul c a) = c* Inum bs a"

datatype fm  =
  T| F| Lt num| Le num| Gt num| Ge num| Eq num| NEq num| Dvd int num| NDvd int num|
  NOT fm| And fm fm|  Or fm fm| Imp fm fm| Iff fm fm| E fm| A fm
  | Closed nat | NClosed nat


fun fmsize :: "fm \<Rightarrow> nat"  \<comment> \<open>A size for fm\<close>
where
  "fmsize (NOT p) = 1 + fmsize p"
| "fmsize (And p q) = 1 + fmsize p + fmsize q"
| "fmsize (Or p q) = 1 + fmsize p + fmsize q"
| "fmsize (Imp p q) = 3 + fmsize p + fmsize q"
| "fmsize (Iff p q) = 3 + 2*(fmsize p + fmsize q)"
| "fmsize (E p) = 1 + fmsize p"
| "fmsize (A p) = 4+ fmsize p"
| "fmsize (Dvd i t) = 2"
| "fmsize (NDvd i t) = 2"
| "fmsize p = 1"

lemma fmsize_pos: "fmsize p > 0"
  by (induct p rule: fmsize.induct) simp_all

primrec Ifm :: "bool list \<Rightarrow> int list \<Rightarrow> fm \<Rightarrow> bool"  \<comment> \<open>Semantics of formulae (fm)\<close>
where
  "Ifm bbs bs T \<longleftrightarrow> True"
| "Ifm bbs bs F \<longleftrightarrow> False"
| "Ifm bbs bs (Lt a) \<longleftrightarrow> Inum bs a < 0"
| "Ifm bbs bs (Gt a) \<longleftrightarrow> Inum bs a > 0"
| "Ifm bbs bs (Le a) \<longleftrightarrow> Inum bs a \<le> 0"
| "Ifm bbs bs (Ge a) \<longleftrightarrow> Inum bs a \<ge> 0"
| "Ifm bbs bs (Eq a) \<longleftrightarrow> Inum bs a = 0"
| "Ifm bbs bs (NEq a) \<longleftrightarrow> Inum bs a \<noteq> 0"
| "Ifm bbs bs (Dvd i b) \<longleftrightarrow> i dvd Inum bs b"
| "Ifm bbs bs (NDvd i b) \<longleftrightarrow> \<not> i dvd Inum bs b"
| "Ifm bbs bs (NOT p) \<longleftrightarrow> \<not> Ifm bbs bs p"
| "Ifm bbs bs (And p q) \<longleftrightarrow> Ifm bbs bs p \<and> Ifm bbs bs q"
| "Ifm bbs bs (Or p q) \<longleftrightarrow> Ifm bbs bs p \<or> Ifm bbs bs q"
| "Ifm bbs bs (Imp p q) \<longleftrightarrow> (Ifm bbs bs p \<longrightarrow> Ifm bbs bs q)"
| "Ifm bbs bs (Iff p q) \<longleftrightarrow> Ifm bbs bs p = Ifm bbs bs q"
| "Ifm bbs bs (E p) \<longleftrightarrow> (\<exists>x. Ifm bbs (x # bs) p)"
| "Ifm bbs bs (A p) \<longleftrightarrow> (\<forall>x. Ifm bbs (x # bs) p)"
| "Ifm bbs bs (Closed n) \<longleftrightarrow> bbs!n"
| "Ifm bbs bs (NClosed n) \<longleftrightarrow> \<not> bbs!n"

consts prep :: "fm \<Rightarrow> fm"
recdef prep "measure fmsize"
  "prep (E T) = T"
  "prep (E F) = F"
  "prep (E (Or p q)) = Or (prep (E p)) (prep (E q))"
  "prep (E (Imp p q)) = Or (prep (E (NOT p))) (prep (E q))"
  "prep (E (Iff p q)) = Or (prep (E (And p q))) (prep (E (And (NOT p) (NOT q))))"
  "prep (E (NOT (And p q))) = Or (prep (E (NOT p))) (prep (E(NOT q)))"
  "prep (E (NOT (Imp p q))) = prep (E (And p (NOT q)))"
  "prep (E (NOT (Iff p q))) = Or (prep (E (And p (NOT q)))) (prep (E(And (NOT p) q)))"
  "prep (E p) = E (prep p)"
  "prep (A (And p q)) = And (prep (A p)) (prep (A q))"
  "prep (A p) = prep (NOT (E (NOT p)))"
  "prep (NOT (NOT p)) = prep p"
  "prep (NOT (And p q)) = Or (prep (NOT p)) (prep (NOT q))"
  "prep (NOT (A p)) = prep (E (NOT p))"
  "prep (NOT (Or p q)) = And (prep (NOT p)) (prep (NOT q))"
  "prep (NOT (Imp p q)) = And (prep p) (prep (NOT q))"
  "prep (NOT (Iff p q)) = Or (prep (And p (NOT q))) (prep (And (NOT p) q))"
  "prep (NOT p) = NOT (prep p)"
  "prep (Or p q) = Or (prep p) (prep q)"
  "prep (And p q) = And (prep p) (prep q)"
  "prep (Imp p q) = prep (Or (NOT p) q)"
  "prep (Iff p q) = Or (prep (And p q)) (prep (And (NOT p) (NOT q)))"
  "prep p = p"
  (hints simp add: fmsize_pos)

lemma prep: "Ifm bbs bs (prep p) = Ifm bbs bs p"
  by (induct p arbitrary: bs rule: prep.induct) auto


fun qfree :: "fm \<Rightarrow> bool"  \<comment> \<open>Quantifier freeness\<close>
where
  "qfree (E p) \<longleftrightarrow> False"
| "qfree (A p) \<longleftrightarrow> False"
| "qfree (NOT p) \<longleftrightarrow> qfree p"
| "qfree (And p q) \<longleftrightarrow> qfree p \<and> qfree q"
| "qfree (Or  p q) \<longleftrightarrow> qfree p \<and> qfree q"
| "qfree (Imp p q) \<longleftrightarrow> qfree p \<and> qfree q"
| "qfree (Iff p q) \<longleftrightarrow> qfree p \<and> qfree q"
| "qfree p \<longleftrightarrow> True"


text \<open>Boundedness and substitution\<close>

primrec numbound0 :: "num \<Rightarrow> bool"  \<comment> \<open>a num is INDEPENDENT of Bound 0\<close>
where
  "numbound0 (C c) \<longleftrightarrow> True"
| "numbound0 (Bound n) \<longleftrightarrow> n > 0"
| "numbound0 (CN n i a) \<longleftrightarrow> n > 0 \<and> numbound0 a"
| "numbound0 (Neg a) \<longleftrightarrow> numbound0 a"
| "numbound0 (Add a b) \<longleftrightarrow> numbound0 a \<and> numbound0 b"
| "numbound0 (Sub a b) \<longleftrightarrow> numbound0 a \<and> numbound0 b"
| "numbound0 (Mul i a) \<longleftrightarrow> numbound0 a"

lemma numbound0_I:
  assumes nb: "numbound0 a"
  shows "Inum (b # bs) a = Inum (b' # bs) a"
  using nb by (induct a rule: num.induct) (auto simp add: gr0_conv_Suc)

primrec bound0 :: "fm \<Rightarrow> bool" \<comment> \<open>A Formula is independent of Bound 0\<close>
where
  "bound0 T \<longleftrightarrow> True"
| "bound0 F \<longleftrightarrow> True"
| "bound0 (Lt a) \<longleftrightarrow> numbound0 a"
| "bound0 (Le a) \<longleftrightarrow> numbound0 a"
| "bound0 (Gt a) \<longleftrightarrow> numbound0 a"
| "bound0 (Ge a) \<longleftrightarrow> numbound0 a"
| "bound0 (Eq a) \<longleftrightarrow> numbound0 a"
| "bound0 (NEq a) \<longleftrightarrow> numbound0 a"
| "bound0 (Dvd i a) \<longleftrightarrow> numbound0 a"
| "bound0 (NDvd i a) \<longleftrightarrow> numbound0 a"
| "bound0 (NOT p) \<longleftrightarrow> bound0 p"
| "bound0 (And p q) \<longleftrightarrow> bound0 p \<and> bound0 q"
| "bound0 (Or p q) \<longleftrightarrow> bound0 p \<and> bound0 q"
| "bound0 (Imp p q) \<longleftrightarrow> bound0 p \<and> bound0 q"
| "bound0 (Iff p q) \<longleftrightarrow> bound0 p \<and> bound0 q"
| "bound0 (E p) \<longleftrightarrow> False"
| "bound0 (A p) \<longleftrightarrow> False"
| "bound0 (Closed P) \<longleftrightarrow> True"
| "bound0 (NClosed P) \<longleftrightarrow> True"

lemma bound0_I:
  assumes bp: "bound0 p"
  shows "Ifm bbs (b # bs) p = Ifm bbs (b' # bs) p"
  using bp numbound0_I[where b="b" and bs="bs" and b'="b'"]
  by (induct p rule: fm.induct) (auto simp add: gr0_conv_Suc)

fun numsubst0 :: "num \<Rightarrow> num \<Rightarrow> num"
where
  "numsubst0 t (C c) = (C c)"
| "numsubst0 t (Bound n) = (if n=0 then t else Bound n)"
| "numsubst0 t (CN 0 i a) = Add (Mul i t) (numsubst0 t a)"
| "numsubst0 t (CN n i a) = CN n i (numsubst0 t a)"
| "numsubst0 t (Neg a) = Neg (numsubst0 t a)"
| "numsubst0 t (Add a b) = Add (numsubst0 t a) (numsubst0 t b)"
| "numsubst0 t (Sub a b) = Sub (numsubst0 t a) (numsubst0 t b)"
| "numsubst0 t (Mul i a) = Mul i (numsubst0 t a)"

lemma numsubst0_I: "Inum (b#bs) (numsubst0 a t) = Inum ((Inum (b#bs) a)#bs) t"
  by (induct t rule: numsubst0.induct) (auto simp: nth_Cons')

lemma numsubst0_I':
  "numbound0 a \<Longrightarrow> Inum (b#bs) (numsubst0 a t) = Inum ((Inum (b'#bs) a)#bs) t"
  by (induct t rule: numsubst0.induct) (auto simp: nth_Cons' numbound0_I[where b="b" and b'="b'"])

primrec subst0:: "num \<Rightarrow> fm \<Rightarrow> fm"  \<comment> \<open>substitue a num into a formula for Bound 0\<close>
where
  "subst0 t T = T"
| "subst0 t F = F"
| "subst0 t (Lt a) = Lt (numsubst0 t a)"
| "subst0 t (Le a) = Le (numsubst0 t a)"
| "subst0 t (Gt a) = Gt (numsubst0 t a)"
| "subst0 t (Ge a) = Ge (numsubst0 t a)"
| "subst0 t (Eq a) = Eq (numsubst0 t a)"
| "subst0 t (NEq a) = NEq (numsubst0 t a)"
| "subst0 t (Dvd i a) = Dvd i (numsubst0 t a)"
| "subst0 t (NDvd i a) = NDvd i (numsubst0 t a)"
| "subst0 t (NOT p) = NOT (subst0 t p)"
| "subst0 t (And p q) = And (subst0 t p) (subst0 t q)"
| "subst0 t (Or p q) = Or (subst0 t p) (subst0 t q)"
| "subst0 t (Imp p q) = Imp (subst0 t p) (subst0 t q)"
| "subst0 t (Iff p q) = Iff (subst0 t p) (subst0 t q)"
| "subst0 t (Closed P) = (Closed P)"
| "subst0 t (NClosed P) = (NClosed P)"

lemma subst0_I:
  assumes "qfree p"
  shows "Ifm bbs (b # bs) (subst0 a p) = Ifm bbs (Inum (b # bs) a # bs) p"
  using assms numsubst0_I[where b="b" and bs="bs" and a="a"]
  by (induct p) (simp_all add: gr0_conv_Suc)

fun decrnum:: "num \<Rightarrow> num"
where
  "decrnum (Bound n) = Bound (n - 1)"
| "decrnum (Neg a) = Neg (decrnum a)"
| "decrnum (Add a b) = Add (decrnum a) (decrnum b)"
| "decrnum (Sub a b) = Sub (decrnum a) (decrnum b)"
| "decrnum (Mul c a) = Mul c (decrnum a)"
| "decrnum (CN n i a) = (CN (n - 1) i (decrnum a))"
| "decrnum a = a"

fun decr :: "fm \<Rightarrow> fm"
where
  "decr (Lt a) = Lt (decrnum a)"
| "decr (Le a) = Le (decrnum a)"
| "decr (Gt a) = Gt (decrnum a)"
| "decr (Ge a) = Ge (decrnum a)"
| "decr (Eq a) = Eq (decrnum a)"
| "decr (NEq a) = NEq (decrnum a)"
| "decr (Dvd i a) = Dvd i (decrnum a)"
| "decr (NDvd i a) = NDvd i (decrnum a)"
| "decr (NOT p) = NOT (decr p)"
| "decr (And p q) = And (decr p) (decr q)"
| "decr (Or p q) = Or (decr p) (decr q)"
| "decr (Imp p q) = Imp (decr p) (decr q)"
| "decr (Iff p q) = Iff (decr p) (decr q)"
| "decr p = p"

lemma decrnum:
  assumes nb: "numbound0 t"
  shows "Inum (x # bs) t = Inum bs (decrnum t)"
  using nb by (induct t rule: decrnum.induct) (auto simp add: gr0_conv_Suc)

lemma decr:
  assumes nb: "bound0 p"
  shows "Ifm bbs (x # bs) p = Ifm bbs bs (decr p)"
  using nb by (induct p rule: decr.induct) (simp_all add: gr0_conv_Suc decrnum)

lemma decr_qf: "bound0 p \<Longrightarrow> qfree (decr p)"
  by (induct p) simp_all

fun isatom :: "fm \<Rightarrow> bool"  \<comment> \<open>test for atomicity\<close>
where
  "isatom T \<longleftrightarrow> True"
| "isatom F \<longleftrightarrow> True"
| "isatom (Lt a) \<longleftrightarrow> True"
| "isatom (Le a) \<longleftrightarrow> True"
| "isatom (Gt a) \<longleftrightarrow> True"
| "isatom (Ge a) \<longleftrightarrow> True"
| "isatom (Eq a) \<longleftrightarrow> True"
| "isatom (NEq a) \<longleftrightarrow> True"
| "isatom (Dvd i b) \<longleftrightarrow> True"
| "isatom (NDvd i b) \<longleftrightarrow> True"
| "isatom (Closed P) \<longleftrightarrow> True"
| "isatom (NClosed P) \<longleftrightarrow> True"
| "isatom p \<longleftrightarrow> False"

lemma numsubst0_numbound0:
  assumes "numbound0 t"
  shows "numbound0 (numsubst0 t a)"
  using assms
proof (induct a)
  case (CN n _ _)
  then show ?case by (cases n) simp_all
qed simp_all

lemma subst0_bound0:
  assumes qf: "qfree p"
    and nb: "numbound0 t"
  shows "bound0 (subst0 t p)"
  using qf numsubst0_numbound0[OF nb] by (induct p) auto

lemma bound0_qf: "bound0 p \<Longrightarrow> qfree p"
  by (induct p) simp_all


definition djf :: "('a \<Rightarrow> fm) \<Rightarrow> 'a \<Rightarrow> fm \<Rightarrow> fm"
where
  "djf f p q =
   (if q = T then T
    else if q = F then f p
    else
      let fp = f p
      in case fp of T \<Rightarrow> T | F \<Rightarrow> q | _ \<Rightarrow> Or (f p) q)"

definition evaldjf :: "('a \<Rightarrow> fm) \<Rightarrow> 'a list \<Rightarrow> fm"
  where "evaldjf f ps = foldr (djf f) ps F"

lemma djf_Or: "Ifm bbs bs (djf f p q) = Ifm bbs bs (Or (f p) q)"
  by (cases "q=T", simp add: djf_def, cases "q = F", simp add: djf_def)
    (cases "f p", simp_all add: Let_def djf_def)

lemma evaldjf_ex: "Ifm bbs bs (evaldjf f ps) \<longleftrightarrow> (\<exists>p \<in> set ps. Ifm bbs bs (f p))"
  by (induct ps) (simp_all add: evaldjf_def djf_Or)

lemma evaldjf_bound0:
  assumes nb: "\<forall>x\<in> set xs. bound0 (f x)"
  shows "bound0 (evaldjf f xs)"
  using nb by (induct xs) (auto simp add: evaldjf_def djf_def Let_def, case_tac "f a", auto)

lemma evaldjf_qf:
  assumes nb: "\<forall>x\<in> set xs. qfree (f x)"
  shows "qfree (evaldjf f xs)"
  using nb by (induct xs) (auto simp add: evaldjf_def djf_def Let_def, case_tac "f a", auto)

fun disjuncts :: "fm \<Rightarrow> fm list"
where
  "disjuncts (Or p q) = disjuncts p @ disjuncts q"
| "disjuncts F = []"
| "disjuncts p = [p]"

lemma disjuncts: "(\<exists>q \<in> set (disjuncts p). Ifm bbs bs q) \<longleftrightarrow> Ifm bbs bs p"
  by (induct p rule: disjuncts.induct) auto

lemma disjuncts_nb:
  assumes "bound0 p"
  shows "\<forall>q \<in> set (disjuncts p). bound0 q"
proof -
  from assms have "list_all bound0 (disjuncts p)"
    by (induct p rule: disjuncts.induct) auto
  then show ?thesis
    by (simp only: list_all_iff)
qed

lemma disjuncts_qf:
  assumes "qfree p"
  shows "\<forall>q \<in> set (disjuncts p). qfree q"
proof -
  from assms have "list_all qfree (disjuncts p)"
    by (induct p rule: disjuncts.induct) auto
  then show ?thesis by (simp only: list_all_iff)
qed

definition DJ :: "(fm \<Rightarrow> fm) \<Rightarrow> fm \<Rightarrow> fm"
  where "DJ f p = evaldjf f (disjuncts p)"

lemma DJ:
  assumes "\<forall>p q. f (Or p q) = Or (f p) (f q)"
    and "f F = F"
  shows "Ifm bbs bs (DJ f p) = Ifm bbs bs (f p)"
proof -
  have "Ifm bbs bs (DJ f p) \<longleftrightarrow> (\<exists>q \<in> set (disjuncts p). Ifm bbs bs (f q))"
    by (simp add: DJ_def evaldjf_ex)
  also from assms have "\<dots> = Ifm bbs bs (f p)"
    by (induct p rule: disjuncts.induct) auto
  finally show ?thesis .
qed

lemma DJ_qf:
  assumes "\<forall>p. qfree p \<longrightarrow> qfree (f p)"
  shows "\<forall>p. qfree p \<longrightarrow> qfree (DJ f p) "
proof clarify
  fix p
  assume qf: "qfree p"
  have th: "DJ f p = evaldjf f (disjuncts p)"
    by (simp add: DJ_def)
  from disjuncts_qf[OF qf] have "\<forall>q \<in> set (disjuncts p). qfree q" .
  with assms have th': "\<forall>q \<in> set (disjuncts p). qfree (f q)"
    by blast
  from evaldjf_qf[OF th'] th show "qfree (DJ f p)"
    by simp
qed

lemma DJ_qe:
  assumes qe: "\<forall>bs p. qfree p \<longrightarrow> qfree (qe p) \<and> Ifm bbs bs (qe p) = Ifm bbs bs (E p)"
  shows "\<forall>bs p. qfree p \<longrightarrow> qfree (DJ qe p) \<and> Ifm bbs bs ((DJ qe p)) = Ifm bbs bs (E p)"
proof clarify
  fix p :: fm
  fix bs
  assume qf: "qfree p"
  from qe have qth: "\<forall>p. qfree p \<longrightarrow> qfree (qe p)"
    by blast
  from DJ_qf[OF qth] qf have qfth: "qfree (DJ qe p)"
    by auto
  have "Ifm bbs bs (DJ qe p) = (\<exists>q\<in> set (disjuncts p). Ifm bbs bs (qe q))"
    by (simp add: DJ_def evaldjf_ex)
  also have "\<dots> \<longleftrightarrow> (\<exists>q \<in> set (disjuncts p). Ifm bbs bs (E q))"
    using qe disjuncts_qf[OF qf] by auto
  also have "\<dots> \<longleftrightarrow> Ifm bbs bs (E p)"
    by (induct p rule: disjuncts.induct) auto
  finally show "qfree (DJ qe p) \<and> Ifm bbs bs (DJ qe p) = Ifm bbs bs (E p)"
    using qfth by blast
qed


text \<open>Simplification\<close>

text \<open>Algebraic simplifications for nums\<close>

fun bnds :: "num \<Rightarrow> nat list"
where
  "bnds (Bound n) = [n]"
| "bnds (CN n c a) = n # bnds a"
| "bnds (Neg a) = bnds a"
| "bnds (Add a b) = bnds a @ bnds b"
| "bnds (Sub a b) = bnds a @ bnds b"
| "bnds (Mul i a) = bnds a"
| "bnds a = []"

fun lex_ns:: "nat list \<Rightarrow> nat list \<Rightarrow> bool"
where
  "lex_ns [] ms \<longleftrightarrow> True"
| "lex_ns ns [] \<longleftrightarrow> False"
| "lex_ns (n # ns) (m # ms) \<longleftrightarrow> n < m \<or> (n = m \<and> lex_ns ns ms)"

definition lex_bnd :: "num \<Rightarrow> num \<Rightarrow> bool"
  where "lex_bnd t s = lex_ns (bnds t) (bnds s)"

consts numadd:: "num \<times> num \<Rightarrow> num"
recdef numadd "measure (\<lambda>(t, s). num_size t + num_size s)"
  "numadd (CN n1 c1 r1, CN n2 c2 r2) =
    (if n1 = n2 then
       let c = c1 + c2
       in if c = 0 then numadd (r1, r2) else CN n1 c (numadd (r1, r2))
     else if n1 \<le> n2 then CN n1 c1 (numadd (r1, Add (Mul c2 (Bound n2)) r2))
     else CN n2 c2 (numadd (Add (Mul c1 (Bound n1)) r1, r2)))"
  "numadd (CN n1 c1 r1, t) = CN n1 c1 (numadd (r1, t))"
  "numadd (t, CN n2 c2 r2) = CN n2 c2 (numadd (t, r2))"
  "numadd (C b1, C b2) = C (b1 + b2)"
  "numadd (a, b) = Add a b"

(*function (sequential)
  numadd :: "num \<Rightarrow> num \<Rightarrow> num"
where
  "numadd (Add (Mul c1 (Bound n1)) r1) (Add (Mul c2 (Bound n2)) r2) =
      (if n1 = n2 then (let c = c1 + c2
      in (if c = 0 then numadd r1 r2 else
        Add (Mul c (Bound n1)) (numadd r1 r2)))
      else if n1 \<le> n2 then
        Add (Mul c1 (Bound n1)) (numadd r1 (Add (Mul c2 (Bound n2)) r2))
      else
        Add (Mul c2 (Bound n2)) (numadd (Add (Mul c1 (Bound n1)) r1) r2))"
  | "numadd (Add (Mul c1 (Bound n1)) r1) t =
      Add (Mul c1 (Bound n1)) (numadd r1 t)"
  | "numadd t (Add (Mul c2 (Bound n2)) r2) =
      Add (Mul c2 (Bound n2)) (numadd t r2)"
  | "numadd (C b1) (C b2) = C (b1 + b2)"
  | "numadd a b = Add a b"
apply pat_completeness apply auto*)

lemma numadd: "Inum bs (numadd (t,s)) = Inum bs (Add t s)"
  apply (induct t s rule: numadd.induct)
  apply (simp_all add: Let_def)
  subgoal for n1 c1 r1 n2 c2 r2
    apply (cases "c1 + c2 = 0")
    apply (cases "n1 \<le> n2")
    apply simp_all
     apply (cases "n1 = n2")
      apply (simp_all add: algebra_simps)
    apply (simp add: distrib_right[symmetric])
    done
  done

lemma numadd_nb: "numbound0 t \<Longrightarrow> numbound0 s \<Longrightarrow> numbound0 (numadd (t, s))"
  by (induct t s rule: numadd.induct) (auto simp add: Let_def)

fun nummul :: "int \<Rightarrow> num \<Rightarrow> num"
where
  "nummul i (C j) = C (i * j)"
| "nummul i (CN n c t) = CN n (c * i) (nummul i t)"
| "nummul i t = Mul i t"

lemma nummul: "Inum bs (nummul i t) = Inum bs (Mul i t)"
  by (induct t arbitrary: i rule: nummul.induct) (auto simp add: algebra_simps numadd)

lemma nummul_nb: "numbound0 t \<Longrightarrow> numbound0 (nummul i t)"
  by (induct t arbitrary: i rule: nummul.induct) (auto simp add: numadd_nb)

definition numneg :: "num \<Rightarrow> num"
  where "numneg t = nummul (- 1) t"

definition numsub :: "num \<Rightarrow> num \<Rightarrow> num"
  where "numsub s t = (if s = t then C 0 else numadd (s, numneg t))"

lemma numneg: "Inum bs (numneg t) = Inum bs (Neg t)"
  using numneg_def nummul by simp

lemma numneg_nb: "numbound0 t \<Longrightarrow> numbound0 (numneg t)"
  using numneg_def nummul_nb by simp

lemma numsub: "Inum bs (numsub a b) = Inum bs (Sub a b)"
  using numneg numadd numsub_def by simp

lemma numsub_nb: "numbound0 t \<Longrightarrow> numbound0 s \<Longrightarrow> numbound0 (numsub t s)"
  using numsub_def numadd_nb numneg_nb by simp

fun simpnum :: "num \<Rightarrow> num"
where
  "simpnum (C j) = C j"
| "simpnum (Bound n) = CN n 1 (C 0)"
| "simpnum (Neg t) = numneg (simpnum t)"
| "simpnum (Add t s) = numadd (simpnum t, simpnum s)"
| "simpnum (Sub t s) = numsub (simpnum t) (simpnum s)"
| "simpnum (Mul i t) = (if i = 0 then C 0 else nummul i (simpnum t))"
| "simpnum t = t"

lemma simpnum_ci: "Inum bs (simpnum t) = Inum bs t"
  by (induct t rule: simpnum.induct) (auto simp add: numneg numadd numsub nummul)

lemma simpnum_numbound0: "numbound0 t \<Longrightarrow> numbound0 (simpnum t)"
  by (induct t rule: simpnum.induct) (auto simp add: numadd_nb numsub_nb nummul_nb numneg_nb)

fun not :: "fm \<Rightarrow> fm"
where
  "not (NOT p) = p"
| "not T = F"
| "not F = T"
| "not p = NOT p"

lemma not: "Ifm bbs bs (not p) = Ifm bbs bs (NOT p)"
  by (cases p) auto

lemma not_qf: "qfree p \<Longrightarrow> qfree (not p)"
  by (cases p) auto

lemma not_bn: "bound0 p \<Longrightarrow> bound0 (not p)"
  by (cases p) auto

definition conj :: "fm \<Rightarrow> fm \<Rightarrow> fm"
where
  "conj p q =
    (if p = F \<or> q = F then F
     else if p = T then q
     else if q = T then p
     else And p q)"

lemma conj: "Ifm bbs bs (conj p q) = Ifm bbs bs (And p q)"
  by (cases "p = F \<or> q = F", simp_all add: conj_def) (cases p, simp_all)

lemma conj_qf: "qfree p \<Longrightarrow> qfree q \<Longrightarrow> qfree (conj p q)"
  using conj_def by auto

lemma conj_nb: "bound0 p \<Longrightarrow> bound0 q \<Longrightarrow> bound0 (conj p q)"
  using conj_def by auto

definition disj :: "fm \<Rightarrow> fm \<Rightarrow> fm"
where
  "disj p q =
    (if p = T \<or> q = T then T
     else if p = F then q
     else if q = F then p
     else Or p q)"

lemma disj: "Ifm bbs bs (disj p q) = Ifm bbs bs (Or p q)"
  by (cases "p = T \<or> q = T", simp_all add: disj_def) (cases p, simp_all)

lemma disj_qf: "qfree p \<Longrightarrow> qfree q \<Longrightarrow> qfree (disj p q)"
  using disj_def by auto

lemma disj_nb: "bound0 p \<Longrightarrow> bound0 q \<Longrightarrow> bound0 (disj p q)"
  using disj_def by auto

definition imp :: "fm \<Rightarrow> fm \<Rightarrow> fm"
where
  "imp p q =
    (if p = F \<or> q = T then T
     else if p = T then q
     else if q = F then not p
     else Imp p q)"

lemma imp: "Ifm bbs bs (imp p q) = Ifm bbs bs (Imp p q)"
  by (cases "p = F \<or> q = T", simp_all add: imp_def, cases p) (simp_all add: not)

lemma imp_qf: "qfree p \<Longrightarrow> qfree q \<Longrightarrow> qfree (imp p q)"
  using imp_def by (cases "p = F \<or> q = T", simp_all add: imp_def, cases p) (simp_all add: not_qf)

lemma imp_nb: "bound0 p \<Longrightarrow> bound0 q \<Longrightarrow> bound0 (imp p q)"
  using imp_def by (cases "p = F \<or> q = T", simp_all add: imp_def, cases p) simp_all

definition iff :: "fm \<Rightarrow> fm \<Rightarrow> fm"
where
  "iff p q =
    (if p = q then T
     else if p = not q \<or> not p = q then F
     else if p = F then not q
     else if q = F then not p
     else if p = T then q
     else if q = T then p
     else Iff p q)"

lemma iff: "Ifm bbs bs (iff p q) = Ifm bbs bs (Iff p q)"
  by (unfold iff_def, cases "p = q", simp, cases "p = not q", simp add: not)
    (cases "not p = q", auto simp add: not)

lemma iff_qf: "qfree p \<Longrightarrow> qfree q \<Longrightarrow> qfree (iff p q)"
  by (unfold iff_def, cases "p = q", auto simp add: not_qf)

lemma iff_nb: "bound0 p \<Longrightarrow> bound0 q \<Longrightarrow> bound0 (iff p q)"
  using iff_def by (unfold iff_def, cases "p = q", auto simp add: not_bn)

function (sequential) simpfm :: "fm \<Rightarrow> fm"
where
  "simpfm (And p q) = conj (simpfm p) (simpfm q)"
| "simpfm (Or p q) = disj (simpfm p) (simpfm q)"
| "simpfm (Imp p q) = imp (simpfm p) (simpfm q)"
| "simpfm (Iff p q) = iff (simpfm p) (simpfm q)"
| "simpfm (NOT p) = not (simpfm p)"
| "simpfm (Lt a) = (let a' = simpnum a in case a' of C v \<Rightarrow> if v < 0 then T else F | _ \<Rightarrow> Lt a')"
| "simpfm (Le a) = (let a' = simpnum a in case a' of C v \<Rightarrow> if v \<le> 0 then T else F | _ \<Rightarrow> Le a')"
| "simpfm (Gt a) = (let a' = simpnum a in case a' of C v \<Rightarrow> if v > 0 then T else F | _ \<Rightarrow> Gt a')"
| "simpfm (Ge a) = (let a' = simpnum a in case a' of C v \<Rightarrow> if v \<ge> 0 then T else F | _ \<Rightarrow> Ge a')"
| "simpfm (Eq a) = (let a' = simpnum a in case a' of C v \<Rightarrow> if v = 0 then T else F | _ \<Rightarrow> Eq a')"
| "simpfm (NEq a) = (let a' = simpnum a in case a' of C v \<Rightarrow> if v \<noteq> 0 then T else F | _ \<Rightarrow> NEq a')"
| "simpfm (Dvd i a) =
    (if i = 0 then simpfm (Eq a)
     else if \<bar>i\<bar> = 1 then T
     else let a' = simpnum a in case a' of C v \<Rightarrow> if i dvd v then T else F | _ \<Rightarrow> Dvd i a')"
| "simpfm (NDvd i a) =
    (if i = 0 then simpfm (NEq a)
     else if \<bar>i\<bar> = 1 then F
     else let a' = simpnum a in case a' of C v \<Rightarrow> if \<not>( i dvd v) then T else F | _ \<Rightarrow> NDvd i a')"
| "simpfm p = p"
  by pat_completeness auto
termination by (relation "measure fmsize") auto

lemma simpfm: "Ifm bbs bs (simpfm p) = Ifm bbs bs p"
proof (induct p rule: simpfm.induct)
  case (6 a)
  let ?sa = "simpnum a"
  from simpnum_ci have sa: "Inum bs ?sa = Inum bs a"
    by simp
  consider v where "?sa = C v" | "\<not> (\<exists>v. ?sa = C v)" by blast
  then show ?case
  proof cases
    case 1
    with sa show ?thesis by simp
  next
    case 2
    with sa show ?thesis by (cases ?sa) (simp_all add: Let_def)
  qed
next
  case (7 a)
  let ?sa = "simpnum a"
  from simpnum_ci have sa: "Inum bs ?sa = Inum bs a"
    by simp
  consider v where "?sa = C v" | "\<not> (\<exists>v. ?sa = C v)" by blast
  then show ?case
  proof cases
    case 1
    with sa show ?thesis by simp
  next
    case 2
    with sa show ?thesis by (cases ?sa) (simp_all add: Let_def)
  qed
next
  case (8 a)
  let ?sa = "simpnum a"
  from simpnum_ci have sa: "Inum bs ?sa = Inum bs a"
    by simp
  consider v where "?sa = C v" | "\<not> (\<exists>v. ?sa = C v)" by blast
  then show ?case
  proof cases
    case 1
    with sa show ?thesis by simp
  next
    case 2
    with sa show ?thesis by (cases ?sa) (simp_all add: Let_def)
  qed
next
  case (9 a)
  let ?sa = "simpnum a"
  from simpnum_ci have sa: "Inum bs ?sa = Inum bs a"
    by simp
  consider v where "?sa = C v" | "\<not> (\<exists>v. ?sa = C v)" by blast
  then show ?case
  proof cases
    case 1
    with sa show ?thesis by simp
  next
    case 2
    with sa show ?thesis by (cases ?sa) (simp_all add: Let_def)
  qed
next
  case (10 a)
  let ?sa = "simpnum a"
  from simpnum_ci have sa: "Inum bs ?sa = Inum bs a"
    by simp
  consider v where "?sa = C v" | "\<not> (\<exists>v. ?sa = C v)" by blast
  then show ?case
  proof cases
    case 1
    with sa show ?thesis by simp
  next
    case 2
    with sa show ?thesis by (cases ?sa) (simp_all add: Let_def)
  qed
next
  case (11 a)
  let ?sa = "simpnum a"
  from simpnum_ci have sa: "Inum bs ?sa = Inum bs a"
    by simp
  consider v where "?sa = C v" | "\<not> (\<exists>v. ?sa = C v)" by blast
  then show ?case
  proof cases
    case 1
    with sa show ?thesis by simp
  next
    case 2
    with sa show ?thesis by (cases ?sa) (simp_all add: Let_def)
  qed
next
  case (12 i a)
  let ?sa = "simpnum a"
  from simpnum_ci have sa: "Inum bs ?sa = Inum bs a"
    by simp
  consider "i = 0" | "\<bar>i\<bar> = 1" | "i \<noteq> 0" "\<bar>i\<bar> \<noteq> 1" by blast
  then show ?case
  proof cases
    case 1
    then show ?thesis
      using "12.hyps" by (simp add: dvd_def Let_def)
  next
    case 2
    with one_dvd[of "Inum bs a"] uminus_dvd_conv[where d="1" and t="Inum bs a"]
    show ?thesis
      apply (cases "i = 0")
      apply (simp_all add: Let_def)
      apply (cases "i > 0")
      apply simp_all
      done
  next
    case i: 3
    consider v where "?sa = C v" | "\<not> (\<exists>v. ?sa = C v)" by blast
    then show ?thesis
    proof cases
      case 1
      with sa[symmetric] i show ?thesis
        by (cases "\<bar>i\<bar> = 1") auto
    next
      case 2
      then have "simpfm (Dvd i a) = Dvd i ?sa"
        using i by (cases ?sa) (auto simp add: Let_def)
      with sa show ?thesis by simp
    qed
  qed
next
  case (13 i a)
  let ?sa = "simpnum a"
  from simpnum_ci have sa: "Inum bs ?sa = Inum bs a"
    by simp
  consider "i = 0" | "\<bar>i\<bar> = 1" | "i \<noteq> 0" "\<bar>i\<bar> \<noteq> 1" by blast
  then show ?case
  proof cases
    case 1
    then show ?thesis
      using "13.hyps" by (simp add: dvd_def Let_def)
  next
    case 2
    with one_dvd[of "Inum bs a"] uminus_dvd_conv[where d="1" and t="Inum bs a"]
    show ?thesis
      apply (cases "i = 0")
      apply (simp_all add: Let_def)
      apply (cases "i > 0")
      apply simp_all
      done
  next
    case i: 3
    consider v where "?sa = C v" | "\<not> (\<exists>v. ?sa = C v)" by blast
    then show ?thesis
    proof cases
      case 1
      with sa[symmetric] i show ?thesis
        by (cases "\<bar>i\<bar> = 1") auto
    next
      case 2
      then have "simpfm (NDvd i a) = NDvd i ?sa"
        using i by (cases ?sa) (auto simp add: Let_def)
      with sa show ?thesis by simp
    qed
  qed
qed (simp_all add: conj disj imp iff not)

lemma simpfm_bound0: "bound0 p \<Longrightarrow> bound0 (simpfm p)"
proof (induct p rule: simpfm.induct)
  case (6 a)
  then have nb: "numbound0 a" by simp
  then have "numbound0 (simpnum a)" by (simp only: simpnum_numbound0[OF nb])
  then show ?case by (cases "simpnum a") (auto simp add: Let_def)
next
  case (7 a)
  then have nb: "numbound0 a" by simp
  then have "numbound0 (simpnum a)" by (simp only: simpnum_numbound0[OF nb])
  then show ?case by (cases "simpnum a") (auto simp add: Let_def)
next
  case (8 a)
  then have nb: "numbound0 a" by simp
  then have "numbound0 (simpnum a)" by (simp only: simpnum_numbound0[OF nb])
  then show ?case by (cases "simpnum a") (auto simp add: Let_def)
next
  case (9 a)
  then have nb: "numbound0 a" by simp
  then have "numbound0 (simpnum a)" by (simp only: simpnum_numbound0[OF nb])
  then show ?case by (cases "simpnum a") (auto simp add: Let_def)
next
  case (10 a)
  then have nb: "numbound0 a" by simp
  then have "numbound0 (simpnum a)" by (simp only: simpnum_numbound0[OF nb])
  then show ?case by (cases "simpnum a") (auto simp add: Let_def)
next
  case (11 a)
  then have nb: "numbound0 a" by simp
  then have "numbound0 (simpnum a)" by (simp only: simpnum_numbound0[OF nb])
  then show ?case by (cases "simpnum a") (auto simp add: Let_def)
next
  case (12 i a)
  then have nb: "numbound0 a" by simp
  then have "numbound0 (simpnum a)" by (simp only: simpnum_numbound0[OF nb])
  then show ?case by (cases "simpnum a") (auto simp add: Let_def)
next
  case (13 i a)
  then have nb: "numbound0 a" by simp
  then have "numbound0 (simpnum a)" by (simp only: simpnum_numbound0[OF nb])
  then show ?case by (cases "simpnum a") (auto simp add: Let_def)
qed (auto simp add: disj_def imp_def iff_def conj_def not_bn)

lemma simpfm_qf: "qfree p \<Longrightarrow> qfree (simpfm p)"
  apply (induct p rule: simpfm.induct)
  apply (auto simp add: disj_qf imp_qf iff_qf conj_qf not_qf Let_def)
  apply (case_tac "simpnum a", auto)+
  done

text \<open>Generic quantifier elimination\<close>
function (sequential) qelim :: "fm \<Rightarrow> (fm \<Rightarrow> fm) \<Rightarrow> fm"
where
  "qelim (E p) = (\<lambda>qe. DJ qe (qelim p qe))"
| "qelim (A p) = (\<lambda>qe. not (qe ((qelim (NOT p) qe))))"
| "qelim (NOT p) = (\<lambda>qe. not (qelim p qe))"
| "qelim (And p q) = (\<lambda>qe. conj (qelim p qe) (qelim q qe))"
| "qelim (Or  p q) = (\<lambda>qe. disj (qelim p qe) (qelim q qe))"
| "qelim (Imp p q) = (\<lambda>qe. imp (qelim p qe) (qelim q qe))"
| "qelim (Iff p q) = (\<lambda>qe. iff (qelim p qe) (qelim q qe))"
| "qelim p = (\<lambda>y. simpfm p)"
  by pat_completeness auto
termination by (relation "measure fmsize") auto

lemma qelim_ci:
  assumes qe_inv: "\<forall>bs p. qfree p \<longrightarrow> qfree (qe p) \<and> Ifm bbs bs (qe p) = Ifm bbs bs (E p)"
  shows "\<And>bs. qfree (qelim p qe) \<and> Ifm bbs bs (qelim p qe) = Ifm bbs bs p"
  using qe_inv DJ_qe[OF qe_inv]
  by (induct p rule: qelim.induct)
    (auto simp add: not disj conj iff imp not_qf disj_qf conj_qf imp_qf iff_qf
      simpfm simpfm_qf simp del: simpfm.simps)

text \<open>Linearity for fm where Bound 0 ranges over \<open>\<int>\<close>\<close>

fun zsplit0 :: "num \<Rightarrow> int \<times> num"  \<comment> \<open>splits the bounded from the unbounded part\<close>
where
  "zsplit0 (C c) = (0, C c)"
| "zsplit0 (Bound n) = (if n = 0 then (1, C 0) else (0, Bound n))"
| "zsplit0 (CN n i a) =
    (let (i', a') =  zsplit0 a
     in if n = 0 then (i + i', a') else (i', CN n i a'))"
| "zsplit0 (Neg a) = (let (i', a') = zsplit0 a in (-i', Neg a'))"
| "zsplit0 (Add a b) =
    (let
      (ia, a') = zsplit0 a;
      (ib, b') = zsplit0 b
     in (ia + ib, Add a' b'))"
| "zsplit0 (Sub a b) =
    (let
      (ia, a') = zsplit0 a;
      (ib, b') = zsplit0 b
     in (ia - ib, Sub a' b'))"
| "zsplit0 (Mul i a) = (let (i', a') = zsplit0 a in (i*i', Mul i a'))"

lemma zsplit0_I:
  "\<And>n a. zsplit0 t = (n, a) \<Longrightarrow>
    (Inum ((x::int) # bs) (CN 0 n a) = Inum (x # bs) t) \<and> numbound0 a"
  (is "\<And>n a. ?S t = (n,a) \<Longrightarrow> (?I x (CN 0 n a) = ?I x t) \<and> ?N a")
proof (induct t rule: zsplit0.induct)
  case (1 c n a)
  then show ?case by auto
next
  case (2 m n a)
  then show ?case by (cases "m = 0") auto
next
  case (3 m i a n a')
  let ?j = "fst (zsplit0 a)"
  let ?b = "snd (zsplit0 a)"
  have abj: "zsplit0 a = (?j, ?b)" by simp
  show ?case
  proof (cases "m = 0")
    case False
    with 3(1)[OF abj] 3(2) show ?thesis
      by (auto simp add: Let_def split_def)
  next
    case m: True
    with abj have th: "a' = ?b \<and> n = i + ?j"
      using 3 by (simp add: Let_def split_def)
    from abj 3 m have th2: "(?I x (CN 0 ?j ?b) = ?I x a) \<and> ?N ?b"
      by blast
    from th have "?I x (CN 0 n a') = ?I x (CN 0 (i + ?j) ?b)"
      by simp
    also from th2 have "\<dots> = ?I x (CN 0 i (CN 0 ?j ?b))"
      by (simp add: distrib_right)
    finally have "?I x (CN 0 n a') = ?I  x (CN 0 i a)"
      using th2 by simp
    with th2 th m show ?thesis
      by blast
  qed
next
  case (4 t n a)
  let ?nt = "fst (zsplit0 t)"
  let ?at = "snd (zsplit0 t)"
  have abj: "zsplit0 t = (?nt, ?at)"
    by simp
  then have th: "a = Neg ?at \<and> n = - ?nt"
    using 4 by (simp add: Let_def split_def)
  from abj 4 have th2: "(?I x (CN 0 ?nt ?at) = ?I x t) \<and> ?N ?at"
    by blast
  from th2[simplified] th[simplified] show ?case
    by simp
next
  case (5 s t n a)
  let ?ns = "fst (zsplit0 s)"
  let ?as = "snd (zsplit0 s)"
  let ?nt = "fst (zsplit0 t)"
  let ?at = "snd (zsplit0 t)"
  have abjs: "zsplit0 s = (?ns, ?as)"
    by simp
  moreover have abjt: "zsplit0 t = (?nt, ?at)"
    by simp
  ultimately have th: "a = Add ?as ?at \<and> n = ?ns + ?nt"
    using 5 by (simp add: Let_def split_def)
  from abjs[symmetric] have bluddy: "\<exists>x y. (x, y) = zsplit0 s"
    by blast
  from 5 have "(\<exists>x y. (x, y) = zsplit0 s) \<longrightarrow>
    (\<forall>xa xb. zsplit0 t = (xa, xb) \<longrightarrow> Inum (x # bs) (CN 0 xa xb) = Inum (x # bs) t \<and> numbound0 xb)"
    by auto
  with bluddy abjt have th3: "(?I x (CN 0 ?nt ?at) = ?I x t) \<and> ?N ?at"
    by blast
  from abjs 5 have th2: "(?I x (CN 0 ?ns ?as) = ?I x s) \<and> ?N ?as"
    by blast
  from th3[simplified] th2[simplified] th[simplified] show ?case
    by (simp add: distrib_right)
next
  case (6 s t n a)
  let ?ns = "fst (zsplit0 s)"
  let ?as = "snd (zsplit0 s)"
  let ?nt = "fst (zsplit0 t)"
  let ?at = "snd (zsplit0 t)"
  have abjs: "zsplit0 s = (?ns, ?as)"
    by simp
  moreover have abjt: "zsplit0 t = (?nt, ?at)"
    by simp
  ultimately have th: "a = Sub ?as ?at \<and> n = ?ns - ?nt"
    using 6 by (simp add: Let_def split_def)
  from abjs[symmetric] have bluddy: "\<exists>x y. (x, y) = zsplit0 s"
    by blast
  from 6 have "(\<exists>x y. (x,y) = zsplit0 s) \<longrightarrow>
    (\<forall>xa xb. zsplit0 t = (xa, xb) \<longrightarrow> Inum (x # bs) (CN 0 xa xb) = Inum (x # bs) t \<and> numbound0 xb)"
    by auto
  with bluddy abjt have th3: "(?I x (CN 0 ?nt ?at) = ?I x t) \<and> ?N ?at"
    by blast
  from abjs 6 have th2: "(?I x (CN 0 ?ns ?as) = ?I x s) \<and> ?N ?as"
    by blast
  from th3[simplified] th2[simplified] th[simplified] show ?case
    by (simp add: left_diff_distrib)
next
  case (7 i t n a)
  let ?nt = "fst (zsplit0 t)"
  let ?at = "snd (zsplit0 t)"
  have abj: "zsplit0 t = (?nt,?at)"
    by simp
  then have th: "a = Mul i ?at \<and> n = i * ?nt"
    using 7 by (simp add: Let_def split_def)
  from abj 7 have th2: "(?I x (CN 0 ?nt ?at) = ?I x t) \<and> ?N ?at"
    by blast
  then have "?I x (Mul i t) = i * ?I x (CN 0 ?nt ?at)"
    by simp
  also have "\<dots> = ?I x (CN 0 (i*?nt) (Mul i ?at))"
    by (simp add: distrib_left)
  finally show ?case using th th2
    by simp
qed

consts iszlfm :: "fm \<Rightarrow> bool"  \<comment> \<open>Linearity test for fm\<close>
recdef iszlfm "measure size"
  "iszlfm (And p q) \<longleftrightarrow> iszlfm p \<and> iszlfm q"
  "iszlfm (Or p q) \<longleftrightarrow> iszlfm p \<and> iszlfm q"
  "iszlfm (Eq  (CN 0 c e)) \<longleftrightarrow> c > 0 \<and> numbound0 e"
  "iszlfm (NEq (CN 0 c e)) \<longleftrightarrow> c > 0 \<and> numbound0 e"
  "iszlfm (Lt  (CN 0 c e)) \<longleftrightarrow> c > 0 \<and> numbound0 e"
  "iszlfm (Le  (CN 0 c e)) \<longleftrightarrow> c > 0 \<and> numbound0 e"
  "iszlfm (Gt  (CN 0 c e)) \<longleftrightarrow> c > 0 \<and> numbound0 e"
  "iszlfm (Ge  (CN 0 c e)) \<longleftrightarrow> c > 0 \<and> numbound0 e"
  "iszlfm (Dvd i (CN 0 c e)) \<longleftrightarrow> c > 0 \<and> i > 0 \<and> numbound0 e"
  "iszlfm (NDvd i (CN 0 c e)) \<longleftrightarrow> c > 0 \<and> i > 0 \<and> numbound0 e"
  "iszlfm p \<longleftrightarrow> isatom p \<and> bound0 p"

lemma zlin_qfree: "iszlfm p \<Longrightarrow> qfree p"
  by (induct p rule: iszlfm.induct) auto

consts zlfm :: "fm \<Rightarrow> fm"  \<comment> \<open>Linearity transformation for fm\<close>
recdef zlfm "measure fmsize"
  "zlfm (And p q) = And (zlfm p) (zlfm q)"
  "zlfm (Or p q) = Or (zlfm p) (zlfm q)"
  "zlfm (Imp p q) = Or (zlfm (NOT p)) (zlfm q)"
  "zlfm (Iff p q) = Or (And (zlfm p) (zlfm q)) (And (zlfm (NOT p)) (zlfm (NOT q)))"
  "zlfm (Lt a) =
    (let (c, r) = zsplit0 a in
      if c = 0 then Lt r else
      if c > 0 then (Lt (CN 0 c r))
      else Gt (CN 0 (- c) (Neg r)))"
  "zlfm (Le a) =
    (let (c, r) = zsplit0 a in
      if c = 0 then Le r
      else if c > 0 then Le (CN 0 c r)
      else Ge (CN 0 (- c) (Neg r)))"
  "zlfm (Gt a) =
    (let (c, r) = zsplit0 a in
      if c = 0 then Gt r else
      if c > 0 then Gt (CN 0 c r)
      else Lt (CN 0 (- c) (Neg r)))"
  "zlfm (Ge a) =
    (let (c, r) = zsplit0 a in
      if c = 0 then Ge r
      else if c > 0 then Ge (CN 0 c r)
      else Le (CN 0 (- c) (Neg r)))"
  "zlfm (Eq a) =
    (let (c, r) = zsplit0 a in
      if c = 0 then Eq r
      else if c > 0 then Eq (CN 0 c r)
      else Eq (CN 0 (- c) (Neg r)))"
  "zlfm (NEq a) =
    (let (c, r) = zsplit0 a in
      if c = 0 then NEq r
      else if c > 0 then NEq (CN 0 c r)
      else NEq (CN 0 (- c) (Neg r)))"
  "zlfm (Dvd i a) =
    (if i = 0 then zlfm (Eq a)
     else
      let (c, r) = zsplit0 a in
        if c = 0 then Dvd \<bar>i\<bar> r
        else if c > 0 then Dvd \<bar>i\<bar> (CN 0 c r)
        else Dvd \<bar>i\<bar> (CN 0 (- c) (Neg r)))"
  "zlfm (NDvd i a) =
    (if i = 0 then zlfm (NEq a)
     else
      let (c, r) = zsplit0 a in
        if c = 0 then NDvd \<bar>i\<bar> r
        else if c > 0 then NDvd \<bar>i\<bar> (CN 0 c r)
        else NDvd \<bar>i\<bar> (CN 0 (- c) (Neg r)))"
  "zlfm (NOT (And p q)) = Or (zlfm (NOT p)) (zlfm (NOT q))"
  "zlfm (NOT (Or p q)) = And (zlfm (NOT p)) (zlfm (NOT q))"
  "zlfm (NOT (Imp p q)) = And (zlfm p) (zlfm (NOT q))"
  "zlfm (NOT (Iff p q)) = Or (And(zlfm p) (zlfm(NOT q))) (And (zlfm(NOT p)) (zlfm q))"
  "zlfm (NOT (NOT p)) = zlfm p"
  "zlfm (NOT T) = F"
  "zlfm (NOT F) = T"
  "zlfm (NOT (Lt a)) = zlfm (Ge a)"
  "zlfm (NOT (Le a)) = zlfm (Gt a)"
  "zlfm (NOT (Gt a)) = zlfm (Le a)"
  "zlfm (NOT (Ge a)) = zlfm (Lt a)"
  "zlfm (NOT (Eq a)) = zlfm (NEq a)"
  "zlfm (NOT (NEq a)) = zlfm (Eq a)"
  "zlfm (NOT (Dvd i a)) = zlfm (NDvd i a)"
  "zlfm (NOT (NDvd i a)) = zlfm (Dvd i a)"
  "zlfm (NOT (Closed P)) = NClosed P"
  "zlfm (NOT (NClosed P)) = Closed P"
  "zlfm p = p" (hints simp add: fmsize_pos)

lemma zlfm_I:
  assumes qfp: "qfree p"
  shows "Ifm bbs (i # bs) (zlfm p) = Ifm bbs (i # bs) p \<and> iszlfm (zlfm p)"
    (is "?I (?l p) = ?I p \<and> ?L (?l p)")
  using qfp
proof (induct p rule: zlfm.induct)
  case (5 a)
  let ?c = "fst (zsplit0 a)"
  let ?r = "snd (zsplit0 a)"
  have spl: "zsplit0 a = (?c, ?r)"
    by simp
  from zsplit0_I[OF spl, where x="i" and bs="bs"]
  have Ia: "Inum (i # bs) a = Inum (i #bs) (CN 0 ?c ?r)" and nb: "numbound0 ?r"
    by auto
  let ?N = "\<lambda>t. Inum (i # bs) t"
  from 5 Ia nb show ?case
    apply (auto simp add: Let_def split_def algebra_simps)
    apply (cases "?r")
    apply auto
    subgoal for nat a b by (cases nat) auto
    done
next
  case (6 a)
  let ?c = "fst (zsplit0 a)"
  let ?r = "snd (zsplit0 a)"
  have spl: "zsplit0 a = (?c, ?r)"
    by simp
  from zsplit0_I[OF spl, where x="i" and bs="bs"]
  have Ia: "Inum (i # bs) a = Inum (i #bs) (CN 0 ?c ?r)" and nb: "numbound0 ?r"
    by auto
  let ?N = "\<lambda>t. Inum (i # bs) t"
  from 6 Ia nb show ?case
    apply (auto simp add: Let_def split_def algebra_simps)
    apply (cases "?r")
    apply auto
    subgoal for nat a b by (cases nat) auto
    done
next
  case (7 a)
  let ?c = "fst (zsplit0 a)"
  let ?r = "snd (zsplit0 a)"
  have spl: "zsplit0 a = (?c, ?r)"
    by simp
  from zsplit0_I[OF spl, where x="i" and bs="bs"]
  have Ia: "Inum (i # bs) a = Inum (i #bs) (CN 0 ?c ?r)" and nb: "numbound0 ?r"
    by auto
  let ?N = "\<lambda>t. Inum (i # bs) t"
  from 7 Ia nb show ?case
    apply (auto simp add: Let_def split_def algebra_simps)
    apply (cases "?r")
    apply auto
    subgoal for nat a b by (cases nat) auto
    done
next
  case (8 a)
  let ?c = "fst (zsplit0 a)"
  let ?r = "snd (zsplit0 a)"
  have spl: "zsplit0 a = (?c, ?r)"
    by simp
  from zsplit0_I[OF spl, where x="i" and bs="bs"]
  have Ia: "Inum (i # bs) a = Inum (i #bs) (CN 0 ?c ?r)" and nb: "numbound0 ?r"
    by auto
  let ?N = "\<lambda>t. Inum (i # bs) t"
  from 8 Ia nb show ?case
    apply (auto simp add: Let_def split_def algebra_simps)
    apply (cases "?r")
    apply auto
    subgoal for nat a b by (cases nat) auto
    done
next
  case (9 a)
  let ?c = "fst (zsplit0 a)"
  let ?r = "snd (zsplit0 a)"
  have spl: "zsplit0 a = (?c, ?r)"
    by simp
  from zsplit0_I[OF spl, where x="i" and bs="bs"]
  have Ia:"Inum (i # bs) a = Inum (i #bs) (CN 0 ?c ?r)" and nb: "numbound0 ?r"
    by auto
  let ?N = "\<lambda>t. Inum (i # bs) t"
  from 9 Ia nb show ?case
    apply (auto simp add: Let_def split_def algebra_simps)
    apply (cases "?r")
    apply auto
    subgoal for nat a b by (cases nat) auto
    done
next
  case (10 a)
  let ?c = "fst (zsplit0 a)"
  let ?r = "snd (zsplit0 a)"
  have spl: "zsplit0 a = (?c, ?r)"
    by simp
  from zsplit0_I[OF spl, where x="i" and bs="bs"]
  have Ia: "Inum (i # bs) a = Inum (i #bs) (CN 0 ?c ?r)" and nb: "numbound0 ?r"
    by auto
  let ?N = "\<lambda>t. Inum (i # bs) t"
  from 10 Ia nb show ?case
    apply (auto simp add: Let_def split_def algebra_simps)
    apply (cases "?r")
    apply auto
    subgoal for nat a b by (cases nat) auto
    done
next
  case (11 j a)
  let ?c = "fst (zsplit0 a)"
  let ?r = "snd (zsplit0 a)"
  have spl: "zsplit0 a = (?c,?r)"
    by simp
  from zsplit0_I[OF spl, where x="i" and bs="bs"]
  have Ia: "Inum (i # bs) a = Inum (i #bs) (CN 0 ?c ?r)" and nb: "numbound0 ?r"
    by auto
  let ?N = "\<lambda>t. Inum (i#bs) t"
  consider "j = 0" | "j \<noteq> 0" "?c = 0" | "j \<noteq> 0" "?c > 0" | "j \<noteq> 0" "?c < 0"
    by arith
  then show ?case
  proof cases
    case 1
    then have z: "zlfm (Dvd j a) = (zlfm (Eq a))"
      by (simp add: Let_def)
    with 11 \<open>j = 0\<close> show ?thesis
      by (simp del: zlfm.simps)
  next
    case 2
    with zsplit0_I[OF spl, where x="i" and bs="bs"] show ?thesis
      apply (auto simp add: Let_def split_def algebra_simps)
      apply (cases "?r")
      apply auto
      subgoal for nat a b by (cases nat) auto
      done
  next
    case 3
    then have l: "?L (?l (Dvd j a))"
      by (simp add: nb Let_def split_def)
    with Ia 3 show ?thesis
      by (simp add: Let_def split_def)
  next
    case 4
    then have l: "?L (?l (Dvd j a))"
      by (simp add: nb Let_def split_def)
    with Ia 4 dvd_minus_iff[of "\<bar>j\<bar>" "?c*i + ?N ?r"] show ?thesis
      by (simp add: Let_def split_def)
  qed
next
  case (12 j a)
  let ?c = "fst (zsplit0 a)"
  let ?r = "snd (zsplit0 a)"
  have spl: "zsplit0 a = (?c, ?r)"
    by simp
  from zsplit0_I[OF spl, where x="i" and bs="bs"]
  have Ia:"Inum (i # bs) a = Inum (i #bs) (CN 0 ?c ?r)" and nb: "numbound0 ?r"
    by auto
  let ?N = "\<lambda>t. Inum (i # bs) t"
  consider "j = 0" | "j \<noteq> 0" "?c = 0" | "j \<noteq> 0" "?c > 0" | "j \<noteq> 0" "?c < 0"
    by arith
  then show ?case
  proof cases
    case 1
    then have z: "zlfm (NDvd j a) = zlfm (NEq a)"
      by (simp add: Let_def)
    with assms 12 \<open>j = 0\<close> show ?thesis
      by (simp del: zlfm.simps)
  next
    case 2
    with zsplit0_I[OF spl, where x="i" and bs="bs"] show ?thesis
      apply (auto simp add: Let_def split_def algebra_simps)
      apply (cases "?r")
      apply auto
      subgoal for nat a b by (cases nat) auto
      done
  next
    case 3
    then have l: "?L (?l (Dvd j a))"
      by (simp add: nb Let_def split_def)
    with Ia 3 show ?thesis
      by (simp add: Let_def split_def)
  next
    case 4
    then have l: "?L (?l (Dvd j a))"
      by (simp add: nb Let_def split_def)
    with Ia 4 dvd_minus_iff[of "\<bar>j\<bar>" "?c*i + ?N ?r"] show ?thesis
      by (simp add: Let_def split_def)
  qed
qed auto

consts minusinf :: "fm \<Rightarrow> fm" \<comment> \<open>Virtual substitution of \<open>-\<infinity>\<close>\<close>
recdef minusinf "measure size"
  "minusinf (And p q) = And (minusinf p) (minusinf q)"
  "minusinf (Or p q) = Or (minusinf p) (minusinf q)"
  "minusinf (Eq  (CN 0 c e)) = F"
  "minusinf (NEq (CN 0 c e)) = T"
  "minusinf (Lt  (CN 0 c e)) = T"
  "minusinf (Le  (CN 0 c e)) = T"
  "minusinf (Gt  (CN 0 c e)) = F"
  "minusinf (Ge  (CN 0 c e)) = F"
  "minusinf p = p"

lemma minusinf_qfree: "qfree p \<Longrightarrow> qfree (minusinf p)"
  by (induct p rule: minusinf.induct) auto

consts plusinf :: "fm \<Rightarrow> fm"  \<comment> \<open>Virtual substitution of \<open>+\<infinity>\<close>\<close>
recdef plusinf "measure size"
  "plusinf (And p q) = And (plusinf p) (plusinf q)"
  "plusinf (Or p q) = Or (plusinf p) (plusinf q)"
  "plusinf (Eq  (CN 0 c e)) = F"
  "plusinf (NEq (CN 0 c e)) = T"
  "plusinf (Lt  (CN 0 c e)) = F"
  "plusinf (Le  (CN 0 c e)) = F"
  "plusinf (Gt  (CN 0 c e)) = T"
  "plusinf (Ge  (CN 0 c e)) = T"
  "plusinf p = p"

consts \<delta> :: "fm \<Rightarrow> int"  \<comment> \<open>Compute \<open>lcm {d| N\<^sup>? Dvd c*x+t \<in> p}\<close>\<close>
recdef \<delta> "measure size"
  "\<delta> (And p q) = lcm (\<delta> p) (\<delta> q)"
  "\<delta> (Or p q) = lcm (\<delta> p) (\<delta> q)"
  "\<delta> (Dvd i (CN 0 c e)) = i"
  "\<delta> (NDvd i (CN 0 c e)) = i"
  "\<delta> p = 1"

consts d_\<delta> :: "fm \<Rightarrow> int \<Rightarrow> bool"  \<comment> \<open>check if a given l divides all the ds above\<close>
recdef d_\<delta> "measure size"
  "d_\<delta> (And p q) = (\<lambda>d. d_\<delta> p d \<and> d_\<delta> q d)"
  "d_\<delta> (Or p q) = (\<lambda>d. d_\<delta> p d \<and> d_\<delta> q d)"
  "d_\<delta> (Dvd i (CN 0 c e)) = (\<lambda>d. i dvd d)"
  "d_\<delta> (NDvd i (CN 0 c e)) = (\<lambda>d. i dvd d)"
  "d_\<delta> p = (\<lambda>d. True)"

lemma delta_mono:
  assumes lin: "iszlfm p"
    and d: "d dvd d'"
    and ad: "d_\<delta> p d"
  shows "d_\<delta> p d'"
  using lin ad
proof (induct p rule: iszlfm.induct)
  case (9 i c e)
  then show ?case using d
    by (simp add: dvd_trans[of "i" "d" "d'"])
next
  case (10 i c e)
  then show ?case using d
    by (simp add: dvd_trans[of "i" "d" "d'"])
qed simp_all

lemma \<delta>:
  assumes lin: "iszlfm p"
  shows "d_\<delta> p (\<delta> p) \<and> \<delta> p >0"
  using lin
proof (induct p rule: iszlfm.induct)
  case (1 p q)
  let ?d = "\<delta> (And p q)"
  from 1 lcm_pos_int have dp: "?d > 0"
    by simp
  have d1: "\<delta> p dvd \<delta> (And p q)"
    using 1 by simp
  then have th: "d_\<delta> p ?d"
    using delta_mono 1(2,3) by (simp only: iszlfm.simps)
  have "\<delta> q dvd \<delta> (And p q)"
    using 1 by simp
  then have th': "d_\<delta> q ?d"
    using delta_mono 1 by (simp only: iszlfm.simps)
  from th th' dp show ?case
    by simp
next
  case (2 p q)
  let ?d = "\<delta> (And p q)"
  from 2 lcm_pos_int have dp: "?d > 0"
    by simp
  have "\<delta> p dvd \<delta> (And p q)"
    using 2 by simp
  then have th: "d_\<delta> p ?d"
    using delta_mono 2 by (simp only: iszlfm.simps)
  have "\<delta> q dvd \<delta> (And p q)"
    using 2 by simp
  then have th': "d_\<delta> q ?d"
    using delta_mono 2 by (simp only: iszlfm.simps)
  from th th' dp show ?case
    by simp
qed simp_all


consts a_\<beta> :: "fm \<Rightarrow> int \<Rightarrow> fm"  \<comment> \<open>adjust the coefficients of a formula\<close>
recdef a_\<beta> "measure size"
  "a_\<beta> (And p q) = (\<lambda>k. And (a_\<beta> p k) (a_\<beta> q k))"
  "a_\<beta> (Or p q) = (\<lambda>k. Or (a_\<beta> p k) (a_\<beta> q k))"
  "a_\<beta> (Eq  (CN 0 c e)) = (\<lambda>k. Eq (CN 0 1 (Mul (k div c) e)))"
  "a_\<beta> (NEq (CN 0 c e)) = (\<lambda>k. NEq (CN 0 1 (Mul (k div c) e)))"
  "a_\<beta> (Lt  (CN 0 c e)) = (\<lambda>k. Lt (CN 0 1 (Mul (k div c) e)))"
  "a_\<beta> (Le  (CN 0 c e)) = (\<lambda>k. Le (CN 0 1 (Mul (k div c) e)))"
  "a_\<beta> (Gt  (CN 0 c e)) = (\<lambda>k. Gt (CN 0 1 (Mul (k div c) e)))"
  "a_\<beta> (Ge  (CN 0 c e)) = (\<lambda>k. Ge (CN 0 1 (Mul (k div c) e)))"
  "a_\<beta> (Dvd i (CN 0 c e)) =(\<lambda>k. Dvd ((k div c)*i) (CN 0 1 (Mul (k div c) e)))"
  "a_\<beta> (NDvd i (CN 0 c e))=(\<lambda>k. NDvd ((k div c)*i) (CN 0 1 (Mul (k div c) e)))"
  "a_\<beta> p = (\<lambda>k. p)"

consts d_\<beta> :: "fm \<Rightarrow> int \<Rightarrow> bool"  \<comment> \<open>test if all coeffs c of c divide a given l\<close>
recdef d_\<beta> "measure size"
  "d_\<beta> (And p q) = (\<lambda>k. (d_\<beta> p k) \<and> (d_\<beta> q k))"
  "d_\<beta> (Or p q) = (\<lambda>k. (d_\<beta> p k) \<and> (d_\<beta> q k))"
  "d_\<beta> (Eq  (CN 0 c e)) = (\<lambda>k. c dvd k)"
  "d_\<beta> (NEq (CN 0 c e)) = (\<lambda>k. c dvd k)"
  "d_\<beta> (Lt  (CN 0 c e)) = (\<lambda>k. c dvd k)"
  "d_\<beta> (Le  (CN 0 c e)) = (\<lambda>k. c dvd k)"
  "d_\<beta> (Gt  (CN 0 c e)) = (\<lambda>k. c dvd k)"
  "d_\<beta> (Ge  (CN 0 c e)) = (\<lambda>k. c dvd k)"
  "d_\<beta> (Dvd i (CN 0 c e)) =(\<lambda>k. c dvd k)"
  "d_\<beta> (NDvd i (CN 0 c e))=(\<lambda>k. c dvd k)"
  "d_\<beta> p = (\<lambda>k. True)"

consts \<zeta> :: "fm \<Rightarrow> int"  \<comment> \<open>computes the lcm of all coefficients of x\<close>
recdef \<zeta> "measure size"
  "\<zeta> (And p q) = lcm (\<zeta> p) (\<zeta> q)"
  "\<zeta> (Or p q) = lcm (\<zeta> p) (\<zeta> q)"
  "\<zeta> (Eq  (CN 0 c e)) = c"
  "\<zeta> (NEq (CN 0 c e)) = c"
  "\<zeta> (Lt  (CN 0 c e)) = c"
  "\<zeta> (Le  (CN 0 c e)) = c"
  "\<zeta> (Gt  (CN 0 c e)) = c"
  "\<zeta> (Ge  (CN 0 c e)) = c"
  "\<zeta> (Dvd i (CN 0 c e)) = c"
  "\<zeta> (NDvd i (CN 0 c e))= c"
  "\<zeta> p = 1"

consts \<beta> :: "fm \<Rightarrow> num list"
recdef \<beta> "measure size"
  "\<beta> (And p q) = (\<beta> p @ \<beta> q)"
  "\<beta> (Or p q) = (\<beta> p @ \<beta> q)"
  "\<beta> (Eq  (CN 0 c e)) = [Sub (C (- 1)) e]"
  "\<beta> (NEq (CN 0 c e)) = [Neg e]"
  "\<beta> (Lt  (CN 0 c e)) = []"
  "\<beta> (Le  (CN 0 c e)) = []"
  "\<beta> (Gt  (CN 0 c e)) = [Neg e]"
  "\<beta> (Ge  (CN 0 c e)) = [Sub (C (- 1)) e]"
  "\<beta> p = []"

consts \<alpha> :: "fm \<Rightarrow> num list"
recdef \<alpha> "measure size"
  "\<alpha> (And p q) = \<alpha> p @ \<alpha> q"
  "\<alpha> (Or p q) = \<alpha> p @ \<alpha> q"
  "\<alpha> (Eq  (CN 0 c e)) = [Add (C (- 1)) e]"
  "\<alpha> (NEq (CN 0 c e)) = [e]"
  "\<alpha> (Lt  (CN 0 c e)) = [e]"
  "\<alpha> (Le  (CN 0 c e)) = [Add (C (- 1)) e]"
  "\<alpha> (Gt  (CN 0 c e)) = []"
  "\<alpha> (Ge  (CN 0 c e)) = []"
  "\<alpha> p = []"

consts mirror :: "fm \<Rightarrow> fm"
recdef mirror "measure size"
  "mirror (And p q) = And (mirror p) (mirror q)"
  "mirror (Or p q) = Or (mirror p) (mirror q)"
  "mirror (Eq  (CN 0 c e)) = Eq (CN 0 c (Neg e))"
  "mirror (NEq (CN 0 c e)) = NEq (CN 0 c (Neg e))"
  "mirror (Lt  (CN 0 c e)) = Gt (CN 0 c (Neg e))"
  "mirror (Le  (CN 0 c e)) = Ge (CN 0 c (Neg e))"
  "mirror (Gt  (CN 0 c e)) = Lt (CN 0 c (Neg e))"
  "mirror (Ge  (CN 0 c e)) = Le (CN 0 c (Neg e))"
  "mirror (Dvd i (CN 0 c e)) = Dvd i (CN 0 c (Neg e))"
  "mirror (NDvd i (CN 0 c e)) = NDvd i (CN 0 c (Neg e))"
  "mirror p = p"

text \<open>Lemmas for the correctness of \<open>\<sigma>_\<rho>\<close>\<close>

lemma dvd1_eq1:
  fixes x :: int
  shows "x > 0 \<Longrightarrow> x dvd 1 \<longleftrightarrow> x = 1"
  by simp

lemma minusinf_inf:
  assumes linp: "iszlfm p"
    and u: "d_\<beta> p 1"
  shows "\<exists>z::int. \<forall>x < z. Ifm bbs (x # bs) (minusinf p) = Ifm bbs (x # bs) p"
  (is "?P p" is "\<exists>(z::int). \<forall>x < z. ?I x (?M p) = ?I x p")
  using linp u
proof (induct p rule: minusinf.induct)
  case (1 p q)
  then show ?case
    apply auto
    subgoal for z z' by (rule exI [where x = "min z z'"]) simp
    done
next
  case (2 p q)
  then show ?case
    apply auto
    subgoal for z z' by (rule exI [where x = "min z z'"]) simp
    done
next
  case (3 c e)
  then have c1: "c = 1" and nb: "numbound0 e"
    by simp_all
  fix a
  from 3 have "\<forall>x<(- Inum (a # bs) e). c * x + Inum (x # bs) e \<noteq> 0"
  proof clarsimp
    fix x
    assume "x < (- Inum (a # bs) e)" and "x + Inum (x # bs) e = 0"
    with numbound0_I[OF nb, where bs="bs" and b="a" and b'="x"]
    show False by simp
  qed
  then show ?case by auto
next
  case (4 c e)
  then have c1: "c = 1" and nb: "numbound0 e"
    by simp_all
  fix a
  from 4 have "\<forall>x < (- Inum (a # bs) e). c * x + Inum (x # bs) e \<noteq> 0"
  proof clarsimp
    fix x
    assume "x < (- Inum (a # bs) e)" and "x + Inum (x # bs) e = 0"
    with numbound0_I[OF nb, where bs="bs" and b="a" and b'="x"]
    show "False" by simp
  qed
  then show ?case by auto
next
  case (5 c e)
  then have c1: "c = 1" and nb: "numbound0 e"
    by simp_all
  fix a
  from 5 have "\<forall>x<(- Inum (a # bs) e). c * x + Inum (x # bs) e < 0"
  proof clarsimp
    fix x
    assume "x < (- Inum (a # bs) e)"
    with numbound0_I[OF nb, where bs="bs" and b="a" and b'="x"]
    show "x + Inum (x # bs) e < 0"
      by simp
  qed
  then show ?case by auto
next
  case (6 c e)
  then have c1: "c = 1" and nb: "numbound0 e"
    by simp_all
  fix a
  from 6 have "\<forall>x<(- Inum (a # bs) e). c * x + Inum (x # bs) e \<le> 0"
  proof clarsimp
    fix x
    assume "x < (- Inum (a # bs) e)"
    with numbound0_I[OF nb, where bs="bs" and b="a" and b'="x"]
    show "x + Inum (x # bs) e \<le> 0" by simp
  qed
  then show ?case by auto
next
  case (7 c e)
  then have c1: "c = 1" and nb: "numbound0 e"
    by simp_all
  fix a
  from 7 have "\<forall>x<(- Inum (a # bs) e). \<not> (c * x + Inum (x # bs) e > 0)"
  proof clarsimp
    fix x
    assume "x < - Inum (a # bs) e" and "x + Inum (x # bs) e > 0"
    with numbound0_I[OF nb, where bs="bs" and b="a" and b'="x"]
    show False by simp
  qed
  then show ?case by auto
next
  case (8 c e)
  then have c1: "c = 1" and nb: "numbound0 e"
    by simp_all
  fix a
  from 8 have "\<forall>x<(- Inum (a # bs) e). \<not> c * x + Inum (x # bs) e \<ge> 0"
  proof clarsimp
    fix x
    assume "x < (- Inum (a # bs) e)" and "x + Inum (x # bs) e \<ge> 0"
    with numbound0_I[OF nb, where bs="bs" and b="a" and b'="x"]
    show False by simp
  qed
  then show ?case by auto
qed auto

lemma minusinf_repeats:
  assumes d: "d_\<delta> p d"
    and linp: "iszlfm p"
  shows "Ifm bbs ((x - k * d) # bs) (minusinf p) = Ifm bbs (x # bs) (minusinf p)"
  using linp d
proof (induct p rule: iszlfm.induct)
  case (9 i c e)
  then have nbe: "numbound0 e" and id: "i dvd d"
    by simp_all
  then have "\<exists>k. d = i * k"
    by (simp add: dvd_def)
  then obtain "di" where di_def: "d = i * di"
    by blast
  show ?case
  proof (simp add: numbound0_I[OF nbe,where bs="bs" and b="x - k * d" and b'="x"] right_diff_distrib,
      rule iffI)
    assume "i dvd c * x - c * (k * d) + Inum (x # bs) e"
      (is "?ri dvd ?rc * ?rx - ?rc * (?rk * ?rd) + ?I x e" is "?ri dvd ?rt")
    then have "\<exists>l::int. ?rt = i * l"
      by (simp add: dvd_def)
    then have "\<exists>l::int. c * x + ?I x e = i * l + c * (k * i * di)"
      by (simp add: algebra_simps di_def)
    then have "\<exists>l::int. c * x + ?I x e = i* (l + c * k * di)"
      by (simp add: algebra_simps)
    then have "\<exists>l::int. c * x + ?I x e = i * l"
      by blast
    then show "i dvd c * x + Inum (x # bs) e"
      by (simp add: dvd_def)
  next
    assume "i dvd c * x + Inum (x # bs) e"  (is "?ri dvd ?rc * ?rx + ?e")
    then have "\<exists>l::int. c * x + ?e = i * l"
      by (simp add: dvd_def)
    then have "\<exists>l::int. c * x - c * (k * d) + ?e = i * l - c * (k * d)"
      by simp
    then have "\<exists>l::int. c * x - c * (k * d) + ?e = i * l - c * (k * i * di)"
      by (simp add: di_def)
    then have "\<exists>l::int. c * x - c * (k * d) + ?e = i * (l - c * k * di)"
      by (simp add: algebra_simps)
    then have "\<exists>l::int. c * x - c * (k * d) + ?e = i * l"
      by blast
    then show "i dvd c * x - c * (k * d) + Inum (x # bs) e"
      by (simp add: dvd_def)
  qed
next
  case (10 i c e)
  then have nbe: "numbound0 e" and id: "i dvd d"
    by simp_all
  then have "\<exists>k. d = i * k"
    by (simp add: dvd_def)
  then obtain di where di_def: "d = i * di"
    by blast
  show ?case
  proof (simp add: numbound0_I[OF nbe,where bs="bs" and b="x - k * d" and b'="x"] right_diff_distrib,
      rule iffI)
    assume "i dvd c * x - c * (k * d) + Inum (x # bs) e"
      (is "?ri dvd ?rc * ?rx - ?rc * (?rk * ?rd) + ?I x e" is "?ri dvd ?rt")
    then have "\<exists>l::int. ?rt = i * l"
      by (simp add: dvd_def)
    then have "\<exists>l::int. c * x + ?I x e = i * l + c * (k * i * di)"
      by (simp add: algebra_simps di_def)
    then have "\<exists>l::int. c * x+ ?I x e = i * (l + c * k * di)"
      by (simp add: algebra_simps)
    then have "\<exists>l::int. c * x + ?I x e = i * l"
      by blast
    then show "i dvd c * x + Inum (x # bs) e"
      by (simp add: dvd_def)
  next
    assume "i dvd c * x + Inum (x # bs) e" (is "?ri dvd ?rc * ?rx + ?e")
    then have "\<exists>l::int. c * x + ?e = i * l"
      by (simp add: dvd_def)
    then have "\<exists>l::int. c * x - c * (k * d) + ?e = i * l - c * (k * d)"
      by simp
    then have "\<exists>l::int. c * x - c * (k * d) + ?e = i * l - c * (k * i * di)"
      by (simp add: di_def)
    then have "\<exists>l::int. c * x - c * (k * d) + ?e = i * (l - c * k * di)"
      by (simp add: algebra_simps)
    then have "\<exists>l::int. c * x - c * (k * d) + ?e = i * l"
      by blast
    then show "i dvd c * x - c * (k * d) + Inum (x # bs) e"
      by (simp add: dvd_def)
  qed
qed (auto simp add: gr0_conv_Suc numbound0_I[where bs="bs" and b="x - k*d" and b'="x"])

lemma mirror_\<alpha>_\<beta>:
  assumes lp: "iszlfm p"
  shows "Inum (i # bs) ` set (\<alpha> p) = Inum (i # bs) ` set (\<beta> (mirror p))"
  using lp by (induct p rule: mirror.induct) auto

lemma mirror:
  assumes lp: "iszlfm p"
  shows "Ifm bbs (x # bs) (mirror p) = Ifm bbs ((- x) # bs) p"
  using lp
proof (induct p rule: iszlfm.induct)
  case (9 j c e)
  then have nb: "numbound0 e"
    by simp
  have "Ifm bbs (x # bs) (mirror (Dvd j (CN 0 c e))) \<longleftrightarrow> j dvd c * x - Inum (x # bs) e"
    (is "_ = (j dvd c*x - ?e)") by simp
  also have "\<dots> \<longleftrightarrow> j dvd (- (c * x - ?e))"
    by (simp only: dvd_minus_iff)
  also have "\<dots> \<longleftrightarrow> j dvd (c * (- x)) + ?e"
    by (simp only: minus_mult_right[symmetric] minus_mult_left[symmetric] ac_simps minus_add_distrib)
      (simp add: algebra_simps)
  also have "\<dots> = Ifm bbs ((- x) # bs) (Dvd j (CN 0 c e))"
    using numbound0_I[OF nb, where bs="bs" and b="x" and b'="- x"] by simp
  finally show ?case .
next
  case (10 j c e)
  then have nb: "numbound0 e"
    by simp
  have "Ifm bbs (x # bs) (mirror (Dvd j (CN 0 c e))) \<longleftrightarrow> j dvd c * x - Inum (x # bs) e"
    (is "_ = (j dvd c * x - ?e)") by simp
  also have "\<dots> \<longleftrightarrow> j dvd (- (c * x - ?e))"
    by (simp only: dvd_minus_iff)
  also have "\<dots> \<longleftrightarrow> j dvd (c * (- x)) + ?e"
    by (simp only: minus_mult_right[symmetric] minus_mult_left[symmetric] ac_simps minus_add_distrib)
      (simp add: algebra_simps)
  also have "\<dots> \<longleftrightarrow> Ifm bbs ((- x) # bs) (Dvd j (CN 0 c e))"
    using numbound0_I[OF nb, where bs="bs" and b="x" and b'="- x"] by simp
  finally show ?case by simp
qed (auto simp add: numbound0_I[where bs="bs" and b="x" and b'="- x"] gr0_conv_Suc)

lemma mirror_l: "iszlfm p \<and> d_\<beta> p 1 \<Longrightarrow> iszlfm (mirror p) \<and> d_\<beta> (mirror p) 1"
  by (induct p rule: mirror.induct) auto

lemma mirror_\<delta>: "iszlfm p \<Longrightarrow> \<delta> (mirror p) = \<delta> p"
  by (induct p rule: mirror.induct) auto

lemma \<beta>_numbound0:
  assumes lp: "iszlfm p"
  shows "\<forall>b \<in> set (\<beta> p). numbound0 b"
  using lp by (induct p rule: \<beta>.induct) auto

lemma d_\<beta>_mono:
  assumes linp: "iszlfm p"
    and dr: "d_\<beta> p l"
    and d: "l dvd l'"
  shows "d_\<beta> p l'"
  using dr linp dvd_trans[of _ "l" "l'", simplified d]
  by (induct p rule: iszlfm.induct) simp_all

lemma \<alpha>_l:
  assumes "iszlfm p"
  shows "\<forall>b \<in> set (\<alpha> p). numbound0 b"
  using assms by (induct p rule: \<alpha>.induct) auto

lemma \<zeta>:
  assumes "iszlfm p"
  shows "\<zeta> p > 0 \<and> d_\<beta> p (\<zeta> p)"
  using assms
proof (induct p rule: iszlfm.induct)
  case (1 p q)
  from 1 have dl1: "\<zeta> p dvd lcm (\<zeta> p) (\<zeta> q)"
    by simp
  from 1 have dl2: "\<zeta> q dvd lcm (\<zeta> p) (\<zeta> q)"
    by simp
  from 1 d_\<beta>_mono[where p = "p" and l="\<zeta> p" and l'="lcm (\<zeta> p) (\<zeta> q)"]
      d_\<beta>_mono[where p = "q" and l="\<zeta> q" and l'="lcm (\<zeta> p) (\<zeta> q)"]
      dl1 dl2
  show ?case
    by (auto simp add: lcm_pos_int)
next
  case (2 p q)
  from 2 have dl1: "\<zeta> p dvd lcm (\<zeta> p) (\<zeta> q)"
    by simp
  from 2 have dl2: "\<zeta> q dvd lcm (\<zeta> p) (\<zeta> q)"
    by simp
  from 2 d_\<beta>_mono[where p = "p" and l="\<zeta> p" and l'="lcm (\<zeta> p) (\<zeta> q)"]
      d_\<beta>_mono[where p = "q" and l="\<zeta> q" and l'="lcm (\<zeta> p) (\<zeta> q)"]
      dl1 dl2
  show ?case
    by (auto simp add: lcm_pos_int)
qed (auto simp add: lcm_pos_int)

lemma a_\<beta>:
  assumes linp: "iszlfm p"
    and d: "d_\<beta> p l"
    and lp: "l > 0"
  shows "iszlfm (a_\<beta> p l) \<and> d_\<beta> (a_\<beta> p l) 1 \<and> Ifm bbs (l * x # bs) (a_\<beta> p l) = Ifm bbs (x # bs) p"
  using linp d
proof (induct p rule: iszlfm.induct)
  case (5 c e)
  then have cp: "c > 0" and be: "numbound0 e" and d': "c dvd l"
    by simp_all
  from lp cp have clel: "c \<le> l"
    by (simp add: zdvd_imp_le [OF d' lp])
  from cp have cnz: "c \<noteq> 0"
    by simp
  have "c div c \<le> l div c"
    by (simp add: zdiv_mono1[OF clel cp])
  then have ldcp: "0 < l div c"
    by (simp add: div_self[OF cnz])
  have "c * (l div c) = c * (l div c) + l mod c"
    using d' dvd_eq_mod_eq_0[of "c" "l"] by simp
  then have cl: "c * (l div c) =l"
    using mult_div_mod_eq [where a="l" and b="c"] by simp
  then have "(l * x + (l div c) * Inum (x # bs) e < 0) \<longleftrightarrow>
      ((c * (l div c)) * x + (l div c) * Inum (x # bs) e < 0)"
    by simp
  also have "\<dots> \<longleftrightarrow> (l div c) * (c * x + Inum (x # bs) e) < (l div c) * 0"
    by (simp add: algebra_simps)
  also have "\<dots> \<longleftrightarrow> c * x + Inum (x # bs) e < 0"
    using mult_less_0_iff [where a="(l div c)" and b="c*x + Inum (x # bs) e"] ldcp
    by simp
  finally show ?case
    using numbound0_I[OF be,where b="l*x" and b'="x" and bs="bs"] be
    by simp
next
  case (6 c e)
  then have cp: "c > 0" and be: "numbound0 e" and d': "c dvd l"
    by simp_all
  from lp cp have clel: "c \<le> l"
    by (simp add: zdvd_imp_le [OF d' lp])
  from cp have cnz: "c \<noteq> 0"
    by simp
  have "c div c \<le> l div c"
    by (simp add: zdiv_mono1[OF clel cp])
  then have ldcp:"0 < l div c"
    by (simp add: div_self[OF cnz])
  have "c * (l div c) = c * (l div c) + l mod c"
    using d' dvd_eq_mod_eq_0[of "c" "l"] by simp
  then have cl: "c * (l div c) = l"
    using mult_div_mod_eq [where a="l" and b="c"] by simp
  then have "l * x + (l div c) * Inum (x # bs) e \<le> 0 \<longleftrightarrow>
      (c * (l div c)) * x + (l div c) * Inum (x # bs) e \<le> 0"
    by simp
  also have "\<dots> \<longleftrightarrow> (l div c) * (c * x + Inum (x # bs) e) \<le> (l div c) * 0"
    by (simp add: algebra_simps)
  also have "\<dots> \<longleftrightarrow> c * x + Inum (x # bs) e \<le> 0"
    using mult_le_0_iff [where a="(l div c)" and b="c*x + Inum (x # bs) e"] ldcp by simp
  finally show ?case
    using numbound0_I[OF be,where b="l*x" and b'="x" and bs="bs"] be by simp
next
  case (7 c e)
  then have cp: "c > 0" and be: "numbound0 e" and d': "c dvd l"
    by simp_all
  from lp cp have clel: "c \<le> l"
    by (simp add: zdvd_imp_le [OF d' lp])
  from cp have cnz: "c \<noteq> 0"
    by simp
  have "c div c \<le> l div c"
    by (simp add: zdiv_mono1[OF clel cp])
  then have ldcp: "0 < l div c"
    by (simp add: div_self[OF cnz])
  have "c * (l div c) = c * (l div c) + l mod c"
    using d' dvd_eq_mod_eq_0[of "c" "l"] by simp
  then have cl: "c * (l div c) = l"
    using mult_div_mod_eq [where a="l" and b="c"] by simp
  then have "l * x + (l div c) * Inum (x # bs) e > 0 \<longleftrightarrow>
      (c * (l div c)) * x + (l div c) * Inum (x # bs) e > 0"
    by simp
  also have "\<dots> \<longleftrightarrow> (l div c) * (c * x + Inum (x # bs) e) > (l div c) * 0"
    by (simp add: algebra_simps)
  also have "\<dots> \<longleftrightarrow> c * x + Inum (x # bs) e > 0"
    using zero_less_mult_iff [where a="(l div c)" and b="c * x + Inum (x # bs) e"] ldcp
    by simp
  finally show ?case
    using numbound0_I[OF be,where b="(l * x)" and b'="x" and bs="bs"] be
    by simp
next
  case (8 c e)
  then have cp: "c > 0" and be: "numbound0 e" and d': "c dvd l"
    by simp_all
  from lp cp have clel: "c \<le> l"
    by (simp add: zdvd_imp_le [OF d' lp])
  from cp have cnz: "c \<noteq> 0"
    by simp
  have "c div c \<le> l div c"
    by (simp add: zdiv_mono1[OF clel cp])
  then have ldcp: "0 < l div c"
    by (simp add: div_self[OF cnz])
  have "c * (l div c) = c * (l div c) + l mod c"
    using d' dvd_eq_mod_eq_0[of "c" "l"] by simp
  then have cl: "c * (l div c) =l"
    using mult_div_mod_eq [where a="l" and b="c"]
    by simp
  then have "l * x + (l div c) * Inum (x # bs) e \<ge> 0 \<longleftrightarrow>
      (c * (l div c)) * x + (l div c) * Inum (x # bs) e \<ge> 0"
    by simp
  also have "\<dots> \<longleftrightarrow> (l div c) * (c * x + Inum (x # bs) e) \<ge> (l div c) * 0"
    by (simp add: algebra_simps)
  also have "\<dots> \<longleftrightarrow> c * x + Inum (x # bs) e \<ge> 0"
    using ldcp zero_le_mult_iff [where a="l div c" and b="c*x + Inum (x # bs) e"]
    by simp
  finally show ?case
    using be numbound0_I[OF be,where b="l*x" and b'="x" and bs="bs"]
    by simp
next
  case (3 c e)
  then have cp: "c > 0" and be: "numbound0 e" and d': "c dvd l"
    by simp_all
  from lp cp have clel: "c \<le> l"
    by (simp add: zdvd_imp_le [OF d' lp])
  from cp have cnz: "c \<noteq> 0"
    by simp
  have "c div c \<le> l div c"
    by (simp add: zdiv_mono1[OF clel cp])
  then have ldcp:"0 < l div c"
    by (simp add: div_self[OF cnz])
  have "c * (l div c) = c * (l div c) + l mod c"
    using d' dvd_eq_mod_eq_0[of "c" "l"] by simp
  then have cl:"c * (l div c) =l" using mult_div_mod_eq [where a="l" and b="c"]
    by simp
  then have "l * x + (l div c) * Inum (x # bs) e = 0 \<longleftrightarrow>
      (c * (l div c)) * x + (l div c) * Inum (x # bs) e = 0"
    by simp
  also have "\<dots> \<longleftrightarrow> (l div c) * (c * x + Inum (x # bs) e) = ((l div c)) * 0"
    by (simp add: algebra_simps)
  also have "\<dots> \<longleftrightarrow> c * x + Inum (x # bs) e = 0"
    using mult_eq_0_iff [where a="(l div c)" and b="c * x + Inum (x # bs) e"] ldcp
    by simp
  finally show ?case
    using numbound0_I[OF be,where b="(l * x)" and b'="x" and bs="bs"] be
    by simp
next
  case (4 c e)
  then have cp: "c > 0" and be: "numbound0 e" and d': "c dvd l"
    by simp_all
  from lp cp have clel: "c \<le> l"
    by (simp add: zdvd_imp_le [OF d' lp])
  from cp have cnz: "c \<noteq> 0"
    by simp
  have "c div c \<le> l div c"
    by (simp add: zdiv_mono1[OF clel cp])
  then have ldcp:"0 < l div c"
    by (simp add: div_self[OF cnz])
  have "c * (l div c) = c * (l div c) + l mod c"
    using d' dvd_eq_mod_eq_0[of "c" "l"] by simp
  then have cl: "c * (l div c) = l"
    using mult_div_mod_eq [where a="l" and b="c"] by simp
  then have "l * x + (l div c) * Inum (x # bs) e \<noteq> 0 \<longleftrightarrow>
      (c * (l div c)) * x + (l div c) * Inum (x # bs) e \<noteq> 0"
    by simp
  also have "\<dots> \<longleftrightarrow> (l div c) * (c * x + Inum (x # bs) e) \<noteq> (l div c) * 0"
    by (simp add: algebra_simps)
  also have "\<dots> \<longleftrightarrow> c * x + Inum (x # bs) e \<noteq> 0"
    using zero_le_mult_iff [where a="(l div c)" and b="c * x + Inum (x # bs) e"] ldcp
    by simp
  finally show ?case
    using numbound0_I[OF be,where b="(l * x)" and b'="x" and bs="bs"] be
    by simp
next
  case (9 j c e)
  then have cp: "c > 0" and be: "numbound0 e" and jp: "j > 0" and d': "c dvd l"
    by simp_all
  from lp cp have clel: "c \<le> l"
    by (simp add: zdvd_imp_le [OF d' lp])
  from cp have cnz: "c \<noteq> 0" by simp
  have "c div c\<le> l div c"
    by (simp add: zdiv_mono1[OF clel cp])
  then have ldcp:"0 < l div c"
    by (simp add: div_self[OF cnz])
  have "c * (l div c) = c * (l div c) + l mod c"
    using d' dvd_eq_mod_eq_0[of "c" "l"] by simp
  then have cl: "c * (l div c) = l"
    using mult_div_mod_eq [where a="l" and b="c"] by simp
  then have "(\<exists>k::int. l * x + (l div c) * Inum (x # bs) e = ((l div c) * j) * k) \<longleftrightarrow>
      (\<exists>k::int. (c * (l div c)) * x + (l div c) * Inum (x # bs) e = ((l div c) * j) * k)"
    by simp
  also have "\<dots> \<longleftrightarrow> (\<exists>k::int. (l div c) * (c * x + Inum (x # bs) e - j * k) = (l div c) * 0)"
    by (simp add: algebra_simps)
  also have "\<dots> \<longleftrightarrow> (\<exists>k::int. c * x + Inum (x # bs) e - j * k = 0)"
    using zero_le_mult_iff [where a="(l div c)" and b="c * x + Inum (x # bs) e - j * k" for k] ldcp
    by simp
  also have "\<dots> \<longleftrightarrow> (\<exists>k::int. c * x + Inum (x # bs) e = j * k)"
    by simp
  finally show ?case
    using numbound0_I[OF be,where b="(l * x)" and b'="x" and bs="bs"]
      be mult_strict_mono[OF ldcp jp ldcp ]
    by (simp add: dvd_def)
next
  case (10 j c e)
  then have cp: "c > 0" and be: "numbound0 e" and jp: "j > 0" and d': "c dvd l"
    by simp_all
  from lp cp have clel: "c \<le> l"
    by (simp add: zdvd_imp_le [OF d' lp])
  from cp have cnz: "c \<noteq> 0"
    by simp
  have "c div c \<le> l div c"
    by (simp add: zdiv_mono1[OF clel cp])
  then have ldcp: "0 < l div c"
    by (simp add: div_self[OF cnz])
  have "c * (l div c) = c* (l div c) + l mod c"
    using d' dvd_eq_mod_eq_0[of "c" "l"] by simp
  then have cl:"c * (l div c) =l"
    using mult_div_mod_eq [where a="l" and b="c"]
    by simp
  then have "(\<exists>k::int. l * x + (l div c) * Inum (x # bs) e = ((l div c) * j) * k) \<longleftrightarrow>
      (\<exists>k::int. (c * (l div c)) * x + (l div c) * Inum (x # bs) e = ((l div c) * j) * k)"
    by simp
  also have "\<dots> \<longleftrightarrow> (\<exists>k::int. (l div c) * (c * x + Inum (x # bs) e - j * k) = (l div c) * 0)"
    by (simp add: algebra_simps)
  also have "\<dots> \<longleftrightarrow> (\<exists>k::int. c * x + Inum (x # bs) e - j * k = 0)"
    using zero_le_mult_iff [where a="(l div c)" and b="c * x + Inum (x # bs) e - j * k" for k] ldcp
    by simp
  also have "\<dots> \<longleftrightarrow> (\<exists>k::int. c * x + Inum (x # bs) e = j * k)"
    by simp
  finally show ?case
    using numbound0_I[OF be,where b="(l * x)" and b'="x" and bs="bs"] be
      mult_strict_mono[OF ldcp jp ldcp ]
    by (simp add: dvd_def)
qed (auto simp add: gr0_conv_Suc numbound0_I[where bs="bs" and b="(l * x)" and b'="x"])

lemma a_\<beta>_ex:
  assumes linp: "iszlfm p"
    and d: "d_\<beta> p l"
    and lp: "l > 0"
  shows "(\<exists>x. l dvd x \<and> Ifm bbs (x #bs) (a_\<beta> p l)) \<longleftrightarrow> (\<exists>x::int. Ifm bbs (x#bs) p)"
  (is "(\<exists>x. l dvd x \<and> ?P x) \<longleftrightarrow> (\<exists>x. ?P' x)")
proof-
  have "(\<exists>x. l dvd x \<and> ?P x) \<longleftrightarrow> (\<exists>x::int. ?P (l * x))"
    using unity_coeff_ex[where l="l" and P="?P", simplified] by simp
  also have "\<dots> = (\<exists>x::int. ?P' x)"
    using a_\<beta>[OF linp d lp] by simp
  finally show ?thesis  .
qed

lemma \<beta>:
  assumes "iszlfm p"
    and "d_\<beta> p 1"
    and "d_\<delta> p d"
    and dp: "d > 0"
    and "\<not> (\<exists>j::int \<in> {1 .. d}. \<exists>b \<in> Inum (a # bs) ` set (\<beta> p). x = b + j)"
    and p: "Ifm bbs (x # bs) p" (is "?P x")
  shows "?P (x - d)"
  using assms
proof (induct p rule: iszlfm.induct)
  case (5 c e)
  then have c1: "c = 1" and  bn: "numbound0 e"
    by simp_all
  with dp p c1 numbound0_I[OF bn,where b = "(x - d)" and b' = "x" and bs = "bs"] 5
  show ?case by simp
next
  case (6 c e)
  then have c1: "c = 1" and  bn: "numbound0 e"
    by simp_all
  with dp p c1 numbound0_I[OF bn,where b="(x-d)" and b'="x" and bs="bs"] 6
  show ?case by simp
next
  case (7 c e)
  then have p: "Ifm bbs (x # bs) (Gt (CN 0 c e))" and c1: "c=1" and bn: "numbound0 e"
    by simp_all
  let ?e = "Inum (x # bs) e"
  show ?case
  proof (cases "(x - d) + ?e > 0")
    case True
    then show ?thesis
      using c1 numbound0_I[OF bn,where b="(x-d)" and b'="x" and bs="bs"] by simp
  next
    case False
    let ?v = "Neg e"
    have vb: "?v \<in> set (\<beta> (Gt (CN 0 c e)))"
      by simp
    from 7(5)[simplified simp_thms Inum.simps \<beta>.simps list.set bex_simps numbound0_I[OF bn,where b="a" and b'="x" and bs="bs"]]
    have nob: "\<not> (\<exists>j\<in> {1 ..d}. x = - ?e + j)"
      by auto
    from False p have "x + ?e > 0 \<and> x + ?e \<le> d"
      by (simp add: c1)
    then have "x + ?e \<ge> 1 \<and> x + ?e \<le> d"
      by simp
    then have "\<exists>j::int \<in> {1 .. d}. j = x + ?e"
      by simp
    then have "\<exists>j::int \<in> {1 .. d}. x = (- ?e + j)"
      by (simp add: algebra_simps)
    with nob show ?thesis
      by auto
  qed
next
  case (8 c e)
  then have p: "Ifm bbs (x # bs) (Ge (CN 0 c e))" and c1: "c = 1" and bn: "numbound0 e"
    by simp_all
  let ?e = "Inum (x # bs) e"
  show ?case
  proof (cases "(x - d) + ?e \<ge> 0")
    case True
    then show ?thesis
      using c1 numbound0_I[OF bn,where b="(x-d)" and b'="x" and bs="bs"]
      by simp
  next
    case False
    let ?v = "Sub (C (- 1)) e"
    have vb: "?v \<in> set (\<beta> (Ge (CN 0 c e)))"
      by simp
    from 8(5)[simplified simp_thms Inum.simps \<beta>.simps list.set bex_simps numbound0_I[OF bn,where b="a" and b'="x" and bs="bs"]]
    have nob: "\<not> (\<exists>j\<in> {1 ..d}. x =  - ?e - 1 + j)"
      by auto
    from False p have "x + ?e \<ge> 0 \<and> x + ?e < d"
      by (simp add: c1)
    then have "x + ?e +1 \<ge> 1 \<and> x + ?e + 1 \<le> d"
      by simp
    then have "\<exists>j::int \<in> {1 .. d}. j = x + ?e + 1"
      by simp
    then have "\<exists>j::int \<in> {1 .. d}. x= - ?e - 1 + j"
      by (simp add: algebra_simps)
    with nob show ?thesis
      by simp
  qed
next
  case (3 c e)
  then
  have p: "Ifm bbs (x #bs) (Eq (CN 0 c e))" (is "?p x")
    and c1: "c = 1"
    and bn: "numbound0 e"
    by simp_all
  let ?e = "Inum (x # bs) e"
  let ?v="(Sub (C (- 1)) e)"
  have vb: "?v \<in> set (\<beta> (Eq (CN 0 c e)))"
    by simp
  from p have "x= - ?e"
    by (simp add: c1) with 3(5)
  show ?case
    using dp apply simp
    apply (erule ballE[where x="1"])
    apply (simp_all add:algebra_simps numbound0_I[OF bn,where b="x"and b'="a"and bs="bs"])
    done
next
  case (4 c e)
  then
  have p: "Ifm bbs (x # bs) (NEq (CN 0 c e))" (is "?p x")
    and c1: "c = 1"
    and bn: "numbound0 e"
    by simp_all
  let ?e = "Inum (x # bs) e"
  let ?v="Neg e"
  have vb: "?v \<in> set (\<beta> (NEq (CN 0 c e)))"
    by simp
  show ?case
  proof (cases "x - d + Inum ((x - d) # bs) e = 0")
    case False
    then show ?thesis by (simp add: c1)
  next
    case True
    then have "x = - Inum ((x - d) # bs) e + d"
      by simp
    then have "x = - Inum (a # bs) e + d"
      by (simp add: numbound0_I[OF bn,where b="x - d"and b'="a"and bs="bs"])
     with 4(5) show ?thesis
      using dp by simp
  qed
next
  case (9 j c e)
  then
  have p: "Ifm bbs (x # bs) (Dvd j (CN 0 c e))" (is "?p x")
    and c1: "c = 1"
    and bn: "numbound0 e"
    by simp_all
  let ?e = "Inum (x # bs) e"
  from 9 have id: "j dvd d"
    by simp
  from c1 have "?p x \<longleftrightarrow> j dvd (x + ?e)"
    by simp
  also have "\<dots> \<longleftrightarrow> j dvd x - d + ?e"
    using zdvd_period[OF id, where x="x" and c="-1" and t="?e"]
    by simp
  finally show ?case
    using numbound0_I[OF bn,where b="(x-d)" and b'="x" and bs="bs"] c1 p
    by simp
next
  case (10 j c e)
  then
  have p: "Ifm bbs (x # bs) (NDvd j (CN 0 c e))" (is "?p x")
    and c1: "c = 1"
    and bn: "numbound0 e"
    by simp_all
  let ?e = "Inum (x # bs) e"
  from 10 have id: "j dvd d"
    by simp
  from c1 have "?p x \<longleftrightarrow> \<not> j dvd (x + ?e)"
    by simp
  also have "\<dots> \<longleftrightarrow> \<not> j dvd x - d + ?e"
    using zdvd_period[OF id, where x="x" and c="-1" and t="?e"]
    by simp
  finally show ?case
    using numbound0_I[OF bn,where b="(x-d)" and b'="x" and bs="bs"] c1 p
    by simp
qed (auto simp add: numbound0_I[where bs="bs" and b="(x - d)" and b'="x"] gr0_conv_Suc)

lemma \<beta>':
  assumes lp: "iszlfm p"
    and u: "d_\<beta> p 1"
    and d: "d_\<delta> p d"
    and dp: "d > 0"
  shows "\<forall>x. \<not> (\<exists>j::int \<in> {1 .. d}. \<exists>b \<in> set(\<beta> p). Ifm bbs ((Inum (a#bs) b + j) #bs) p) \<longrightarrow>
    Ifm bbs (x # bs) p \<longrightarrow> Ifm bbs ((x - d) # bs) p" (is "\<forall>x. ?b \<longrightarrow> ?P x \<longrightarrow> ?P (x - d)")
proof clarify
  fix x
  assume nb: "?b" and px: "?P x"
  then have nb2: "\<not> (\<exists>j::int \<in> {1 .. d}. \<exists>b \<in> Inum (a # bs) ` set (\<beta> p). x = b + j)"
    by auto
  show "?P (x - d)" by (rule \<beta>[OF lp u d dp nb2 px])
qed

lemma cpmi_eq:
  fixes P P1 :: "int \<Rightarrow> bool"
  assumes "0 < D"
    and "\<exists>z. \<forall>x. x < z \<longrightarrow> P x = P1 x"
    and "\<forall>x. \<not> (\<exists>j \<in> {1..D}. \<exists>b \<in> B. P (b + j)) \<longrightarrow> P x \<longrightarrow> P (x - D)"
    and "\<forall>x k. P1 x = P1 (x - k * D)"
  shows "(\<exists>x. P x) \<longleftrightarrow> (\<exists>j \<in> {1..D}. P1 j) \<or> (\<exists>j \<in> {1..D}. \<exists>b \<in> B. P (b + j))"
  apply (insert assms)
  apply (rule iffI)
  prefer 2
  apply (drule minusinfinity)
  apply assumption+
  apply fastforce
  apply clarsimp
  apply (subgoal_tac "\<And>k. 0 \<le> k \<Longrightarrow> \<forall>x. P x \<longrightarrow> P (x - k * D)")
  apply (frule_tac x = x and z=z in decr_lemma)
  apply (subgoal_tac "P1 (x - (\<bar>x - z\<bar> + 1) * D)")
  prefer 2
  apply (subgoal_tac "0 \<le> \<bar>x - z\<bar> + 1")
  prefer 2 apply arith
   apply fastforce
  apply (drule (1)  periodic_finite_ex)
  apply blast
  apply (blast dest: decr_mult_lemma)
  done

theorem cp_thm:
  assumes lp: "iszlfm p"
    and u: "d_\<beta> p 1"
    and d: "d_\<delta> p d"
    and dp: "d > 0"
  shows "(\<exists>x. Ifm bbs (x # bs) p) \<longleftrightarrow>
    (\<exists>j \<in> {1.. d}. Ifm bbs (j # bs) (minusinf p) \<or>
      (\<exists>b \<in> set (\<beta> p). Ifm bbs ((Inum (i # bs) b + j) # bs) p))"
  (is "(\<exists>x. ?P x) \<longleftrightarrow> (\<exists>j \<in> ?D. ?M j \<or> (\<exists>b \<in> ?B. ?P (?I b + j)))")
proof -
  from minusinf_inf[OF lp u]
  have th: "\<exists>z. \<forall>x<z. ?P x = ?M x"
    by blast
  let ?B' = "{?I b | b. b \<in> ?B}"
  have BB': "(\<exists>j\<in>?D. \<exists>b \<in> ?B. ?P (?I b + j)) \<longleftrightarrow> (\<exists>j \<in> ?D. \<exists>b \<in> ?B'. ?P (b + j))"
    by auto
  then have th2: "\<forall>x. \<not> (\<exists>j \<in> ?D. \<exists>b \<in> ?B'. ?P (b + j)) \<longrightarrow> ?P x \<longrightarrow> ?P (x - d)"
    using \<beta>'[OF lp u d dp, where a="i" and bbs = "bbs"] by blast
  from minusinf_repeats[OF d lp]
  have th3: "\<forall>x k. ?M x = ?M (x-k*d)"
    by simp
  from cpmi_eq[OF dp th th2 th3] BB' show ?thesis
    by blast
qed

(* Implement the right hand sides of Cooper's theorem and Ferrante and Rackoff. *)
lemma mirror_ex:
  assumes "iszlfm p"
  shows "(\<exists>x. Ifm bbs (x#bs) (mirror p)) \<longleftrightarrow> (\<exists>x. Ifm bbs (x#bs) p)"
  (is "(\<exists>x. ?I x ?mp) = (\<exists>x. ?I x p)")
proof auto
  fix x
  assume "?I x ?mp"
  then have "?I (- x) p"
    using mirror[OF assms] by blast
  then show "\<exists>x. ?I x p"
    by blast
next
  fix x
  assume "?I x p"
  then have "?I (- x) ?mp"
    using mirror[OF assms, where x="- x", symmetric] by auto
  then show "\<exists>x. ?I x ?mp"
    by blast
qed

lemma cp_thm':
  assumes "iszlfm p"
    and "d_\<beta> p 1"
    and "d_\<delta> p d"
    and "d > 0"
  shows "(\<exists>x. Ifm bbs (x # bs) p) \<longleftrightarrow>
    ((\<exists>j\<in> {1 .. d}. Ifm bbs (j#bs) (minusinf p)) \<or>
      (\<exists>j\<in> {1.. d}. \<exists>b\<in> (Inum (i#bs)) ` set (\<beta> p). Ifm bbs ((b + j) # bs) p))"
  using cp_thm[OF assms,where i="i"] by auto

definition unit :: "fm \<Rightarrow> fm \<times> num list \<times> int"
where
  "unit p =
     (let
        p' = zlfm p;
        l = \<zeta> p';
        q = And (Dvd l (CN 0 1 (C 0))) (a_\<beta> p' l);
        d = \<delta> q;
        B = remdups (map simpnum (\<beta> q));
        a = remdups (map simpnum (\<alpha> q))
      in if length B \<le> length a then (q, B, d) else (mirror q, a, d))"

lemma unit:
  assumes qf: "qfree p"
  fixes q B d
  assumes qBd: "unit p = (q, B, d)"
  shows "((\<exists>x. Ifm bbs (x # bs) p) \<longleftrightarrow> (\<exists>x. Ifm bbs (x # bs) q)) \<and>
    (Inum (i # bs)) ` set B = (Inum (i # bs)) ` set (\<beta> q) \<and> d_\<beta> q 1 \<and> d_\<delta> q d \<and> d > 0 \<and>
    iszlfm q \<and> (\<forall>b\<in> set B. numbound0 b)"
proof -
  let ?I = "\<lambda>x p. Ifm bbs (x#bs) p"
  let ?p' = "zlfm p"
  let ?l = "\<zeta> ?p'"
  let ?q = "And (Dvd ?l (CN 0 1 (C 0))) (a_\<beta> ?p' ?l)"
  let ?d = "\<delta> ?q"
  let ?B = "set (\<beta> ?q)"
  let ?B'= "remdups (map simpnum (\<beta> ?q))"
  let ?A = "set (\<alpha> ?q)"
  let ?A'= "remdups (map simpnum (\<alpha> ?q))"
  from conjunct1[OF zlfm_I[OF qf, where bs="bs"]]
  have pp': "\<forall>i. ?I i ?p' = ?I i p" by auto
  from conjunct2[OF zlfm_I[OF qf, where bs="bs" and i="i"]]
  have lp': "iszlfm ?p'" .
  from lp' \<zeta>[where p="?p'"] have lp: "?l >0" and dl: "d_\<beta> ?p' ?l" by auto
  from a_\<beta>_ex[where p="?p'" and l="?l" and bs="bs", OF lp' dl lp] pp'
  have pq_ex:"(\<exists>(x::int). ?I x p) = (\<exists>x. ?I x ?q)" by simp
  from lp' lp a_\<beta>[OF lp' dl lp] have lq:"iszlfm ?q" and uq: "d_\<beta> ?q 1"  by auto
  from \<delta>[OF lq] have dp:"?d >0" and dd: "d_\<delta> ?q ?d" by blast+
  let ?N = "\<lambda>t. Inum (i#bs) t"
  have "?N ` set ?B' = ((?N \<circ> simpnum) ` ?B)"
    by auto
  also have "\<dots> = ?N ` ?B"
    using simpnum_ci[where bs="i#bs"] by auto
  finally have BB': "?N ` set ?B' = ?N ` ?B" .
  have "?N ` set ?A' = ((?N \<circ> simpnum) ` ?A)"
    by auto
  also have "\<dots> = ?N ` ?A"
    using simpnum_ci[where bs="i#bs"] by auto
  finally have AA': "?N ` set ?A' = ?N ` ?A" .
  from \<beta>_numbound0[OF lq] have B_nb:"\<forall>b\<in> set ?B'. numbound0 b"
    by (simp add: simpnum_numbound0)
  from \<alpha>_l[OF lq] have A_nb: "\<forall>b\<in> set ?A'. numbound0 b"
    by (simp add: simpnum_numbound0)
  show ?thesis
  proof (cases "length ?B' \<le> length ?A'")
    case True
    then have q: "q = ?q" and "B = ?B'" and d: "d = ?d"
      using qBd by (auto simp add: Let_def unit_def)
    with BB' B_nb
    have b: "?N ` (set B) = ?N ` set (\<beta> q)" and bn: "\<forall>b\<in> set B. numbound0 b"
      by simp_all
    with pq_ex dp uq dd lq q d show ?thesis
      by simp
  next
    case False
    then have q:"q=mirror ?q" and "B = ?A'" and d:"d = ?d"
      using qBd by (auto simp add: Let_def unit_def)
    with AA' mirror_\<alpha>_\<beta>[OF lq] A_nb have b:"?N ` (set B) = ?N ` set (\<beta> q)"
      and bn: "\<forall>b\<in> set B. numbound0 b" by simp_all
    from mirror_ex[OF lq] pq_ex q
    have pqm_eq:"(\<exists>(x::int). ?I x p) = (\<exists>(x::int). ?I x q)"
      by simp
    from lq uq q mirror_l[where p="?q"]
    have lq': "iszlfm q" and uq: "d_\<beta> q 1"
      by auto
    from \<delta>[OF lq'] mirror_\<delta>[OF lq] q d have dq: "d_\<delta> q d"
      by auto
    from pqm_eq b bn uq lq' dp dq q dp d show ?thesis
      by simp
  qed
qed


text \<open>Cooper's Algorithm\<close>

definition cooper :: "fm \<Rightarrow> fm"
where
  "cooper p =
    (let
      (q, B, d) = unit p;
      js = [1..d];
      mq = simpfm (minusinf q);
      md = evaldjf (\<lambda>j. simpfm (subst0 (C j) mq)) js
     in
      if md = T then T
      else
        (let
          qd = evaldjf (\<lambda>(b, j). simpfm (subst0 (Add b (C j)) q)) [(b, j). b \<leftarrow> B, j \<leftarrow> js]
         in decr (disj md qd)))"

lemma cooper:
  assumes qf: "qfree p"
  shows "(\<exists>x. Ifm bbs (x#bs) p) = Ifm bbs bs (cooper p) \<and> qfree (cooper p)"
    (is "?lhs = ?rhs \<and> _")
proof -
  let ?I = "\<lambda>x p. Ifm bbs (x#bs) p"
  let ?q = "fst (unit p)"
  let ?B = "fst (snd(unit p))"
  let ?d = "snd (snd (unit p))"
  let ?js = "[1..?d]"
  let ?mq = "minusinf ?q"
  let ?smq = "simpfm ?mq"
  let ?md = "evaldjf (\<lambda>j. simpfm (subst0 (C j) ?smq)) ?js"
  fix i
  let ?N = "\<lambda>t. Inum (i#bs) t"
  let ?Bjs = "[(b,j). b\<leftarrow>?B,j\<leftarrow>?js]"
  let ?qd = "evaldjf (\<lambda>(b,j). simpfm (subst0 (Add b (C j)) ?q)) ?Bjs"
  have qbf:"unit p = (?q,?B,?d)" by simp
  from unit[OF qf qbf]
  have pq_ex: "(\<exists>(x::int). ?I x p) \<longleftrightarrow> (\<exists>(x::int). ?I x ?q)"
    and B: "?N ` set ?B = ?N ` set (\<beta> ?q)"
    and uq: "d_\<beta> ?q 1"
    and dd: "d_\<delta> ?q ?d"
    and dp: "?d > 0"
    and lq: "iszlfm ?q"
    and Bn: "\<forall>b\<in> set ?B. numbound0 b"
    by auto
  from zlin_qfree[OF lq] have qfq: "qfree ?q" .
  from simpfm_qf[OF minusinf_qfree[OF qfq]] have qfmq: "qfree ?smq" .
  have jsnb: "\<forall>j \<in> set ?js. numbound0 (C j)"
    by simp
  then have "\<forall>j\<in> set ?js. bound0 (subst0 (C j) ?smq)"
    by (auto simp only: subst0_bound0[OF qfmq])
  then have th: "\<forall>j\<in> set ?js. bound0 (simpfm (subst0 (C j) ?smq))"
    by (auto simp add: simpfm_bound0)
  from evaldjf_bound0[OF th] have mdb: "bound0 ?md"
    by simp
  from Bn jsnb have "\<forall>(b,j) \<in> set ?Bjs. numbound0 (Add b (C j))"
    by simp
  then have "\<forall>(b,j) \<in> set ?Bjs. bound0 (subst0 (Add b (C j)) ?q)"
    using subst0_bound0[OF qfq] by blast
  then have "\<forall>(b,j) \<in> set ?Bjs. bound0 (simpfm (subst0 (Add b (C j)) ?q))"
    using simpfm_bound0 by blast
  then have th': "\<forall>x \<in> set ?Bjs. bound0 ((\<lambda>(b,j). simpfm (subst0 (Add b (C j)) ?q)) x)"
    by auto
  from evaldjf_bound0 [OF th'] have qdb: "bound0 ?qd"
    by simp
  from mdb qdb have mdqdb: "bound0 (disj ?md ?qd)"
    unfolding disj_def by (cases "?md = T \<or> ?qd = T") simp_all
  from trans [OF pq_ex cp_thm'[OF lq uq dd dp,where i="i"]] B
  have "?lhs \<longleftrightarrow> (\<exists>j \<in> {1.. ?d}. ?I j ?mq \<or> (\<exists>b \<in> ?N ` set ?B. Ifm bbs ((b + j) # bs) ?q))"
    by auto
  also have "\<dots> \<longleftrightarrow> (\<exists>j \<in> {1.. ?d}. ?I j ?mq \<or> (\<exists>b \<in> set ?B. Ifm bbs ((?N b + j) # bs) ?q))"
    by simp
  also have "\<dots> \<longleftrightarrow> (\<exists>j \<in> {1.. ?d}. ?I j ?mq ) \<or>
      (\<exists>j\<in> {1.. ?d}. \<exists>b \<in> set ?B. Ifm bbs ((?N (Add b (C j))) # bs) ?q)"
    by (simp only: Inum.simps) blast
  also have "\<dots> \<longleftrightarrow> (\<exists>j \<in> {1.. ?d}. ?I j ?smq) \<or>
      (\<exists>j \<in> {1.. ?d}. \<exists>b \<in> set ?B. Ifm bbs ((?N (Add b (C j))) # bs) ?q)"
    by (simp add: simpfm)
  also have "\<dots> \<longleftrightarrow> (\<exists>j\<in> set ?js. (\<lambda>j. ?I i (simpfm (subst0 (C j) ?smq))) j) \<or>
      (\<exists>j\<in> set ?js. \<exists>b\<in> set ?B. Ifm bbs ((?N (Add b (C j)))#bs) ?q)"
    by (simp only: simpfm subst0_I[OF qfmq] set_upto) auto
  also have "\<dots> \<longleftrightarrow> ?I i (evaldjf (\<lambda>j. simpfm (subst0 (C j) ?smq)) ?js) \<or>
      (\<exists>j\<in> set ?js. \<exists>b\<in> set ?B. ?I i (subst0 (Add b (C j)) ?q))"
    by (simp only: evaldjf_ex subst0_I[OF qfq])
  also have "\<dots> \<longleftrightarrow> ?I i ?md \<or>
      (\<exists>(b,j) \<in> set ?Bjs. (\<lambda>(b,j). ?I i (simpfm (subst0 (Add b (C j)) ?q))) (b,j))"
    by (simp only: simpfm set_concat set_map concat_map_singleton UN_simps) blast
  also have "\<dots> \<longleftrightarrow> ?I i ?md \<or> ?I i (evaldjf (\<lambda>(b,j). simpfm (subst0 (Add b (C j)) ?q)) ?Bjs)"
    by (simp only: evaldjf_ex[where bs="i#bs" and f="\<lambda>(b,j). simpfm (subst0 (Add b (C j)) ?q)" and ps="?Bjs"])
      (auto simp add: split_def)
  finally have mdqd: "?lhs \<longleftrightarrow> ?I i ?md \<or> ?I i ?qd"
    by simp
  also have "\<dots> \<longleftrightarrow> ?I i (disj ?md ?qd)"
    by (simp add: disj)
  also have "\<dots> \<longleftrightarrow> Ifm bbs bs (decr (disj ?md ?qd))"
    by (simp only: decr [OF mdqdb])
  finally have mdqd2: "?lhs \<longleftrightarrow> Ifm bbs bs (decr (disj ?md ?qd))" .
  show ?thesis
  proof (cases "?md = T")
    case True
    then have cT: "cooper p = T"
      by (simp only: cooper_def unit_def split_def Let_def if_True) simp
    from True have lhs: "?lhs"
      using mdqd by simp
    from True have "?rhs"
      by (simp add: cooper_def unit_def split_def)
    with lhs cT show ?thesis
      by simp
  next
    case False
    then have "cooper p = decr (disj ?md ?qd)"
      by (simp only: cooper_def unit_def split_def Let_def if_False)
    with mdqd2 decr_qf[OF mdqdb] show ?thesis
      by simp
  qed
qed

definition pa :: "fm \<Rightarrow> fm"
  where "pa p = qelim (prep p) cooper"

theorem mirqe: "Ifm bbs bs (pa p) = Ifm bbs bs p \<and> qfree (pa p)"
  using qelim_ci cooper prep by (auto simp add: pa_def)

definition cooper_test :: "unit \<Rightarrow> fm"
  where
    "cooper_test u =
      pa (E (A (Imp (Ge (Sub (Bound 0) (Bound 1)))
        (E (E (Eq (Sub (Add (Mul 3 (Bound 1)) (Mul 5 (Bound 0))) (Bound 2))))))))"

ML_val \<open>@{code cooper_test} ()\<close>

(*code_reflect Cooper_Procedure
  functions pa T Bound nat_of_integer integer_of_nat int_of_integer integer_of_int
  file "~~/src/HOL/Tools/Qelim/cooper_procedure.ML"*)

oracle linzqe_oracle = \<open>
let

fun num_of_term vs (t as Free (xn, xT)) =
      (case AList.lookup (op =) vs t of
        NONE => error "Variable not found in the list!"
      | SOME n => @{code Bound} (@{code nat_of_integer} n))
  | num_of_term vs @{term "0::int"} = @{code C} (@{code int_of_integer} 0)
  | num_of_term vs @{term "1::int"} = @{code C} (@{code int_of_integer} 1)
  | num_of_term vs @{term "- 1::int"} = @{code C} (@{code int_of_integer} (~ 1))
  | num_of_term vs (@{term "numeral :: _ \<Rightarrow> int"} $ t) =
      @{code C} (@{code int_of_integer} (HOLogic.dest_numeral t))
  | num_of_term vs (@{term "- numeral :: _ \<Rightarrow> int"} $ t) =
      @{code C} (@{code int_of_integer} (~(HOLogic.dest_numeral t)))
  | num_of_term vs (Bound i) = @{code Bound} (@{code nat_of_integer} i)
  | num_of_term vs (@{term "uminus :: int \<Rightarrow> int"} $ t') = @{code Neg} (num_of_term vs t')
  | num_of_term vs (@{term "op + :: int \<Rightarrow> int \<Rightarrow> int"} $ t1 $ t2) =
      @{code Add} (num_of_term vs t1, num_of_term vs t2)
  | num_of_term vs (@{term "op - :: int \<Rightarrow> int \<Rightarrow> int"} $ t1 $ t2) =
      @{code Sub} (num_of_term vs t1, num_of_term vs t2)
  | num_of_term vs (@{term "op * :: int \<Rightarrow> int \<Rightarrow> int"} $ t1 $ t2) =
      (case try HOLogic.dest_number t1 of
        SOME (_, i) => @{code Mul} (@{code int_of_integer} i, num_of_term vs t2)
      | NONE =>
          (case try HOLogic.dest_number t2 of
            SOME (_, i) => @{code Mul} (@{code int_of_integer} i, num_of_term vs t1)
          | NONE => error "num_of_term: unsupported multiplication"))
  | num_of_term vs t = error ("num_of_term: unknown term " ^ Syntax.string_of_term @{context} t);

fun fm_of_term ps vs @{term True} = @{code T}
  | fm_of_term ps vs @{term False} = @{code F}
  | fm_of_term ps vs (@{term "op < :: int \<Rightarrow> int \<Rightarrow> bool"} $ t1 $ t2) =
      @{code Lt} (@{code Sub} (num_of_term vs t1, num_of_term vs t2))
  | fm_of_term ps vs (@{term "op \<le> :: int \<Rightarrow> int \<Rightarrow> bool"} $ t1 $ t2) =
      @{code Le} (@{code Sub} (num_of_term vs t1, num_of_term vs t2))
  | fm_of_term ps vs (@{term "op = :: int \<Rightarrow> int \<Rightarrow> bool"} $ t1 $ t2) =
      @{code Eq} (@{code Sub} (num_of_term vs t1, num_of_term vs t2))
  | fm_of_term ps vs (@{term "op dvd :: int \<Rightarrow> int \<Rightarrow> bool"} $ t1 $ t2) =
      (case try HOLogic.dest_number t1 of
        SOME (_, i) => @{code Dvd} (@{code int_of_integer} i, num_of_term vs t2)
      | NONE => error "num_of_term: unsupported dvd")
  | fm_of_term ps vs (@{term "op = :: bool \<Rightarrow> bool \<Rightarrow> bool"} $ t1 $ t2) =
      @{code Iff} (fm_of_term ps vs t1, fm_of_term ps vs t2)
  | fm_of_term ps vs (@{term HOL.conj} $ t1 $ t2) =
      @{code And} (fm_of_term ps vs t1, fm_of_term ps vs t2)
  | fm_of_term ps vs (@{term HOL.disj} $ t1 $ t2) =
      @{code Or} (fm_of_term ps vs t1, fm_of_term ps vs t2)
  | fm_of_term ps vs (@{term HOL.implies} $ t1 $ t2) =
      @{code Imp} (fm_of_term ps vs t1, fm_of_term ps vs t2)
  | fm_of_term ps vs (@{term "Not"} $ t') =
      @{code NOT} (fm_of_term ps vs t')
  | fm_of_term ps vs (Const (@{const_name Ex}, _) $ Abs (xn, xT, p)) =
      let
        val (xn', p') = Syntax_Trans.variant_abs (xn, xT, p);  (* FIXME !? *)
        val vs' = (Free (xn', xT), 0) :: map (fn (v, n) => (v, n + 1)) vs;
      in @{code E} (fm_of_term ps vs' p) end
  | fm_of_term ps vs (Const (@{const_name All}, _) $ Abs (xn, xT, p)) =
      let
        val (xn', p') = Syntax_Trans.variant_abs (xn, xT, p);  (* FIXME !? *)
        val vs' = (Free (xn', xT), 0) :: map (fn (v, n) => (v, n + 1)) vs;
      in @{code A} (fm_of_term ps vs' p) end
  | fm_of_term ps vs t = error ("fm_of_term : unknown term " ^ Syntax.string_of_term @{context} t);

fun term_of_num vs (@{code C} i) = HOLogic.mk_number HOLogic.intT (@{code integer_of_int} i)
  | term_of_num vs (@{code Bound} n) =
      let
        val q = @{code integer_of_nat} n
      in fst (the (find_first (fn (_, m) => q = m) vs)) end
  | term_of_num vs (@{code Neg} t') = @{term "uminus :: int \<Rightarrow> int"} $ term_of_num vs t'
  | term_of_num vs (@{code Add} (t1, t2)) = @{term "op + :: int \<Rightarrow> int \<Rightarrow> int"} $
      term_of_num vs t1 $ term_of_num vs t2
  | term_of_num vs (@{code Sub} (t1, t2)) = @{term "op - :: int \<Rightarrow> int \<Rightarrow> int"} $
      term_of_num vs t1 $ term_of_num vs t2
  | term_of_num vs (@{code Mul} (i, t2)) = @{term "op * :: int \<Rightarrow> int \<Rightarrow> int"} $
      term_of_num vs (@{code C} i) $ term_of_num vs t2
  | term_of_num vs (@{code CN} (n, i, t)) =
      term_of_num vs (@{code Add} (@{code Mul} (i, @{code Bound} n), t));

fun term_of_fm ps vs @{code T} = @{term True}
  | term_of_fm ps vs @{code F} = @{term False}
  | term_of_fm ps vs (@{code Lt} t) =
      @{term "op < :: int \<Rightarrow> int \<Rightarrow> bool"} $ term_of_num vs t $ @{term "0::int"}
  | term_of_fm ps vs (@{code Le} t) =
      @{term "op \<le> :: int \<Rightarrow> int \<Rightarrow> bool"} $ term_of_num vs t $ @{term "0::int"}
  | term_of_fm ps vs (@{code Gt} t) =
      @{term "op < :: int \<Rightarrow> int \<Rightarrow> bool"} $ @{term "0::int"} $ term_of_num vs t
  | term_of_fm ps vs (@{code Ge} t) =
      @{term "op \<le> :: int \<Rightarrow> int \<Rightarrow> bool"} $ @{term "0::int"} $ term_of_num vs t
  | term_of_fm ps vs (@{code Eq} t) =
      @{term "op = :: int \<Rightarrow> int \<Rightarrow> bool"} $ term_of_num vs t $ @{term "0::int"}
  | term_of_fm ps vs (@{code NEq} t) =
      term_of_fm ps vs (@{code NOT} (@{code Eq} t))
  | term_of_fm ps vs (@{code Dvd} (i, t)) =
      @{term "op dvd :: int \<Rightarrow> int \<Rightarrow> bool"} $ term_of_num vs (@{code C} i) $ term_of_num vs t
  | term_of_fm ps vs (@{code NDvd} (i, t)) =
      term_of_fm ps vs (@{code NOT} (@{code Dvd} (i, t)))
  | term_of_fm ps vs (@{code NOT} t') =
      HOLogic.Not $ term_of_fm ps vs t'
  | term_of_fm ps vs (@{code And} (t1, t2)) =
      HOLogic.conj $ term_of_fm ps vs t1 $ term_of_fm ps vs t2
  | term_of_fm ps vs (@{code Or} (t1, t2)) =
      HOLogic.disj $ term_of_fm ps vs t1 $ term_of_fm ps vs t2
  | term_of_fm ps vs (@{code Imp} (t1, t2)) =
      HOLogic.imp $ term_of_fm ps vs t1 $ term_of_fm ps vs t2
  | term_of_fm ps vs (@{code Iff} (t1, t2)) =
      @{term "op = :: bool \<Rightarrow> bool \<Rightarrow> bool"} $ term_of_fm ps vs t1 $ term_of_fm ps vs t2
  | term_of_fm ps vs (@{code Closed} n) =
      let
        val q = @{code integer_of_nat} n
      in (fst o the) (find_first (fn (_, m) => m = q) ps) end
  | term_of_fm ps vs (@{code NClosed} n) = term_of_fm ps vs (@{code NOT} (@{code Closed} n));

fun term_bools acc t =
  let
    val is_op =
      member (op =) [@{term HOL.conj}, @{term HOL.disj}, @{term HOL.implies},
      @{term "op = :: bool => _"},
      @{term "op = :: int => _"}, @{term "op < :: int => _"},
      @{term "op <= :: int => _"}, @{term "Not"}, @{term "All :: (int => _) => _"},
      @{term "Ex :: (int => _) => _"}, @{term "True"}, @{term "False"}]
    fun is_ty t = not (fastype_of t = HOLogic.boolT)
  in
    (case t of
      (l as f $ a) $ b =>
        if is_ty t orelse is_op t then term_bools (term_bools acc l) b
        else insert (op aconv) t acc
    | f $ a =>
        if is_ty t orelse is_op t then term_bools (term_bools acc f) a
        else insert (op aconv) t acc
    | Abs p => term_bools acc (snd (Syntax_Trans.variant_abs p))  (* FIXME !? *)
    | _ => if is_ty t orelse is_op t then acc else insert (op aconv) t acc)
  end;

in
  fn (ctxt, t) =>
    let
      val fs = Misc_Legacy.term_frees t;
      val bs = term_bools [] t;
      val vs = map_index swap fs;
      val ps = map_index swap bs;
      val t' = term_of_fm ps vs (@{code pa} (fm_of_term ps vs t));
    in Thm.cterm_of ctxt (HOLogic.mk_Trueprop (HOLogic.mk_eq (t, t'))) end
end;
\<close>

ML_file "cooper_tac.ML"

method_setup cooper = \<open>
  Scan.lift (Args.mode "no_quantify") >>
    (fn q => fn ctxt => SIMPLE_METHOD' (Cooper_Tac.linz_tac ctxt (not q)))
\<close> "decision procedure for linear integer arithmetic"


text \<open>Tests\<close>

lemma "\<exists>(j::int). \<forall>x\<ge>j. \<exists>a b. x = 3*a+5*b"
  by cooper

lemma "\<forall>(x::int) \<ge> 8. \<exists>i j. 5*i + 3*j = x"
  by cooper

theorem "(\<forall>(y::int). 3 dvd y) \<Longrightarrow> \<forall>(x::int). b < x \<longrightarrow> a \<le> x"
  by cooper

theorem "\<And>(y::int) (z::int) (n::int). 3 dvd z \<Longrightarrow> 2 dvd (y::int) \<Longrightarrow>
    (\<exists>(x::int). 2*x = y) \<and> (\<exists>(k::int). 3*k = z)"
  by cooper

theorem "\<And>(y::int) (z::int) n. Suc n < 6 \<Longrightarrow> 3 dvd z \<Longrightarrow>
    2 dvd (y::int) \<Longrightarrow> (\<exists>(x::int).  2*x = y) \<and> (\<exists>(k::int). 3*k = z)"
  by cooper

theorem "\<forall>(x::nat). \<exists>(y::nat). (0::nat) \<le> 5 \<longrightarrow> y = 5 + x"
  by cooper

lemma "\<forall>(x::int) \<ge> 8. \<exists>i j. 5*i + 3*j = x"
  by cooper

lemma "\<forall>(y::int) (z::int) (n::int).
    3 dvd z \<longrightarrow> 2 dvd (y::int) \<longrightarrow> (\<exists>(x::int). 2*x = y) \<and> (\<exists>(k::int). 3*k = z)"
  by cooper

lemma "\<forall>(x::int) y. x < y \<longrightarrow> 2 * x + 1 < 2 * y"
  by cooper

lemma "\<forall>(x::int) y. 2 * x + 1 \<noteq> 2 * y"
  by cooper

lemma "\<exists>(x::int) y. 0 < x \<and> 0 \<le> y \<and> 3 * x - 5 * y = 1"
  by cooper

lemma "\<not> (\<exists>(x::int) (y::int) (z::int). 4*x + (-6::int)*y = 1)"
  by cooper

lemma "\<forall>(x::int). 2 dvd x \<longrightarrow> (\<exists>(y::int). x = 2*y)"
  by cooper

lemma "\<forall>(x::int). 2 dvd x \<longleftrightarrow> (\<exists>(y::int). x = 2*y)"
  by cooper

lemma "\<forall>(x::int). 2 dvd x \<longleftrightarrow> (\<forall>(y::int). x \<noteq> 2*y + 1)"
  by cooper

lemma "\<not> (\<forall>(x::int).
    (2 dvd x \<longleftrightarrow> (\<forall>(y::int). x \<noteq> 2*y+1) \<or>
      (\<exists>(q::int) (u::int) i. 3*i + 2*q - u < 17) \<longrightarrow> 0 < x \<or> (\<not> 3 dvd x \<and> x + 8 = 0)))"
  by cooper

lemma "\<not> (\<forall>(i::int). 4 \<le> i \<longrightarrow> (\<exists>x y. 0 \<le> x \<and> 0 \<le> y \<and> 3 * x + 5 * y = i))"
  by cooper

lemma "\<exists>j. \<forall>(x::int) \<ge> j. \<exists>i j. 5*i + 3*j = x"
  by cooper

theorem "(\<forall>(y::int). 3 dvd y) \<Longrightarrow> \<forall>(x::int). b < x \<longrightarrow> a \<le> x"
  by cooper

theorem "\<And>(y::int) (z::int) (n::int). 3 dvd z \<Longrightarrow> 2 dvd (y::int) \<Longrightarrow>
  (\<exists>(x::int). 2*x = y) \<and> (\<exists>(k::int). 3*k = z)"
  by cooper

theorem "\<And>(y::int) (z::int) n. Suc n < 6 \<Longrightarrow> 3 dvd z \<Longrightarrow>
    2 dvd (y::int) \<Longrightarrow> (\<exists>(x::int). 2*x = y) \<and> (\<exists>(k::int). 3*k = z)"
  by cooper

theorem "\<forall>(x::nat). \<exists>(y::nat). (0::nat) \<le> 5 \<longrightarrow> y = 5 + x"
  by cooper

theorem "\<forall>(x::nat). \<exists>(y::nat). y = 5 + x \<or> x div 6 + 1 = 2"
  by cooper

theorem "\<exists>(x::int). 0 < x"
  by cooper

theorem "\<forall>(x::int) y. x < y \<longrightarrow> 2 * x + 1 < 2 * y"
  by cooper

theorem "\<forall>(x::int) y. 2 * x + 1 \<noteq> 2 * y"
  by cooper

theorem "\<exists>(x::int) y. 0 < x  & 0 \<le> y  & 3 * x - 5 * y = 1"
  by cooper

theorem "\<not> (\<exists>(x::int) (y::int) (z::int). 4*x + (-6::int)*y = 1)"
  by cooper

theorem "\<not> (\<exists>(x::int). False)"
  by cooper

theorem "\<forall>(x::int). 2 dvd x \<longrightarrow> (\<exists>(y::int). x = 2*y)"
  by cooper

theorem "\<forall>(x::int). 2 dvd x \<longrightarrow> (\<exists>(y::int). x = 2*y)"
  by cooper

theorem "\<forall>(x::int). 2 dvd x \<longleftrightarrow> (\<exists>(y::int). x = 2*y)"
  by cooper

theorem "\<forall>(x::int). 2 dvd x \<longleftrightarrow> (\<forall>(y::int). x \<noteq> 2*y + 1)"
  by cooper

theorem
  "\<not> (\<forall>(x::int).
    (2 dvd x \<longleftrightarrow>
      (\<forall>(y::int). x \<noteq> 2*y+1) \<or>
      (\<exists>(q::int) (u::int) i. 3*i + 2*q - u < 17)
       \<longrightarrow> 0 < x \<or> (\<not> 3 dvd x \<and> x + 8 = 0)))"
  by cooper

theorem "\<not> (\<forall>(i::int). 4 \<le> i \<longrightarrow> (\<exists>x y. 0 \<le> x \<and> 0 \<le> y \<and> 3 * x + 5 * y = i))"
  by cooper

theorem "\<forall>(i::int). 8 \<le> i \<longrightarrow> (\<exists>x y. 0 \<le> x \<and> 0 \<le> y \<and> 3 * x + 5 * y = i)"
  by cooper

theorem "\<exists>(j::int). \<forall>i. j \<le> i \<longrightarrow> (\<exists>x y. 0 \<le> x \<and> 0 \<le> y \<and> 3 * x + 5 * y = i)"
  by cooper

theorem "\<not> (\<forall>j (i::int). j \<le> i \<longrightarrow> (\<exists>x y. 0 \<le> x \<and> 0 \<le> y \<and> 3 * x + 5 * y = i))"
  by cooper

theorem "(\<exists>m::nat. n = 2 * m) \<longrightarrow> (n + 1) div 2 = n div 2"
  by cooper

end
