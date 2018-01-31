(*  Title:      HOL/Int.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Author:     Tobias Nipkow, Florian Haftmann, TU Muenchen
*)

section \<open>The Integers as Equivalence Classes over Pairs of Natural Numbers\<close>

theory Int
  imports Equiv_Relations Power Quotient Fun_Def
begin

subsection \<open>Definition of integers as a quotient type\<close>

definition intrel :: "(nat \<times> nat) \<Rightarrow> (nat \<times> nat) \<Rightarrow> bool"
  where "intrel = (\<lambda>(x, y) (u, v). x + v = u + y)"

lemma intrel_iff [simp]: "intrel (x, y) (u, v) \<longleftrightarrow> x + v = u + y"
  by (simp add: intrel_def)

quotient_type int = "nat \<times> nat" / "intrel"
  morphisms Rep_Integ Abs_Integ
proof (rule equivpI)
  show "reflp intrel" by (auto simp: reflp_def)
  show "symp intrel" by (auto simp: symp_def)
  show "transp intrel" by (auto simp: transp_def)
qed

lemma eq_Abs_Integ [case_names Abs_Integ, cases type: int]:
  "(\<And>x y. z = Abs_Integ (x, y) \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct z) auto


subsection \<open>Integers form a commutative ring\<close>

instantiation int :: comm_ring_1
begin

lift_definition zero_int :: "int" is "(0, 0)" .

lift_definition one_int :: "int" is "(1, 0)" .

lift_definition plus_int :: "int \<Rightarrow> int \<Rightarrow> int"
  is "\<lambda>(x, y) (u, v). (x + u, y + v)"
  by clarsimp

lift_definition uminus_int :: "int \<Rightarrow> int"
  is "\<lambda>(x, y). (y, x)"
  by clarsimp

lift_definition minus_int :: "int \<Rightarrow> int \<Rightarrow> int"
  is "\<lambda>(x, y) (u, v). (x + v, y + u)"
  by clarsimp

lift_definition times_int :: "int \<Rightarrow> int \<Rightarrow> int"
  is "\<lambda>(x, y) (u, v). (x*u + y*v, x*v + y*u)"
proof (clarsimp)
  fix s t u v w x y z :: nat
  assume "s + v = u + t" and "w + z = y + x"
  then have "(s + v) * w + (u + t) * x + u * (w + z) + v * (y + x) =
    (u + t) * w + (s + v) * x + u * (y + x) + v * (w + z)"
    by simp
  then show "(s * w + t * x) + (u * z + v * y) = (u * y + v * z) + (s * x + t * w)"
    by (simp add: algebra_simps)
qed

instance
  by standard (transfer; clarsimp simp: algebra_simps)+

end

abbreviation int :: "nat \<Rightarrow> int"
  where "int \<equiv> of_nat"

lemma int_def: "int n = Abs_Integ (n, 0)"
  by (induct n) (simp add: zero_int.abs_eq, simp add: one_int.abs_eq plus_int.abs_eq)

lemma int_transfer [transfer_rule]: "(rel_fun (op =) pcr_int) (\<lambda>n. (n, 0)) int"
  by (simp add: rel_fun_def int.pcr_cr_eq cr_int_def int_def)

lemma int_diff_cases: obtains (diff) m n where "z = int m - int n"
  by transfer clarsimp


subsection \<open>Integers are totally ordered\<close>

instantiation int :: linorder
begin

lift_definition less_eq_int :: "int \<Rightarrow> int \<Rightarrow> bool"
  is "\<lambda>(x, y) (u, v). x + v \<le> u + y"
  by auto

lift_definition less_int :: "int \<Rightarrow> int \<Rightarrow> bool"
  is "\<lambda>(x, y) (u, v). x + v < u + y"
  by auto

instance
  by standard (transfer, force)+

end

instantiation int :: distrib_lattice
begin

definition "(inf :: int \<Rightarrow> int \<Rightarrow> int) = min"

definition "(sup :: int \<Rightarrow> int \<Rightarrow> int) = max"

instance
  by standard (auto simp add: inf_int_def sup_int_def max_min_distrib2)

end


subsection \<open>Ordering properties of arithmetic operations\<close>

instance int :: ordered_cancel_ab_semigroup_add
proof
  fix i j k :: int
  show "i \<le> j \<Longrightarrow> k + i \<le> k + j"
    by transfer clarsimp
qed

text \<open>Strict Monotonicity of Multiplication.\<close>

text \<open>Strict, in 1st argument; proof is by induction on \<open>k > 0\<close>.\<close>
lemma zmult_zless_mono2_lemma: "i < j \<Longrightarrow> 0 < k \<Longrightarrow> int k * i < int k * j"
  for i j :: int
proof (induct k)
  case 0
  then show ?case by simp
next
  case (Suc k)
  then show ?case
    by (cases "k = 0") (simp_all add: distrib_right add_strict_mono)
qed

lemma zero_le_imp_eq_int: "0 \<le> k \<Longrightarrow> \<exists>n. k = int n"
  for k :: int
  apply transfer
  apply clarsimp
  apply (rule_tac x="a - b" in exI)
  apply simp
  done

lemma zero_less_imp_eq_int: "0 < k \<Longrightarrow> \<exists>n>0. k = int n"
  for k :: int
  apply transfer
  apply clarsimp
  apply (rule_tac x="a - b" in exI)
  apply simp
  done

lemma zmult_zless_mono2: "i < j \<Longrightarrow> 0 < k \<Longrightarrow> k * i < k * j"
  for i j k :: int
  by (drule zero_less_imp_eq_int) (auto simp add: zmult_zless_mono2_lemma)


text \<open>The integers form an ordered integral domain.\<close>

instantiation int :: linordered_idom
begin

definition zabs_def: "\<bar>i::int\<bar> = (if i < 0 then - i else i)"

definition zsgn_def: "sgn (i::int) = (if i = 0 then 0 else if 0 < i then 1 else - 1)"

instance
proof
  fix i j k :: int
  show "i < j \<Longrightarrow> 0 < k \<Longrightarrow> k * i < k * j"
    by (rule zmult_zless_mono2)
  show "\<bar>i\<bar> = (if i < 0 then -i else i)"
    by (simp only: zabs_def)
  show "sgn (i::int) = (if i=0 then 0 else if 0<i then 1 else - 1)"
    by (simp only: zsgn_def)
qed

end

lemma zless_imp_add1_zle: "w < z \<Longrightarrow> w + 1 \<le> z"
  for w z :: int
  by transfer clarsimp

lemma zless_iff_Suc_zadd: "w < z \<longleftrightarrow> (\<exists>n. z = w + int (Suc n))"
  for w z :: int
  apply transfer
  apply auto
  apply (rename_tac a b c d)
  apply (rule_tac x="c+b - Suc(a+d)" in exI)
  apply arith
  done

lemma zabs_less_one_iff [simp]: "\<bar>z\<bar> < 1 \<longleftrightarrow> z = 0" (is "?lhs \<longleftrightarrow> ?rhs")
  for z :: int
proof
  assume ?rhs
  then show ?lhs by simp
next
  assume ?lhs
  with zless_imp_add1_zle [of "\<bar>z\<bar>" 1] have "\<bar>z\<bar> + 1 \<le> 1" by simp
  then have "\<bar>z\<bar> \<le> 0" by simp
  then show ?rhs by simp
qed

lemmas int_distrib =
  distrib_right [of z1 z2 w]
  distrib_left [of w z1 z2]
  left_diff_distrib [of z1 z2 w]
  right_diff_distrib [of w z1 z2]
  for z1 z2 w :: int


subsection \<open>Embedding of the Integers into any \<open>ring_1\<close>: \<open>of_int\<close>\<close>

context ring_1
begin

lift_definition of_int :: "int \<Rightarrow> 'a"
  is "\<lambda>(i, j). of_nat i - of_nat j"
  by (clarsimp simp add: diff_eq_eq eq_diff_eq diff_add_eq
      of_nat_add [symmetric] simp del: of_nat_add)

lemma of_int_0 [simp]: "of_int 0 = 0"
  by transfer simp

lemma of_int_1 [simp]: "of_int 1 = 1"
  by transfer simp

lemma of_int_add [simp]: "of_int (w + z) = of_int w + of_int z"
  by transfer (clarsimp simp add: algebra_simps)

lemma of_int_minus [simp]: "of_int (- z) = - (of_int z)"
  by (transfer fixing: uminus) clarsimp

lemma of_int_diff [simp]: "of_int (w - z) = of_int w - of_int z"
  using of_int_add [of w "- z"] by simp

lemma of_int_mult [simp]: "of_int (w*z) = of_int w * of_int z"
  by (transfer fixing: times) (clarsimp simp add: algebra_simps)

lemma mult_of_int_commute: "of_int x * y = y * of_int x"
  by (transfer fixing: times) (auto simp: algebra_simps mult_of_nat_commute)

text \<open>Collapse nested embeddings.\<close>
lemma of_int_of_nat_eq [simp]: "of_int (int n) = of_nat n"
  by (induct n) auto

lemma of_int_numeral [simp, code_post]: "of_int (numeral k) = numeral k"
  by (simp add: of_nat_numeral [symmetric] of_int_of_nat_eq [symmetric])

lemma of_int_neg_numeral [code_post]: "of_int (- numeral k) = - numeral k"
  by simp

lemma of_int_power [simp]: "of_int (z ^ n) = of_int z ^ n"
  by (induct n) simp_all

end

context ring_char_0
begin

lemma of_int_eq_iff [simp]: "of_int w = of_int z \<longleftrightarrow> w = z"
  by transfer (clarsimp simp add: algebra_simps of_nat_add [symmetric] simp del: of_nat_add)

text \<open>Special cases where either operand is zero.\<close>
lemma of_int_eq_0_iff [simp]: "of_int z = 0 \<longleftrightarrow> z = 0"
  using of_int_eq_iff [of z 0] by simp

lemma of_int_0_eq_iff [simp]: "0 = of_int z \<longleftrightarrow> z = 0"
  using of_int_eq_iff [of 0 z] by simp

lemma of_int_eq_1_iff [iff]: "of_int z = 1 \<longleftrightarrow> z = 1"
  using of_int_eq_iff [of z 1] by simp

end

context linordered_idom
begin

text \<open>Every \<open>linordered_idom\<close> has characteristic zero.\<close>
subclass ring_char_0 ..

lemma of_int_le_iff [simp]: "of_int w \<le> of_int z \<longleftrightarrow> w \<le> z"
  by (transfer fixing: less_eq)
    (clarsimp simp add: algebra_simps of_nat_add [symmetric] simp del: of_nat_add)

lemma of_int_less_iff [simp]: "of_int w < of_int z \<longleftrightarrow> w < z"
  by (simp add: less_le order_less_le)

lemma of_int_0_le_iff [simp]: "0 \<le> of_int z \<longleftrightarrow> 0 \<le> z"
  using of_int_le_iff [of 0 z] by simp

lemma of_int_le_0_iff [simp]: "of_int z \<le> 0 \<longleftrightarrow> z \<le> 0"
  using of_int_le_iff [of z 0] by simp

lemma of_int_0_less_iff [simp]: "0 < of_int z \<longleftrightarrow> 0 < z"
  using of_int_less_iff [of 0 z] by simp

lemma of_int_less_0_iff [simp]: "of_int z < 0 \<longleftrightarrow> z < 0"
  using of_int_less_iff [of z 0] by simp

lemma of_int_1_le_iff [simp]: "1 \<le> of_int z \<longleftrightarrow> 1 \<le> z"
  using of_int_le_iff [of 1 z] by simp

lemma of_int_le_1_iff [simp]: "of_int z \<le> 1 \<longleftrightarrow> z \<le> 1"
  using of_int_le_iff [of z 1] by simp

lemma of_int_1_less_iff [simp]: "1 < of_int z \<longleftrightarrow> 1 < z"
  using of_int_less_iff [of 1 z] by simp

lemma of_int_less_1_iff [simp]: "of_int z < 1 \<longleftrightarrow> z < 1"
  using of_int_less_iff [of z 1] by simp

lemma of_int_pos: "z > 0 \<Longrightarrow> of_int z > 0"
  by simp

lemma of_int_nonneg: "z \<ge> 0 \<Longrightarrow> of_int z \<ge> 0"
  by simp

lemma of_int_abs [simp]: "of_int \<bar>x\<bar> = \<bar>of_int x\<bar>"
  by (auto simp add: abs_if)

lemma of_int_lessD:
  assumes "\<bar>of_int n\<bar> < x"
  shows "n = 0 \<or> x > 1"
proof (cases "n = 0")
  case True
  then show ?thesis by simp
next
  case False
  then have "\<bar>n\<bar> \<noteq> 0" by simp
  then have "\<bar>n\<bar> > 0" by simp
  then have "\<bar>n\<bar> \<ge> 1"
    using zless_imp_add1_zle [of 0 "\<bar>n\<bar>"] by simp
  then have "\<bar>of_int n\<bar> \<ge> 1"
    unfolding of_int_1_le_iff [of "\<bar>n\<bar>", symmetric] by simp
  then have "1 < x" using assms by (rule le_less_trans)
  then show ?thesis ..
qed

lemma of_int_leD:
  assumes "\<bar>of_int n\<bar> \<le> x"
  shows "n = 0 \<or> 1 \<le> x"
proof (cases "n = 0")
  case True
  then show ?thesis by simp
next
  case False
  then have "\<bar>n\<bar> \<noteq> 0" by simp
  then have "\<bar>n\<bar> > 0" by simp
  then have "\<bar>n\<bar> \<ge> 1"
    using zless_imp_add1_zle [of 0 "\<bar>n\<bar>"] by simp
  then have "\<bar>of_int n\<bar> \<ge> 1"
    unfolding of_int_1_le_iff [of "\<bar>n\<bar>", symmetric] by simp
  then have "1 \<le> x" using assms by (rule order_trans)
  then show ?thesis ..
qed


end

text \<open>Comparisons involving @{term of_int}.\<close>

lemma of_int_eq_numeral_iff [iff]: "of_int z = (numeral n :: 'a::ring_char_0) \<longleftrightarrow> z = numeral n"
  using of_int_eq_iff by fastforce

lemma of_int_le_numeral_iff [simp]:
  "of_int z \<le> (numeral n :: 'a::linordered_idom) \<longleftrightarrow> z \<le> numeral n"
  using of_int_le_iff [of z "numeral n"] by simp

lemma of_int_numeral_le_iff [simp]:
  "(numeral n :: 'a::linordered_idom) \<le> of_int z \<longleftrightarrow> numeral n \<le> z"
  using of_int_le_iff [of "numeral n"] by simp

lemma of_int_less_numeral_iff [simp]:
  "of_int z < (numeral n :: 'a::linordered_idom) \<longleftrightarrow> z < numeral n"
  using of_int_less_iff [of z "numeral n"] by simp

lemma of_int_numeral_less_iff [simp]:
  "(numeral n :: 'a::linordered_idom) < of_int z \<longleftrightarrow> numeral n < z"
  using of_int_less_iff [of "numeral n" z] by simp

lemma of_nat_less_of_int_iff: "(of_nat n::'a::linordered_idom) < of_int x \<longleftrightarrow> int n < x"
  by (metis of_int_of_nat_eq of_int_less_iff)

lemma of_int_eq_id [simp]: "of_int = id"
proof
  show "of_int z = id z" for z
    by (cases z rule: int_diff_cases) simp
qed

instance int :: no_top
  apply standard
  apply (rule_tac x="x + 1" in exI)
  apply simp
  done

instance int :: no_bot
  apply standard
  apply (rule_tac x="x - 1" in exI)
  apply simp
  done


subsection \<open>Magnitude of an Integer, as a Natural Number: \<open>nat\<close>\<close>

lift_definition nat :: "int \<Rightarrow> nat" is "\<lambda>(x, y). x - y"
  by auto

lemma nat_int [simp]: "nat (int n) = n"
  by transfer simp

lemma int_nat_eq [simp]: "int (nat z) = (if 0 \<le> z then z else 0)"
  by transfer clarsimp

lemma nat_0_le: "0 \<le> z \<Longrightarrow> int (nat z) = z"
  by simp

lemma nat_le_0 [simp]: "z \<le> 0 \<Longrightarrow> nat z = 0"
  by transfer clarsimp

lemma nat_le_eq_zle: "0 < w \<or> 0 \<le> z \<Longrightarrow> nat w \<le> nat z \<longleftrightarrow> w \<le> z"
  by transfer (clarsimp, arith)

text \<open>An alternative condition is @{term "0 \<le> w"}.\<close>
lemma nat_mono_iff: "0 < z \<Longrightarrow> nat w < nat z \<longleftrightarrow> w < z"
  by (simp add: nat_le_eq_zle linorder_not_le [symmetric])

lemma nat_less_eq_zless: "0 \<le> w \<Longrightarrow> nat w < nat z \<longleftrightarrow> w < z"
  by (simp add: nat_le_eq_zle linorder_not_le [symmetric])

lemma zless_nat_conj [simp]: "nat w < nat z \<longleftrightarrow> 0 < z \<and> w < z"
  by transfer (clarsimp, arith)

lemma nonneg_eq_int:
  fixes z :: int
  assumes "0 \<le> z" and "\<And>m. z = int m \<Longrightarrow> P"
  shows P
  using assms by (blast dest: nat_0_le sym)

lemma nat_eq_iff: "nat w = m \<longleftrightarrow> (if 0 \<le> w then w = int m else m = 0)"
  by transfer (clarsimp simp add: le_imp_diff_is_add)

lemma nat_eq_iff2: "m = nat w \<longleftrightarrow> (if 0 \<le> w then w = int m else m = 0)"
  using nat_eq_iff [of w m] by auto

lemma nat_0 [simp]: "nat 0 = 0"
  by (simp add: nat_eq_iff)

lemma nat_1 [simp]: "nat 1 = Suc 0"
  by (simp add: nat_eq_iff)

lemma nat_numeral [simp]: "nat (numeral k) = numeral k"
  by (simp add: nat_eq_iff)

lemma nat_neg_numeral [simp]: "nat (- numeral k) = 0"
  by simp

lemma nat_2: "nat 2 = Suc (Suc 0)"
  by simp

lemma nat_less_iff: "0 \<le> w \<Longrightarrow> nat w < m \<longleftrightarrow> w < of_nat m"
  by transfer (clarsimp, arith)

lemma nat_le_iff: "nat x \<le> n \<longleftrightarrow> x \<le> int n"
  by transfer (clarsimp simp add: le_diff_conv)

lemma nat_mono: "x \<le> y \<Longrightarrow> nat x \<le> nat y"
  by transfer auto

lemma nat_0_iff[simp]: "nat i = 0 \<longleftrightarrow> i \<le> 0"
  for i :: int
  by transfer clarsimp

lemma int_eq_iff: "of_nat m = z \<longleftrightarrow> m = nat z \<and> 0 \<le> z"
  by (auto simp add: nat_eq_iff2)

lemma zero_less_nat_eq [simp]: "0 < nat z \<longleftrightarrow> 0 < z"
  using zless_nat_conj [of 0] by auto

lemma nat_add_distrib: "0 \<le> z \<Longrightarrow> 0 \<le> z' \<Longrightarrow> nat (z + z') = nat z + nat z'"
  by transfer clarsimp

lemma nat_diff_distrib': "0 \<le> x \<Longrightarrow> 0 \<le> y \<Longrightarrow> nat (x - y) = nat x - nat y"
  by transfer clarsimp

lemma nat_diff_distrib: "0 \<le> z' \<Longrightarrow> z' \<le> z \<Longrightarrow> nat (z - z') = nat z - nat z'"
  by (rule nat_diff_distrib') auto

lemma nat_zminus_int [simp]: "nat (- int n) = 0"
  by transfer simp

lemma le_nat_iff: "k \<ge> 0 \<Longrightarrow> n \<le> nat k \<longleftrightarrow> int n \<le> k"
  by transfer auto

lemma zless_nat_eq_int_zless: "m < nat z \<longleftrightarrow> int m < z"
  by transfer (clarsimp simp add: less_diff_conv)

lemma (in ring_1) of_nat_nat [simp]: "0 \<le> z \<Longrightarrow> of_nat (nat z) = of_int z"
  by transfer (clarsimp simp add: of_nat_diff)

lemma diff_nat_numeral [simp]: "(numeral v :: nat) - numeral v' = nat (numeral v - numeral v')"
  by (simp only: nat_diff_distrib' zero_le_numeral nat_numeral)


text \<open>For termination proofs:\<close>
lemma measure_function_int[measure_function]: "is_measure (nat \<circ> abs)" ..


subsection \<open>Lemmas about the Function @{term of_nat} and Orderings\<close>

lemma negative_zless_0: "- (int (Suc n)) < (0 :: int)"
  by (simp add: order_less_le del: of_nat_Suc)

lemma negative_zless [iff]: "- (int (Suc n)) < int m"
  by (rule negative_zless_0 [THEN order_less_le_trans], simp)

lemma negative_zle_0: "- int n \<le> 0"
  by (simp add: minus_le_iff)

lemma negative_zle [iff]: "- int n \<le> int m"
  by (rule order_trans [OF negative_zle_0 of_nat_0_le_iff])

lemma not_zle_0_negative [simp]: "\<not> 0 \<le> - int (Suc n)"
  by (subst le_minus_iff) (simp del: of_nat_Suc)

lemma int_zle_neg: "int n \<le> - int m \<longleftrightarrow> n = 0 \<and> m = 0"
  by transfer simp

lemma not_int_zless_negative [simp]: "\<not> int n < - int m"
  by (simp add: linorder_not_less)

lemma negative_eq_positive [simp]: "- int n = of_nat m \<longleftrightarrow> n = 0 \<and> m = 0"
  by (force simp add: order_eq_iff [of "- of_nat n"] int_zle_neg)

lemma zle_iff_zadd: "w \<le> z \<longleftrightarrow> (\<exists>n. z = w + int n)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?rhs
  then show ?lhs by auto
next
  assume ?lhs
  then have "0 \<le> z - w" by simp
  then obtain n where "z - w = int n"
    using zero_le_imp_eq_int [of "z - w"] by blast
  then have "z = w + int n" by simp
  then show ?rhs ..
qed

lemma zadd_int_left: "int m + (int n + z) = int (m + n) + z"
  by simp

text \<open>
  This version is proved for all ordered rings, not just integers!
  It is proved here because attribute \<open>arith_split\<close> is not available
  in theory \<open>Rings\<close>.
  But is it really better than just rewriting with \<open>abs_if\<close>?
\<close>
lemma abs_split [arith_split, no_atp]: "P \<bar>a\<bar> \<longleftrightarrow> (0 \<le> a \<longrightarrow> P a) \<and> (a < 0 \<longrightarrow> P (- a))"
  for a :: "'a::linordered_idom"
  by (force dest: order_less_le_trans simp add: abs_if linorder_not_less)

lemma negD: "x < 0 \<Longrightarrow> \<exists>n. x = - (int (Suc n))"
  apply transfer
  apply clarsimp
  apply (rule_tac x="b - Suc a" in exI)
  apply arith
  done


subsection \<open>Cases and induction\<close>

text \<open>
  Now we replace the case analysis rule by a more conventional one:
  whether an integer is negative or not.
\<close>

text \<open>This version is symmetric in the two subgoals.\<close>
lemma int_cases2 [case_names nonneg nonpos, cases type: int]:
  "(\<And>n. z = int n \<Longrightarrow> P) \<Longrightarrow> (\<And>n. z = - (int n) \<Longrightarrow> P) \<Longrightarrow> P"
  by (cases "z < 0") (auto simp add: linorder_not_less dest!: negD nat_0_le [THEN sym])

text \<open>This is the default, with a negative case.\<close>
lemma int_cases [case_names nonneg neg, cases type: int]:
  "(\<And>n. z = int n \<Longrightarrow> P) \<Longrightarrow> (\<And>n. z = - (int (Suc n)) \<Longrightarrow> P) \<Longrightarrow> P"
  apply (cases "z < 0")
   apply (blast dest!: negD)
  apply (simp add: linorder_not_less del: of_nat_Suc)
  apply auto
  apply (blast dest: nat_0_le [THEN sym])
  done

lemma int_cases3 [case_names zero pos neg]:
  fixes k :: int
  assumes "k = 0 \<Longrightarrow> P" and "\<And>n. k = int n \<Longrightarrow> n > 0 \<Longrightarrow> P"
    and "\<And>n. k = - int n \<Longrightarrow> n > 0 \<Longrightarrow> P"
  shows "P"
proof (cases k "0::int" rule: linorder_cases)
  case equal
  with assms(1) show P by simp
next
  case greater
  then have *: "nat k > 0" by simp
  moreover from * have "k = int (nat k)" by auto
  ultimately show P using assms(2) by blast
next
  case less
  then have *: "nat (- k) > 0" by simp
  moreover from * have "k = - int (nat (- k))" by auto
  ultimately show P using assms(3) by blast
qed

lemma int_of_nat_induct [case_names nonneg neg, induct type: int]:
  "(\<And>n. P (int n)) \<Longrightarrow> (\<And>n. P (- (int (Suc n)))) \<Longrightarrow> P z"
  by (cases z) auto

lemma nonneg_int_cases:
  assumes "0 \<le> k"
  obtains n where "k = int n"
  using assms by (rule nonneg_eq_int)

lemma Let_numeral [simp]: "Let (numeral v) f = f (numeral v)"
  \<comment> \<open>Unfold all \<open>let\<close>s involving constants\<close>
  by (fact Let_numeral) \<comment> \<open>FIXME drop\<close>

lemma Let_neg_numeral [simp]: "Let (- numeral v) f = f (- numeral v)"
  \<comment> \<open>Unfold all \<open>let\<close>s involving constants\<close>
  by (fact Let_neg_numeral) \<comment> \<open>FIXME drop\<close>

text \<open>Unfold \<open>min\<close> and \<open>max\<close> on numerals.\<close>

lemmas max_number_of [simp] =
  max_def [of "numeral u" "numeral v"]
  max_def [of "numeral u" "- numeral v"]
  max_def [of "- numeral u" "numeral v"]
  max_def [of "- numeral u" "- numeral v"] for u v

lemmas min_number_of [simp] =
  min_def [of "numeral u" "numeral v"]
  min_def [of "numeral u" "- numeral v"]
  min_def [of "- numeral u" "numeral v"]
  min_def [of "- numeral u" "- numeral v"] for u v


subsubsection \<open>Binary comparisons\<close>

text \<open>Preliminaries\<close>

lemma le_imp_0_less:
  fixes z :: int
  assumes le: "0 \<le> z"
  shows "0 < 1 + z"
proof -
  have "0 \<le> z" by fact
  also have "\<dots> < z + 1" by (rule less_add_one)
  also have "\<dots> = 1 + z" by (simp add: ac_simps)
  finally show "0 < 1 + z" .
qed

lemma odd_less_0_iff: "1 + z + z < 0 \<longleftrightarrow> z < 0"
  for z :: int
proof (cases z)
  case (nonneg n)
  then show ?thesis
    by (simp add: linorder_not_less add.assoc add_increasing le_imp_0_less [THEN order_less_imp_le])
next
  case (neg n)
  then show ?thesis
    by (simp del: of_nat_Suc of_nat_add of_nat_1
        add: algebra_simps of_nat_1 [where 'a=int, symmetric] of_nat_add [symmetric])
qed


subsubsection \<open>Comparisons, for Ordered Rings\<close>

lemmas double_eq_0_iff = double_zero

lemma odd_nonzero: "1 + z + z \<noteq> 0"
  for z :: int
proof (cases z)
  case (nonneg n)
  have le: "0 \<le> z + z"
    by (simp add: nonneg add_increasing)
  then show ?thesis
    using  le_imp_0_less [OF le] by (auto simp: add.assoc)
next
  case (neg n)
  show ?thesis
  proof
    assume eq: "1 + z + z = 0"
    have "0 < 1 + (int n + int n)"
      by (simp add: le_imp_0_less add_increasing)
    also have "\<dots> = - (1 + z + z)"
      by (simp add: neg add.assoc [symmetric])
    also have "\<dots> = 0" by (simp add: eq)
    finally have "0<0" ..
    then show False by blast
  qed
qed


subsection \<open>The Set of Integers\<close>

context ring_1
begin

definition Ints :: "'a set"  ("\<int>")
  where "\<int> = range of_int"

lemma Ints_of_int [simp]: "of_int z \<in> \<int>"
  by (simp add: Ints_def)

lemma Ints_of_nat [simp]: "of_nat n \<in> \<int>"
  using Ints_of_int [of "of_nat n"] by simp

lemma Ints_0 [simp]: "0 \<in> \<int>"
  using Ints_of_int [of "0"] by simp

lemma Ints_1 [simp]: "1 \<in> \<int>"
  using Ints_of_int [of "1"] by simp

lemma Ints_numeral [simp]: "numeral n \<in> \<int>"
  by (subst of_nat_numeral [symmetric], rule Ints_of_nat)

lemma Ints_add [simp]: "a \<in> \<int> \<Longrightarrow> b \<in> \<int> \<Longrightarrow> a + b \<in> \<int>"
  apply (auto simp add: Ints_def)
  apply (rule range_eqI)
  apply (rule of_int_add [symmetric])
  done

lemma Ints_minus [simp]: "a \<in> \<int> \<Longrightarrow> -a \<in> \<int>"
  apply (auto simp add: Ints_def)
  apply (rule range_eqI)
  apply (rule of_int_minus [symmetric])
  done

lemma Ints_diff [simp]: "a \<in> \<int> \<Longrightarrow> b \<in> \<int> \<Longrightarrow> a - b \<in> \<int>"
  apply (auto simp add: Ints_def)
  apply (rule range_eqI)
  apply (rule of_int_diff [symmetric])
  done

lemma Ints_mult [simp]: "a \<in> \<int> \<Longrightarrow> b \<in> \<int> \<Longrightarrow> a * b \<in> \<int>"
  apply (auto simp add: Ints_def)
  apply (rule range_eqI)
  apply (rule of_int_mult [symmetric])
  done

lemma Ints_power [simp]: "a \<in> \<int> \<Longrightarrow> a ^ n \<in> \<int>"
  by (induct n) simp_all

lemma Ints_cases [cases set: Ints]:
  assumes "q \<in> \<int>"
  obtains (of_int) z where "q = of_int z"
  unfolding Ints_def
proof -
  from \<open>q \<in> \<int>\<close> have "q \<in> range of_int" unfolding Ints_def .
  then obtain z where "q = of_int z" ..
  then show thesis ..
qed

lemma Ints_induct [case_names of_int, induct set: Ints]:
  "q \<in> \<int> \<Longrightarrow> (\<And>z. P (of_int z)) \<Longrightarrow> P q"
  by (rule Ints_cases) auto

lemma Nats_subset_Ints: "\<nat> \<subseteq> \<int>"
  unfolding Nats_def Ints_def
  by (rule subsetI, elim imageE, hypsubst, subst of_int_of_nat_eq[symmetric], rule imageI) simp_all

lemma Nats_altdef1: "\<nat> = {of_int n |n. n \<ge> 0}"
proof (intro subsetI equalityI)
  fix x :: 'a
  assume "x \<in> {of_int n |n. n \<ge> 0}"
  then obtain n where "x = of_int n" "n \<ge> 0"
    by (auto elim!: Ints_cases)
  then have "x = of_nat (nat n)"
    by (subst of_nat_nat) simp_all
  then show "x \<in> \<nat>"
    by simp
next
  fix x :: 'a
  assume "x \<in> \<nat>"
  then obtain n where "x = of_nat n"
    by (auto elim!: Nats_cases)
  then have "x = of_int (int n)" by simp
  also have "int n \<ge> 0" by simp
  then have "of_int (int n) \<in> {of_int n |n. n \<ge> 0}" by blast
  finally show "x \<in> {of_int n |n. n \<ge> 0}" .
qed

end

lemma (in linordered_idom) Nats_altdef2: "\<nat> = {n \<in> \<int>. n \<ge> 0}"
proof (intro subsetI equalityI)
  fix x :: 'a
  assume "x \<in> {n \<in> \<int>. n \<ge> 0}"
  then obtain n where "x = of_int n" "n \<ge> 0"
    by (auto elim!: Ints_cases)
  then have "x = of_nat (nat n)"
    by (subst of_nat_nat) simp_all
  then show "x \<in> \<nat>"
    by simp
qed (auto elim!: Nats_cases)


text \<open>The premise involving @{term Ints} prevents @{term "a = 1/2"}.\<close>

lemma Ints_double_eq_0_iff:
  fixes a :: "'a::ring_char_0"
  assumes in_Ints: "a \<in> \<int>"
  shows "a + a = 0 \<longleftrightarrow> a = 0"
    (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  from in_Ints have "a \<in> range of_int"
    unfolding Ints_def [symmetric] .
  then obtain z where a: "a = of_int z" ..
  show ?thesis
  proof
    assume ?rhs
    then show ?lhs by simp
  next
    assume ?lhs
    with a have "of_int (z + z) = (of_int 0 :: 'a)" by simp
    then have "z + z = 0" by (simp only: of_int_eq_iff)
    then have "z = 0" by (simp only: double_eq_0_iff)
    with a show ?rhs by simp
  qed
qed

lemma Ints_odd_nonzero:
  fixes a :: "'a::ring_char_0"
  assumes in_Ints: "a \<in> \<int>"
  shows "1 + a + a \<noteq> 0"
proof -
  from in_Ints have "a \<in> range of_int"
    unfolding Ints_def [symmetric] .
  then obtain z where a: "a = of_int z" ..
  show ?thesis
  proof
    assume "1 + a + a = 0"
    with a have "of_int (1 + z + z) = (of_int 0 :: 'a)" by simp
    then have "1 + z + z = 0" by (simp only: of_int_eq_iff)
    with odd_nonzero show False by blast
  qed
qed

lemma Nats_numeral [simp]: "numeral w \<in> \<nat>"
  using of_nat_in_Nats [of "numeral w"] by simp

lemma Ints_odd_less_0:
  fixes a :: "'a::linordered_idom"
  assumes in_Ints: "a \<in> \<int>"
  shows "1 + a + a < 0 \<longleftrightarrow> a < 0"
proof -
  from in_Ints have "a \<in> range of_int"
    unfolding Ints_def [symmetric] .
  then obtain z where a: "a = of_int z" ..
  with a have "1 + a + a < 0 \<longleftrightarrow> of_int (1 + z + z) < (of_int 0 :: 'a)"
    by simp
  also have "\<dots> \<longleftrightarrow> z < 0"
    by (simp only: of_int_less_iff odd_less_0_iff)
  also have "\<dots> \<longleftrightarrow> a < 0"
    by (simp add: a)
  finally show ?thesis .
qed


subsection \<open>@{term sum} and @{term prod}\<close>

lemma of_nat_sum [simp]: "of_nat (sum f A) = (\<Sum>x\<in>A. of_nat(f x))"
  by (induct A rule: infinite_finite_induct) auto

lemma of_int_sum [simp]: "of_int (sum f A) = (\<Sum>x\<in>A. of_int(f x))"
  by (induct A rule: infinite_finite_induct) auto

lemma of_nat_prod [simp]: "of_nat (prod f A) = (\<Prod>x\<in>A. of_nat(f x))"
  by (induct A rule: infinite_finite_induct) auto

lemma of_int_prod [simp]: "of_int (prod f A) = (\<Prod>x\<in>A. of_int(f x))"
  by (induct A rule: infinite_finite_induct) auto

lemmas int_sum = of_nat_sum [where 'a=int]
lemmas int_prod = of_nat_prod [where 'a=int]


text \<open>Legacy theorems\<close>

lemmas zle_int = of_nat_le_iff [where 'a=int]
lemmas int_int_eq = of_nat_eq_iff [where 'a=int]


subsection \<open>Setting up simplification procedures\<close>

lemmas of_int_simps =
  of_int_0 of_int_1 of_int_add of_int_mult

ML_file "Tools/int_arith.ML"
declaration \<open>K Int_Arith.setup\<close>

simproc_setup fast_arith
  ("(m::'a::linordered_idom) < n" |
    "(m::'a::linordered_idom) \<le> n" |
    "(m::'a::linordered_idom) = n") =
  \<open>K Lin_Arith.simproc\<close>


subsection\<open>More Inequality Reasoning\<close>

lemma zless_add1_eq: "w < z + 1 \<longleftrightarrow> w < z \<or> w = z"
  for w z :: int
  by arith

lemma add1_zle_eq: "w + 1 \<le> z \<longleftrightarrow> w < z"
  for w z :: int
  by arith

lemma zle_diff1_eq [simp]: "w \<le> z - 1 \<longleftrightarrow> w < z"
  for w z :: int
  by arith

lemma zle_add1_eq_le [simp]: "w < z + 1 \<longleftrightarrow> w \<le> z"
  for w z :: int
  by arith

lemma int_one_le_iff_zero_less: "1 \<le> z \<longleftrightarrow> 0 < z"
  for z :: int
  by arith


subsection \<open>The functions @{term nat} and @{term int}\<close>

text \<open>Simplify the term @{term "w + - z"}.\<close>

lemma one_less_nat_eq [simp]: "Suc 0 < nat z \<longleftrightarrow> 1 < z"
  using zless_nat_conj [of 1 z] by auto

text \<open>
  This simplifies expressions of the form @{term "int n = z"} where
  \<open>z\<close> is an integer literal.
\<close>
lemmas int_eq_iff_numeral [simp] = int_eq_iff [of _ "numeral v"] for v

lemma split_nat [arith_split]: "P (nat i) = ((\<forall>n. i = int n \<longrightarrow> P n) \<and> (i < 0 \<longrightarrow> P 0))"
  (is "?P = (?L \<and> ?R)")
  for i :: int
proof (cases "i < 0")
  case True
  then show ?thesis by auto
next
  case False
  have "?P = ?L"
  proof
    assume ?P
    then show ?L using False by auto
  next
    assume ?L
    then show ?P using False by simp
  qed
  with False show ?thesis by simp
qed

lemma nat_abs_int_diff: "nat \<bar>int a - int b\<bar> = (if a \<le> b then b - a else a - b)"
  by auto

lemma nat_int_add: "nat (int a + int b) = a + b"
  by auto

context ring_1
begin

lemma of_int_of_nat [nitpick_simp]:
  "of_int k = (if k < 0 then - of_nat (nat (- k)) else of_nat (nat k))"
proof (cases "k < 0")
  case True
  then have "0 \<le> - k" by simp
  then have "of_nat (nat (- k)) = of_int (- k)" by (rule of_nat_nat)
  with True show ?thesis by simp
next
  case False
  then show ?thesis by (simp add: not_less)
qed

end

lemma transfer_rule_of_int:
  fixes R :: "'a::ring_1 \<Rightarrow> 'b::ring_1 \<Rightarrow> bool"
  assumes [transfer_rule]: "R 0 0" "R 1 1"
    "rel_fun R (rel_fun R R) plus plus"
    "rel_fun R R uminus uminus"
  shows "rel_fun HOL.eq R of_int of_int"
proof -
  note transfer_rule_of_nat [transfer_rule]
  have [transfer_rule]: "rel_fun HOL.eq R of_nat of_nat"
    by transfer_prover
  show ?thesis
    by (unfold of_int_of_nat [abs_def]) transfer_prover
qed

lemma nat_mult_distrib:
  fixes z z' :: int
  assumes "0 \<le> z"
  shows "nat (z * z') = nat z * nat z'"
proof (cases "0 \<le> z'")
  case False
  with assms have "z * z' \<le> 0"
    by (simp add: not_le mult_le_0_iff)
  then have "nat (z * z') = 0" by simp
  moreover from False have "nat z' = 0" by simp
  ultimately show ?thesis by simp
next
  case True
  with assms have ge_0: "z * z' \<ge> 0" by (simp add: zero_le_mult_iff)
  show ?thesis
    by (rule injD [of "of_nat :: nat \<Rightarrow> int", OF inj_of_nat])
      (simp only: of_nat_mult of_nat_nat [OF True]
         of_nat_nat [OF assms] of_nat_nat [OF ge_0], simp)
qed

lemma nat_mult_distrib_neg: "z \<le> 0 \<Longrightarrow> nat (z * z') = nat (- z) * nat (- z')"
  for z z' :: int
  apply (rule trans)
   apply (rule_tac [2] nat_mult_distrib)
   apply auto
  done

lemma nat_abs_mult_distrib: "nat \<bar>w * z\<bar> = nat \<bar>w\<bar> * nat \<bar>z\<bar>"
  by (cases "z = 0 \<or> w = 0")
    (auto simp add: abs_if nat_mult_distrib [symmetric]
      nat_mult_distrib_neg [symmetric] mult_less_0_iff)

lemma int_in_range_abs [simp]: "int n \<in> range abs"
proof (rule range_eqI)
  show "int n = \<bar>int n\<bar>" by simp
qed

lemma range_abs_Nats [simp]: "range abs = (\<nat> :: int set)"
proof -
  have "\<bar>k\<bar> \<in> \<nat>" for k :: int
    by (cases k) simp_all
  moreover have "k \<in> range abs" if "k \<in> \<nat>" for k :: int
    using that by induct simp
  ultimately show ?thesis by blast
qed

lemma Suc_nat_eq_nat_zadd1: "0 \<le> z \<Longrightarrow> Suc (nat z) = nat (1 + z)"
  for z :: int
  by (rule sym) (simp add: nat_eq_iff)

lemma diff_nat_eq_if:
  "nat z - nat z' =
    (if z' < 0 then nat z
     else
      let d = z - z'
      in if d < 0 then 0 else nat d)"
  by (simp add: Let_def nat_diff_distrib [symmetric])

lemma nat_numeral_diff_1 [simp]: "numeral v - (1::nat) = nat (numeral v - 1)"
  using diff_nat_numeral [of v Num.One] by simp


subsection \<open>Induction principles for int\<close>

text \<open>Well-founded segments of the integers.\<close>

definition int_ge_less_than :: "int \<Rightarrow> (int \<times> int) set"
  where "int_ge_less_than d = {(z', z). d \<le> z' \<and> z' < z}"

lemma wf_int_ge_less_than: "wf (int_ge_less_than d)"
proof -
  have "int_ge_less_than d \<subseteq> measure (\<lambda>z. nat (z - d))"
    by (auto simp add: int_ge_less_than_def)
  then show ?thesis
    by (rule wf_subset [OF wf_measure])
qed

text \<open>
  This variant looks odd, but is typical of the relations suggested
  by RankFinder.\<close>

definition int_ge_less_than2 :: "int \<Rightarrow> (int \<times> int) set"
  where "int_ge_less_than2 d = {(z',z). d \<le> z \<and> z' < z}"

lemma wf_int_ge_less_than2: "wf (int_ge_less_than2 d)"
proof -
  have "int_ge_less_than2 d \<subseteq> measure (\<lambda>z. nat (1 + z - d))"
    by (auto simp add: int_ge_less_than2_def)
  then show ?thesis
    by (rule wf_subset [OF wf_measure])
qed

(* `set:int': dummy construction *)
theorem int_ge_induct [case_names base step, induct set: int]:
  fixes i :: int
  assumes ge: "k \<le> i"
    and base: "P k"
    and step: "\<And>i. k \<le> i \<Longrightarrow> P i \<Longrightarrow> P (i + 1)"
  shows "P i"
proof -
  have "\<And>i::int. n = nat (i - k) \<Longrightarrow> k \<le> i \<Longrightarrow> P i" for n
  proof (induct n)
    case 0
    then have "i = k" by arith
    with base show "P i" by simp
  next
    case (Suc n)
    then have "n = nat ((i - 1) - k)" by arith
    moreover have k: "k \<le> i - 1" using Suc.prems by arith
    ultimately have "P (i - 1)" by (rule Suc.hyps)
    from step [OF k this] show ?case by simp
  qed
  with ge show ?thesis by fast
qed

(* `set:int': dummy construction *)
theorem int_gr_induct [case_names base step, induct set: int]:
  fixes i k :: int
  assumes gr: "k < i"
    and base: "P (k + 1)"
    and step: "\<And>i. k < i \<Longrightarrow> P i \<Longrightarrow> P (i + 1)"
  shows "P i"
  apply (rule int_ge_induct[of "k + 1"])
  using gr apply arith
   apply (rule base)
  apply (rule step)
   apply simp_all
  done

theorem int_le_induct [consumes 1, case_names base step]:
  fixes i k :: int
  assumes le: "i \<le> k"
    and base: "P k"
    and step: "\<And>i. i \<le> k \<Longrightarrow> P i \<Longrightarrow> P (i - 1)"
  shows "P i"
proof -
  have "\<And>i::int. n = nat(k-i) \<Longrightarrow> i \<le> k \<Longrightarrow> P i" for n
  proof (induct n)
    case 0
    then have "i = k" by arith
    with base show "P i" by simp
  next
    case (Suc n)
    then have "n = nat (k - (i + 1))" by arith
    moreover have k: "i + 1 \<le> k" using Suc.prems by arith
    ultimately have "P (i + 1)" by (rule Suc.hyps)
    from step[OF k this] show ?case by simp
  qed
  with le show ?thesis by fast
qed

theorem int_less_induct [consumes 1, case_names base step]:
  fixes i k :: int
  assumes less: "i < k"
    and base: "P (k - 1)"
    and step: "\<And>i. i < k \<Longrightarrow> P i \<Longrightarrow> P (i - 1)"
  shows "P i"
  apply (rule int_le_induct[of _ "k - 1"])
  using less apply arith
   apply (rule base)
  apply (rule step)
   apply simp_all
  done

theorem int_induct [case_names base step1 step2]:
  fixes k :: int
  assumes base: "P k"
    and step1: "\<And>i. k \<le> i \<Longrightarrow> P i \<Longrightarrow> P (i + 1)"
    and step2: "\<And>i. k \<ge> i \<Longrightarrow> P i \<Longrightarrow> P (i - 1)"
  shows "P i"
proof -
  have "i \<le> k \<or> i \<ge> k" by arith
  then show ?thesis
  proof
    assume "i \<ge> k"
    then show ?thesis
      using base by (rule int_ge_induct) (fact step1)
  next
    assume "i \<le> k"
    then show ?thesis
      using base by (rule int_le_induct) (fact step2)
  qed
qed


subsection \<open>Intermediate value theorems\<close>

lemma int_val_lemma: "(\<forall>i<n. \<bar>f (i + 1) - f i\<bar> \<le> 1) \<longrightarrow> f 0 \<le> k \<longrightarrow> k \<le> f n \<longrightarrow> (\<exists>i \<le> n. f i = k)"
  for n :: nat and k :: int
  unfolding One_nat_def
  apply (induct n)
   apply simp
  apply (intro strip)
  apply (erule impE)
   apply simp
  apply (erule_tac x = n in allE)
  apply simp
  apply (case_tac "k = f (Suc n)")
   apply force
  apply (erule impE)
   apply (simp add: abs_if split: if_split_asm)
  apply (blast intro: le_SucI)
  done

lemmas nat0_intermed_int_val = int_val_lemma [rule_format (no_asm)]

lemma nat_intermed_int_val:
  "\<forall>i. m \<le> i \<and> i < n \<longrightarrow> \<bar>f (i + 1) - f i\<bar> \<le> 1 \<Longrightarrow> m < n \<Longrightarrow>
    f m \<le> k \<Longrightarrow> k \<le> f n \<Longrightarrow> \<exists>i. m \<le> i \<and> i \<le> n \<and> f i = k"
    for f :: "nat \<Rightarrow> int" and k :: int
  apply (cut_tac n = "n-m" and f = "\<lambda>i. f (i + m)" and k = k in int_val_lemma)
  unfolding One_nat_def
  apply simp
  apply (erule exE)
  apply (rule_tac x = "i+m" in exI)
  apply arith
  done


subsection \<open>Products and 1, by T. M. Rasmussen\<close>

lemma abs_zmult_eq_1:
  fixes m n :: int
  assumes mn: "\<bar>m * n\<bar> = 1"
  shows "\<bar>m\<bar> = 1"
proof -
  from mn have 0: "m \<noteq> 0" "n \<noteq> 0" by auto
  have "\<not> 2 \<le> \<bar>m\<bar>"
  proof
    assume "2 \<le> \<bar>m\<bar>"
    then have "2 * \<bar>n\<bar> \<le> \<bar>m\<bar> * \<bar>n\<bar>" by (simp add: mult_mono 0)
    also have "\<dots> = \<bar>m * n\<bar>" by (simp add: abs_mult)
    also from mn have "\<dots> = 1" by simp
    finally have "2 * \<bar>n\<bar> \<le> 1" .
    with 0 show "False" by arith
  qed
  with 0 show ?thesis by auto
qed

lemma pos_zmult_eq_1_iff_lemma: "m * n = 1 \<Longrightarrow> m = 1 \<or> m = - 1"
  for m n :: int
  using abs_zmult_eq_1 [of m n] by arith

lemma pos_zmult_eq_1_iff:
  fixes m n :: int
  assumes "0 < m"
  shows "m * n = 1 \<longleftrightarrow> m = 1 \<and> n = 1"
proof -
  from assms have "m * n = 1 \<Longrightarrow> m = 1"
    by (auto dest: pos_zmult_eq_1_iff_lemma)
  then show ?thesis
    by (auto dest: pos_zmult_eq_1_iff_lemma)
qed

lemma zmult_eq_1_iff: "m * n = 1 \<longleftrightarrow> (m = 1 \<and> n = 1) \<or> (m = - 1 \<and> n = - 1)"
  for m n :: int
  apply (rule iffI)
   apply (frule pos_zmult_eq_1_iff_lemma)
   apply (simp add: mult.commute [of m])
   apply (frule pos_zmult_eq_1_iff_lemma)
   apply auto
  done

lemma infinite_UNIV_int: "\<not> finite (UNIV::int set)"
proof
  assume "finite (UNIV::int set)"
  moreover have "inj (\<lambda>i::int. 2 * i)"
    by (rule injI) simp
  ultimately have "surj (\<lambda>i::int. 2 * i)"
    by (rule finite_UNIV_inj_surj)
  then obtain i :: int where "1 = 2 * i" by (rule surjE)
  then show False by (simp add: pos_zmult_eq_1_iff)
qed


subsection \<open>Further theorems on numerals\<close>

subsubsection \<open>Special Simplification for Constants\<close>

text \<open>These distributive laws move literals inside sums and differences.\<close>

lemmas distrib_right_numeral [simp] = distrib_right [of _ _ "numeral v"] for v
lemmas distrib_left_numeral [simp] = distrib_left [of "numeral v"] for v
lemmas left_diff_distrib_numeral [simp] = left_diff_distrib [of _ _ "numeral v"] for v
lemmas right_diff_distrib_numeral [simp] = right_diff_distrib [of "numeral v"] for v

text \<open>These are actually for fields, like real: but where else to put them?\<close>

lemmas zero_less_divide_iff_numeral [simp, no_atp] = zero_less_divide_iff [of "numeral w"] for w
lemmas divide_less_0_iff_numeral [simp, no_atp] = divide_less_0_iff [of "numeral w"] for w
lemmas zero_le_divide_iff_numeral [simp, no_atp] = zero_le_divide_iff [of "numeral w"] for w
lemmas divide_le_0_iff_numeral [simp, no_atp] = divide_le_0_iff [of "numeral w"] for w


text \<open>Replaces \<open>inverse #nn\<close> by \<open>1/#nn\<close>.  It looks
  strange, but then other simprocs simplify the quotient.\<close>

lemmas inverse_eq_divide_numeral [simp] =
  inverse_eq_divide [of "numeral w"] for w

lemmas inverse_eq_divide_neg_numeral [simp] =
  inverse_eq_divide [of "- numeral w"] for w

text \<open>These laws simplify inequalities, moving unary minus from a term
  into the literal.\<close>

lemmas equation_minus_iff_numeral [no_atp] =
  equation_minus_iff [of "numeral v"] for v

lemmas minus_equation_iff_numeral [no_atp] =
  minus_equation_iff [of _ "numeral v"] for v

lemmas le_minus_iff_numeral [no_atp] =
  le_minus_iff [of "numeral v"] for v

lemmas minus_le_iff_numeral [no_atp] =
  minus_le_iff [of _ "numeral v"] for v

lemmas less_minus_iff_numeral [no_atp] =
  less_minus_iff [of "numeral v"] for v

lemmas minus_less_iff_numeral [no_atp] =
  minus_less_iff [of _ "numeral v"] for v

(* FIXME maybe simproc *)


text \<open>Cancellation of constant factors in comparisons (\<open><\<close> and \<open>\<le>\<close>)\<close>

lemmas mult_less_cancel_left_numeral [simp, no_atp] = mult_less_cancel_left [of "numeral v"] for v
lemmas mult_less_cancel_right_numeral [simp, no_atp] = mult_less_cancel_right [of _ "numeral v"] for v
lemmas mult_le_cancel_left_numeral [simp, no_atp] = mult_le_cancel_left [of "numeral v"] for v
lemmas mult_le_cancel_right_numeral [simp, no_atp] = mult_le_cancel_right [of _ "numeral v"] for v


text \<open>Multiplying out constant divisors in comparisons (\<open><\<close>, \<open>\<le>\<close> and \<open>=\<close>)\<close>

named_theorems divide_const_simps "simplification rules to simplify comparisons involving constant divisors"

lemmas le_divide_eq_numeral1 [simp,divide_const_simps] =
  pos_le_divide_eq [of "numeral w", OF zero_less_numeral]
  neg_le_divide_eq [of "- numeral w", OF neg_numeral_less_zero] for w

lemmas divide_le_eq_numeral1 [simp,divide_const_simps] =
  pos_divide_le_eq [of "numeral w", OF zero_less_numeral]
  neg_divide_le_eq [of "- numeral w", OF neg_numeral_less_zero] for w

lemmas less_divide_eq_numeral1 [simp,divide_const_simps] =
  pos_less_divide_eq [of "numeral w", OF zero_less_numeral]
  neg_less_divide_eq [of "- numeral w", OF neg_numeral_less_zero] for w

lemmas divide_less_eq_numeral1 [simp,divide_const_simps] =
  pos_divide_less_eq [of "numeral w", OF zero_less_numeral]
  neg_divide_less_eq [of "- numeral w", OF neg_numeral_less_zero] for w

lemmas eq_divide_eq_numeral1 [simp,divide_const_simps] =
  eq_divide_eq [of _ _ "numeral w"]
  eq_divide_eq [of _ _ "- numeral w"] for w

lemmas divide_eq_eq_numeral1 [simp,divide_const_simps] =
  divide_eq_eq [of _ "numeral w"]
  divide_eq_eq [of _ "- numeral w"] for w


subsubsection \<open>Optional Simplification Rules Involving Constants\<close>

text \<open>Simplify quotients that are compared with a literal constant.\<close>

lemmas le_divide_eq_numeral [divide_const_simps] =
  le_divide_eq [of "numeral w"]
  le_divide_eq [of "- numeral w"] for w

lemmas divide_le_eq_numeral [divide_const_simps] =
  divide_le_eq [of _ _ "numeral w"]
  divide_le_eq [of _ _ "- numeral w"] for w

lemmas less_divide_eq_numeral [divide_const_simps] =
  less_divide_eq [of "numeral w"]
  less_divide_eq [of "- numeral w"] for w

lemmas divide_less_eq_numeral [divide_const_simps] =
  divide_less_eq [of _ _ "numeral w"]
  divide_less_eq [of _ _ "- numeral w"] for w

lemmas eq_divide_eq_numeral [divide_const_simps] =
  eq_divide_eq [of "numeral w"]
  eq_divide_eq [of "- numeral w"] for w

lemmas divide_eq_eq_numeral [divide_const_simps] =
  divide_eq_eq [of _ _ "numeral w"]
  divide_eq_eq [of _ _ "- numeral w"] for w


text \<open>Not good as automatic simprules because they cause case splits.\<close>
lemmas [divide_const_simps] =
  le_divide_eq_1 divide_le_eq_1 less_divide_eq_1 divide_less_eq_1


subsection \<open>The divides relation\<close>

lemma zdvd_antisym_nonneg: "0 \<le> m \<Longrightarrow> 0 \<le> n \<Longrightarrow> m dvd n \<Longrightarrow> n dvd m \<Longrightarrow> m = n"
  for m n :: int
  by (auto simp add: dvd_def mult.assoc zero_le_mult_iff zmult_eq_1_iff)

lemma zdvd_antisym_abs:
  fixes a b :: int
  assumes "a dvd b" and "b dvd a"
  shows "\<bar>a\<bar> = \<bar>b\<bar>"
proof (cases "a = 0")
  case True
  with assms show ?thesis by simp
next
  case False
  from \<open>a dvd b\<close> obtain k where k: "b = a * k"
    unfolding dvd_def by blast
  from \<open>b dvd a\<close> obtain k' where k': "a = b * k'"
    unfolding dvd_def by blast
  from k k' have "a = a * k * k'" by simp
  with mult_cancel_left1[where c="a" and b="k*k'"] have kk': "k * k' = 1"
    using \<open>a \<noteq> 0\<close> by (simp add: mult.assoc)
  then have "k = 1 \<and> k' = 1 \<or> k = -1 \<and> k' = -1"
    by (simp add: zmult_eq_1_iff)
  with k k' show ?thesis by auto
qed

lemma zdvd_zdiffD: "k dvd m - n \<Longrightarrow> k dvd n \<Longrightarrow> k dvd m"
  for k m n :: int
  using dvd_add_right_iff [of k "- n" m] by simp

lemma zdvd_reduce: "k dvd n + k * m \<longleftrightarrow> k dvd n"
  for k m n :: int
  using dvd_add_times_triv_right_iff [of k n m] by (simp add: ac_simps)

lemma dvd_imp_le_int:
  fixes d i :: int
  assumes "i \<noteq> 0" and "d dvd i"
  shows "\<bar>d\<bar> \<le> \<bar>i\<bar>"
proof -
  from \<open>d dvd i\<close> obtain k where "i = d * k" ..
  with \<open>i \<noteq> 0\<close> have "k \<noteq> 0" by auto
  then have "1 \<le> \<bar>k\<bar>" and "0 \<le> \<bar>d\<bar>" by auto
  then have "\<bar>d\<bar> * 1 \<le> \<bar>d\<bar> * \<bar>k\<bar>" by (rule mult_left_mono)
  with \<open>i = d * k\<close> show ?thesis by (simp add: abs_mult)
qed

lemma zdvd_not_zless:
  fixes m n :: int
  assumes "0 < m" and "m < n"
  shows "\<not> n dvd m"
proof
  from assms have "0 < n" by auto
  assume "n dvd m" then obtain k where k: "m = n * k" ..
  with \<open>0 < m\<close> have "0 < n * k" by auto
  with \<open>0 < n\<close> have "0 < k" by (simp add: zero_less_mult_iff)
  with k \<open>0 < n\<close> \<open>m < n\<close> have "n * k < n * 1" by simp
  with \<open>0 < n\<close> \<open>0 < k\<close> show False unfolding mult_less_cancel_left by auto
qed

lemma zdvd_mult_cancel:
  fixes k m n :: int
  assumes d: "k * m dvd k * n"
    and "k \<noteq> 0"
  shows "m dvd n"
proof -
  from d obtain h where h: "k * n = k * m * h"
    unfolding dvd_def by blast
  have "n = m * h"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    with \<open>k \<noteq> 0\<close> have "k * n \<noteq> k * (m * h)" by simp
    with h show False
      by (simp add: mult.assoc)
  qed
  then show ?thesis by simp
qed

theorem zdvd_int: "x dvd y \<longleftrightarrow> int x dvd int y"
proof -
  have "x dvd y" if "int y = int x * k" for k
  proof (cases k)
    case (nonneg n)
    with that have "y = x * n"
      by (simp del: of_nat_mult add: of_nat_mult [symmetric])
    then show ?thesis ..
  next
    case (neg n)
    with that have "int y = int x * (- int (Suc n))"
      by simp
    also have "\<dots> = - (int x * int (Suc n))"
      by (simp only: mult_minus_right)
    also have "\<dots> = - int (x * Suc n)"
      by (simp only: of_nat_mult [symmetric])
    finally have "- int (x * Suc n) = int y" ..
    then show ?thesis
      by (simp only: negative_eq_positive) auto
  qed
  then show ?thesis
    by (auto elim!: dvdE simp only: dvd_triv_left of_nat_mult)
qed

lemma zdvd1_eq[simp]: "x dvd 1 \<longleftrightarrow> \<bar>x\<bar> = 1"
  (is "?lhs \<longleftrightarrow> ?rhs")
  for x :: int
proof
  assume ?lhs
  then have "int (nat \<bar>x\<bar>) dvd int (nat 1)" by simp
  then have "nat \<bar>x\<bar> dvd 1" by (simp add: zdvd_int)
  then have "nat \<bar>x\<bar> = 1" by simp
  then show ?rhs by (cases "x < 0") auto
next
  assume ?rhs
  then have "x = 1 \<or> x = - 1" by auto
  then show ?lhs by (auto intro: dvdI)
qed

lemma zdvd_mult_cancel1:
  fixes m :: int
  assumes mp: "m \<noteq> 0"
  shows "m * n dvd m \<longleftrightarrow> \<bar>n\<bar> = 1"
    (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?rhs
  then show ?lhs
    by (cases "n > 0") (auto simp add: minus_equation_iff)
next
  assume ?lhs
  then have "m * n dvd m * 1" by simp
  from zdvd_mult_cancel[OF this mp] show ?rhs
    by (simp only: zdvd1_eq)
qed

lemma int_dvd_iff: "int m dvd z \<longleftrightarrow> m dvd nat \<bar>z\<bar>"
  by (cases "z \<ge> 0") (simp_all add: zdvd_int)

lemma dvd_int_iff: "z dvd int m \<longleftrightarrow> nat \<bar>z\<bar> dvd m"
  by (cases "z \<ge> 0") (simp_all add: zdvd_int)

lemma dvd_int_unfold_dvd_nat: "k dvd l \<longleftrightarrow> nat \<bar>k\<bar> dvd nat \<bar>l\<bar>"
  by (simp add: dvd_int_iff [symmetric])

lemma nat_dvd_iff: "nat z dvd m \<longleftrightarrow> (if 0 \<le> z then z dvd int m else m = 0)"
  by (auto simp add: dvd_int_iff)

lemma eq_nat_nat_iff: "0 \<le> z \<Longrightarrow> 0 \<le> z' \<Longrightarrow> nat z = nat z' \<longleftrightarrow> z = z'"
  by (auto elim!: nonneg_eq_int)

lemma nat_power_eq: "0 \<le> z \<Longrightarrow> nat (z ^ n) = nat z ^ n"
  by (induct n) (simp_all add: nat_mult_distrib)

lemma zdvd_imp_le: "z dvd n \<Longrightarrow> 0 < n \<Longrightarrow> z \<le> n"
  for n z :: int
  apply (cases n)
   apply (auto simp add: dvd_int_iff)
  apply (cases z)
   apply (auto simp add: dvd_imp_le)
  done

lemma zdvd_period:
  fixes a d :: int
  assumes "a dvd d"
  shows "a dvd (x + t) \<longleftrightarrow> a dvd ((x + c * d) + t)"
    (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  from assms obtain k where "d = a * k" by (rule dvdE)
  show ?thesis
  proof
    assume ?lhs
    then obtain l where "x + t = a * l" by (rule dvdE)
    then have "x = a * l - t" by simp
    with \<open>d = a * k\<close> show ?rhs by simp
  next
    assume ?rhs
    then obtain l where "x + c * d + t = a * l" by (rule dvdE)
    then have "x = a * l - c * d - t" by simp
    with \<open>d = a * k\<close> show ?lhs by simp
  qed
qed


subsection \<open>Finiteness of intervals\<close>

lemma finite_interval_int1 [iff]: "finite {i :: int. a \<le> i \<and> i \<le> b}"
proof (cases "a \<le> b")
  case True
  then show ?thesis
  proof (induct b rule: int_ge_induct)
    case base
    have "{i. a \<le> i \<and> i \<le> a} = {a}" by auto
    then show ?case by simp
  next
    case (step b)
    then have "{i. a \<le> i \<and> i \<le> b + 1} = {i. a \<le> i \<and> i \<le> b} \<union> {b + 1}" by auto
    with step show ?case by simp
  qed
next
  case False
  then show ?thesis
    by (metis (lifting, no_types) Collect_empty_eq finite.emptyI order_trans)
qed

lemma finite_interval_int2 [iff]: "finite {i :: int. a \<le> i \<and> i < b}"
  by (rule rev_finite_subset[OF finite_interval_int1[of "a" "b"]]) auto

lemma finite_interval_int3 [iff]: "finite {i :: int. a < i \<and> i \<le> b}"
  by (rule rev_finite_subset[OF finite_interval_int1[of "a" "b"]]) auto

lemma finite_interval_int4 [iff]: "finite {i :: int. a < i \<and> i < b}"
  by (rule rev_finite_subset[OF finite_interval_int1[of "a" "b"]]) auto


subsection \<open>Configuration of the code generator\<close>

text \<open>Constructors\<close>

definition Pos :: "num \<Rightarrow> int"
  where [simp, code_abbrev]: "Pos = numeral"

definition Neg :: "num \<Rightarrow> int"
  where [simp, code_abbrev]: "Neg n = - (Pos n)"

code_datatype "0::int" Pos Neg


text \<open>Auxiliary operations.\<close>

definition dup :: "int \<Rightarrow> int"
  where [simp]: "dup k = k + k"

lemma dup_code [code]:
  "dup 0 = 0"
  "dup (Pos n) = Pos (Num.Bit0 n)"
  "dup (Neg n) = Neg (Num.Bit0 n)"
  by (simp_all add: numeral_Bit0)

definition sub :: "num \<Rightarrow> num \<Rightarrow> int"
  where [simp]: "sub m n = numeral m - numeral n"

lemma sub_code [code]:
  "sub Num.One Num.One = 0"
  "sub (Num.Bit0 m) Num.One = Pos (Num.BitM m)"
  "sub (Num.Bit1 m) Num.One = Pos (Num.Bit0 m)"
  "sub Num.One (Num.Bit0 n) = Neg (Num.BitM n)"
  "sub Num.One (Num.Bit1 n) = Neg (Num.Bit0 n)"
  "sub (Num.Bit0 m) (Num.Bit0 n) = dup (sub m n)"
  "sub (Num.Bit1 m) (Num.Bit1 n) = dup (sub m n)"
  "sub (Num.Bit1 m) (Num.Bit0 n) = dup (sub m n) + 1"
  "sub (Num.Bit0 m) (Num.Bit1 n) = dup (sub m n) - 1"
          apply (simp_all only: sub_def dup_def numeral.simps Pos_def Neg_def numeral_BitM)
        apply (simp_all only: algebra_simps minus_diff_eq)
  apply (simp_all only: add.commute [of _ "- (numeral n + numeral n)"])
  apply (simp_all only: minus_add add.assoc left_minus)
  done

text \<open>Implementations.\<close>

lemma one_int_code [code, code_unfold]: "1 = Pos Num.One"
  by simp

lemma plus_int_code [code]:
  "k + 0 = k"
  "0 + l = l"
  "Pos m + Pos n = Pos (m + n)"
  "Pos m + Neg n = sub m n"
  "Neg m + Pos n = sub n m"
  "Neg m + Neg n = Neg (m + n)"
  for k l :: int
  by simp_all

lemma uminus_int_code [code]:
  "uminus 0 = (0::int)"
  "uminus (Pos m) = Neg m"
  "uminus (Neg m) = Pos m"
  by simp_all

lemma minus_int_code [code]:
  "k - 0 = k"
  "0 - l = uminus l"
  "Pos m - Pos n = sub m n"
  "Pos m - Neg n = Pos (m + n)"
  "Neg m - Pos n = Neg (m + n)"
  "Neg m - Neg n = sub n m"
  for k l :: int
  by simp_all

lemma times_int_code [code]:
  "k * 0 = 0"
  "0 * l = 0"
  "Pos m * Pos n = Pos (m * n)"
  "Pos m * Neg n = Neg (m * n)"
  "Neg m * Pos n = Neg (m * n)"
  "Neg m * Neg n = Pos (m * n)"
  for k l :: int
  by simp_all

instantiation int :: equal
begin

definition "HOL.equal k l \<longleftrightarrow> k = (l::int)"

instance
  by standard (rule equal_int_def)

end

lemma equal_int_code [code]:
  "HOL.equal 0 (0::int) \<longleftrightarrow> True"
  "HOL.equal 0 (Pos l) \<longleftrightarrow> False"
  "HOL.equal 0 (Neg l) \<longleftrightarrow> False"
  "HOL.equal (Pos k) 0 \<longleftrightarrow> False"
  "HOL.equal (Pos k) (Pos l) \<longleftrightarrow> HOL.equal k l"
  "HOL.equal (Pos k) (Neg l) \<longleftrightarrow> False"
  "HOL.equal (Neg k) 0 \<longleftrightarrow> False"
  "HOL.equal (Neg k) (Pos l) \<longleftrightarrow> False"
  "HOL.equal (Neg k) (Neg l) \<longleftrightarrow> HOL.equal k l"
  by (auto simp add: equal)

lemma equal_int_refl [code nbe]: "HOL.equal k k \<longleftrightarrow> True"
  for k :: int
  by (fact equal_refl)

lemma less_eq_int_code [code]:
  "0 \<le> (0::int) \<longleftrightarrow> True"
  "0 \<le> Pos l \<longleftrightarrow> True"
  "0 \<le> Neg l \<longleftrightarrow> False"
  "Pos k \<le> 0 \<longleftrightarrow> False"
  "Pos k \<le> Pos l \<longleftrightarrow> k \<le> l"
  "Pos k \<le> Neg l \<longleftrightarrow> False"
  "Neg k \<le> 0 \<longleftrightarrow> True"
  "Neg k \<le> Pos l \<longleftrightarrow> True"
  "Neg k \<le> Neg l \<longleftrightarrow> l \<le> k"
  by simp_all

lemma less_int_code [code]:
  "0 < (0::int) \<longleftrightarrow> False"
  "0 < Pos l \<longleftrightarrow> True"
  "0 < Neg l \<longleftrightarrow> False"
  "Pos k < 0 \<longleftrightarrow> False"
  "Pos k < Pos l \<longleftrightarrow> k < l"
  "Pos k < Neg l \<longleftrightarrow> False"
  "Neg k < 0 \<longleftrightarrow> True"
  "Neg k < Pos l \<longleftrightarrow> True"
  "Neg k < Neg l \<longleftrightarrow> l < k"
  by simp_all

lemma nat_code [code]:
  "nat (Int.Neg k) = 0"
  "nat 0 = 0"
  "nat (Int.Pos k) = nat_of_num k"
  by (simp_all add: nat_of_num_numeral)

lemma (in ring_1) of_int_code [code]:
  "of_int (Int.Neg k) = - numeral k"
  "of_int 0 = 0"
  "of_int (Int.Pos k) = numeral k"
  by simp_all


text \<open>Serializer setup.\<close>

code_identifier
  code_module Int \<rightharpoonup> (SML) Arith and (OCaml) Arith and (Haskell) Arith

quickcheck_params [default_type = int]

hide_const (open) Pos Neg sub dup


text \<open>De-register \<open>int\<close> as a quotient type:\<close>

lifting_update int.lifting
lifting_forget int.lifting

end
