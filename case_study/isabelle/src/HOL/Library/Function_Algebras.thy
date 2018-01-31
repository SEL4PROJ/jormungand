(*  Title:      HOL/Library/Function_Algebras.thy
    Author:     Jeremy Avigad and Kevin Donnelly; Florian Haftmann, TUM
*)

section \<open>Pointwise instantiation of functions to algebra type classes\<close>

theory Function_Algebras
imports Main
begin

text \<open>Pointwise operations\<close>

instantiation "fun" :: (type, plus) plus
begin

definition "f + g = (\<lambda>x. f x + g x)"
instance ..

end

lemma plus_fun_apply [simp]:
  "(f + g) x = f x + g x"
  by (simp add: plus_fun_def)

instantiation "fun" :: (type, zero) zero
begin

definition "0 = (\<lambda>x. 0)"
instance ..

end

lemma zero_fun_apply [simp]:
  "0 x = 0"
  by (simp add: zero_fun_def)

instantiation "fun" :: (type, times) times
begin

definition "f * g = (\<lambda>x. f x * g x)"
instance ..

end

lemma times_fun_apply [simp]:
  "(f * g) x = f x * g x"
  by (simp add: times_fun_def)

instantiation "fun" :: (type, one) one
begin

definition "1 = (\<lambda>x. 1)"
instance ..

end

lemma one_fun_apply [simp]:
  "1 x = 1"
  by (simp add: one_fun_def)


text \<open>Additive structures\<close>

instance "fun" :: (type, semigroup_add) semigroup_add
  by standard (simp add: fun_eq_iff add.assoc)

instance "fun" :: (type, cancel_semigroup_add) cancel_semigroup_add
  by standard (simp_all add: fun_eq_iff)

instance "fun" :: (type, ab_semigroup_add) ab_semigroup_add
  by standard (simp add: fun_eq_iff add.commute)

instance "fun" :: (type, cancel_ab_semigroup_add) cancel_ab_semigroup_add
  by standard (simp_all add: fun_eq_iff diff_diff_eq)

instance "fun" :: (type, monoid_add) monoid_add
  by standard (simp_all add: fun_eq_iff)

instance "fun" :: (type, comm_monoid_add) comm_monoid_add
  by standard simp

instance "fun" :: (type, cancel_comm_monoid_add) cancel_comm_monoid_add ..

instance "fun" :: (type, group_add) group_add
  by standard (simp_all add: fun_eq_iff)

instance "fun" :: (type, ab_group_add) ab_group_add
  by standard simp_all


text \<open>Multiplicative structures\<close>

instance "fun" :: (type, semigroup_mult) semigroup_mult
  by standard (simp add: fun_eq_iff mult.assoc)

instance "fun" :: (type, ab_semigroup_mult) ab_semigroup_mult
  by standard (simp add: fun_eq_iff mult.commute)

instance "fun" :: (type, monoid_mult) monoid_mult
  by standard (simp_all add: fun_eq_iff)

instance "fun" :: (type, comm_monoid_mult) comm_monoid_mult
  by standard simp


text \<open>Misc\<close>

instance "fun" :: (type, "Rings.dvd") "Rings.dvd" ..

instance "fun" :: (type, mult_zero) mult_zero
  by standard (simp_all add: fun_eq_iff)

instance "fun" :: (type, zero_neq_one) zero_neq_one
  by standard (simp add: fun_eq_iff)


text \<open>Ring structures\<close>

instance "fun" :: (type, semiring) semiring
  by standard (simp_all add: fun_eq_iff algebra_simps)

instance "fun" :: (type, comm_semiring) comm_semiring
  by standard (simp add: fun_eq_iff  algebra_simps)

instance "fun" :: (type, semiring_0) semiring_0 ..

instance "fun" :: (type, comm_semiring_0) comm_semiring_0 ..

instance "fun" :: (type, semiring_0_cancel) semiring_0_cancel ..

instance "fun" :: (type, comm_semiring_0_cancel) comm_semiring_0_cancel ..

instance "fun" :: (type, semiring_1) semiring_1 ..

lemma of_nat_fun: "of_nat n = (\<lambda>x::'a. of_nat n)"
proof -
  have comp: "comp = (\<lambda>f g x. f (g x))"
    by (rule ext)+ simp
  have plus_fun: "plus = (\<lambda>f g x. f x + g x)"
    by (rule ext, rule ext) (fact plus_fun_def)
  have "of_nat n = (comp (plus (1::'b)) ^^ n) (\<lambda>x::'a. 0)"
    by (simp add: of_nat_def plus_fun zero_fun_def one_fun_def comp)
  also have "... = comp ((plus 1) ^^ n) (\<lambda>x::'a. 0)"
    by (simp only: comp_funpow)
  finally show ?thesis by (simp add: of_nat_def comp)
qed

lemma of_nat_fun_apply [simp]:
  "of_nat n x = of_nat n"
  by (simp add: of_nat_fun)

instance "fun" :: (type, comm_semiring_1) comm_semiring_1 ..

instance "fun" :: (type, semiring_1_cancel) semiring_1_cancel ..

instance "fun" :: (type, comm_semiring_1_cancel) comm_semiring_1_cancel
  by standard (auto simp add: times_fun_def algebra_simps)

instance "fun" :: (type, semiring_char_0) semiring_char_0
proof
  from inj_of_nat have "inj (\<lambda>n (x::'a). of_nat n :: 'b)"
    by (rule inj_fun)
  then have "inj (\<lambda>n. of_nat n :: 'a \<Rightarrow> 'b)"
    by (simp add: of_nat_fun)
  then show "inj (of_nat :: nat \<Rightarrow> 'a \<Rightarrow> 'b)" .
qed

instance "fun" :: (type, ring) ring ..

instance "fun" :: (type, comm_ring) comm_ring ..

instance "fun" :: (type, ring_1) ring_1 ..

instance "fun" :: (type, comm_ring_1) comm_ring_1 ..

instance "fun" :: (type, ring_char_0) ring_char_0 ..


text \<open>Ordered structures\<close>

instance "fun" :: (type, ordered_ab_semigroup_add) ordered_ab_semigroup_add
  by standard (auto simp add: le_fun_def intro: add_left_mono)

instance "fun" :: (type, ordered_cancel_ab_semigroup_add) ordered_cancel_ab_semigroup_add ..

instance "fun" :: (type, ordered_ab_semigroup_add_imp_le) ordered_ab_semigroup_add_imp_le
  by standard (simp add: le_fun_def)

instance "fun" :: (type, ordered_comm_monoid_add) ordered_comm_monoid_add ..

instance "fun" :: (type, ordered_cancel_comm_monoid_add) ordered_cancel_comm_monoid_add ..

instance "fun" :: (type, ordered_ab_group_add) ordered_ab_group_add ..

instance "fun" :: (type, ordered_semiring) ordered_semiring
  by standard (auto simp add: le_fun_def intro: mult_left_mono mult_right_mono)

instance "fun" :: (type, dioid) dioid
proof standard
  fix a b :: "'a \<Rightarrow> 'b"
  show "a \<le> b \<longleftrightarrow> (\<exists>c. b = a + c)"
    unfolding le_fun_def plus_fun_def fun_eq_iff choice_iff[symmetric, of "\<lambda>x c. b x = a x + c"]
    by (intro arg_cong[where f=All] ext canonically_ordered_monoid_add_class.le_iff_add)
qed

instance "fun" :: (type, ordered_comm_semiring) ordered_comm_semiring
  by standard (fact mult_left_mono)

instance "fun" :: (type, ordered_cancel_semiring) ordered_cancel_semiring ..

instance "fun" :: (type, ordered_cancel_comm_semiring) ordered_cancel_comm_semiring ..

instance "fun" :: (type, ordered_ring) ordered_ring ..

instance "fun" :: (type, ordered_comm_ring) ordered_comm_ring ..


lemmas func_plus = plus_fun_def
lemmas func_zero = zero_fun_def
lemmas func_times = times_fun_def
lemmas func_one = one_fun_def

end

