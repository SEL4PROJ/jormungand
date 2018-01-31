(*  Title:      HOL/Real_Vector_Spaces.thy
    Author:     Brian Huffman
    Author:     Johannes Hölzl
*)

section \<open>Vector Spaces and Algebras over the Reals\<close>

theory Real_Vector_Spaces
imports Real Topological_Spaces
begin

subsection \<open>Locale for additive functions\<close>

locale additive =
  fixes f :: "'a::ab_group_add \<Rightarrow> 'b::ab_group_add"
  assumes add: "f (x + y) = f x + f y"
begin

lemma zero: "f 0 = 0"
proof -
  have "f 0 = f (0 + 0)" by simp
  also have "\<dots> = f 0 + f 0" by (rule add)
  finally show "f 0 = 0" by simp
qed

lemma minus: "f (- x) = - f x"
proof -
  have "f (- x) + f x = f (- x + x)" by (rule add [symmetric])
  also have "\<dots> = - f x + f x" by (simp add: zero)
  finally show "f (- x) = - f x" by (rule add_right_imp_eq)
qed

lemma diff: "f (x - y) = f x - f y"
  using add [of x "- y"] by (simp add: minus)

lemma sum: "f (sum g A) = (\<Sum>x\<in>A. f (g x))"
  by (induct A rule: infinite_finite_induct) (simp_all add: zero add)

end


subsection \<open>Vector spaces\<close>

locale vector_space =
  fixes scale :: "'a::field \<Rightarrow> 'b::ab_group_add \<Rightarrow> 'b"
  assumes scale_right_distrib [algebra_simps]: "scale a (x + y) = scale a x + scale a y"
    and scale_left_distrib [algebra_simps]: "scale (a + b) x = scale a x + scale b x"
    and scale_scale [simp]: "scale a (scale b x) = scale (a * b) x"
    and scale_one [simp]: "scale 1 x = x"
begin

lemma scale_left_commute: "scale a (scale b x) = scale b (scale a x)"
  by (simp add: mult.commute)

lemma scale_zero_left [simp]: "scale 0 x = 0"
  and scale_minus_left [simp]: "scale (- a) x = - (scale a x)"
  and scale_left_diff_distrib [algebra_simps]: "scale (a - b) x = scale a x - scale b x"
  and scale_sum_left: "scale (sum f A) x = (\<Sum>a\<in>A. scale (f a) x)"
proof -
  interpret s: additive "\<lambda>a. scale a x"
    by standard (rule scale_left_distrib)
  show "scale 0 x = 0" by (rule s.zero)
  show "scale (- a) x = - (scale a x)" by (rule s.minus)
  show "scale (a - b) x = scale a x - scale b x" by (rule s.diff)
  show "scale (sum f A) x = (\<Sum>a\<in>A. scale (f a) x)" by (rule s.sum)
qed

lemma scale_zero_right [simp]: "scale a 0 = 0"
  and scale_minus_right [simp]: "scale a (- x) = - (scale a x)"
  and scale_right_diff_distrib [algebra_simps]: "scale a (x - y) = scale a x - scale a y"
  and scale_sum_right: "scale a (sum f A) = (\<Sum>x\<in>A. scale a (f x))"
proof -
  interpret s: additive "\<lambda>x. scale a x"
    by standard (rule scale_right_distrib)
  show "scale a 0 = 0" by (rule s.zero)
  show "scale a (- x) = - (scale a x)" by (rule s.minus)
  show "scale a (x - y) = scale a x - scale a y" by (rule s.diff)
  show "scale a (sum f A) = (\<Sum>x\<in>A. scale a (f x))" by (rule s.sum)
qed

lemma scale_eq_0_iff [simp]: "scale a x = 0 \<longleftrightarrow> a = 0 \<or> x = 0"
proof (cases "a = 0")
  case True
  then show ?thesis by simp
next
  case False
  have "x = 0" if "scale a x = 0"
  proof -
    from False that have "scale (inverse a) (scale a x) = 0" by simp
    with False show ?thesis by simp
  qed
  then show ?thesis by force
qed

lemma scale_left_imp_eq:
  assumes nonzero: "a \<noteq> 0"
    and scale: "scale a x = scale a y"
  shows "x = y"
proof -
  from scale have "scale a (x - y) = 0"
     by (simp add: scale_right_diff_distrib)
  with nonzero have "x - y = 0" by simp
  then show "x = y" by (simp only: right_minus_eq)
qed

lemma scale_right_imp_eq:
  assumes nonzero: "x \<noteq> 0"
    and scale: "scale a x = scale b x"
  shows "a = b"
proof -
  from scale have "scale (a - b) x = 0"
     by (simp add: scale_left_diff_distrib)
  with nonzero have "a - b = 0" by simp
  then show "a = b" by (simp only: right_minus_eq)
qed

lemma scale_cancel_left [simp]: "scale a x = scale a y \<longleftrightarrow> x = y \<or> a = 0"
  by (auto intro: scale_left_imp_eq)

lemma scale_cancel_right [simp]: "scale a x = scale b x \<longleftrightarrow> a = b \<or> x = 0"
  by (auto intro: scale_right_imp_eq)

end


subsection \<open>Real vector spaces\<close>

class scaleR =
  fixes scaleR :: "real \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "*\<^sub>R" 75)
begin

abbreviation divideR :: "'a \<Rightarrow> real \<Rightarrow> 'a"  (infixl "'/\<^sub>R" 70)
  where "x /\<^sub>R r \<equiv> scaleR (inverse r) x"

end

class real_vector = scaleR + ab_group_add +
  assumes scaleR_add_right: "scaleR a (x + y) = scaleR a x + scaleR a y"
  and scaleR_add_left: "scaleR (a + b) x = scaleR a x + scaleR b x"
  and scaleR_scaleR: "scaleR a (scaleR b x) = scaleR (a * b) x"
  and scaleR_one: "scaleR 1 x = x"

interpretation real_vector: vector_space "scaleR :: real \<Rightarrow> 'a \<Rightarrow> 'a::real_vector"
  apply unfold_locales
     apply (rule scaleR_add_right)
    apply (rule scaleR_add_left)
   apply (rule scaleR_scaleR)
  apply (rule scaleR_one)
  done

text \<open>Recover original theorem names\<close>

lemmas scaleR_left_commute = real_vector.scale_left_commute
lemmas scaleR_zero_left = real_vector.scale_zero_left
lemmas scaleR_minus_left = real_vector.scale_minus_left
lemmas scaleR_diff_left = real_vector.scale_left_diff_distrib
lemmas scaleR_sum_left = real_vector.scale_sum_left
lemmas scaleR_zero_right = real_vector.scale_zero_right
lemmas scaleR_minus_right = real_vector.scale_minus_right
lemmas scaleR_diff_right = real_vector.scale_right_diff_distrib
lemmas scaleR_sum_right = real_vector.scale_sum_right
lemmas scaleR_eq_0_iff = real_vector.scale_eq_0_iff
lemmas scaleR_left_imp_eq = real_vector.scale_left_imp_eq
lemmas scaleR_right_imp_eq = real_vector.scale_right_imp_eq
lemmas scaleR_cancel_left = real_vector.scale_cancel_left
lemmas scaleR_cancel_right = real_vector.scale_cancel_right

text \<open>Legacy names\<close>

lemmas scaleR_left_distrib = scaleR_add_left
lemmas scaleR_right_distrib = scaleR_add_right
lemmas scaleR_left_diff_distrib = scaleR_diff_left
lemmas scaleR_right_diff_distrib = scaleR_diff_right

lemma scaleR_minus1_left [simp]: "scaleR (-1) x = - x"
  for x :: "'a::real_vector"
  using scaleR_minus_left [of 1 x] by simp

class real_algebra = real_vector + ring +
  assumes mult_scaleR_left [simp]: "scaleR a x * y = scaleR a (x * y)"
    and mult_scaleR_right [simp]: "x * scaleR a y = scaleR a (x * y)"

class real_algebra_1 = real_algebra + ring_1

class real_div_algebra = real_algebra_1 + division_ring

class real_field = real_div_algebra + field

instantiation real :: real_field
begin

definition real_scaleR_def [simp]: "scaleR a x = a * x"

instance
  by standard (simp_all add: algebra_simps)

end

interpretation scaleR_left: additive "(\<lambda>a. scaleR a x :: 'a::real_vector)"
  by standard (rule scaleR_left_distrib)

interpretation scaleR_right: additive "(\<lambda>x. scaleR a x :: 'a::real_vector)"
  by standard (rule scaleR_right_distrib)

lemma nonzero_inverse_scaleR_distrib:
  "a \<noteq> 0 \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> inverse (scaleR a x) = scaleR (inverse a) (inverse x)"
  for x :: "'a::real_div_algebra"
  by (rule inverse_unique) simp

lemma inverse_scaleR_distrib: "inverse (scaleR a x) = scaleR (inverse a) (inverse x)"
  for x :: "'a::{real_div_algebra,division_ring}"
  apply (cases "a = 0")
   apply simp
  apply (cases "x = 0")
   apply simp
  apply (erule (1) nonzero_inverse_scaleR_distrib)
  done

lemma sum_constant_scaleR: "(\<Sum>x\<in>A. y) = of_nat (card A) *\<^sub>R y"
  for y :: "'a::real_vector"
  by (induct A rule: infinite_finite_induct) (simp_all add: algebra_simps)

named_theorems vector_add_divide_simps "to simplify sums of scaled vectors"

lemma [vector_add_divide_simps]:
  "v + (b / z) *\<^sub>R w = (if z = 0 then v else (z *\<^sub>R v + b *\<^sub>R w) /\<^sub>R z)"
  "a *\<^sub>R v + (b / z) *\<^sub>R w = (if z = 0 then a *\<^sub>R v else ((a * z) *\<^sub>R v + b *\<^sub>R w) /\<^sub>R z)"
  "(a / z) *\<^sub>R v + w = (if z = 0 then w else (a *\<^sub>R v + z *\<^sub>R w) /\<^sub>R z)"
  "(a / z) *\<^sub>R v + b *\<^sub>R w = (if z = 0 then b *\<^sub>R w else (a *\<^sub>R v + (b * z) *\<^sub>R w) /\<^sub>R z)"
  "v - (b / z) *\<^sub>R w = (if z = 0 then v else (z *\<^sub>R v - b *\<^sub>R w) /\<^sub>R z)"
  "a *\<^sub>R v - (b / z) *\<^sub>R w = (if z = 0 then a *\<^sub>R v else ((a * z) *\<^sub>R v - b *\<^sub>R w) /\<^sub>R z)"
  "(a / z) *\<^sub>R v - w = (if z = 0 then -w else (a *\<^sub>R v - z *\<^sub>R w) /\<^sub>R z)"
  "(a / z) *\<^sub>R v - b *\<^sub>R w = (if z = 0 then -b *\<^sub>R w else (a *\<^sub>R v - (b * z) *\<^sub>R w) /\<^sub>R z)"
  for v :: "'a :: real_vector"
  by (simp_all add: divide_inverse_commute scaleR_add_right real_vector.scale_right_diff_distrib)


lemma eq_vector_fraction_iff [vector_add_divide_simps]:
  fixes x :: "'a :: real_vector"
  shows "(x = (u / v) *\<^sub>R a) \<longleftrightarrow> (if v=0 then x = 0 else v *\<^sub>R x = u *\<^sub>R a)"
by auto (metis (no_types) divide_eq_1_iff divide_inverse_commute scaleR_one scaleR_scaleR)

lemma vector_fraction_eq_iff [vector_add_divide_simps]:
  fixes x :: "'a :: real_vector"
  shows "((u / v) *\<^sub>R a = x) \<longleftrightarrow> (if v=0 then x = 0 else u *\<^sub>R a = v *\<^sub>R x)"
by (metis eq_vector_fraction_iff)

lemma real_vector_affinity_eq:
  fixes x :: "'a :: real_vector"
  assumes m0: "m \<noteq> 0"
  shows "m *\<^sub>R x + c = y \<longleftrightarrow> x = inverse m *\<^sub>R y - (inverse m *\<^sub>R c)"
    (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then have "m *\<^sub>R x = y - c" by (simp add: field_simps)
  then have "inverse m *\<^sub>R (m *\<^sub>R x) = inverse m *\<^sub>R (y - c)" by simp
  then show "x = inverse m *\<^sub>R y - (inverse m *\<^sub>R c)"
    using m0
  by (simp add: real_vector.scale_right_diff_distrib)
next
  assume ?rhs
  with m0 show "m *\<^sub>R x + c = y"
    by (simp add: real_vector.scale_right_diff_distrib)
qed

lemma real_vector_eq_affinity: "m \<noteq> 0 \<Longrightarrow> y = m *\<^sub>R x + c \<longleftrightarrow> inverse m *\<^sub>R y - (inverse m *\<^sub>R c) = x"
  for x :: "'a::real_vector"
  using real_vector_affinity_eq[where m=m and x=x and y=y and c=c]
  by metis

lemma scaleR_eq_iff [simp]: "b + u *\<^sub>R a = a + u *\<^sub>R b \<longleftrightarrow> a = b \<or> u = 1"
  for a :: "'a::real_vector"
proof (cases "u = 1")
  case True
  then show ?thesis by auto
next
  case False
  have "a = b" if "b + u *\<^sub>R a = a + u *\<^sub>R b"
  proof -
    from that have "(u - 1) *\<^sub>R a = (u - 1) *\<^sub>R b"
      by (simp add: algebra_simps)
    with False show ?thesis
      by auto
  qed
  then show ?thesis by auto
qed

lemma scaleR_collapse [simp]: "(1 - u) *\<^sub>R a + u *\<^sub>R a = a"
  for a :: "'a::real_vector"
  by (simp add: algebra_simps)


subsection \<open>Embedding of the Reals into any \<open>real_algebra_1\<close>: \<open>of_real\<close>\<close>

definition of_real :: "real \<Rightarrow> 'a::real_algebra_1"
  where "of_real r = scaleR r 1"

lemma scaleR_conv_of_real: "scaleR r x = of_real r * x"
  by (simp add: of_real_def)

lemma of_real_0 [simp]: "of_real 0 = 0"
  by (simp add: of_real_def)

lemma of_real_1 [simp]: "of_real 1 = 1"
  by (simp add: of_real_def)

lemma of_real_add [simp]: "of_real (x + y) = of_real x + of_real y"
  by (simp add: of_real_def scaleR_left_distrib)

lemma of_real_minus [simp]: "of_real (- x) = - of_real x"
  by (simp add: of_real_def)

lemma of_real_diff [simp]: "of_real (x - y) = of_real x - of_real y"
  by (simp add: of_real_def scaleR_left_diff_distrib)

lemma of_real_mult [simp]: "of_real (x * y) = of_real x * of_real y"
  by (simp add: of_real_def mult.commute)

lemma of_real_sum[simp]: "of_real (sum f s) = (\<Sum>x\<in>s. of_real (f x))"
  by (induct s rule: infinite_finite_induct) auto

lemma of_real_prod[simp]: "of_real (prod f s) = (\<Prod>x\<in>s. of_real (f x))"
  by (induct s rule: infinite_finite_induct) auto

lemma nonzero_of_real_inverse:
  "x \<noteq> 0 \<Longrightarrow> of_real (inverse x) = inverse (of_real x :: 'a::real_div_algebra)"
  by (simp add: of_real_def nonzero_inverse_scaleR_distrib)

lemma of_real_inverse [simp]:
  "of_real (inverse x) = inverse (of_real x :: 'a::{real_div_algebra,division_ring})"
  by (simp add: of_real_def inverse_scaleR_distrib)

lemma nonzero_of_real_divide:
  "y \<noteq> 0 \<Longrightarrow> of_real (x / y) = (of_real x / of_real y :: 'a::real_field)"
  by (simp add: divide_inverse nonzero_of_real_inverse)

lemma of_real_divide [simp]:
  "of_real (x / y) = (of_real x / of_real y :: 'a::real_div_algebra)"
  by (simp add: divide_inverse)

lemma of_real_power [simp]:
  "of_real (x ^ n) = (of_real x :: 'a::{real_algebra_1}) ^ n"
  by (induct n) simp_all

lemma of_real_eq_iff [simp]: "of_real x = of_real y \<longleftrightarrow> x = y"
  by (simp add: of_real_def)

lemma inj_of_real: "inj of_real"
  by (auto intro: injI)

lemmas of_real_eq_0_iff [simp] = of_real_eq_iff [of _ 0, simplified]

lemma of_real_eq_id [simp]: "of_real = (id :: real \<Rightarrow> real)"
  by (rule ext) (simp add: of_real_def)

text \<open>Collapse nested embeddings.\<close>
lemma of_real_of_nat_eq [simp]: "of_real (of_nat n) = of_nat n"
  by (induct n) auto

lemma of_real_of_int_eq [simp]: "of_real (of_int z) = of_int z"
  by (cases z rule: int_diff_cases) simp

lemma of_real_numeral [simp]: "of_real (numeral w) = numeral w"
  using of_real_of_int_eq [of "numeral w"] by simp

lemma of_real_neg_numeral [simp]: "of_real (- numeral w) = - numeral w"
  using of_real_of_int_eq [of "- numeral w"] by simp

text \<open>Every real algebra has characteristic zero.\<close>
instance real_algebra_1 < ring_char_0
proof
  from inj_of_real inj_of_nat have "inj (of_real \<circ> of_nat)"
    by (rule inj_comp)
  then show "inj (of_nat :: nat \<Rightarrow> 'a)"
    by (simp add: comp_def)
qed

lemma fraction_scaleR_times [simp]:
  fixes a :: "'a::real_algebra_1"
  shows "(numeral u / numeral v) *\<^sub>R (numeral w * a) = (numeral u * numeral w / numeral v) *\<^sub>R a"
by (metis (no_types, lifting) of_real_numeral scaleR_conv_of_real scaleR_scaleR times_divide_eq_left)

lemma inverse_scaleR_times [simp]:
  fixes a :: "'a::real_algebra_1"
  shows "(1 / numeral v) *\<^sub>R (numeral w * a) = (numeral w / numeral v) *\<^sub>R a"
by (metis divide_inverse_commute inverse_eq_divide of_real_numeral scaleR_conv_of_real scaleR_scaleR)

lemma scaleR_times [simp]:
  fixes a :: "'a::real_algebra_1"
  shows "(numeral u) *\<^sub>R (numeral w * a) = (numeral u * numeral w) *\<^sub>R a"
by (simp add: scaleR_conv_of_real)

instance real_field < field_char_0 ..


subsection \<open>The Set of Real Numbers\<close>

definition Reals :: "'a::real_algebra_1 set"  ("\<real>")
  where "\<real> = range of_real"

lemma Reals_of_real [simp]: "of_real r \<in> \<real>"
  by (simp add: Reals_def)

lemma Reals_of_int [simp]: "of_int z \<in> \<real>"
  by (subst of_real_of_int_eq [symmetric], rule Reals_of_real)

lemma Reals_of_nat [simp]: "of_nat n \<in> \<real>"
  by (subst of_real_of_nat_eq [symmetric], rule Reals_of_real)

lemma Reals_numeral [simp]: "numeral w \<in> \<real>"
  by (subst of_real_numeral [symmetric], rule Reals_of_real)

lemma Reals_0 [simp]: "0 \<in> \<real>"
  apply (unfold Reals_def)
  apply (rule range_eqI)
  apply (rule of_real_0 [symmetric])
  done

lemma Reals_1 [simp]: "1 \<in> \<real>"
  apply (unfold Reals_def)
  apply (rule range_eqI)
  apply (rule of_real_1 [symmetric])
  done

lemma Reals_add [simp]: "a \<in> \<real> \<Longrightarrow> b \<in> \<real> \<Longrightarrow> a + b \<in> \<real>"
  apply (auto simp add: Reals_def)
  apply (rule range_eqI)
  apply (rule of_real_add [symmetric])
  done

lemma Reals_minus [simp]: "a \<in> \<real> \<Longrightarrow> - a \<in> \<real>"
  apply (auto simp add: Reals_def)
  apply (rule range_eqI)
  apply (rule of_real_minus [symmetric])
  done

lemma Reals_diff [simp]: "a \<in> \<real> \<Longrightarrow> b \<in> \<real> \<Longrightarrow> a - b \<in> \<real>"
  apply (auto simp add: Reals_def)
  apply (rule range_eqI)
  apply (rule of_real_diff [symmetric])
  done

lemma Reals_mult [simp]: "a \<in> \<real> \<Longrightarrow> b \<in> \<real> \<Longrightarrow> a * b \<in> \<real>"
  apply (auto simp add: Reals_def)
  apply (rule range_eqI)
  apply (rule of_real_mult [symmetric])
  done

lemma nonzero_Reals_inverse: "a \<in> \<real> \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> inverse a \<in> \<real>"
  for a :: "'a::real_div_algebra"
  apply (auto simp add: Reals_def)
  apply (rule range_eqI)
  apply (erule nonzero_of_real_inverse [symmetric])
  done

lemma Reals_inverse: "a \<in> \<real> \<Longrightarrow> inverse a \<in> \<real>"
  for a :: "'a::{real_div_algebra,division_ring}"
  apply (auto simp add: Reals_def)
  apply (rule range_eqI)
  apply (rule of_real_inverse [symmetric])
  done

lemma Reals_inverse_iff [simp]: "inverse x \<in> \<real> \<longleftrightarrow> x \<in> \<real>"
  for x :: "'a::{real_div_algebra,division_ring}"
  by (metis Reals_inverse inverse_inverse_eq)

lemma nonzero_Reals_divide: "a \<in> \<real> \<Longrightarrow> b \<in> \<real> \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> a / b \<in> \<real>"
  for a b :: "'a::real_field"
  apply (auto simp add: Reals_def)
  apply (rule range_eqI)
  apply (erule nonzero_of_real_divide [symmetric])
  done

lemma Reals_divide [simp]: "a \<in> \<real> \<Longrightarrow> b \<in> \<real> \<Longrightarrow> a / b \<in> \<real>"
  for a b :: "'a::{real_field,field}"
  apply (auto simp add: Reals_def)
  apply (rule range_eqI)
  apply (rule of_real_divide [symmetric])
  done

lemma Reals_power [simp]: "a \<in> \<real> \<Longrightarrow> a ^ n \<in> \<real>"
  for a :: "'a::real_algebra_1"
  apply (auto simp add: Reals_def)
  apply (rule range_eqI)
  apply (rule of_real_power [symmetric])
  done

lemma Reals_cases [cases set: Reals]:
  assumes "q \<in> \<real>"
  obtains (of_real) r where "q = of_real r"
  unfolding Reals_def
proof -
  from \<open>q \<in> \<real>\<close> have "q \<in> range of_real" unfolding Reals_def .
  then obtain r where "q = of_real r" ..
  then show thesis ..
qed

lemma sum_in_Reals [intro,simp]: "(\<And>i. i \<in> s \<Longrightarrow> f i \<in> \<real>) \<Longrightarrow> sum f s \<in> \<real>"
proof (induct s rule: infinite_finite_induct)
  case infinite
  then show ?case by (metis Reals_0 sum.infinite)
qed simp_all

lemma prod_in_Reals [intro,simp]: "(\<And>i. i \<in> s \<Longrightarrow> f i \<in> \<real>) \<Longrightarrow> prod f s \<in> \<real>"
proof (induct s rule: infinite_finite_induct)
  case infinite
  then show ?case by (metis Reals_1 prod.infinite)
qed simp_all

lemma Reals_induct [case_names of_real, induct set: Reals]:
  "q \<in> \<real> \<Longrightarrow> (\<And>r. P (of_real r)) \<Longrightarrow> P q"
  by (rule Reals_cases) auto


subsection \<open>Ordered real vector spaces\<close>

class ordered_real_vector = real_vector + ordered_ab_group_add +
  assumes scaleR_left_mono: "x \<le> y \<Longrightarrow> 0 \<le> a \<Longrightarrow> a *\<^sub>R x \<le> a *\<^sub>R y"
    and scaleR_right_mono: "a \<le> b \<Longrightarrow> 0 \<le> x \<Longrightarrow> a *\<^sub>R x \<le> b *\<^sub>R x"
begin

lemma scaleR_mono: "a \<le> b \<Longrightarrow> x \<le> y \<Longrightarrow> 0 \<le> b \<Longrightarrow> 0 \<le> x \<Longrightarrow> a *\<^sub>R x \<le> b *\<^sub>R y"
  apply (erule scaleR_right_mono [THEN order_trans])
   apply assumption
  apply (erule scaleR_left_mono)
  apply assumption
  done

lemma scaleR_mono': "a \<le> b \<Longrightarrow> c \<le> d \<Longrightarrow> 0 \<le> a \<Longrightarrow> 0 \<le> c \<Longrightarrow> a *\<^sub>R c \<le> b *\<^sub>R d"
  by (rule scaleR_mono) (auto intro: order.trans)

lemma pos_le_divideRI:
  assumes "0 < c"
    and "c *\<^sub>R a \<le> b"
  shows "a \<le> b /\<^sub>R c"
proof -
  from scaleR_left_mono[OF assms(2)] assms(1)
  have "c *\<^sub>R a /\<^sub>R c \<le> b /\<^sub>R c"
    by simp
  with assms show ?thesis
    by (simp add: scaleR_one scaleR_scaleR inverse_eq_divide)
qed

lemma pos_le_divideR_eq:
  assumes "0 < c"
  shows "a \<le> b /\<^sub>R c \<longleftrightarrow> c *\<^sub>R a \<le> b"
    (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  from scaleR_left_mono[OF this] assms have "c *\<^sub>R a \<le> c *\<^sub>R (b /\<^sub>R c)"
    by simp
  with assms show ?rhs
    by (simp add: scaleR_one scaleR_scaleR inverse_eq_divide)
next
  assume ?rhs
  with assms show ?lhs by (rule pos_le_divideRI)
qed

lemma scaleR_image_atLeastAtMost: "c > 0 \<Longrightarrow> scaleR c ` {x..y} = {c *\<^sub>R x..c *\<^sub>R y}"
  apply (auto intro!: scaleR_left_mono)
  apply (rule_tac x = "inverse c *\<^sub>R xa" in image_eqI)
   apply (simp_all add: pos_le_divideR_eq[symmetric] scaleR_scaleR scaleR_one)
  done

end

lemma neg_le_divideR_eq:
  fixes a :: "'a :: ordered_real_vector"
  assumes "c < 0"
  shows "a \<le> b /\<^sub>R c \<longleftrightarrow> b \<le> c *\<^sub>R a"
  using pos_le_divideR_eq [of "-c" a "-b"] assms by simp

lemma scaleR_nonneg_nonneg: "0 \<le> a \<Longrightarrow> 0 \<le> x \<Longrightarrow> 0 \<le> a *\<^sub>R x"
  for x :: "'a::ordered_real_vector"
  using scaleR_left_mono [of 0 x a] by simp

lemma scaleR_nonneg_nonpos: "0 \<le> a \<Longrightarrow> x \<le> 0 \<Longrightarrow> a *\<^sub>R x \<le> 0"
  for x :: "'a::ordered_real_vector"
  using scaleR_left_mono [of x 0 a] by simp

lemma scaleR_nonpos_nonneg: "a \<le> 0 \<Longrightarrow> 0 \<le> x \<Longrightarrow> a *\<^sub>R x \<le> 0"
  for x :: "'a::ordered_real_vector"
  using scaleR_right_mono [of a 0 x] by simp

lemma split_scaleR_neg_le: "(0 \<le> a \<and> x \<le> 0) \<or> (a \<le> 0 \<and> 0 \<le> x) \<Longrightarrow> a *\<^sub>R x \<le> 0"
  for x :: "'a::ordered_real_vector"
  by (auto simp add: scaleR_nonneg_nonpos scaleR_nonpos_nonneg)

lemma le_add_iff1: "a *\<^sub>R e + c \<le> b *\<^sub>R e + d \<longleftrightarrow> (a - b) *\<^sub>R e + c \<le> d"
  for c d e :: "'a::ordered_real_vector"
  by (simp add: algebra_simps)

lemma le_add_iff2: "a *\<^sub>R e + c \<le> b *\<^sub>R e + d \<longleftrightarrow> c \<le> (b - a) *\<^sub>R e + d"
  for c d e :: "'a::ordered_real_vector"
  by (simp add: algebra_simps)

lemma scaleR_left_mono_neg: "b \<le> a \<Longrightarrow> c \<le> 0 \<Longrightarrow> c *\<^sub>R a \<le> c *\<^sub>R b"
  for a b :: "'a::ordered_real_vector"
  apply (drule scaleR_left_mono [of _ _ "- c"])
   apply simp_all
  done

lemma scaleR_right_mono_neg: "b \<le> a \<Longrightarrow> c \<le> 0 \<Longrightarrow> a *\<^sub>R c \<le> b *\<^sub>R c"
  for c :: "'a::ordered_real_vector"
  apply (drule scaleR_right_mono [of _ _ "- c"])
   apply simp_all
  done

lemma scaleR_nonpos_nonpos: "a \<le> 0 \<Longrightarrow> b \<le> 0 \<Longrightarrow> 0 \<le> a *\<^sub>R b"
  for b :: "'a::ordered_real_vector"
  using scaleR_right_mono_neg [of a 0 b] by simp

lemma split_scaleR_pos_le: "(0 \<le> a \<and> 0 \<le> b) \<or> (a \<le> 0 \<and> b \<le> 0) \<Longrightarrow> 0 \<le> a *\<^sub>R b"
  for b :: "'a::ordered_real_vector"
  by (auto simp add: scaleR_nonneg_nonneg scaleR_nonpos_nonpos)

lemma zero_le_scaleR_iff:
  fixes b :: "'a::ordered_real_vector"
  shows "0 \<le> a *\<^sub>R b \<longleftrightarrow> 0 < a \<and> 0 \<le> b \<or> a < 0 \<and> b \<le> 0 \<or> a = 0"
    (is "?lhs = ?rhs")
proof (cases "a = 0")
  case True
  then show ?thesis by simp
next
  case False
  show ?thesis
  proof
    assume ?lhs
    from \<open>a \<noteq> 0\<close> consider "a > 0" | "a < 0" by arith
    then show ?rhs
    proof cases
      case 1
      with \<open>?lhs\<close> have "inverse a *\<^sub>R 0 \<le> inverse a *\<^sub>R (a *\<^sub>R b)"
        by (intro scaleR_mono) auto
      with 1 show ?thesis
        by simp
    next
      case 2
      with \<open>?lhs\<close> have "- inverse a *\<^sub>R 0 \<le> - inverse a *\<^sub>R (a *\<^sub>R b)"
        by (intro scaleR_mono) auto
      with 2 show ?thesis
        by simp
    qed
  next
    assume ?rhs
    then show ?lhs
      by (auto simp: not_le \<open>a \<noteq> 0\<close> intro!: split_scaleR_pos_le)
  qed
qed

lemma scaleR_le_0_iff: "a *\<^sub>R b \<le> 0 \<longleftrightarrow> 0 < a \<and> b \<le> 0 \<or> a < 0 \<and> 0 \<le> b \<or> a = 0"
  for b::"'a::ordered_real_vector"
  by (insert zero_le_scaleR_iff [of "-a" b]) force

lemma scaleR_le_cancel_left: "c *\<^sub>R a \<le> c *\<^sub>R b \<longleftrightarrow> (0 < c \<longrightarrow> a \<le> b) \<and> (c < 0 \<longrightarrow> b \<le> a)"
  for b :: "'a::ordered_real_vector"
  by (auto simp add: neq_iff scaleR_left_mono scaleR_left_mono_neg
      dest: scaleR_left_mono[where a="inverse c"] scaleR_left_mono_neg[where c="inverse c"])

lemma scaleR_le_cancel_left_pos: "0 < c \<Longrightarrow> c *\<^sub>R a \<le> c *\<^sub>R b \<longleftrightarrow> a \<le> b"
  for b :: "'a::ordered_real_vector"
  by (auto simp: scaleR_le_cancel_left)

lemma scaleR_le_cancel_left_neg: "c < 0 \<Longrightarrow> c *\<^sub>R a \<le> c *\<^sub>R b \<longleftrightarrow> b \<le> a"
  for b :: "'a::ordered_real_vector"
  by (auto simp: scaleR_le_cancel_left)

lemma scaleR_left_le_one_le: "0 \<le> x \<Longrightarrow> a \<le> 1 \<Longrightarrow> a *\<^sub>R x \<le> x"
  for x :: "'a::ordered_real_vector" and a :: real
  using scaleR_right_mono[of a 1 x] by simp


subsection \<open>Real normed vector spaces\<close>

class dist =
  fixes dist :: "'a \<Rightarrow> 'a \<Rightarrow> real"

class norm =
  fixes norm :: "'a \<Rightarrow> real"

class sgn_div_norm = scaleR + norm + sgn +
  assumes sgn_div_norm: "sgn x = x /\<^sub>R norm x"

class dist_norm = dist + norm + minus +
  assumes dist_norm: "dist x y = norm (x - y)"

class uniformity_dist = dist + uniformity +
  assumes uniformity_dist: "uniformity = (INF e:{0 <..}. principal {(x, y). dist x y < e})"
begin

lemma eventually_uniformity_metric:
  "eventually P uniformity \<longleftrightarrow> (\<exists>e>0. \<forall>x y. dist x y < e \<longrightarrow> P (x, y))"
  unfolding uniformity_dist
  by (subst eventually_INF_base)
     (auto simp: eventually_principal subset_eq intro: bexI[of _ "min _ _"])

end

class real_normed_vector = real_vector + sgn_div_norm + dist_norm + uniformity_dist + open_uniformity +
  assumes norm_eq_zero [simp]: "norm x = 0 \<longleftrightarrow> x = 0"
    and norm_triangle_ineq: "norm (x + y) \<le> norm x + norm y"
    and norm_scaleR [simp]: "norm (scaleR a x) = \<bar>a\<bar> * norm x"
begin

lemma norm_ge_zero [simp]: "0 \<le> norm x"
proof -
  have "0 = norm (x + -1 *\<^sub>R x)"
    using scaleR_add_left[of 1 "-1" x] norm_scaleR[of 0 x] by (simp add: scaleR_one)
  also have "\<dots> \<le> norm x + norm (-1 *\<^sub>R x)" by (rule norm_triangle_ineq)
  finally show ?thesis by simp
qed

end

class real_normed_algebra = real_algebra + real_normed_vector +
  assumes norm_mult_ineq: "norm (x * y) \<le> norm x * norm y"

class real_normed_algebra_1 = real_algebra_1 + real_normed_algebra +
  assumes norm_one [simp]: "norm 1 = 1"

lemma (in real_normed_algebra_1) scaleR_power [simp]: "(scaleR x y) ^ n = scaleR (x^n) (y^n)"
  by (induct n) (simp_all add: scaleR_one scaleR_scaleR mult_ac)

class real_normed_div_algebra = real_div_algebra + real_normed_vector +
  assumes norm_mult: "norm (x * y) = norm x * norm y"

class real_normed_field = real_field + real_normed_div_algebra

instance real_normed_div_algebra < real_normed_algebra_1
proof
  show "norm (x * y) \<le> norm x * norm y" for x y :: 'a
    by (simp add: norm_mult)
next
  have "norm (1 * 1::'a) = norm (1::'a) * norm (1::'a)"
    by (rule norm_mult)
  then show "norm (1::'a) = 1" by simp
qed

lemma norm_zero [simp]: "norm (0::'a::real_normed_vector) = 0"
  by simp

lemma zero_less_norm_iff [simp]: "norm x > 0 \<longleftrightarrow> x \<noteq> 0"
  for x :: "'a::real_normed_vector"
  by (simp add: order_less_le)

lemma norm_not_less_zero [simp]: "\<not> norm x < 0"
  for x :: "'a::real_normed_vector"
  by (simp add: linorder_not_less)

lemma norm_le_zero_iff [simp]: "norm x \<le> 0 \<longleftrightarrow> x = 0"
  for x :: "'a::real_normed_vector"
  by (simp add: order_le_less)

lemma norm_minus_cancel [simp]: "norm (- x) = norm x"
  for x :: "'a::real_normed_vector"
proof -
  have "norm (- x) = norm (scaleR (- 1) x)"
    by (simp only: scaleR_minus_left scaleR_one)
  also have "\<dots> = \<bar>- 1\<bar> * norm x"
    by (rule norm_scaleR)
  finally show ?thesis by simp
qed

lemma norm_minus_commute: "norm (a - b) = norm (b - a)"
  for a b :: "'a::real_normed_vector"
proof -
  have "norm (- (b - a)) = norm (b - a)"
    by (rule norm_minus_cancel)
  then show ?thesis by simp
qed

lemma dist_add_cancel [simp]: "dist (a + b) (a + c) = dist b c"
  for a :: "'a::real_normed_vector"
  by (simp add: dist_norm)

lemma dist_add_cancel2 [simp]: "dist (b + a) (c + a) = dist b c"
  for a :: "'a::real_normed_vector"
  by (simp add: dist_norm)

lemma dist_scaleR [simp]: "dist (x *\<^sub>R a) (y *\<^sub>R a) = \<bar>x - y\<bar> * norm a"
  for a :: "'a::real_normed_vector"
  by (metis dist_norm norm_scaleR scaleR_left.diff)

lemma norm_uminus_minus: "norm (- x - y :: 'a :: real_normed_vector) = norm (x + y)"
  by (subst (2) norm_minus_cancel[symmetric], subst minus_add_distrib) simp

lemma norm_triangle_ineq2: "norm a - norm b \<le> norm (a - b)"
  for a b :: "'a::real_normed_vector"
proof -
  have "norm (a - b + b) \<le> norm (a - b) + norm b"
    by (rule norm_triangle_ineq)
  then show ?thesis by simp
qed

lemma norm_triangle_ineq3: "\<bar>norm a - norm b\<bar> \<le> norm (a - b)"
  for a b :: "'a::real_normed_vector"
  apply (subst abs_le_iff)
  apply auto
   apply (rule norm_triangle_ineq2)
  apply (subst norm_minus_commute)
  apply (rule norm_triangle_ineq2)
  done

lemma norm_triangle_ineq4: "norm (a - b) \<le> norm a + norm b"
  for a b :: "'a::real_normed_vector"
proof -
  have "norm (a + - b) \<le> norm a + norm (- b)"
    by (rule norm_triangle_ineq)
  then show ?thesis by simp
qed

lemma norm_diff_ineq: "norm a - norm b \<le> norm (a + b)"
  for a b :: "'a::real_normed_vector"
proof -
  have "norm a - norm (- b) \<le> norm (a - - b)"
    by (rule norm_triangle_ineq2)
  then show ?thesis by simp
qed

lemma norm_add_leD: "norm (a + b) \<le> c \<Longrightarrow> norm b \<le> norm a + c"
  for a b :: "'a::real_normed_vector"
  by (metis add.commute diff_le_eq norm_diff_ineq order.trans)

lemma norm_diff_triangle_ineq: "norm ((a + b) - (c + d)) \<le> norm (a - c) + norm (b - d)"
  for a b c d :: "'a::real_normed_vector"
proof -
  have "norm ((a + b) - (c + d)) = norm ((a - c) + (b - d))"
    by (simp add: algebra_simps)
  also have "\<dots> \<le> norm (a - c) + norm (b - d)"
    by (rule norm_triangle_ineq)
  finally show ?thesis .
qed

lemma norm_diff_triangle_le:
  fixes x y z :: "'a::real_normed_vector"
  assumes "norm (x - y) \<le> e1"  "norm (y - z) \<le> e2"
  shows "norm (x - z) \<le> e1 + e2"
  using norm_diff_triangle_ineq [of x y y z] assms by simp

lemma norm_diff_triangle_less:
  fixes x y z :: "'a::real_normed_vector"
  assumes "norm (x - y) < e1"  "norm (y - z) < e2"
  shows "norm (x - z) < e1 + e2"
  using norm_diff_triangle_ineq [of x y y z] assms by simp

lemma norm_triangle_mono:
  fixes a b :: "'a::real_normed_vector"
  shows "norm a \<le> r \<Longrightarrow> norm b \<le> s \<Longrightarrow> norm (a + b) \<le> r + s"
  by (metis add_mono_thms_linordered_semiring(1) norm_triangle_ineq order.trans)

lemma norm_sum:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
  shows "norm (sum f A) \<le> (\<Sum>i\<in>A. norm (f i))"
  by (induct A rule: infinite_finite_induct) (auto intro: norm_triangle_mono)

lemma sum_norm_le:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
  assumes fg: "\<forall>x \<in> S. norm (f x) \<le> g x"
  shows "norm (sum f S) \<le> sum g S"
  by (rule order_trans [OF norm_sum sum_mono]) (simp add: fg)

lemma abs_norm_cancel [simp]: "\<bar>norm a\<bar> = norm a"
  for a :: "'a::real_normed_vector"
  by (rule abs_of_nonneg [OF norm_ge_zero])

lemma norm_add_less: "norm x < r \<Longrightarrow> norm y < s \<Longrightarrow> norm (x + y) < r + s"
  for x y :: "'a::real_normed_vector"
  by (rule order_le_less_trans [OF norm_triangle_ineq add_strict_mono])

lemma norm_mult_less: "norm x < r \<Longrightarrow> norm y < s \<Longrightarrow> norm (x * y) < r * s"
  for x y :: "'a::real_normed_algebra"
  by (rule order_le_less_trans [OF norm_mult_ineq]) (simp add: mult_strict_mono')

lemma norm_of_real [simp]: "norm (of_real r :: 'a::real_normed_algebra_1) = \<bar>r\<bar>"
  by (simp add: of_real_def)

lemma norm_numeral [simp]: "norm (numeral w::'a::real_normed_algebra_1) = numeral w"
  by (subst of_real_numeral [symmetric], subst norm_of_real, simp)

lemma norm_neg_numeral [simp]: "norm (- numeral w::'a::real_normed_algebra_1) = numeral w"
  by (subst of_real_neg_numeral [symmetric], subst norm_of_real, simp)

lemma norm_of_real_add1 [simp]: "norm (of_real x + 1 :: 'a :: real_normed_div_algebra) = \<bar>x + 1\<bar>"
  by (metis norm_of_real of_real_1 of_real_add)

lemma norm_of_real_addn [simp]:
  "norm (of_real x + numeral b :: 'a :: real_normed_div_algebra) = \<bar>x + numeral b\<bar>"
  by (metis norm_of_real of_real_add of_real_numeral)

lemma norm_of_int [simp]: "norm (of_int z::'a::real_normed_algebra_1) = \<bar>of_int z\<bar>"
  by (subst of_real_of_int_eq [symmetric], rule norm_of_real)

lemma norm_of_nat [simp]: "norm (of_nat n::'a::real_normed_algebra_1) = of_nat n"
  apply (subst of_real_of_nat_eq [symmetric])
  apply (subst norm_of_real, simp)
  done

lemma nonzero_norm_inverse: "a \<noteq> 0 \<Longrightarrow> norm (inverse a) = inverse (norm a)"
  for a :: "'a::real_normed_div_algebra"
  apply (rule inverse_unique [symmetric])
  apply (simp add: norm_mult [symmetric])
  done

lemma norm_inverse: "norm (inverse a) = inverse (norm a)"
  for a :: "'a::{real_normed_div_algebra,division_ring}"
  apply (cases "a = 0")
   apply simp
  apply (erule nonzero_norm_inverse)
  done

lemma nonzero_norm_divide: "b \<noteq> 0 \<Longrightarrow> norm (a / b) = norm a / norm b"
  for a b :: "'a::real_normed_field"
  by (simp add: divide_inverse norm_mult nonzero_norm_inverse)

lemma norm_divide: "norm (a / b) = norm a / norm b"
  for a b :: "'a::{real_normed_field,field}"
  by (simp add: divide_inverse norm_mult norm_inverse)

lemma norm_power_ineq: "norm (x ^ n) \<le> norm x ^ n"
  for x :: "'a::real_normed_algebra_1"
proof (induct n)
  case 0
  show "norm (x ^ 0) \<le> norm x ^ 0" by simp
next
  case (Suc n)
  have "norm (x * x ^ n) \<le> norm x * norm (x ^ n)"
    by (rule norm_mult_ineq)
  also from Suc have "\<dots> \<le> norm x * norm x ^ n"
    using norm_ge_zero by (rule mult_left_mono)
  finally show "norm (x ^ Suc n) \<le> norm x ^ Suc n"
    by simp
qed

lemma norm_power: "norm (x ^ n) = norm x ^ n"
  for x :: "'a::real_normed_div_algebra"
  by (induct n) (simp_all add: norm_mult)

lemma power_eq_imp_eq_norm:
  fixes w :: "'a::real_normed_div_algebra"
  assumes eq: "w ^ n = z ^ n" and "n > 0"
    shows "norm w = norm z"
proof -
  have "norm w ^ n = norm z ^ n"
    by (metis (no_types) eq norm_power)
  then show ?thesis
    using assms by (force intro: power_eq_imp_eq_base)
qed

lemma norm_mult_numeral1 [simp]: "norm (numeral w * a) = numeral w * norm a"
  for a b :: "'a::{real_normed_field,field}"
  by (simp add: norm_mult)

lemma norm_mult_numeral2 [simp]: "norm (a * numeral w) = norm a * numeral w"
  for a b :: "'a::{real_normed_field,field}"
  by (simp add: norm_mult)

lemma norm_divide_numeral [simp]: "norm (a / numeral w) = norm a / numeral w"
  for a b :: "'a::{real_normed_field,field}"
  by (simp add: norm_divide)

lemma norm_of_real_diff [simp]:
  "norm (of_real b - of_real a :: 'a::real_normed_algebra_1) \<le> \<bar>b - a\<bar>"
  by (metis norm_of_real of_real_diff order_refl)

text \<open>Despite a superficial resemblance, \<open>norm_eq_1\<close> is not relevant.\<close>
lemma square_norm_one:
  fixes x :: "'a::real_normed_div_algebra"
  assumes "x\<^sup>2 = 1"
  shows "norm x = 1"
  by (metis assms norm_minus_cancel norm_one power2_eq_1_iff)

lemma norm_less_p1: "norm x < norm (of_real (norm x) + 1 :: 'a)"
  for x :: "'a::real_normed_algebra_1"
proof -
  have "norm x < norm (of_real (norm x + 1) :: 'a)"
    by (simp add: of_real_def)
  then show ?thesis
    by simp
qed

lemma prod_norm: "prod (\<lambda>x. norm (f x)) A = norm (prod f A)"
  for f :: "'a \<Rightarrow> 'b::{comm_semiring_1,real_normed_div_algebra}"
  by (induct A rule: infinite_finite_induct) (auto simp: norm_mult)

lemma norm_prod_le:
  "norm (prod f A) \<le> (\<Prod>a\<in>A. norm (f a :: 'a :: {real_normed_algebra_1,comm_monoid_mult}))"
proof (induct A rule: infinite_finite_induct)
  case empty
  then show ?case by simp
next
  case (insert a A)
  then have "norm (prod f (insert a A)) \<le> norm (f a) * norm (prod f A)"
    by (simp add: norm_mult_ineq)
  also have "norm (prod f A) \<le> (\<Prod>a\<in>A. norm (f a))"
    by (rule insert)
  finally show ?case
    by (simp add: insert mult_left_mono)
next
  case infinite
  then show ?case by simp
qed

lemma norm_prod_diff:
  fixes z w :: "'i \<Rightarrow> 'a::{real_normed_algebra_1, comm_monoid_mult}"
  shows "(\<And>i. i \<in> I \<Longrightarrow> norm (z i) \<le> 1) \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> norm (w i) \<le> 1) \<Longrightarrow>
    norm ((\<Prod>i\<in>I. z i) - (\<Prod>i\<in>I. w i)) \<le> (\<Sum>i\<in>I. norm (z i - w i))"
proof (induction I rule: infinite_finite_induct)
  case empty
  then show ?case by simp
next
  case (insert i I)
  note insert.hyps[simp]

  have "norm ((\<Prod>i\<in>insert i I. z i) - (\<Prod>i\<in>insert i I. w i)) =
    norm ((\<Prod>i\<in>I. z i) * (z i - w i) + ((\<Prod>i\<in>I. z i) - (\<Prod>i\<in>I. w i)) * w i)"
    (is "_ = norm (?t1 + ?t2)")
    by (auto simp add: field_simps)
  also have "\<dots> \<le> norm ?t1 + norm ?t2"
    by (rule norm_triangle_ineq)
  also have "norm ?t1 \<le> norm (\<Prod>i\<in>I. z i) * norm (z i - w i)"
    by (rule norm_mult_ineq)
  also have "\<dots> \<le> (\<Prod>i\<in>I. norm (z i)) * norm(z i - w i)"
    by (rule mult_right_mono) (auto intro: norm_prod_le)
  also have "(\<Prod>i\<in>I. norm (z i)) \<le> (\<Prod>i\<in>I. 1)"
    by (intro prod_mono) (auto intro!: insert)
  also have "norm ?t2 \<le> norm ((\<Prod>i\<in>I. z i) - (\<Prod>i\<in>I. w i)) * norm (w i)"
    by (rule norm_mult_ineq)
  also have "norm (w i) \<le> 1"
    by (auto intro: insert)
  also have "norm ((\<Prod>i\<in>I. z i) - (\<Prod>i\<in>I. w i)) \<le> (\<Sum>i\<in>I. norm (z i - w i))"
    using insert by auto
  finally show ?case
    by (auto simp add: ac_simps mult_right_mono mult_left_mono)
next
  case infinite
  then show ?case by simp
qed

lemma norm_power_diff:
  fixes z w :: "'a::{real_normed_algebra_1, comm_monoid_mult}"
  assumes "norm z \<le> 1" "norm w \<le> 1"
  shows "norm (z^m - w^m) \<le> m * norm (z - w)"
proof -
  have "norm (z^m - w^m) = norm ((\<Prod> i < m. z) - (\<Prod> i < m. w))"
    by (simp add: prod_constant)
  also have "\<dots> \<le> (\<Sum>i<m. norm (z - w))"
    by (intro norm_prod_diff) (auto simp add: assms)
  also have "\<dots> = m * norm (z - w)"
    by simp
  finally show ?thesis .
qed


subsection \<open>Metric spaces\<close>

class metric_space = uniformity_dist + open_uniformity +
  assumes dist_eq_0_iff [simp]: "dist x y = 0 \<longleftrightarrow> x = y"
    and dist_triangle2: "dist x y \<le> dist x z + dist y z"
begin

lemma dist_self [simp]: "dist x x = 0"
  by simp

lemma zero_le_dist [simp]: "0 \<le> dist x y"
  using dist_triangle2 [of x x y] by simp

lemma zero_less_dist_iff: "0 < dist x y \<longleftrightarrow> x \<noteq> y"
  by (simp add: less_le)

lemma dist_not_less_zero [simp]: "\<not> dist x y < 0"
  by (simp add: not_less)

lemma dist_le_zero_iff [simp]: "dist x y \<le> 0 \<longleftrightarrow> x = y"
  by (simp add: le_less)

lemma dist_commute: "dist x y = dist y x"
proof (rule order_antisym)
  show "dist x y \<le> dist y x"
    using dist_triangle2 [of x y x] by simp
  show "dist y x \<le> dist x y"
    using dist_triangle2 [of y x y] by simp
qed

lemma dist_commute_lessI: "dist y x < e \<Longrightarrow> dist x y < e"
  by (simp add: dist_commute)

lemma dist_triangle: "dist x z \<le> dist x y + dist y z"
  using dist_triangle2 [of x z y] by (simp add: dist_commute)

lemma dist_triangle3: "dist x y \<le> dist a x + dist a y"
  using dist_triangle2 [of x y a] by (simp add: dist_commute)

lemma dist_pos_lt: "x \<noteq> y \<Longrightarrow> 0 < dist x y"
  by (simp add: zero_less_dist_iff)

lemma dist_nz: "x \<noteq> y \<longleftrightarrow> 0 < dist x y"
  by (simp add: zero_less_dist_iff)

declare dist_nz [symmetric, simp]

lemma dist_triangle_le: "dist x z + dist y z \<le> e \<Longrightarrow> dist x y \<le> e"
  by (rule order_trans [OF dist_triangle2])

lemma dist_triangle_lt: "dist x z + dist y z < e \<Longrightarrow> dist x y < e"
  by (rule le_less_trans [OF dist_triangle2])

lemma dist_triangle_less_add: "dist x1 y < e1 \<Longrightarrow> dist x2 y < e2 \<Longrightarrow> dist x1 x2 < e1 + e2"
  by (rule dist_triangle_lt [where z=y]) simp

lemma dist_triangle_half_l: "dist x1 y < e / 2 \<Longrightarrow> dist x2 y < e / 2 \<Longrightarrow> dist x1 x2 < e"
  by (rule dist_triangle_lt [where z=y]) simp

lemma dist_triangle_half_r: "dist y x1 < e / 2 \<Longrightarrow> dist y x2 < e / 2 \<Longrightarrow> dist x1 x2 < e"
  by (rule dist_triangle_half_l) (simp_all add: dist_commute)

subclass uniform_space
proof
  fix E x
  assume "eventually E uniformity"
  then obtain e where E: "0 < e" "\<And>x y. dist x y < e \<Longrightarrow> E (x, y)"
    by (auto simp: eventually_uniformity_metric)
  then show "E (x, x)" "\<forall>\<^sub>F (x, y) in uniformity. E (y, x)"
    by (auto simp: eventually_uniformity_metric dist_commute)
  show "\<exists>D. eventually D uniformity \<and> (\<forall>x y z. D (x, y) \<longrightarrow> D (y, z) \<longrightarrow> E (x, z))"
    using E dist_triangle_half_l[where e=e]
    unfolding eventually_uniformity_metric
    by (intro exI[of _ "\<lambda>(x, y). dist x y < e / 2"] exI[of _ "e/2"] conjI)
      (auto simp: dist_commute)
qed

lemma open_dist: "open S \<longleftrightarrow> (\<forall>x\<in>S. \<exists>e>0. \<forall>y. dist y x < e \<longrightarrow> y \<in> S)"
  by (simp add: dist_commute open_uniformity eventually_uniformity_metric)

lemma open_ball: "open {y. dist x y < d}"
  unfolding open_dist
proof (intro ballI)
  fix y
  assume *: "y \<in> {y. dist x y < d}"
  then show "\<exists>e>0. \<forall>z. dist z y < e \<longrightarrow> z \<in> {y. dist x y < d}"
    by (auto intro!: exI[of _ "d - dist x y"] simp: field_simps dist_triangle_lt)
qed

subclass first_countable_topology
proof
  fix x
  show "\<exists>A::nat \<Rightarrow> 'a set. (\<forall>i. x \<in> A i \<and> open (A i)) \<and> (\<forall>S. open S \<and> x \<in> S \<longrightarrow> (\<exists>i. A i \<subseteq> S))"
  proof (safe intro!: exI[of _ "\<lambda>n. {y. dist x y < inverse (Suc n)}"])
    fix S
    assume "open S" "x \<in> S"
    then obtain e where e: "0 < e" and "{y. dist x y < e} \<subseteq> S"
      by (auto simp: open_dist subset_eq dist_commute)
    moreover
    from e obtain i where "inverse (Suc i) < e"
      by (auto dest!: reals_Archimedean)
    then have "{y. dist x y < inverse (Suc i)} \<subseteq> {y. dist x y < e}"
      by auto
    ultimately show "\<exists>i. {y. dist x y < inverse (Suc i)} \<subseteq> S"
      by blast
  qed (auto intro: open_ball)
qed

end

instance metric_space \<subseteq> t2_space
proof
  fix x y :: "'a::metric_space"
  assume xy: "x \<noteq> y"
  let ?U = "{y'. dist x y' < dist x y / 2}"
  let ?V = "{x'. dist y x' < dist x y / 2}"
  have *: "d x z \<le> d x y + d y z \<Longrightarrow> d y z = d z y \<Longrightarrow> \<not> (d x y * 2 < d x z \<and> d z y * 2 < d x z)"
    for d :: "'a \<Rightarrow> 'a \<Rightarrow> real" and x y z :: 'a
    by arith
  have "open ?U \<and> open ?V \<and> x \<in> ?U \<and> y \<in> ?V \<and> ?U \<inter> ?V = {}"
    using dist_pos_lt[OF xy] *[of dist, OF dist_triangle dist_commute]
    using open_ball[of _ "dist x y / 2"] by auto
  then show "\<exists>U V. open U \<and> open V \<and> x \<in> U \<and> y \<in> V \<and> U \<inter> V = {}"
    by blast
qed

text \<open>Every normed vector space is a metric space.\<close>
instance real_normed_vector < metric_space
proof
  fix x y z :: 'a
  show "dist x y = 0 \<longleftrightarrow> x = y"
    by (simp add: dist_norm)
  show "dist x y \<le> dist x z + dist y z"
    using norm_triangle_ineq4 [of "x - z" "y - z"] by (simp add: dist_norm)
qed


subsection \<open>Class instances for real numbers\<close>

instantiation real :: real_normed_field
begin

definition dist_real_def: "dist x y = \<bar>x - y\<bar>"

definition uniformity_real_def [code del]:
  "(uniformity :: (real \<times> real) filter) = (INF e:{0 <..}. principal {(x, y). dist x y < e})"

definition open_real_def [code del]:
  "open (U :: real set) \<longleftrightarrow> (\<forall>x\<in>U. eventually (\<lambda>(x', y). x' = x \<longrightarrow> y \<in> U) uniformity)"

definition real_norm_def [simp]: "norm r = \<bar>r\<bar>"

instance
  apply intro_classes
         apply (unfold real_norm_def real_scaleR_def)
         apply (rule dist_real_def)
        apply (simp add: sgn_real_def)
       apply (rule uniformity_real_def)
      apply (rule open_real_def)
     apply (rule abs_eq_0)
    apply (rule abs_triangle_ineq)
   apply (rule abs_mult)
  apply (rule abs_mult)
  done

end

declare uniformity_Abort[where 'a=real, code]

lemma dist_of_real [simp]: "dist (of_real x :: 'a) (of_real y) = dist x y"
  for a :: "'a::real_normed_div_algebra"
  by (metis dist_norm norm_of_real of_real_diff real_norm_def)

declare [[code abort: "open :: real set \<Rightarrow> bool"]]

instance real :: linorder_topology
proof
  show "(open :: real set \<Rightarrow> bool) = generate_topology (range lessThan \<union> range greaterThan)"
  proof (rule ext, safe)
    fix S :: "real set"
    assume "open S"
    then obtain f where "\<forall>x\<in>S. 0 < f x \<and> (\<forall>y. dist y x < f x \<longrightarrow> y \<in> S)"
      unfolding open_dist bchoice_iff ..
    then have *: "S = (\<Union>x\<in>S. {x - f x <..} \<inter> {..< x + f x})"
      by (fastforce simp: dist_real_def)
    show "generate_topology (range lessThan \<union> range greaterThan) S"
      apply (subst *)
      apply (intro generate_topology_Union generate_topology.Int)
       apply (auto intro: generate_topology.Basis)
      done
  next
    fix S :: "real set"
    assume "generate_topology (range lessThan \<union> range greaterThan) S"
    moreover have "\<And>a::real. open {..<a}"
      unfolding open_dist dist_real_def
    proof clarify
      fix x a :: real
      assume "x < a"
      then have "0 < a - x \<and> (\<forall>y. \<bar>y - x\<bar> < a - x \<longrightarrow> y \<in> {..<a})" by auto
      then show "\<exists>e>0. \<forall>y. \<bar>y - x\<bar> < e \<longrightarrow> y \<in> {..<a}" ..
    qed
    moreover have "\<And>a::real. open {a <..}"
      unfolding open_dist dist_real_def
    proof clarify
      fix x a :: real
      assume "a < x"
      then have "0 < x - a \<and> (\<forall>y. \<bar>y - x\<bar> < x - a \<longrightarrow> y \<in> {a<..})" by auto
      then show "\<exists>e>0. \<forall>y. \<bar>y - x\<bar> < e \<longrightarrow> y \<in> {a<..}" ..
    qed
    ultimately show "open S"
      by induct auto
  qed
qed

instance real :: linear_continuum_topology ..

lemmas open_real_greaterThan = open_greaterThan[where 'a=real]
lemmas open_real_lessThan = open_lessThan[where 'a=real]
lemmas open_real_greaterThanLessThan = open_greaterThanLessThan[where 'a=real]
lemmas closed_real_atMost = closed_atMost[where 'a=real]
lemmas closed_real_atLeast = closed_atLeast[where 'a=real]
lemmas closed_real_atLeastAtMost = closed_atLeastAtMost[where 'a=real]


subsection \<open>Extra type constraints\<close>

text \<open>Only allow @{term "open"} in class \<open>topological_space\<close>.\<close>
setup \<open>Sign.add_const_constraint
  (@{const_name "open"}, SOME @{typ "'a::topological_space set \<Rightarrow> bool"})\<close>

text \<open>Only allow @{term "uniformity"} in class \<open>uniform_space\<close>.\<close>
setup \<open>Sign.add_const_constraint
  (@{const_name "uniformity"}, SOME @{typ "('a::uniformity \<times> 'a) filter"})\<close>

text \<open>Only allow @{term dist} in class \<open>metric_space\<close>.\<close>
setup \<open>Sign.add_const_constraint
  (@{const_name dist}, SOME @{typ "'a::metric_space \<Rightarrow> 'a \<Rightarrow> real"})\<close>

text \<open>Only allow @{term norm} in class \<open>real_normed_vector\<close>.\<close>
setup \<open>Sign.add_const_constraint
  (@{const_name norm}, SOME @{typ "'a::real_normed_vector \<Rightarrow> real"})\<close>


subsection \<open>Sign function\<close>

lemma norm_sgn: "norm (sgn x) = (if x = 0 then 0 else 1)"
  for x :: "'a::real_normed_vector"
  by (simp add: sgn_div_norm)

lemma sgn_zero [simp]: "sgn (0::'a::real_normed_vector) = 0"
  by (simp add: sgn_div_norm)

lemma sgn_zero_iff: "sgn x = 0 \<longleftrightarrow> x = 0"
  for x :: "'a::real_normed_vector"
  by (simp add: sgn_div_norm)

lemma sgn_minus: "sgn (- x) = - sgn x"
  for x :: "'a::real_normed_vector"
  by (simp add: sgn_div_norm)

lemma sgn_scaleR: "sgn (scaleR r x) = scaleR (sgn r) (sgn x)"
  for x :: "'a::real_normed_vector"
  by (simp add: sgn_div_norm ac_simps)

lemma sgn_one [simp]: "sgn (1::'a::real_normed_algebra_1) = 1"
  by (simp add: sgn_div_norm)

lemma sgn_of_real: "sgn (of_real r :: 'a::real_normed_algebra_1) = of_real (sgn r)"
  unfolding of_real_def by (simp only: sgn_scaleR sgn_one)

lemma sgn_mult: "sgn (x * y) = sgn x * sgn y"
  for x y :: "'a::real_normed_div_algebra"
  by (simp add: sgn_div_norm norm_mult mult.commute)

hide_fact (open) sgn_mult

lemma real_sgn_eq: "sgn x = x / \<bar>x\<bar>"
  for x :: real
  by (simp add: sgn_div_norm divide_inverse)

lemma zero_le_sgn_iff [simp]: "0 \<le> sgn x \<longleftrightarrow> 0 \<le> x"
  for x :: real
  by (cases "0::real" x rule: linorder_cases) simp_all

lemma sgn_le_0_iff [simp]: "sgn x \<le> 0 \<longleftrightarrow> x \<le> 0"
  for x :: real
  by (cases "0::real" x rule: linorder_cases) simp_all

lemma norm_conv_dist: "norm x = dist x 0"
  unfolding dist_norm by simp

declare norm_conv_dist [symmetric, simp]

lemma dist_0_norm [simp]: "dist 0 x = norm x"
  for x :: "'a::real_normed_vector"
  by (simp add: dist_norm)

lemma dist_diff [simp]: "dist a (a - b) = norm b"  "dist (a - b) a = norm b"
  by (simp_all add: dist_norm)

lemma dist_of_int: "dist (of_int m) (of_int n :: 'a :: real_normed_algebra_1) = of_int \<bar>m - n\<bar>"
proof -
  have "dist (of_int m) (of_int n :: 'a) = dist (of_int m :: 'a) (of_int m - (of_int (m - n)))"
    by simp
  also have "\<dots> = of_int \<bar>m - n\<bar>" by (subst dist_diff, subst norm_of_int) simp
  finally show ?thesis .
qed

lemma dist_of_nat:
  "dist (of_nat m) (of_nat n :: 'a :: real_normed_algebra_1) = of_int \<bar>int m - int n\<bar>"
  by (subst (1 2) of_int_of_nat_eq [symmetric]) (rule dist_of_int)


subsection \<open>Bounded Linear and Bilinear Operators\<close>

locale linear = additive f for f :: "'a::real_vector \<Rightarrow> 'b::real_vector" +
  assumes scaleR: "f (scaleR r x) = scaleR r (f x)"

lemma linear_imp_scaleR:
  assumes "linear D"
  obtains d where "D = (\<lambda>x. x *\<^sub>R d)"
  by (metis assms linear.scaleR mult.commute mult.left_neutral real_scaleR_def)

corollary real_linearD:
  fixes f :: "real \<Rightarrow> real"
  assumes "linear f" obtains c where "f = op* c"
  by (rule linear_imp_scaleR [OF assms]) (force simp: scaleR_conv_of_real)

lemma linearI:
  assumes "\<And>x y. f (x + y) = f x + f y"
    and "\<And>c x. f (c *\<^sub>R x) = c *\<^sub>R f x"
  shows "linear f"
  by standard (rule assms)+

locale bounded_linear = linear f for f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector" +
  assumes bounded: "\<exists>K. \<forall>x. norm (f x) \<le> norm x * K"
begin

lemma pos_bounded: "\<exists>K>0. \<forall>x. norm (f x) \<le> norm x * K"
proof -
  obtain K where K: "\<And>x. norm (f x) \<le> norm x * K"
    using bounded by blast
  show ?thesis
  proof (intro exI impI conjI allI)
    show "0 < max 1 K"
      by (rule order_less_le_trans [OF zero_less_one max.cobounded1])
  next
    fix x
    have "norm (f x) \<le> norm x * K" using K .
    also have "\<dots> \<le> norm x * max 1 K"
      by (rule mult_left_mono [OF max.cobounded2 norm_ge_zero])
    finally show "norm (f x) \<le> norm x * max 1 K" .
  qed
qed

lemma nonneg_bounded: "\<exists>K\<ge>0. \<forall>x. norm (f x) \<le> norm x * K"
  using pos_bounded by (auto intro: order_less_imp_le)

lemma linear: "linear f"
  by (fact local.linear_axioms)

end

lemma bounded_linear_intro:
  assumes "\<And>x y. f (x + y) = f x + f y"
    and "\<And>r x. f (scaleR r x) = scaleR r (f x)"
    and "\<And>x. norm (f x) \<le> norm x * K"
  shows "bounded_linear f"
  by standard (blast intro: assms)+

locale bounded_bilinear =
  fixes prod :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector \<Rightarrow> 'c::real_normed_vector"
    (infixl "**" 70)
  assumes add_left: "prod (a + a') b = prod a b + prod a' b"
    and add_right: "prod a (b + b') = prod a b + prod a b'"
    and scaleR_left: "prod (scaleR r a) b = scaleR r (prod a b)"
    and scaleR_right: "prod a (scaleR r b) = scaleR r (prod a b)"
    and bounded: "\<exists>K. \<forall>a b. norm (prod a b) \<le> norm a * norm b * K"
begin

lemma pos_bounded: "\<exists>K>0. \<forall>a b. norm (a ** b) \<le> norm a * norm b * K"
  apply (insert bounded)
  apply (erule exE)
  apply (rule_tac x="max 1 K" in exI)
  apply safe
   apply (rule order_less_le_trans [OF zero_less_one max.cobounded1])
  apply (drule spec)
  apply (drule spec)
  apply (erule order_trans)
  apply (rule mult_left_mono [OF max.cobounded2])
  apply (intro mult_nonneg_nonneg norm_ge_zero)
  done

lemma nonneg_bounded: "\<exists>K\<ge>0. \<forall>a b. norm (a ** b) \<le> norm a * norm b * K"
  using pos_bounded by (auto intro: order_less_imp_le)

lemma additive_right: "additive (\<lambda>b. prod a b)"
  by (rule additive.intro, rule add_right)

lemma additive_left: "additive (\<lambda>a. prod a b)"
  by (rule additive.intro, rule add_left)

lemma zero_left: "prod 0 b = 0"
  by (rule additive.zero [OF additive_left])

lemma zero_right: "prod a 0 = 0"
  by (rule additive.zero [OF additive_right])

lemma minus_left: "prod (- a) b = - prod a b"
  by (rule additive.minus [OF additive_left])

lemma minus_right: "prod a (- b) = - prod a b"
  by (rule additive.minus [OF additive_right])

lemma diff_left: "prod (a - a') b = prod a b - prod a' b"
  by (rule additive.diff [OF additive_left])

lemma diff_right: "prod a (b - b') = prod a b - prod a b'"
  by (rule additive.diff [OF additive_right])

lemma sum_left: "prod (sum g S) x = sum ((\<lambda>i. prod (g i) x)) S"
  by (rule additive.sum [OF additive_left])

lemma sum_right: "prod x (sum g S) = sum ((\<lambda>i. (prod x (g i)))) S"
  by (rule additive.sum [OF additive_right])


lemma bounded_linear_left: "bounded_linear (\<lambda>a. a ** b)"
  apply (insert bounded)
  apply safe
  apply (rule_tac K="norm b * K" in bounded_linear_intro)
    apply (rule add_left)
   apply (rule scaleR_left)
  apply (simp add: ac_simps)
  done

lemma bounded_linear_right: "bounded_linear (\<lambda>b. a ** b)"
  apply (insert bounded)
  apply safe
  apply (rule_tac K="norm a * K" in bounded_linear_intro)
    apply (rule add_right)
   apply (rule scaleR_right)
  apply (simp add: ac_simps)
  done

lemma prod_diff_prod: "(x ** y - a ** b) = (x - a) ** (y - b) + (x - a) ** b + a ** (y - b)"
  by (simp add: diff_left diff_right)

lemma flip: "bounded_bilinear (\<lambda>x y. y ** x)"
  apply standard
      apply (rule add_right)
     apply (rule add_left)
    apply (rule scaleR_right)
   apply (rule scaleR_left)
  apply (subst mult.commute)
  apply (insert bounded)
  apply blast
  done

lemma comp1:
  assumes "bounded_linear g"
  shows "bounded_bilinear (\<lambda>x. op ** (g x))"
proof unfold_locales
  interpret g: bounded_linear g by fact
  show "\<And>a a' b. g (a + a') ** b = g a ** b + g a' ** b"
    "\<And>a b b'. g a ** (b + b') = g a ** b + g a ** b'"
    "\<And>r a b. g (r *\<^sub>R a) ** b = r *\<^sub>R (g a ** b)"
    "\<And>a r b. g a ** (r *\<^sub>R b) = r *\<^sub>R (g a ** b)"
    by (auto simp: g.add add_left add_right g.scaleR scaleR_left scaleR_right)
  from g.nonneg_bounded nonneg_bounded obtain K L
    where nn: "0 \<le> K" "0 \<le> L"
      and K: "\<And>x. norm (g x) \<le> norm x * K"
      and L: "\<And>a b. norm (a ** b) \<le> norm a * norm b * L"
    by auto
  have "norm (g a ** b) \<le> norm a * K * norm b * L" for a b
    by (auto intro!:  order_trans[OF K] order_trans[OF L] mult_mono simp: nn)
  then show "\<exists>K. \<forall>a b. norm (g a ** b) \<le> norm a * norm b * K"
    by (auto intro!: exI[where x="K * L"] simp: ac_simps)
qed

lemma comp: "bounded_linear f \<Longrightarrow> bounded_linear g \<Longrightarrow> bounded_bilinear (\<lambda>x y. f x ** g y)"
  by (rule bounded_bilinear.flip[OF bounded_bilinear.comp1[OF bounded_bilinear.flip[OF comp1]]])

end

lemma bounded_linear_ident[simp]: "bounded_linear (\<lambda>x. x)"
  by standard (auto intro!: exI[of _ 1])

lemma bounded_linear_zero[simp]: "bounded_linear (\<lambda>x. 0)"
  by standard (auto intro!: exI[of _ 1])

lemma bounded_linear_add:
  assumes "bounded_linear f"
    and "bounded_linear g"
  shows "bounded_linear (\<lambda>x. f x + g x)"
proof -
  interpret f: bounded_linear f by fact
  interpret g: bounded_linear g by fact
  show ?thesis
  proof
    from f.bounded obtain Kf where Kf: "norm (f x) \<le> norm x * Kf" for x
      by blast
    from g.bounded obtain Kg where Kg: "norm (g x) \<le> norm x * Kg" for x
      by blast
    show "\<exists>K. \<forall>x. norm (f x + g x) \<le> norm x * K"
      using add_mono[OF Kf Kg]
      by (intro exI[of _ "Kf + Kg"]) (auto simp: field_simps intro: norm_triangle_ineq order_trans)
  qed (simp_all add: f.add g.add f.scaleR g.scaleR scaleR_right_distrib)
qed

lemma bounded_linear_minus:
  assumes "bounded_linear f"
  shows "bounded_linear (\<lambda>x. - f x)"
proof -
  interpret f: bounded_linear f by fact
  show ?thesis
    apply unfold_locales
      apply (simp add: f.add)
     apply (simp add: f.scaleR)
    apply (simp add: f.bounded)
    done
qed

lemma bounded_linear_sub: "bounded_linear f \<Longrightarrow> bounded_linear g \<Longrightarrow> bounded_linear (\<lambda>x. f x - g x)"
  using bounded_linear_add[of f "\<lambda>x. - g x"] bounded_linear_minus[of g]
  by (auto simp add: algebra_simps)

lemma bounded_linear_sum:
  fixes f :: "'i \<Rightarrow> 'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  shows "(\<And>i. i \<in> I \<Longrightarrow> bounded_linear (f i)) \<Longrightarrow> bounded_linear (\<lambda>x. \<Sum>i\<in>I. f i x)"
  by (induct I rule: infinite_finite_induct) (auto intro!: bounded_linear_add)

lemma bounded_linear_compose:
  assumes "bounded_linear f"
    and "bounded_linear g"
  shows "bounded_linear (\<lambda>x. f (g x))"
proof -
  interpret f: bounded_linear f by fact
  interpret g: bounded_linear g by fact
  show ?thesis
  proof unfold_locales
    show "f (g (x + y)) = f (g x) + f (g y)" for x y
      by (simp only: f.add g.add)
    show "f (g (scaleR r x)) = scaleR r (f (g x))" for r x
      by (simp only: f.scaleR g.scaleR)
    from f.pos_bounded obtain Kf where f: "\<And>x. norm (f x) \<le> norm x * Kf" and Kf: "0 < Kf"
      by blast
    from g.pos_bounded obtain Kg where g: "\<And>x. norm (g x) \<le> norm x * Kg"
      by blast
    show "\<exists>K. \<forall>x. norm (f (g x)) \<le> norm x * K"
    proof (intro exI allI)
      fix x
      have "norm (f (g x)) \<le> norm (g x) * Kf"
        using f .
      also have "\<dots> \<le> (norm x * Kg) * Kf"
        using g Kf [THEN order_less_imp_le] by (rule mult_right_mono)
      also have "(norm x * Kg) * Kf = norm x * (Kg * Kf)"
        by (rule mult.assoc)
      finally show "norm (f (g x)) \<le> norm x * (Kg * Kf)" .
    qed
  qed
qed

lemma bounded_bilinear_mult: "bounded_bilinear (op * :: 'a \<Rightarrow> 'a \<Rightarrow> 'a::real_normed_algebra)"
  apply (rule bounded_bilinear.intro)
      apply (rule distrib_right)
     apply (rule distrib_left)
    apply (rule mult_scaleR_left)
   apply (rule mult_scaleR_right)
  apply (rule_tac x="1" in exI)
  apply (simp add: norm_mult_ineq)
  done

lemma bounded_linear_mult_left: "bounded_linear (\<lambda>x::'a::real_normed_algebra. x * y)"
  using bounded_bilinear_mult
  by (rule bounded_bilinear.bounded_linear_left)

lemma bounded_linear_mult_right: "bounded_linear (\<lambda>y::'a::real_normed_algebra. x * y)"
  using bounded_bilinear_mult
  by (rule bounded_bilinear.bounded_linear_right)

lemmas bounded_linear_mult_const =
  bounded_linear_mult_left [THEN bounded_linear_compose]

lemmas bounded_linear_const_mult =
  bounded_linear_mult_right [THEN bounded_linear_compose]

lemma bounded_linear_divide: "bounded_linear (\<lambda>x. x / y)"
  for y :: "'a::real_normed_field"
  unfolding divide_inverse by (rule bounded_linear_mult_left)

lemma bounded_bilinear_scaleR: "bounded_bilinear scaleR"
  apply (rule bounded_bilinear.intro)
      apply (rule scaleR_left_distrib)
     apply (rule scaleR_right_distrib)
    apply simp
   apply (rule scaleR_left_commute)
  apply (rule_tac x="1" in exI)
  apply simp
  done

lemma bounded_linear_scaleR_left: "bounded_linear (\<lambda>r. scaleR r x)"
  using bounded_bilinear_scaleR
  by (rule bounded_bilinear.bounded_linear_left)

lemma bounded_linear_scaleR_right: "bounded_linear (\<lambda>x. scaleR r x)"
  using bounded_bilinear_scaleR
  by (rule bounded_bilinear.bounded_linear_right)

lemmas bounded_linear_scaleR_const =
  bounded_linear_scaleR_left[THEN bounded_linear_compose]

lemmas bounded_linear_const_scaleR =
  bounded_linear_scaleR_right[THEN bounded_linear_compose]

lemma bounded_linear_of_real: "bounded_linear (\<lambda>r. of_real r)"
  unfolding of_real_def by (rule bounded_linear_scaleR_left)

lemma real_bounded_linear: "bounded_linear f \<longleftrightarrow> (\<exists>c::real. f = (\<lambda>x. x * c))"
  for f :: "real \<Rightarrow> real"
proof -
  {
    fix x
    assume "bounded_linear f"
    then interpret bounded_linear f .
    from scaleR[of x 1] have "f x = x * f 1"
      by simp
  }
  then show ?thesis
    by (auto intro: exI[of _ "f 1"] bounded_linear_mult_left)
qed

lemma bij_linear_imp_inv_linear: "linear f \<Longrightarrow> bij f \<Longrightarrow> linear (inv f)"
  by (auto simp: linear_def linear_axioms_def additive_def bij_is_surj bij_is_inj surj_f_inv_f
      intro!:  Hilbert_Choice.inv_f_eq)

instance real_normed_algebra_1 \<subseteq> perfect_space
proof
  show "\<not> open {x}" for x :: 'a
    apply (simp only: open_dist dist_norm)
    apply clarsimp
    apply (rule_tac x = "x + of_real (e/2)" in exI)
    apply simp
    done
qed


subsection \<open>Filters and Limits on Metric Space\<close>

lemma (in metric_space) nhds_metric: "nhds x = (INF e:{0 <..}. principal {y. dist y x < e})"
  unfolding nhds_def
proof (safe intro!: INF_eq)
  fix S
  assume "open S" "x \<in> S"
  then obtain e where "{y. dist y x < e} \<subseteq> S" "0 < e"
    by (auto simp: open_dist subset_eq)
  then show "\<exists>e\<in>{0<..}. principal {y. dist y x < e} \<le> principal S"
    by auto
qed (auto intro!: exI[of _ "{y. dist x y < e}" for e] open_ball simp: dist_commute)

lemma (in metric_space) tendsto_iff: "(f \<longlongrightarrow> l) F \<longleftrightarrow> (\<forall>e>0. eventually (\<lambda>x. dist (f x) l < e) F)"
  unfolding nhds_metric filterlim_INF filterlim_principal by auto

lemma (in metric_space) tendstoI [intro?]:
  "(\<And>e. 0 < e \<Longrightarrow> eventually (\<lambda>x. dist (f x) l < e) F) \<Longrightarrow> (f \<longlongrightarrow> l) F"
  by (auto simp: tendsto_iff)

lemma (in metric_space) tendstoD: "(f \<longlongrightarrow> l) F \<Longrightarrow> 0 < e \<Longrightarrow> eventually (\<lambda>x. dist (f x) l < e) F"
  by (auto simp: tendsto_iff)

lemma (in metric_space) eventually_nhds_metric:
  "eventually P (nhds a) \<longleftrightarrow> (\<exists>d>0. \<forall>x. dist x a < d \<longrightarrow> P x)"
  unfolding nhds_metric
  by (subst eventually_INF_base)
     (auto simp: eventually_principal Bex_def subset_eq intro: exI[of _ "min a b" for a b])

lemma eventually_at: "eventually P (at a within S) \<longleftrightarrow> (\<exists>d>0. \<forall>x\<in>S. x \<noteq> a \<and> dist x a < d \<longrightarrow> P x)"
  for a :: "'a :: metric_space"
  by (auto simp: eventually_at_filter eventually_nhds_metric)

lemma eventually_at_le: "eventually P (at a within S) \<longleftrightarrow> (\<exists>d>0. \<forall>x\<in>S. x \<noteq> a \<and> dist x a \<le> d \<longrightarrow> P x)"
  for a :: "'a::metric_space"
  apply (simp only: eventually_at_filter eventually_nhds_metric)
  apply auto
  apply (rule_tac x="d / 2" in exI)
  apply auto
  done

lemma eventually_at_left_real: "a > (b :: real) \<Longrightarrow> eventually (\<lambda>x. x \<in> {b<..<a}) (at_left a)"
  by (subst eventually_at, rule exI[of _ "a - b"]) (force simp: dist_real_def)

lemma eventually_at_right_real: "a < (b :: real) \<Longrightarrow> eventually (\<lambda>x. x \<in> {a<..<b}) (at_right a)"
  by (subst eventually_at, rule exI[of _ "b - a"]) (force simp: dist_real_def)

lemma metric_tendsto_imp_tendsto:
  fixes a :: "'a :: metric_space"
    and b :: "'b :: metric_space"
  assumes f: "(f \<longlongrightarrow> a) F"
    and le: "eventually (\<lambda>x. dist (g x) b \<le> dist (f x) a) F"
  shows "(g \<longlongrightarrow> b) F"
proof (rule tendstoI)
  fix e :: real
  assume "0 < e"
  with f have "eventually (\<lambda>x. dist (f x) a < e) F" by (rule tendstoD)
  with le show "eventually (\<lambda>x. dist (g x) b < e) F"
    using le_less_trans by (rule eventually_elim2)
qed

lemma filterlim_real_sequentially: "LIM x sequentially. real x :> at_top"
  apply (simp only: filterlim_at_top)
  apply (intro allI)
  apply (rule_tac c="nat \<lceil>Z + 1\<rceil>" in eventually_sequentiallyI)
  apply linarith
  done

lemma filterlim_nat_sequentially: "filterlim nat sequentially at_top"
  unfolding filterlim_at_top
  apply (rule allI)
  subgoal for Z by (auto intro!: eventually_at_top_linorderI[where c="int Z"])
  done

lemma filterlim_floor_sequentially: "filterlim floor at_top at_top"
  unfolding filterlim_at_top
  apply (rule allI)
  subgoal for Z by (auto simp: le_floor_iff intro!: eventually_at_top_linorderI[where c="of_int Z"])
  done

lemma filterlim_sequentially_iff_filterlim_real:
  "filterlim f sequentially F \<longleftrightarrow> filterlim (\<lambda>x. real (f x)) at_top F"
  apply (rule iffI)
  subgoal using filterlim_compose filterlim_real_sequentially by blast
  subgoal premises prems
  proof -
    have "filterlim (\<lambda>x. nat (floor (real (f x)))) sequentially F"
      by (intro filterlim_compose[OF filterlim_nat_sequentially]
          filterlim_compose[OF filterlim_floor_sequentially] prems)
    then show ?thesis by simp
  qed
  done


subsubsection \<open>Limits of Sequences\<close>

lemma lim_sequentially: "X \<longlonglongrightarrow> L \<longleftrightarrow> (\<forall>r>0. \<exists>no. \<forall>n\<ge>no. dist (X n) L < r)"
  for L :: "'a::metric_space"
  unfolding tendsto_iff eventually_sequentially ..

lemmas LIMSEQ_def = lim_sequentially  (*legacy binding*)

lemma LIMSEQ_iff_nz: "X \<longlonglongrightarrow> L \<longleftrightarrow> (\<forall>r>0. \<exists>no>0. \<forall>n\<ge>no. dist (X n) L < r)"
  for L :: "'a::metric_space"
  unfolding lim_sequentially by (metis Suc_leD zero_less_Suc)

lemma metric_LIMSEQ_I: "(\<And>r. 0 < r \<Longrightarrow> \<exists>no. \<forall>n\<ge>no. dist (X n) L < r) \<Longrightarrow> X \<longlonglongrightarrow> L"
  for L :: "'a::metric_space"
  by (simp add: lim_sequentially)

lemma metric_LIMSEQ_D: "X \<longlonglongrightarrow> L \<Longrightarrow> 0 < r \<Longrightarrow> \<exists>no. \<forall>n\<ge>no. dist (X n) L < r"
  for L :: "'a::metric_space"
  by (simp add: lim_sequentially)


subsubsection \<open>Limits of Functions\<close>

lemma LIM_def: "f \<midarrow>a\<rightarrow> L \<longleftrightarrow> (\<forall>r > 0. \<exists>s > 0. \<forall>x. x \<noteq> a \<and> dist x a < s \<longrightarrow> dist (f x) L < r)"
  for a :: "'a::metric_space" and L :: "'b::metric_space"
  unfolding tendsto_iff eventually_at by simp

lemma metric_LIM_I:
  "(\<And>r. 0 < r \<Longrightarrow> \<exists>s>0. \<forall>x. x \<noteq> a \<and> dist x a < s \<longrightarrow> dist (f x) L < r) \<Longrightarrow> f \<midarrow>a\<rightarrow> L"
  for a :: "'a::metric_space" and L :: "'b::metric_space"
  by (simp add: LIM_def)

lemma metric_LIM_D: "f \<midarrow>a\<rightarrow> L \<Longrightarrow> 0 < r \<Longrightarrow> \<exists>s>0. \<forall>x. x \<noteq> a \<and> dist x a < s \<longrightarrow> dist (f x) L < r"
  for a :: "'a::metric_space" and L :: "'b::metric_space"
  by (simp add: LIM_def)

lemma metric_LIM_imp_LIM:
  fixes l :: "'a::metric_space"
    and m :: "'b::metric_space"
  assumes f: "f \<midarrow>a\<rightarrow> l"
    and le: "\<And>x. x \<noteq> a \<Longrightarrow> dist (g x) m \<le> dist (f x) l"
  shows "g \<midarrow>a\<rightarrow> m"
  by (rule metric_tendsto_imp_tendsto [OF f]) (auto simp add: eventually_at_topological le)

lemma metric_LIM_equal2:
  fixes a :: "'a::metric_space"
  assumes "0 < R"
    and "\<And>x. x \<noteq> a \<Longrightarrow> dist x a < R \<Longrightarrow> f x = g x"
  shows "g \<midarrow>a\<rightarrow> l \<Longrightarrow> f \<midarrow>a\<rightarrow> l"
  apply (rule topological_tendstoI)
  apply (drule (2) topological_tendstoD)
  apply (simp add: eventually_at)
  apply safe
  apply (rule_tac x="min d R" in exI)
  apply safe
   apply (simp add: assms(1))
  apply (simp add: assms(2))
  done

lemma metric_LIM_compose2:
  fixes a :: "'a::metric_space"
  assumes f: "f \<midarrow>a\<rightarrow> b"
    and g: "g \<midarrow>b\<rightarrow> c"
    and inj: "\<exists>d>0. \<forall>x. x \<noteq> a \<and> dist x a < d \<longrightarrow> f x \<noteq> b"
  shows "(\<lambda>x. g (f x)) \<midarrow>a\<rightarrow> c"
  using inj by (intro tendsto_compose_eventually[OF g f]) (auto simp: eventually_at)

lemma metric_isCont_LIM_compose2:
  fixes f :: "'a :: metric_space \<Rightarrow> _"
  assumes f [unfolded isCont_def]: "isCont f a"
    and g: "g \<midarrow>f a\<rightarrow> l"
    and inj: "\<exists>d>0. \<forall>x. x \<noteq> a \<and> dist x a < d \<longrightarrow> f x \<noteq> f a"
  shows "(\<lambda>x. g (f x)) \<midarrow>a\<rightarrow> l"
  by (rule metric_LIM_compose2 [OF f g inj])


subsection \<open>Complete metric spaces\<close>

subsection \<open>Cauchy sequences\<close>

lemma (in metric_space) Cauchy_def: "Cauchy X = (\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (X m) (X n) < e)"
proof -
  have *: "eventually P (INF M. principal {(X m, X n) | n m. m \<ge> M \<and> n \<ge> M}) \<longleftrightarrow>
    (\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. P (X m, X n))" for P
    apply (subst eventually_INF_base)
    subgoal by simp
    subgoal for a b
      by (intro bexI[of _ "max a b"]) (auto simp: eventually_principal subset_eq)
    subgoal by (auto simp: eventually_principal, blast)
    done
  have "Cauchy X \<longleftrightarrow> (INF M. principal {(X m, X n) | n m. m \<ge> M \<and> n \<ge> M}) \<le> uniformity"
    unfolding Cauchy_uniform_iff le_filter_def * ..
  also have "\<dots> = (\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (X m) (X n) < e)"
    unfolding uniformity_dist le_INF_iff by (auto simp: * le_principal)
  finally show ?thesis .
qed

lemma (in metric_space) Cauchy_altdef: "Cauchy f \<longleftrightarrow> (\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n>m. dist (f m) (f n) < e)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?rhs
  show ?lhs
    unfolding Cauchy_def
  proof (intro allI impI)
    fix e :: real assume e: "e > 0"
    with \<open>?rhs\<close> obtain M where M: "m \<ge> M \<Longrightarrow> n > m \<Longrightarrow> dist (f m) (f n) < e" for m n
      by blast
    have "dist (f m) (f n) < e" if "m \<ge> M" "n \<ge> M" for m n
      using M[of m n] M[of n m] e that by (cases m n rule: linorder_cases) (auto simp: dist_commute)
    then show "\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (f m) (f n) < e"
      by blast
  qed
next
  assume ?lhs
  show ?rhs
  proof (intro allI impI)
    fix e :: real
    assume e: "e > 0"
    with \<open>Cauchy f\<close> obtain M where "\<And>m n. m \<ge> M \<Longrightarrow> n \<ge> M \<Longrightarrow> dist (f m) (f n) < e"
      unfolding Cauchy_def by blast
    then show "\<exists>M. \<forall>m\<ge>M. \<forall>n>m. dist (f m) (f n) < e"
      by (intro exI[of _ M]) force
  qed
qed

lemma (in metric_space) metric_CauchyI:
  "(\<And>e. 0 < e \<Longrightarrow> \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (X m) (X n) < e) \<Longrightarrow> Cauchy X"
  by (simp add: Cauchy_def)

lemma (in metric_space) CauchyI':
  "(\<And>e. 0 < e \<Longrightarrow> \<exists>M. \<forall>m\<ge>M. \<forall>n>m. dist (X m) (X n) < e) \<Longrightarrow> Cauchy X"
  unfolding Cauchy_altdef by blast

lemma (in metric_space) metric_CauchyD:
  "Cauchy X \<Longrightarrow> 0 < e \<Longrightarrow> \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (X m) (X n) < e"
  by (simp add: Cauchy_def)

lemma (in metric_space) metric_Cauchy_iff2:
  "Cauchy X = (\<forall>j. (\<exists>M. \<forall>m \<ge> M. \<forall>n \<ge> M. dist (X m) (X n) < inverse(real (Suc j))))"
  apply (simp add: Cauchy_def)
  apply auto
  apply (drule reals_Archimedean)
  apply safe
  apply (drule_tac x = n in spec)
  apply auto
  apply (rule_tac x = M in exI)
  apply auto
  apply (drule_tac x = m in spec)
  apply simp
  apply (drule_tac x = na in spec)
  apply auto
  done

lemma Cauchy_iff2: "Cauchy X \<longleftrightarrow> (\<forall>j. (\<exists>M. \<forall>m \<ge> M. \<forall>n \<ge> M. \<bar>X m - X n\<bar> < inverse (real (Suc j))))"
  by (simp only: metric_Cauchy_iff2 dist_real_def)

lemma lim_1_over_n: "((\<lambda>n. 1 / of_nat n) \<longlongrightarrow> (0::'a::real_normed_field)) sequentially"
proof (subst lim_sequentially, intro allI impI exI)
  fix e :: real
  assume e: "e > 0"
  fix n :: nat
  assume n: "n \<ge> nat \<lceil>inverse e + 1\<rceil>"
  have "inverse e < of_nat (nat \<lceil>inverse e + 1\<rceil>)" by linarith
  also note n
  finally show "dist (1 / of_nat n :: 'a) 0 < e"
    using e by (simp add: divide_simps mult.commute norm_divide)
qed

lemma (in metric_space) complete_def:
  shows "complete S = (\<forall>f. (\<forall>n. f n \<in> S) \<and> Cauchy f \<longrightarrow> (\<exists>l\<in>S. f \<longlonglongrightarrow> l))"
  unfolding complete_uniform
proof safe
  fix f :: "nat \<Rightarrow> 'a"
  assume f: "\<forall>n. f n \<in> S" "Cauchy f"
    and *: "\<forall>F\<le>principal S. F \<noteq> bot \<longrightarrow> cauchy_filter F \<longrightarrow> (\<exists>x\<in>S. F \<le> nhds x)"
  then show "\<exists>l\<in>S. f \<longlonglongrightarrow> l"
    unfolding filterlim_def using f
    by (intro *[rule_format])
       (auto simp: filtermap_sequentually_ne_bot le_principal eventually_filtermap Cauchy_uniform)
next
  fix F :: "'a filter"
  assume "F \<le> principal S" "F \<noteq> bot" "cauchy_filter F"
  assume seq: "\<forall>f. (\<forall>n. f n \<in> S) \<and> Cauchy f \<longrightarrow> (\<exists>l\<in>S. f \<longlonglongrightarrow> l)"

  from \<open>F \<le> principal S\<close> \<open>cauchy_filter F\<close>
  have FF_le: "F \<times>\<^sub>F F \<le> uniformity_on S"
    by (simp add: cauchy_filter_def principal_prod_principal[symmetric] prod_filter_mono)

  let ?P = "\<lambda>P e. eventually P F \<and> (\<forall>x. P x \<longrightarrow> x \<in> S) \<and> (\<forall>x y. P x \<longrightarrow> P y \<longrightarrow> dist x y < e)"
  have P: "\<exists>P. ?P P \<epsilon>" if "0 < \<epsilon>" for \<epsilon> :: real
  proof -
    from that have "eventually (\<lambda>(x, y). x \<in> S \<and> y \<in> S \<and> dist x y < \<epsilon>) (uniformity_on S)"
      by (auto simp: eventually_inf_principal eventually_uniformity_metric)
    from filter_leD[OF FF_le this] show ?thesis
      by (auto simp: eventually_prod_same)
  qed

  have "\<exists>P. \<forall>n. ?P (P n) (1 / Suc n) \<and> P (Suc n) \<le> P n"
  proof (rule dependent_nat_choice)
    show "\<exists>P. ?P P (1 / Suc 0)"
      using P[of 1] by auto
  next
    fix P n assume "?P P (1/Suc n)"
    moreover obtain Q where "?P Q (1 / Suc (Suc n))"
      using P[of "1/Suc (Suc n)"] by auto
    ultimately show "\<exists>Q. ?P Q (1 / Suc (Suc n)) \<and> Q \<le> P"
      by (intro exI[of _ "\<lambda>x. P x \<and> Q x"]) (auto simp: eventually_conj_iff)
  qed
  then obtain P where P: "eventually (P n) F" "P n x \<Longrightarrow> x \<in> S"
    "P n x \<Longrightarrow> P n y \<Longrightarrow> dist x y < 1 / Suc n" "P (Suc n) \<le> P n"
    for n x y
    by metis
  have "antimono P"
    using P(4) unfolding decseq_Suc_iff le_fun_def by blast

  obtain X where X: "P n (X n)" for n
    using P(1)[THEN eventually_happens'[OF \<open>F \<noteq> bot\<close>]] by metis
  have "Cauchy X"
    unfolding metric_Cauchy_iff2 inverse_eq_divide
  proof (intro exI allI impI)
    fix j m n :: nat
    assume "j \<le> m" "j \<le> n"
    with \<open>antimono P\<close> X have "P j (X m)" "P j (X n)"
      by (auto simp: antimono_def)
    then show "dist (X m) (X n) < 1 / Suc j"
      by (rule P)
  qed
  moreover have "\<forall>n. X n \<in> S"
    using P(2) X by auto
  ultimately obtain x where "X \<longlonglongrightarrow> x" "x \<in> S"
    using seq by blast

  show "\<exists>x\<in>S. F \<le> nhds x"
  proof (rule bexI)
    have "eventually (\<lambda>y. dist y x < e) F" if "0 < e" for e :: real
    proof -
      from that have "(\<lambda>n. 1 / Suc n :: real) \<longlonglongrightarrow> 0 \<and> 0 < e / 2"
        by (subst LIMSEQ_Suc_iff) (auto intro!: lim_1_over_n)
      then have "\<forall>\<^sub>F n in sequentially. dist (X n) x < e / 2 \<and> 1 / Suc n < e / 2"
        using \<open>X \<longlonglongrightarrow> x\<close>
        unfolding tendsto_iff order_tendsto_iff[where 'a=real] eventually_conj_iff
        by blast
      then obtain n where "dist x (X n) < e / 2" "1 / Suc n < e / 2"
        by (auto simp: eventually_sequentially dist_commute)
      show ?thesis
        using \<open>eventually (P n) F\<close>
      proof eventually_elim
        case (elim y)
        then have "dist y (X n) < 1 / Suc n"
          by (intro X P)
        also have "\<dots> < e / 2" by fact
        finally show "dist y x < e"
          by (rule dist_triangle_half_l) fact
      qed
    qed
    then show "F \<le> nhds x"
      unfolding nhds_metric le_INF_iff le_principal by auto
  qed fact
qed

lemma (in metric_space) totally_bounded_metric:
  "totally_bounded S \<longleftrightarrow> (\<forall>e>0. \<exists>k. finite k \<and> S \<subseteq> (\<Union>x\<in>k. {y. dist x y < e}))"
  apply (simp only: totally_bounded_def eventually_uniformity_metric imp_ex)
  apply (subst all_comm)
  apply (intro arg_cong[where f=All] ext)
  apply safe
  subgoal for e
    apply (erule allE[of _ "\<lambda>(x, y). dist x y < e"])
    apply auto
    done
  subgoal for e P k
    apply (intro exI[of _ k])
    apply (force simp: subset_eq)
    done
  done


subsubsection \<open>Cauchy Sequences are Convergent\<close>

(* TODO: update to uniform_space *)
class complete_space = metric_space +
  assumes Cauchy_convergent: "Cauchy X \<Longrightarrow> convergent X"

lemma Cauchy_convergent_iff: "Cauchy X \<longleftrightarrow> convergent X"
  for X :: "nat \<Rightarrow> 'a::complete_space"
  by (blast intro: Cauchy_convergent convergent_Cauchy)


subsection \<open>The set of real numbers is a complete metric space\<close>

text \<open>
  Proof that Cauchy sequences converge based on the one from
  \<^url>\<open>http://pirate.shu.edu/~wachsmut/ira/numseq/proofs/cauconv.html\<close>
\<close>

text \<open>
  If sequence @{term "X"} is Cauchy, then its limit is the lub of
  @{term "{r::real. \<exists>N. \<forall>n\<ge>N. r < X n}"}
\<close>
lemma increasing_LIMSEQ:
  fixes f :: "nat \<Rightarrow> real"
  assumes inc: "\<And>n. f n \<le> f (Suc n)"
    and bdd: "\<And>n. f n \<le> l"
    and en: "\<And>e. 0 < e \<Longrightarrow> \<exists>n. l \<le> f n + e"
  shows "f \<longlonglongrightarrow> l"
proof (rule increasing_tendsto)
  fix x
  assume "x < l"
  with dense[of 0 "l - x"] obtain e where "0 < e" "e < l - x"
    by auto
  from en[OF \<open>0 < e\<close>] obtain n where "l - e \<le> f n"
    by (auto simp: field_simps)
  with \<open>e < l - x\<close> \<open>0 < e\<close> have "x < f n"
    by simp
  with incseq_SucI[of f, OF inc] show "eventually (\<lambda>n. x < f n) sequentially"
    by (auto simp: eventually_sequentially incseq_def intro: less_le_trans)
qed (use bdd in auto)

lemma real_Cauchy_convergent:
  fixes X :: "nat \<Rightarrow> real"
  assumes X: "Cauchy X"
  shows "convergent X"
proof -
  define S :: "real set" where "S = {x. \<exists>N. \<forall>n\<ge>N. x < X n}"
  then have mem_S: "\<And>N x. \<forall>n\<ge>N. x < X n \<Longrightarrow> x \<in> S"
    by auto

  have bound_isUb: "y \<le> x" if N: "\<forall>n\<ge>N. X n < x" and "y \<in> S" for N and x y :: real
  proof -
    from that have "\<exists>M. \<forall>n\<ge>M. y < X n"
      by (simp add: S_def)
    then obtain M where "\<forall>n\<ge>M. y < X n" ..
    then have "y < X (max M N)" by simp
    also have "\<dots> < x" using N by simp
    finally show ?thesis by (rule order_less_imp_le)
  qed

  obtain N where "\<forall>m\<ge>N. \<forall>n\<ge>N. dist (X m) (X n) < 1"
    using X[THEN metric_CauchyD, OF zero_less_one] by auto
  then have N: "\<forall>n\<ge>N. dist (X n) (X N) < 1" by simp
  have [simp]: "S \<noteq> {}"
  proof (intro exI ex_in_conv[THEN iffD1])
    from N have "\<forall>n\<ge>N. X N - 1 < X n"
      by (simp add: abs_diff_less_iff dist_real_def)
    then show "X N - 1 \<in> S" by (rule mem_S)
  qed
  have [simp]: "bdd_above S"
  proof
    from N have "\<forall>n\<ge>N. X n < X N + 1"
      by (simp add: abs_diff_less_iff dist_real_def)
    then show "\<And>s. s \<in> S \<Longrightarrow>  s \<le> X N + 1"
      by (rule bound_isUb)
  qed
  have "X \<longlonglongrightarrow> Sup S"
  proof (rule metric_LIMSEQ_I)
    fix r :: real
    assume "0 < r"
    then have r: "0 < r/2" by simp
    obtain N where "\<forall>n\<ge>N. \<forall>m\<ge>N. dist (X n) (X m) < r/2"
      using metric_CauchyD [OF X r] by auto
    then have "\<forall>n\<ge>N. dist (X n) (X N) < r/2" by simp
    then have N: "\<forall>n\<ge>N. X N - r/2 < X n \<and> X n < X N + r/2"
      by (simp only: dist_real_def abs_diff_less_iff)

    from N have "\<forall>n\<ge>N. X N - r/2 < X n" by blast
    then have "X N - r/2 \<in> S" by (rule mem_S)
    then have 1: "X N - r/2 \<le> Sup S" by (simp add: cSup_upper)

    from N have "\<forall>n\<ge>N. X n < X N + r/2" by blast
    from bound_isUb[OF this]
    have 2: "Sup S \<le> X N + r/2"
      by (intro cSup_least) simp_all

    show "\<exists>N. \<forall>n\<ge>N. dist (X n) (Sup S) < r"
    proof (intro exI allI impI)
      fix n
      assume n: "N \<le> n"
      from N n have "X n < X N + r/2" and "X N - r/2 < X n"
        by simp_all
      then show "dist (X n) (Sup S) < r" using 1 2
        by (simp add: abs_diff_less_iff dist_real_def)
    qed
  qed
  then show ?thesis by (auto simp: convergent_def)
qed

instance real :: complete_space
  by intro_classes (rule real_Cauchy_convergent)

class banach = real_normed_vector + complete_space

instance real :: banach ..

lemma tendsto_at_topI_sequentially:
  fixes f :: "real \<Rightarrow> 'b::first_countable_topology"
  assumes *: "\<And>X. filterlim X at_top sequentially \<Longrightarrow> (\<lambda>n. f (X n)) \<longlonglongrightarrow> y"
  shows "(f \<longlongrightarrow> y) at_top"
proof -
  obtain A where A: "decseq A" "open (A n)" "y \<in> A n" "nhds y = (INF n. principal (A n))" for n
    by (rule nhds_countable[of y]) (rule that)

  have "\<forall>m. \<exists>k. \<forall>x\<ge>k. f x \<in> A m"
  proof (rule ccontr)
    assume "\<not> (\<forall>m. \<exists>k. \<forall>x\<ge>k. f x \<in> A m)"
    then obtain m where "\<And>k. \<exists>x\<ge>k. f x \<notin> A m"
      by auto
    then have "\<exists>X. \<forall>n. (f (X n) \<notin> A m) \<and> max n (X n) + 1 \<le> X (Suc n)"
      by (intro dependent_nat_choice) (auto simp del: max.bounded_iff)
    then obtain X where X: "\<And>n. f (X n) \<notin> A m" "\<And>n. max n (X n) + 1 \<le> X (Suc n)"
      by auto
    have "1 \<le> n \<Longrightarrow> real n \<le> X n" for n
      using X[of "n - 1"] by auto
    then have "filterlim X at_top sequentially"
      by (force intro!: filterlim_at_top_mono[OF filterlim_real_sequentially]
          simp: eventually_sequentially)
    from topological_tendstoD[OF *[OF this] A(2, 3), of m] X(1) show False
      by auto
  qed
  then obtain k where "k m \<le> x \<Longrightarrow> f x \<in> A m" for m x
    by metis
  then show ?thesis
    unfolding at_top_def A by (intro filterlim_base[where i=k]) auto
qed

lemma tendsto_at_topI_sequentially_real:
  fixes f :: "real \<Rightarrow> real"
  assumes mono: "mono f"
    and limseq: "(\<lambda>n. f (real n)) \<longlonglongrightarrow> y"
  shows "(f \<longlongrightarrow> y) at_top"
proof (rule tendstoI)
  fix e :: real
  assume "0 < e"
  with limseq obtain N :: nat where N: "N \<le> n \<Longrightarrow> \<bar>f (real n) - y\<bar> < e" for n
    by (auto simp: lim_sequentially dist_real_def)
  have le: "f x \<le> y" for x :: real
  proof -
    obtain n where "x \<le> real_of_nat n"
      using real_arch_simple[of x] ..
    note monoD[OF mono this]
    also have "f (real_of_nat n) \<le> y"
      by (rule LIMSEQ_le_const[OF limseq]) (auto intro!: exI[of _ n] monoD[OF mono])
    finally show ?thesis .
  qed
  have "eventually (\<lambda>x. real N \<le> x) at_top"
    by (rule eventually_ge_at_top)
  then show "eventually (\<lambda>x. dist (f x) y < e) at_top"
  proof eventually_elim
    case (elim x)
    with N[of N] le have "y - f (real N) < e" by auto
    moreover note monoD[OF mono elim]
    ultimately show "dist (f x) y < e"
      using le[of x] by (auto simp: dist_real_def field_simps)
  qed
qed

end
