(*  Title:      HOL/Fields.thy
    Author:     Gertrud Bauer
    Author:     Steven Obua
    Author:     Tobias Nipkow
    Author:     Lawrence C Paulson
    Author:     Markus Wenzel
    Author:     Jeremy Avigad
*)

section \<open>Fields\<close>

theory Fields
imports Nat
begin

subsection \<open>Division rings\<close>

text \<open>
  A division ring is like a field, but without the commutativity requirement.
\<close>

class inverse = divide +
  fixes inverse :: "'a \<Rightarrow> 'a"
begin
  
abbreviation inverse_divide :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "'/" 70)
where
  "inverse_divide \<equiv> divide"

end

text \<open>Setup for linear arithmetic prover\<close>

ML_file "~~/src/Provers/Arith/fast_lin_arith.ML"
ML_file "Tools/lin_arith.ML"
setup \<open>Lin_Arith.global_setup\<close>
declaration \<open>K Lin_Arith.setup\<close>

simproc_setup fast_arith_nat ("(m::nat) < n" | "(m::nat) \<le> n" | "(m::nat) = n") =
  \<open>K Lin_Arith.simproc\<close>
(* Because of this simproc, the arithmetic solver is really only
useful to detect inconsistencies among the premises for subgoals which are
*not* themselves (in)equalities, because the latter activate
fast_nat_arith_simproc anyway. However, it seems cheaper to activate the
solver all the time rather than add the additional check. *)

lemmas [arith_split] = nat_diff_split split_min split_max


text\<open>Lemmas \<open>divide_simps\<close> move division to the outside and eliminates them on (in)equalities.\<close>

named_theorems divide_simps "rewrite rules to eliminate divisions"

class division_ring = ring_1 + inverse +
  assumes left_inverse [simp]:  "a \<noteq> 0 \<Longrightarrow> inverse a * a = 1"
  assumes right_inverse [simp]: "a \<noteq> 0 \<Longrightarrow> a * inverse a = 1"
  assumes divide_inverse: "a / b = a * inverse b"
  assumes inverse_zero [simp]: "inverse 0 = 0"
begin

subclass ring_1_no_zero_divisors
proof
  fix a b :: 'a
  assume a: "a \<noteq> 0" and b: "b \<noteq> 0"
  show "a * b \<noteq> 0"
  proof
    assume ab: "a * b = 0"
    hence "0 = inverse a * (a * b) * inverse b" by simp
    also have "\<dots> = (inverse a * a) * (b * inverse b)"
      by (simp only: mult.assoc)
    also have "\<dots> = 1" using a b by simp
    finally show False by simp
  qed
qed

lemma nonzero_imp_inverse_nonzero:
  "a \<noteq> 0 \<Longrightarrow> inverse a \<noteq> 0"
proof
  assume ianz: "inverse a = 0"
  assume "a \<noteq> 0"
  hence "1 = a * inverse a" by simp
  also have "... = 0" by (simp add: ianz)
  finally have "1 = 0" .
  thus False by (simp add: eq_commute)
qed

lemma inverse_zero_imp_zero:
  "inverse a = 0 \<Longrightarrow> a = 0"
apply (rule classical)
apply (drule nonzero_imp_inverse_nonzero)
apply auto
done

lemma inverse_unique:
  assumes ab: "a * b = 1"
  shows "inverse a = b"
proof -
  have "a \<noteq> 0" using ab by (cases "a = 0") simp_all
  moreover have "inverse a * (a * b) = inverse a" by (simp add: ab)
  ultimately show ?thesis by (simp add: mult.assoc [symmetric])
qed

lemma nonzero_inverse_minus_eq:
  "a \<noteq> 0 \<Longrightarrow> inverse (- a) = - inverse a"
by (rule inverse_unique) simp

lemma nonzero_inverse_inverse_eq:
  "a \<noteq> 0 \<Longrightarrow> inverse (inverse a) = a"
by (rule inverse_unique) simp

lemma nonzero_inverse_eq_imp_eq:
  assumes "inverse a = inverse b" and "a \<noteq> 0" and "b \<noteq> 0"
  shows "a = b"
proof -
  from \<open>inverse a = inverse b\<close>
  have "inverse (inverse a) = inverse (inverse b)" by (rule arg_cong)
  with \<open>a \<noteq> 0\<close> and \<open>b \<noteq> 0\<close> show "a = b"
    by (simp add: nonzero_inverse_inverse_eq)
qed

lemma inverse_1 [simp]: "inverse 1 = 1"
by (rule inverse_unique) simp

lemma nonzero_inverse_mult_distrib:
  assumes "a \<noteq> 0" and "b \<noteq> 0"
  shows "inverse (a * b) = inverse b * inverse a"
proof -
  have "a * (b * inverse b) * inverse a = 1" using assms by simp
  hence "a * b * (inverse b * inverse a) = 1" by (simp only: mult.assoc)
  thus ?thesis by (rule inverse_unique)
qed

lemma division_ring_inverse_add:
  "a \<noteq> 0 \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> inverse a + inverse b = inverse a * (a + b) * inverse b"
by (simp add: algebra_simps)

lemma division_ring_inverse_diff:
  "a \<noteq> 0 \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> inverse a - inverse b = inverse a * (b - a) * inverse b"
by (simp add: algebra_simps)

lemma right_inverse_eq: "b \<noteq> 0 \<Longrightarrow> a / b = 1 \<longleftrightarrow> a = b"
proof
  assume neq: "b \<noteq> 0"
  {
    hence "a = (a / b) * b" by (simp add: divide_inverse mult.assoc)
    also assume "a / b = 1"
    finally show "a = b" by simp
  next
    assume "a = b"
    with neq show "a / b = 1" by (simp add: divide_inverse)
  }
qed

lemma nonzero_inverse_eq_divide: "a \<noteq> 0 \<Longrightarrow> inverse a = 1 / a"
by (simp add: divide_inverse)

lemma divide_self [simp]: "a \<noteq> 0 \<Longrightarrow> a / a = 1"
by (simp add: divide_inverse)

lemma inverse_eq_divide [field_simps, divide_simps]: "inverse a = 1 / a"
by (simp add: divide_inverse)

lemma add_divide_distrib: "(a+b) / c = a/c + b/c"
by (simp add: divide_inverse algebra_simps)

lemma times_divide_eq_right [simp]: "a * (b / c) = (a * b) / c"
  by (simp add: divide_inverse mult.assoc)

lemma minus_divide_left: "- (a / b) = (-a) / b"
  by (simp add: divide_inverse)

lemma nonzero_minus_divide_right: "b \<noteq> 0 ==> - (a / b) = a / (- b)"
  by (simp add: divide_inverse nonzero_inverse_minus_eq)

lemma nonzero_minus_divide_divide: "b \<noteq> 0 ==> (-a) / (-b) = a / b"
  by (simp add: divide_inverse nonzero_inverse_minus_eq)

lemma divide_minus_left [simp]: "(-a) / b = - (a / b)"
  by (simp add: divide_inverse)

lemma diff_divide_distrib: "(a - b) / c = a / c - b / c"
  using add_divide_distrib [of a "- b" c] by simp

lemma nonzero_eq_divide_eq [field_simps]: "c \<noteq> 0 \<Longrightarrow> a = b / c \<longleftrightarrow> a * c = b"
proof -
  assume [simp]: "c \<noteq> 0"
  have "a = b / c \<longleftrightarrow> a * c = (b / c) * c" by simp
  also have "... \<longleftrightarrow> a * c = b" by (simp add: divide_inverse mult.assoc)
  finally show ?thesis .
qed

lemma nonzero_divide_eq_eq [field_simps]: "c \<noteq> 0 \<Longrightarrow> b / c = a \<longleftrightarrow> b = a * c"
proof -
  assume [simp]: "c \<noteq> 0"
  have "b / c = a \<longleftrightarrow> (b / c) * c = a * c" by simp
  also have "... \<longleftrightarrow> b = a * c" by (simp add: divide_inverse mult.assoc)
  finally show ?thesis .
qed

lemma nonzero_neg_divide_eq_eq [field_simps]: "b \<noteq> 0 \<Longrightarrow> - (a / b) = c \<longleftrightarrow> - a = c * b"
  using nonzero_divide_eq_eq[of b "-a" c] by simp

lemma nonzero_neg_divide_eq_eq2 [field_simps]: "b \<noteq> 0 \<Longrightarrow> c = - (a / b) \<longleftrightarrow> c * b = - a"
  using nonzero_neg_divide_eq_eq[of b a c] by auto

lemma divide_eq_imp: "c \<noteq> 0 \<Longrightarrow> b = a * c \<Longrightarrow> b / c = a"
  by (simp add: divide_inverse mult.assoc)

lemma eq_divide_imp: "c \<noteq> 0 \<Longrightarrow> a * c = b \<Longrightarrow> a = b / c"
  by (drule sym) (simp add: divide_inverse mult.assoc)

lemma add_divide_eq_iff [field_simps]:
  "z \<noteq> 0 \<Longrightarrow> x + y / z = (x * z + y) / z"
  by (simp add: add_divide_distrib nonzero_eq_divide_eq)

lemma divide_add_eq_iff [field_simps]:
  "z \<noteq> 0 \<Longrightarrow> x / z + y = (x + y * z) / z"
  by (simp add: add_divide_distrib nonzero_eq_divide_eq)

lemma diff_divide_eq_iff [field_simps]:
  "z \<noteq> 0 \<Longrightarrow> x - y / z = (x * z - y) / z"
  by (simp add: diff_divide_distrib nonzero_eq_divide_eq eq_diff_eq)

lemma minus_divide_add_eq_iff [field_simps]:
  "z \<noteq> 0 \<Longrightarrow> - (x / z) + y = (- x + y * z) / z"
  by (simp add: add_divide_distrib diff_divide_eq_iff)

lemma divide_diff_eq_iff [field_simps]:
  "z \<noteq> 0 \<Longrightarrow> x / z - y = (x - y * z) / z"
  by (simp add: field_simps)

lemma minus_divide_diff_eq_iff [field_simps]:
  "z \<noteq> 0 \<Longrightarrow> - (x / z) - y = (- x - y * z) / z"
  by (simp add: divide_diff_eq_iff[symmetric])

lemma division_ring_divide_zero [simp]:
  "a / 0 = 0"
  by (simp add: divide_inverse)

lemma divide_self_if [simp]:
  "a / a = (if a = 0 then 0 else 1)"
  by simp

lemma inverse_nonzero_iff_nonzero [simp]:
  "inverse a = 0 \<longleftrightarrow> a = 0"
  by rule (fact inverse_zero_imp_zero, simp)

lemma inverse_minus_eq [simp]:
  "inverse (- a) = - inverse a"
proof cases
  assume "a=0" thus ?thesis by simp
next
  assume "a\<noteq>0"
  thus ?thesis by (simp add: nonzero_inverse_minus_eq)
qed

lemma inverse_inverse_eq [simp]:
  "inverse (inverse a) = a"
proof cases
  assume "a=0" thus ?thesis by simp
next
  assume "a\<noteq>0"
  thus ?thesis by (simp add: nonzero_inverse_inverse_eq)
qed

lemma inverse_eq_imp_eq:
  "inverse a = inverse b \<Longrightarrow> a = b"
  by (drule arg_cong [where f="inverse"], simp)

lemma inverse_eq_iff_eq [simp]:
  "inverse a = inverse b \<longleftrightarrow> a = b"
  by (force dest!: inverse_eq_imp_eq)

lemma add_divide_eq_if_simps [divide_simps]:
    "a + b / z = (if z = 0 then a else (a * z + b) / z)"
    "a / z + b = (if z = 0 then b else (a + b * z) / z)"
    "- (a / z) + b = (if z = 0 then b else (-a + b * z) / z)"
    "a - b / z = (if z = 0 then a else (a * z - b) / z)"
    "a / z - b = (if z = 0 then -b else (a - b * z) / z)"
    "- (a / z) - b = (if z = 0 then -b else (- a - b * z) / z)"
  by (simp_all add: add_divide_eq_iff divide_add_eq_iff diff_divide_eq_iff divide_diff_eq_iff
      minus_divide_diff_eq_iff)

lemma [divide_simps]:
  shows divide_eq_eq: "b / c = a \<longleftrightarrow> (if c \<noteq> 0 then b = a * c else a = 0)"
    and eq_divide_eq: "a = b / c \<longleftrightarrow> (if c \<noteq> 0 then a * c = b else a = 0)"
    and minus_divide_eq_eq: "- (b / c) = a \<longleftrightarrow> (if c \<noteq> 0 then - b = a * c else a = 0)"
    and eq_minus_divide_eq: "a = - (b / c) \<longleftrightarrow> (if c \<noteq> 0 then a * c = - b else a = 0)"
  by (auto simp add:  field_simps)

end

subsection \<open>Fields\<close>

class field = comm_ring_1 + inverse +
  assumes field_inverse: "a \<noteq> 0 \<Longrightarrow> inverse a * a = 1"
  assumes field_divide_inverse: "a / b = a * inverse b"
  assumes field_inverse_zero: "inverse 0 = 0"
begin

subclass division_ring
proof
  fix a :: 'a
  assume "a \<noteq> 0"
  thus "inverse a * a = 1" by (rule field_inverse)
  thus "a * inverse a = 1" by (simp only: mult.commute)
next
  fix a b :: 'a
  show "a / b = a * inverse b" by (rule field_divide_inverse)
next
  show "inverse 0 = 0"
    by (fact field_inverse_zero) 
qed

subclass idom_divide
proof
  fix b a
  assume "b \<noteq> 0"
  then show "a * b / b = a"
    by (simp add: divide_inverse ac_simps)
next
  fix a
  show "a / 0 = 0"
    by (simp add: divide_inverse)
qed

text\<open>There is no slick version using division by zero.\<close>
lemma inverse_add:
  "a \<noteq> 0 \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> inverse a + inverse b = (a + b) * inverse a * inverse b"
  by (simp add: division_ring_inverse_add ac_simps)

lemma nonzero_mult_divide_mult_cancel_left [simp]:
  assumes [simp]: "c \<noteq> 0"
  shows "(c * a) / (c * b) = a / b"
proof (cases "b = 0")
  case True then show ?thesis by simp
next
  case False
  then have "(c*a)/(c*b) = c * a * (inverse b * inverse c)"
    by (simp add: divide_inverse nonzero_inverse_mult_distrib)
  also have "... =  a * inverse b * (inverse c * c)"
    by (simp only: ac_simps)
  also have "... =  a * inverse b" by simp
    finally show ?thesis by (simp add: divide_inverse)
qed

lemma nonzero_mult_divide_mult_cancel_right [simp]:
  "c \<noteq> 0 \<Longrightarrow> (a * c) / (b * c) = a / b"
  using nonzero_mult_divide_mult_cancel_left [of c a b] by (simp add: ac_simps)

lemma times_divide_eq_left [simp]: "(b / c) * a = (b * a) / c"
  by (simp add: divide_inverse ac_simps)

lemma divide_inverse_commute: "a / b = inverse b * a"
  by (simp add: divide_inverse mult.commute)

lemma add_frac_eq:
  assumes "y \<noteq> 0" and "z \<noteq> 0"
  shows "x / y + w / z = (x * z + w * y) / (y * z)"
proof -
  have "x / y + w / z = (x * z) / (y * z) + (y * w) / (y * z)"
    using assms by simp
  also have "\<dots> = (x * z + y * w) / (y * z)"
    by (simp only: add_divide_distrib)
  finally show ?thesis
    by (simp only: mult.commute)
qed

text\<open>Special Cancellation Simprules for Division\<close>

lemma nonzero_divide_mult_cancel_right [simp]:
  "b \<noteq> 0 \<Longrightarrow> b / (a * b) = 1 / a"
  using nonzero_mult_divide_mult_cancel_right [of b 1 a] by simp

lemma nonzero_divide_mult_cancel_left [simp]:
  "a \<noteq> 0 \<Longrightarrow> a / (a * b) = 1 / b"
  using nonzero_mult_divide_mult_cancel_left [of a 1 b] by simp

lemma nonzero_mult_divide_mult_cancel_left2 [simp]:
  "c \<noteq> 0 \<Longrightarrow> (c * a) / (b * c) = a / b"
  using nonzero_mult_divide_mult_cancel_left [of c a b] by (simp add: ac_simps)

lemma nonzero_mult_divide_mult_cancel_right2 [simp]:
  "c \<noteq> 0 \<Longrightarrow> (a * c) / (c * b) = a / b"
  using nonzero_mult_divide_mult_cancel_right [of b c a] by (simp add: ac_simps)

lemma diff_frac_eq:
  "y \<noteq> 0 \<Longrightarrow> z \<noteq> 0 \<Longrightarrow> x / y - w / z = (x * z - w * y) / (y * z)"
  by (simp add: field_simps)

lemma frac_eq_eq:
  "y \<noteq> 0 \<Longrightarrow> z \<noteq> 0 \<Longrightarrow> (x / y = w / z) = (x * z = w * y)"
  by (simp add: field_simps)

lemma divide_minus1 [simp]: "x / - 1 = - x"
  using nonzero_minus_divide_right [of "1" x] by simp

text\<open>This version builds in division by zero while also re-orienting
      the right-hand side.\<close>
lemma inverse_mult_distrib [simp]:
  "inverse (a * b) = inverse a * inverse b"
proof cases
  assume "a \<noteq> 0 & b \<noteq> 0"
  thus ?thesis by (simp add: nonzero_inverse_mult_distrib ac_simps)
next
  assume "~ (a \<noteq> 0 & b \<noteq> 0)"
  thus ?thesis by force
qed

lemma inverse_divide [simp]:
  "inverse (a / b) = b / a"
  by (simp add: divide_inverse mult.commute)


text \<open>Calculations with fractions\<close>

text\<open>There is a whole bunch of simp-rules just for class \<open>field\<close> but none for class \<open>field\<close> and \<open>nonzero_divides\<close>
because the latter are covered by a simproc.\<close>

lemma mult_divide_mult_cancel_left:
  "c \<noteq> 0 \<Longrightarrow> (c * a) / (c * b) = a / b"
apply (cases "b = 0")
apply simp_all
done

lemma mult_divide_mult_cancel_right:
  "c \<noteq> 0 \<Longrightarrow> (a * c) / (b * c) = a / b"
apply (cases "b = 0")
apply simp_all
done

lemma divide_divide_eq_right [simp]:
  "a / (b / c) = (a * c) / b"
  by (simp add: divide_inverse ac_simps)

lemma divide_divide_eq_left [simp]:
  "(a / b) / c = a / (b * c)"
  by (simp add: divide_inverse mult.assoc)

lemma divide_divide_times_eq:
  "(x / y) / (z / w) = (x * w) / (y * z)"
  by simp

text \<open>Special Cancellation Simprules for Division\<close>

lemma mult_divide_mult_cancel_left_if [simp]:
  shows "(c * a) / (c * b) = (if c = 0 then 0 else a / b)"
  by simp


text \<open>Division and Unary Minus\<close>

lemma minus_divide_right:
  "- (a / b) = a / - b"
  by (simp add: divide_inverse)

lemma divide_minus_right [simp]:
  "a / - b = - (a / b)"
  by (simp add: divide_inverse)

lemma minus_divide_divide:
  "(- a) / (- b) = a / b"
apply (cases "b=0", simp)
apply (simp add: nonzero_minus_divide_divide)
done

lemma inverse_eq_1_iff [simp]:
  "inverse x = 1 \<longleftrightarrow> x = 1"
  by (insert inverse_eq_iff_eq [of x 1], simp)

lemma divide_eq_0_iff [simp]:
  "a / b = 0 \<longleftrightarrow> a = 0 \<or> b = 0"
  by (simp add: divide_inverse)

lemma divide_cancel_right [simp]:
  "a / c = b / c \<longleftrightarrow> c = 0 \<or> a = b"
  apply (cases "c=0", simp)
  apply (simp add: divide_inverse)
  done

lemma divide_cancel_left [simp]:
  "c / a = c / b \<longleftrightarrow> c = 0 \<or> a = b"
  apply (cases "c=0", simp)
  apply (simp add: divide_inverse)
  done

lemma divide_eq_1_iff [simp]:
  "a / b = 1 \<longleftrightarrow> b \<noteq> 0 \<and> a = b"
  apply (cases "b=0", simp)
  apply (simp add: right_inverse_eq)
  done

lemma one_eq_divide_iff [simp]:
  "1 = a / b \<longleftrightarrow> b \<noteq> 0 \<and> a = b"
  by (simp add: eq_commute [of 1])

lemma times_divide_times_eq:
  "(x / y) * (z / w) = (x * z) / (y * w)"
  by simp

lemma add_frac_num:
  "y \<noteq> 0 \<Longrightarrow> x / y + z = (x + z * y) / y"
  by (simp add: add_divide_distrib)

lemma add_num_frac:
  "y \<noteq> 0 \<Longrightarrow> z + x / y = (x + z * y) / y"
  by (simp add: add_divide_distrib add.commute)

end

class field_char_0 = field + ring_char_0


subsection \<open>Ordered fields\<close>

class field_abs_sgn = field + idom_abs_sgn
begin

lemma sgn_inverse [simp]:
  "sgn (inverse a) = inverse (sgn a)"
proof (cases "a = 0")
  case True then show ?thesis by simp
next
  case False
  then have "a * inverse a = 1"
    by simp
  then have "sgn (a * inverse a) = sgn 1"
    by simp
  then have "sgn a * sgn (inverse a) = 1"
    by (simp add: sgn_mult)
  then have "inverse (sgn a) * (sgn a * sgn (inverse a)) = inverse (sgn a) * 1"
    by simp
  then have "(inverse (sgn a) * sgn a) * sgn (inverse a) = inverse (sgn a)"
    by (simp add: ac_simps)
  with False show ?thesis
    by (simp add: sgn_eq_0_iff)
qed

lemma abs_inverse [simp]:
  "\<bar>inverse a\<bar> = inverse \<bar>a\<bar>"
proof -
  from sgn_mult_abs [of "inverse a"] sgn_mult_abs [of a]
  have "inverse (sgn a) * \<bar>inverse a\<bar> = inverse (sgn a * \<bar>a\<bar>)"
    by simp
  then show ?thesis by (auto simp add: sgn_eq_0_iff)
qed
    
lemma sgn_divide [simp]:
  "sgn (a / b) = sgn a / sgn b"
  unfolding divide_inverse sgn_mult by simp

lemma abs_divide [simp]:
  "\<bar>a / b\<bar> = \<bar>a\<bar> / \<bar>b\<bar>"
  unfolding divide_inverse abs_mult by simp
  
end

class linordered_field = field + linordered_idom
begin

lemma positive_imp_inverse_positive:
  assumes a_gt_0: "0 < a"
  shows "0 < inverse a"
proof -
  have "0 < a * inverse a"
    by (simp add: a_gt_0 [THEN less_imp_not_eq2])
  thus "0 < inverse a"
    by (simp add: a_gt_0 [THEN less_not_sym] zero_less_mult_iff)
qed

lemma negative_imp_inverse_negative:
  "a < 0 \<Longrightarrow> inverse a < 0"
  by (insert positive_imp_inverse_positive [of "-a"],
    simp add: nonzero_inverse_minus_eq less_imp_not_eq)

lemma inverse_le_imp_le:
  assumes invle: "inverse a \<le> inverse b" and apos: "0 < a"
  shows "b \<le> a"
proof (rule classical)
  assume "~ b \<le> a"
  hence "a < b"  by (simp add: linorder_not_le)
  hence bpos: "0 < b"  by (blast intro: apos less_trans)
  hence "a * inverse a \<le> a * inverse b"
    by (simp add: apos invle less_imp_le mult_left_mono)
  hence "(a * inverse a) * b \<le> (a * inverse b) * b"
    by (simp add: bpos less_imp_le mult_right_mono)
  thus "b \<le> a"  by (simp add: mult.assoc apos bpos less_imp_not_eq2)
qed

lemma inverse_positive_imp_positive:
  assumes inv_gt_0: "0 < inverse a" and nz: "a \<noteq> 0"
  shows "0 < a"
proof -
  have "0 < inverse (inverse a)"
    using inv_gt_0 by (rule positive_imp_inverse_positive)
  thus "0 < a"
    using nz by (simp add: nonzero_inverse_inverse_eq)
qed

lemma inverse_negative_imp_negative:
  assumes inv_less_0: "inverse a < 0" and nz: "a \<noteq> 0"
  shows "a < 0"
proof -
  have "inverse (inverse a) < 0"
    using inv_less_0 by (rule negative_imp_inverse_negative)
  thus "a < 0" using nz by (simp add: nonzero_inverse_inverse_eq)
qed

lemma linordered_field_no_lb:
  "\<forall>x. \<exists>y. y < x"
proof
  fix x::'a
  have m1: "- (1::'a) < 0" by simp
  from add_strict_right_mono[OF m1, where c=x]
  have "(- 1) + x < x" by simp
  thus "\<exists>y. y < x" by blast
qed

lemma linordered_field_no_ub:
  "\<forall> x. \<exists>y. y > x"
proof
  fix x::'a
  have m1: " (1::'a) > 0" by simp
  from add_strict_right_mono[OF m1, where c=x]
  have "1 + x > x" by simp
  thus "\<exists>y. y > x" by blast
qed

lemma less_imp_inverse_less:
  assumes less: "a < b" and apos:  "0 < a"
  shows "inverse b < inverse a"
proof (rule ccontr)
  assume "~ inverse b < inverse a"
  hence "inverse a \<le> inverse b" by simp
  hence "~ (a < b)"
    by (simp add: not_less inverse_le_imp_le [OF _ apos])
  thus False by (rule notE [OF _ less])
qed

lemma inverse_less_imp_less:
  "inverse a < inverse b \<Longrightarrow> 0 < a \<Longrightarrow> b < a"
apply (simp add: less_le [of "inverse a"] less_le [of "b"])
apply (force dest!: inverse_le_imp_le nonzero_inverse_eq_imp_eq)
done

text\<open>Both premises are essential. Consider -1 and 1.\<close>
lemma inverse_less_iff_less [simp]:
  "0 < a \<Longrightarrow> 0 < b \<Longrightarrow> inverse a < inverse b \<longleftrightarrow> b < a"
  by (blast intro: less_imp_inverse_less dest: inverse_less_imp_less)

lemma le_imp_inverse_le:
  "a \<le> b \<Longrightarrow> 0 < a \<Longrightarrow> inverse b \<le> inverse a"
  by (force simp add: le_less less_imp_inverse_less)

lemma inverse_le_iff_le [simp]:
  "0 < a \<Longrightarrow> 0 < b \<Longrightarrow> inverse a \<le> inverse b \<longleftrightarrow> b \<le> a"
  by (blast intro: le_imp_inverse_le dest: inverse_le_imp_le)


text\<open>These results refer to both operands being negative.  The opposite-sign
case is trivial, since inverse preserves signs.\<close>
lemma inverse_le_imp_le_neg:
  "inverse a \<le> inverse b \<Longrightarrow> b < 0 \<Longrightarrow> b \<le> a"
apply (rule classical)
apply (subgoal_tac "a < 0")
 prefer 2 apply force
apply (insert inverse_le_imp_le [of "-b" "-a"])
apply (simp add: nonzero_inverse_minus_eq)
done

lemma less_imp_inverse_less_neg:
   "a < b \<Longrightarrow> b < 0 \<Longrightarrow> inverse b < inverse a"
apply (subgoal_tac "a < 0")
 prefer 2 apply (blast intro: less_trans)
apply (insert less_imp_inverse_less [of "-b" "-a"])
apply (simp add: nonzero_inverse_minus_eq)
done

lemma inverse_less_imp_less_neg:
   "inverse a < inverse b \<Longrightarrow> b < 0 \<Longrightarrow> b < a"
apply (rule classical)
apply (subgoal_tac "a < 0")
 prefer 2
 apply force
apply (insert inverse_less_imp_less [of "-b" "-a"])
apply (simp add: nonzero_inverse_minus_eq)
done

lemma inverse_less_iff_less_neg [simp]:
  "a < 0 \<Longrightarrow> b < 0 \<Longrightarrow> inverse a < inverse b \<longleftrightarrow> b < a"
apply (insert inverse_less_iff_less [of "-b" "-a"])
apply (simp del: inverse_less_iff_less
            add: nonzero_inverse_minus_eq)
done

lemma le_imp_inverse_le_neg:
  "a \<le> b \<Longrightarrow> b < 0 ==> inverse b \<le> inverse a"
  by (force simp add: le_less less_imp_inverse_less_neg)

lemma inverse_le_iff_le_neg [simp]:
  "a < 0 \<Longrightarrow> b < 0 \<Longrightarrow> inverse a \<le> inverse b \<longleftrightarrow> b \<le> a"
  by (blast intro: le_imp_inverse_le_neg dest: inverse_le_imp_le_neg)

lemma one_less_inverse:
  "0 < a \<Longrightarrow> a < 1 \<Longrightarrow> 1 < inverse a"
  using less_imp_inverse_less [of a 1, unfolded inverse_1] .

lemma one_le_inverse:
  "0 < a \<Longrightarrow> a \<le> 1 \<Longrightarrow> 1 \<le> inverse a"
  using le_imp_inverse_le [of a 1, unfolded inverse_1] .

lemma pos_le_divide_eq [field_simps]:
  assumes "0 < c"
  shows "a \<le> b / c \<longleftrightarrow> a * c \<le> b"
proof -
  from assms have "a \<le> b / c \<longleftrightarrow> a * c \<le> (b / c) * c"
    using mult_le_cancel_right [of a c "b * inverse c"] by (auto simp add: field_simps)
  also have "... \<longleftrightarrow> a * c \<le> b"
    by (simp add: less_imp_not_eq2 [OF assms] divide_inverse mult.assoc)
  finally show ?thesis .
qed

lemma pos_less_divide_eq [field_simps]:
  assumes "0 < c"
  shows "a < b / c \<longleftrightarrow> a * c < b"
proof -
  from assms have "a < b / c \<longleftrightarrow> a * c < (b / c) * c"
    using mult_less_cancel_right [of a c "b / c"] by auto
  also have "... = (a*c < b)"
    by (simp add: less_imp_not_eq2 [OF assms] divide_inverse mult.assoc)
  finally show ?thesis .
qed

lemma neg_less_divide_eq [field_simps]:
  assumes "c < 0"
  shows "a < b / c \<longleftrightarrow> b < a * c"
proof -
  from assms have "a < b / c \<longleftrightarrow> (b / c) * c < a * c"
    using mult_less_cancel_right [of "b / c" c a] by auto
  also have "... \<longleftrightarrow> b < a * c"
    by (simp add: less_imp_not_eq [OF assms] divide_inverse mult.assoc)
  finally show ?thesis .
qed

lemma neg_le_divide_eq [field_simps]:
  assumes "c < 0"
  shows "a \<le> b / c \<longleftrightarrow> b \<le> a * c"
proof -
  from assms have "a \<le> b / c \<longleftrightarrow> (b / c) * c \<le> a * c"
    using mult_le_cancel_right [of "b * inverse c" c a] by (auto simp add: field_simps)
  also have "... \<longleftrightarrow> b \<le> a * c"
    by (simp add: less_imp_not_eq [OF assms] divide_inverse mult.assoc)
  finally show ?thesis .
qed

lemma pos_divide_le_eq [field_simps]:
  assumes "0 < c"
  shows "b / c \<le> a \<longleftrightarrow> b \<le> a * c"
proof -
  from assms have "b / c \<le> a \<longleftrightarrow> (b / c) * c \<le> a * c"
    using mult_le_cancel_right [of "b / c" c a] by auto
  also have "... \<longleftrightarrow> b \<le> a * c"
    by (simp add: less_imp_not_eq2 [OF assms] divide_inverse mult.assoc)
  finally show ?thesis .
qed

lemma pos_divide_less_eq [field_simps]:
  assumes "0 < c"
  shows "b / c < a \<longleftrightarrow> b < a * c"
proof -
  from assms have "b / c < a \<longleftrightarrow> (b / c) * c < a * c"
    using mult_less_cancel_right [of "b / c" c a] by auto
  also have "... \<longleftrightarrow> b < a * c"
    by (simp add: less_imp_not_eq2 [OF assms] divide_inverse mult.assoc)
  finally show ?thesis .
qed

lemma neg_divide_le_eq [field_simps]:
  assumes "c < 0"
  shows "b / c \<le> a \<longleftrightarrow> a * c \<le> b"
proof -
  from assms have "b / c \<le> a \<longleftrightarrow> a * c \<le> (b / c) * c"
    using mult_le_cancel_right [of a c "b / c"] by auto
  also have "... \<longleftrightarrow> a * c \<le> b"
    by (simp add: less_imp_not_eq [OF assms] divide_inverse mult.assoc)
  finally show ?thesis .
qed

lemma neg_divide_less_eq [field_simps]:
  assumes "c < 0"
  shows "b / c < a \<longleftrightarrow> a * c < b"
proof -
  from assms have "b / c < a \<longleftrightarrow> a * c < b / c * c"
    using mult_less_cancel_right [of a c "b / c"] by auto
  also have "... \<longleftrightarrow> a * c < b"
    by (simp add: less_imp_not_eq [OF assms] divide_inverse mult.assoc)
  finally show ?thesis .
qed

text\<open>The following \<open>field_simps\<close> rules are necessary, as minus is always moved atop of
division but we want to get rid of division.\<close>

lemma pos_le_minus_divide_eq [field_simps]: "0 < c \<Longrightarrow> a \<le> - (b / c) \<longleftrightarrow> a * c \<le> - b"
  unfolding minus_divide_left by (rule pos_le_divide_eq)

lemma neg_le_minus_divide_eq [field_simps]: "c < 0 \<Longrightarrow> a \<le> - (b / c) \<longleftrightarrow> - b \<le> a * c"
  unfolding minus_divide_left by (rule neg_le_divide_eq)

lemma pos_less_minus_divide_eq [field_simps]: "0 < c \<Longrightarrow> a < - (b / c) \<longleftrightarrow> a * c < - b"
  unfolding minus_divide_left by (rule pos_less_divide_eq)

lemma neg_less_minus_divide_eq [field_simps]: "c < 0 \<Longrightarrow> a < - (b / c) \<longleftrightarrow> - b < a * c"
  unfolding minus_divide_left by (rule neg_less_divide_eq)

lemma pos_minus_divide_less_eq [field_simps]: "0 < c \<Longrightarrow> - (b / c) < a \<longleftrightarrow> - b < a * c"
  unfolding minus_divide_left by (rule pos_divide_less_eq)

lemma neg_minus_divide_less_eq [field_simps]: "c < 0 \<Longrightarrow> - (b / c) < a \<longleftrightarrow> a * c < - b"
  unfolding minus_divide_left by (rule neg_divide_less_eq)

lemma pos_minus_divide_le_eq [field_simps]: "0 < c \<Longrightarrow> - (b / c) \<le> a \<longleftrightarrow> - b \<le> a * c"
  unfolding minus_divide_left by (rule pos_divide_le_eq)

lemma neg_minus_divide_le_eq [field_simps]: "c < 0 \<Longrightarrow> - (b / c) \<le> a \<longleftrightarrow> a * c \<le> - b"
  unfolding minus_divide_left by (rule neg_divide_le_eq)

lemma frac_less_eq:
  "y \<noteq> 0 \<Longrightarrow> z \<noteq> 0 \<Longrightarrow> x / y < w / z \<longleftrightarrow> (x * z - w * y) / (y * z) < 0"
  by (subst less_iff_diff_less_0) (simp add: diff_frac_eq )

lemma frac_le_eq:
  "y \<noteq> 0 \<Longrightarrow> z \<noteq> 0 \<Longrightarrow> x / y \<le> w / z \<longleftrightarrow> (x * z - w * y) / (y * z) \<le> 0"
  by (subst le_iff_diff_le_0) (simp add: diff_frac_eq )

text\<open>Lemmas \<open>sign_simps\<close> is a first attempt to automate proofs
of positivity/negativity needed for \<open>field_simps\<close>. Have not added \<open>sign_simps\<close> to \<open>field_simps\<close> because the former can lead to case
explosions.\<close>

lemmas sign_simps = algebra_simps zero_less_mult_iff mult_less_0_iff

lemmas (in -) sign_simps = algebra_simps zero_less_mult_iff mult_less_0_iff

(* Only works once linear arithmetic is installed:
text{*An example:*}
lemma fixes a b c d e f :: "'a::linordered_field"
shows "\<lbrakk>a>b; c<d; e<f; 0 < u \<rbrakk> \<Longrightarrow>
 ((a-b)*(c-d)*(e-f))/((c-d)*(e-f)*(a-b)) <
 ((e-f)*(a-b)*(c-d))/((e-f)*(a-b)*(c-d)) + u"
apply(subgoal_tac "(c-d)*(e-f)*(a-b) > 0")
 prefer 2 apply(simp add:sign_simps)
apply(subgoal_tac "(c-d)*(e-f)*(a-b)*u > 0")
 prefer 2 apply(simp add:sign_simps)
apply(simp add:field_simps)
done
*)

lemma divide_pos_pos[simp]:
  "0 < x ==> 0 < y ==> 0 < x / y"
by(simp add:field_simps)

lemma divide_nonneg_pos:
  "0 <= x ==> 0 < y ==> 0 <= x / y"
by(simp add:field_simps)

lemma divide_neg_pos:
  "x < 0 ==> 0 < y ==> x / y < 0"
by(simp add:field_simps)

lemma divide_nonpos_pos:
  "x <= 0 ==> 0 < y ==> x / y <= 0"
by(simp add:field_simps)

lemma divide_pos_neg:
  "0 < x ==> y < 0 ==> x / y < 0"
by(simp add:field_simps)

lemma divide_nonneg_neg:
  "0 <= x ==> y < 0 ==> x / y <= 0"
by(simp add:field_simps)

lemma divide_neg_neg:
  "x < 0 ==> y < 0 ==> 0 < x / y"
by(simp add:field_simps)

lemma divide_nonpos_neg:
  "x <= 0 ==> y < 0 ==> 0 <= x / y"
by(simp add:field_simps)

lemma divide_strict_right_mono:
     "[|a < b; 0 < c|] ==> a / c < b / c"
by (simp add: less_imp_not_eq2 divide_inverse mult_strict_right_mono
              positive_imp_inverse_positive)


lemma divide_strict_right_mono_neg:
     "[|b < a; c < 0|] ==> a / c < b / c"
apply (drule divide_strict_right_mono [of _ _ "-c"], simp)
apply (simp add: less_imp_not_eq nonzero_minus_divide_right [symmetric])
done

text\<open>The last premise ensures that @{term a} and @{term b}
      have the same sign\<close>
lemma divide_strict_left_mono:
  "[|b < a; 0 < c; 0 < a*b|] ==> c / a < c / b"
  by (auto simp: field_simps zero_less_mult_iff mult_strict_right_mono)

lemma divide_left_mono:
  "[|b \<le> a; 0 \<le> c; 0 < a*b|] ==> c / a \<le> c / b"
  by (auto simp: field_simps zero_less_mult_iff mult_right_mono)

lemma divide_strict_left_mono_neg:
  "[|a < b; c < 0; 0 < a*b|] ==> c / a < c / b"
  by (auto simp: field_simps zero_less_mult_iff mult_strict_right_mono_neg)

lemma mult_imp_div_pos_le: "0 < y ==> x <= z * y ==>
    x / y <= z"
by (subst pos_divide_le_eq, assumption+)

lemma mult_imp_le_div_pos: "0 < y ==> z * y <= x ==>
    z <= x / y"
by(simp add:field_simps)

lemma mult_imp_div_pos_less: "0 < y ==> x < z * y ==>
    x / y < z"
by(simp add:field_simps)

lemma mult_imp_less_div_pos: "0 < y ==> z * y < x ==>
    z < x / y"
by(simp add:field_simps)

lemma frac_le: "0 <= x ==>
    x <= y ==> 0 < w ==> w <= z  ==> x / z <= y / w"
  apply (rule mult_imp_div_pos_le)
  apply simp
  apply (subst times_divide_eq_left)
  apply (rule mult_imp_le_div_pos, assumption)
  apply (rule mult_mono)
  apply simp_all
done

lemma frac_less: "0 <= x ==>
    x < y ==> 0 < w ==> w <= z  ==> x / z < y / w"
  apply (rule mult_imp_div_pos_less)
  apply simp
  apply (subst times_divide_eq_left)
  apply (rule mult_imp_less_div_pos, assumption)
  apply (erule mult_less_le_imp_less)
  apply simp_all
done

lemma frac_less2: "0 < x ==>
    x <= y ==> 0 < w ==> w < z  ==> x / z < y / w"
  apply (rule mult_imp_div_pos_less)
  apply simp_all
  apply (rule mult_imp_less_div_pos, assumption)
  apply (erule mult_le_less_imp_less)
  apply simp_all
done

lemma less_half_sum: "a < b ==> a < (a+b) / (1+1)"
by (simp add: field_simps zero_less_two)

lemma gt_half_sum: "a < b ==> (a+b)/(1+1) < b"
by (simp add: field_simps zero_less_two)

subclass unbounded_dense_linorder
proof
  fix x y :: 'a
  from less_add_one show "\<exists>y. x < y" ..
  from less_add_one have "x + (- 1) < (x + 1) + (- 1)" by (rule add_strict_right_mono)
  then have "x - 1 < x + 1 - 1" by simp
  then have "x - 1 < x" by (simp add: algebra_simps)
  then show "\<exists>y. y < x" ..
  show "x < y \<Longrightarrow> \<exists>z>x. z < y" by (blast intro!: less_half_sum gt_half_sum)
qed

subclass field_abs_sgn ..

lemma inverse_sgn [simp]:
  "inverse (sgn a) = sgn a"
  by (cases a 0 rule: linorder_cases) simp_all

lemma divide_sgn [simp]:
  "a / sgn b = a * sgn b"
  by (cases b 0 rule: linorder_cases) simp_all

lemma nonzero_abs_inverse:
  "a \<noteq> 0 ==> \<bar>inverse a\<bar> = inverse \<bar>a\<bar>"
  by (rule abs_inverse)

lemma nonzero_abs_divide:
  "b \<noteq> 0 ==> \<bar>a / b\<bar> = \<bar>a\<bar> / \<bar>b\<bar>"
  by (rule abs_divide)

lemma field_le_epsilon:
  assumes e: "\<And>e. 0 < e \<Longrightarrow> x \<le> y + e"
  shows "x \<le> y"
proof (rule dense_le)
  fix t assume "t < x"
  hence "0 < x - t" by (simp add: less_diff_eq)
  from e [OF this] have "x + 0 \<le> x + (y - t)" by (simp add: algebra_simps)
  then have "0 \<le> y - t" by (simp only: add_le_cancel_left)
  then show "t \<le> y" by (simp add: algebra_simps)
qed

lemma inverse_positive_iff_positive [simp]:
  "(0 < inverse a) = (0 < a)"
apply (cases "a = 0", simp)
apply (blast intro: inverse_positive_imp_positive positive_imp_inverse_positive)
done

lemma inverse_negative_iff_negative [simp]:
  "(inverse a < 0) = (a < 0)"
apply (cases "a = 0", simp)
apply (blast intro: inverse_negative_imp_negative negative_imp_inverse_negative)
done

lemma inverse_nonnegative_iff_nonnegative [simp]:
  "0 \<le> inverse a \<longleftrightarrow> 0 \<le> a"
  by (simp add: not_less [symmetric])

lemma inverse_nonpositive_iff_nonpositive [simp]:
  "inverse a \<le> 0 \<longleftrightarrow> a \<le> 0"
  by (simp add: not_less [symmetric])

lemma one_less_inverse_iff: "1 < inverse x \<longleftrightarrow> 0 < x \<and> x < 1"
  using less_trans[of 1 x 0 for x]
  by (cases x 0 rule: linorder_cases) (auto simp add: field_simps)

lemma one_le_inverse_iff: "1 \<le> inverse x \<longleftrightarrow> 0 < x \<and> x \<le> 1"
proof (cases "x = 1")
  case True then show ?thesis by simp
next
  case False then have "inverse x \<noteq> 1" by simp
  then have "1 \<noteq> inverse x" by blast
  then have "1 \<le> inverse x \<longleftrightarrow> 1 < inverse x" by (simp add: le_less)
  with False show ?thesis by (auto simp add: one_less_inverse_iff)
qed

lemma inverse_less_1_iff: "inverse x < 1 \<longleftrightarrow> x \<le> 0 \<or> 1 < x"
  by (simp add: not_le [symmetric] one_le_inverse_iff)

lemma inverse_le_1_iff: "inverse x \<le> 1 \<longleftrightarrow> x \<le> 0 \<or> 1 \<le> x"
  by (simp add: not_less [symmetric] one_less_inverse_iff)

lemma [divide_simps]:
  shows le_divide_eq: "a \<le> b / c \<longleftrightarrow> (if 0 < c then a * c \<le> b else if c < 0 then b \<le> a * c else a \<le> 0)"
    and divide_le_eq: "b / c \<le> a \<longleftrightarrow> (if 0 < c then b \<le> a * c else if c < 0 then a * c \<le> b else 0 \<le> a)"
    and less_divide_eq: "a < b / c \<longleftrightarrow> (if 0 < c then a * c < b else if c < 0 then b < a * c else a < 0)"
    and divide_less_eq: "b / c < a \<longleftrightarrow> (if 0 < c then b < a * c else if c < 0 then a * c < b else 0 < a)"
    and le_minus_divide_eq: "a \<le> - (b / c) \<longleftrightarrow> (if 0 < c then a * c \<le> - b else if c < 0 then - b \<le> a * c else a \<le> 0)"
    and minus_divide_le_eq: "- (b / c) \<le> a \<longleftrightarrow> (if 0 < c then - b \<le> a * c else if c < 0 then a * c \<le> - b else 0 \<le> a)"
    and less_minus_divide_eq: "a < - (b / c) \<longleftrightarrow> (if 0 < c then a * c < - b else if c < 0 then - b < a * c else  a < 0)"
    and minus_divide_less_eq: "- (b / c) < a \<longleftrightarrow> (if 0 < c then - b < a * c else if c < 0 then a * c < - b else 0 < a)"
  by (auto simp: field_simps not_less dest: antisym)

text \<open>Division and Signs\<close>

lemma
  shows zero_less_divide_iff: "0 < a / b \<longleftrightarrow> 0 < a \<and> 0 < b \<or> a < 0 \<and> b < 0"
    and divide_less_0_iff: "a / b < 0 \<longleftrightarrow> 0 < a \<and> b < 0 \<or> a < 0 \<and> 0 < b"
    and zero_le_divide_iff: "0 \<le> a / b \<longleftrightarrow> 0 \<le> a \<and> 0 \<le> b \<or> a \<le> 0 \<and> b \<le> 0"
    and divide_le_0_iff: "a / b \<le> 0 \<longleftrightarrow> 0 \<le> a \<and> b \<le> 0 \<or> a \<le> 0 \<and> 0 \<le> b"
  by (auto simp add: divide_simps)

text \<open>Division and the Number One\<close>

text\<open>Simplify expressions equated with 1\<close>

lemma zero_eq_1_divide_iff [simp]: "0 = 1 / a \<longleftrightarrow> a = 0"
  by (cases "a = 0") (auto simp: field_simps)

lemma one_divide_eq_0_iff [simp]: "1 / a = 0 \<longleftrightarrow> a = 0"
  using zero_eq_1_divide_iff[of a] by simp

text\<open>Simplify expressions such as \<open>0 < 1/x\<close> to \<open>0 < x\<close>\<close>

lemma zero_le_divide_1_iff [simp]:
  "0 \<le> 1 / a \<longleftrightarrow> 0 \<le> a"
  by (simp add: zero_le_divide_iff)

lemma zero_less_divide_1_iff [simp]:
  "0 < 1 / a \<longleftrightarrow> 0 < a"
  by (simp add: zero_less_divide_iff)

lemma divide_le_0_1_iff [simp]:
  "1 / a \<le> 0 \<longleftrightarrow> a \<le> 0"
  by (simp add: divide_le_0_iff)

lemma divide_less_0_1_iff [simp]:
  "1 / a < 0 \<longleftrightarrow> a < 0"
  by (simp add: divide_less_0_iff)

lemma divide_right_mono:
     "[|a \<le> b; 0 \<le> c|] ==> a/c \<le> b/c"
by (force simp add: divide_strict_right_mono le_less)

lemma divide_right_mono_neg: "a <= b
    ==> c <= 0 ==> b / c <= a / c"
apply (drule divide_right_mono [of _ _ "- c"])
apply auto
done

lemma divide_left_mono_neg: "a <= b
    ==> c <= 0 ==> 0 < a * b ==> c / a <= c / b"
  apply (drule divide_left_mono [of _ _ "- c"])
  apply (auto simp add: mult.commute)
done

lemma inverse_le_iff: "inverse a \<le> inverse b \<longleftrightarrow> (0 < a * b \<longrightarrow> b \<le> a) \<and> (a * b \<le> 0 \<longrightarrow> a \<le> b)"
  by (cases a 0 b 0 rule: linorder_cases[case_product linorder_cases])
     (auto simp add: field_simps zero_less_mult_iff mult_le_0_iff)

lemma inverse_less_iff: "inverse a < inverse b \<longleftrightarrow> (0 < a * b \<longrightarrow> b < a) \<and> (a * b \<le> 0 \<longrightarrow> a < b)"
  by (subst less_le) (auto simp: inverse_le_iff)

lemma divide_le_cancel: "a / c \<le> b / c \<longleftrightarrow> (0 < c \<longrightarrow> a \<le> b) \<and> (c < 0 \<longrightarrow> b \<le> a)"
  by (simp add: divide_inverse mult_le_cancel_right)

lemma divide_less_cancel: "a / c < b / c \<longleftrightarrow> (0 < c \<longrightarrow> a < b) \<and> (c < 0 \<longrightarrow> b < a) \<and> c \<noteq> 0"
  by (auto simp add: divide_inverse mult_less_cancel_right)

text\<open>Simplify quotients that are compared with the value 1.\<close>

lemma le_divide_eq_1:
  "(1 \<le> b / a) = ((0 < a & a \<le> b) | (a < 0 & b \<le> a))"
by (auto simp add: le_divide_eq)

lemma divide_le_eq_1:
  "(b / a \<le> 1) = ((0 < a & b \<le> a) | (a < 0 & a \<le> b) | a=0)"
by (auto simp add: divide_le_eq)

lemma less_divide_eq_1:
  "(1 < b / a) = ((0 < a & a < b) | (a < 0 & b < a))"
by (auto simp add: less_divide_eq)

lemma divide_less_eq_1:
  "(b / a < 1) = ((0 < a & b < a) | (a < 0 & a < b) | a=0)"
by (auto simp add: divide_less_eq)

lemma divide_nonneg_nonneg [simp]:
  "0 \<le> x \<Longrightarrow> 0 \<le> y \<Longrightarrow> 0 \<le> x / y"
  by (auto simp add: divide_simps)

lemma divide_nonpos_nonpos:
  "x \<le> 0 \<Longrightarrow> y \<le> 0 \<Longrightarrow> 0 \<le> x / y"
  by (auto simp add: divide_simps)

lemma divide_nonneg_nonpos:
  "0 \<le> x \<Longrightarrow> y \<le> 0 \<Longrightarrow> x / y \<le> 0"
  by (auto simp add: divide_simps)

lemma divide_nonpos_nonneg:
  "x \<le> 0 \<Longrightarrow> 0 \<le> y \<Longrightarrow> x / y \<le> 0"
  by (auto simp add: divide_simps)

text \<open>Conditional Simplification Rules: No Case Splits\<close>

lemma le_divide_eq_1_pos [simp]:
  "0 < a \<Longrightarrow> (1 \<le> b/a) = (a \<le> b)"
by (auto simp add: le_divide_eq)

lemma le_divide_eq_1_neg [simp]:
  "a < 0 \<Longrightarrow> (1 \<le> b/a) = (b \<le> a)"
by (auto simp add: le_divide_eq)

lemma divide_le_eq_1_pos [simp]:
  "0 < a \<Longrightarrow> (b/a \<le> 1) = (b \<le> a)"
by (auto simp add: divide_le_eq)

lemma divide_le_eq_1_neg [simp]:
  "a < 0 \<Longrightarrow> (b/a \<le> 1) = (a \<le> b)"
by (auto simp add: divide_le_eq)

lemma less_divide_eq_1_pos [simp]:
  "0 < a \<Longrightarrow> (1 < b/a) = (a < b)"
by (auto simp add: less_divide_eq)

lemma less_divide_eq_1_neg [simp]:
  "a < 0 \<Longrightarrow> (1 < b/a) = (b < a)"
by (auto simp add: less_divide_eq)

lemma divide_less_eq_1_pos [simp]:
  "0 < a \<Longrightarrow> (b/a < 1) = (b < a)"
by (auto simp add: divide_less_eq)

lemma divide_less_eq_1_neg [simp]:
  "a < 0 \<Longrightarrow> b/a < 1 \<longleftrightarrow> a < b"
by (auto simp add: divide_less_eq)

lemma eq_divide_eq_1 [simp]:
  "(1 = b/a) = ((a \<noteq> 0 & a = b))"
by (auto simp add: eq_divide_eq)

lemma divide_eq_eq_1 [simp]:
  "(b/a = 1) = ((a \<noteq> 0 & a = b))"
by (auto simp add: divide_eq_eq)

lemma abs_div_pos: "0 < y ==>
    \<bar>x\<bar> / y = \<bar>x / y\<bar>"
  apply (subst abs_divide)
  apply (simp add: order_less_imp_le)
done

lemma zero_le_divide_abs_iff [simp]: "(0 \<le> a / \<bar>b\<bar>) = (0 \<le> a | b = 0)"
by (auto simp: zero_le_divide_iff)

lemma divide_le_0_abs_iff [simp]: "(a / \<bar>b\<bar> \<le> 0) = (a \<le> 0 | b = 0)"
by (auto simp: divide_le_0_iff)

lemma field_le_mult_one_interval:
  assumes *: "\<And>z. \<lbrakk> 0 < z ; z < 1 \<rbrakk> \<Longrightarrow> z * x \<le> y"
  shows "x \<le> y"
proof (cases "0 < x")
  assume "0 < x"
  thus ?thesis
    using dense_le_bounded[of 0 1 "y/x"] *
    unfolding le_divide_eq if_P[OF \<open>0 < x\<close>] by simp
next
  assume "\<not>0 < x" hence "x \<le> 0" by simp
  obtain s::'a where s: "0 < s" "s < 1" using dense[of 0 "1::'a"] by auto
  hence "x \<le> s * x" using mult_le_cancel_right[of 1 x s] \<open>x \<le> 0\<close> by auto
  also note *[OF s]
  finally show ?thesis .
qed

text\<open>For creating values between @{term u} and @{term v}.\<close>
lemma scaling_mono:
  assumes "u \<le> v" "0 \<le> r" "r \<le> s"
    shows "u + r * (v - u) / s \<le> v"
proof -
  have "r/s \<le> 1" using assms
    using divide_le_eq_1 by fastforce
  then have "(r/s) * (v - u) \<le> 1 * (v - u)"
    apply (rule mult_right_mono)
    using assms by simp
  then show ?thesis
    by (simp add: field_simps)
qed

end

text \<open>Min/max Simplification Rules\<close>

lemma min_mult_distrib_left:
  fixes x::"'a::linordered_idom" 
  shows "p * min x y = (if 0 \<le> p then min (p*x) (p*y) else max (p*x) (p*y))"
by (auto simp add: min_def max_def mult_le_cancel_left)

lemma min_mult_distrib_right:
  fixes x::"'a::linordered_idom" 
  shows "min x y * p = (if 0 \<le> p then min (x*p) (y*p) else max (x*p) (y*p))"
by (auto simp add: min_def max_def mult_le_cancel_right)

lemma min_divide_distrib_right:
  fixes x::"'a::linordered_field" 
  shows "min x y / p = (if 0 \<le> p then min (x/p) (y/p) else max (x/p) (y/p))"
by (simp add: min_mult_distrib_right divide_inverse)

lemma max_mult_distrib_left:
  fixes x::"'a::linordered_idom" 
  shows "p * max x y = (if 0 \<le> p then max (p*x) (p*y) else min (p*x) (p*y))"
by (auto simp add: min_def max_def mult_le_cancel_left)

lemma max_mult_distrib_right:
  fixes x::"'a::linordered_idom" 
  shows "max x y * p = (if 0 \<le> p then max (x*p) (y*p) else min (x*p) (y*p))"
by (auto simp add: min_def max_def mult_le_cancel_right)

lemma max_divide_distrib_right:
  fixes x::"'a::linordered_field" 
  shows "max x y / p = (if 0 \<le> p then max (x/p) (y/p) else min (x/p) (y/p))"
by (simp add: max_mult_distrib_right divide_inverse)

hide_fact (open) field_inverse field_divide_inverse field_inverse_zero

code_identifier
  code_module Fields \<rightharpoonup> (SML) Arith and (OCaml) Arith and (Haskell) Arith

end
