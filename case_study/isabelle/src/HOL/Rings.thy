(*  Title:      HOL/Rings.thy
    Author:     Gertrud Bauer
    Author:     Steven Obua
    Author:     Tobias Nipkow
    Author:     Lawrence C Paulson
    Author:     Markus Wenzel
    Author:     Jeremy Avigad
*)

section \<open>Rings\<close>

theory Rings
  imports Groups Set
begin

class semiring = ab_semigroup_add + semigroup_mult +
  assumes distrib_right[algebra_simps]: "(a + b) * c = a * c + b * c"
  assumes distrib_left[algebra_simps]: "a * (b + c) = a * b + a * c"
begin

text \<open>For the \<open>combine_numerals\<close> simproc\<close>
lemma combine_common_factor: "a * e + (b * e + c) = (a + b) * e + c"
  by (simp add: distrib_right ac_simps)

end

class mult_zero = times + zero +
  assumes mult_zero_left [simp]: "0 * a = 0"
  assumes mult_zero_right [simp]: "a * 0 = 0"
begin

lemma mult_not_zero: "a * b \<noteq> 0 \<Longrightarrow> a \<noteq> 0 \<and> b \<noteq> 0"
  by auto

end

class semiring_0 = semiring + comm_monoid_add + mult_zero

class semiring_0_cancel = semiring + cancel_comm_monoid_add
begin

subclass semiring_0
proof
  fix a :: 'a
  have "0 * a + 0 * a = 0 * a + 0"
    by (simp add: distrib_right [symmetric])
  then show "0 * a = 0"
    by (simp only: add_left_cancel)
  have "a * 0 + a * 0 = a * 0 + 0"
    by (simp add: distrib_left [symmetric])
  then show "a * 0 = 0"
    by (simp only: add_left_cancel)
qed

end

class comm_semiring = ab_semigroup_add + ab_semigroup_mult +
  assumes distrib: "(a + b) * c = a * c + b * c"
begin

subclass semiring
proof
  fix a b c :: 'a
  show "(a + b) * c = a * c + b * c"
    by (simp add: distrib)
  have "a * (b + c) = (b + c) * a"
    by (simp add: ac_simps)
  also have "\<dots> = b * a + c * a"
    by (simp only: distrib)
  also have "\<dots> = a * b + a * c"
    by (simp add: ac_simps)
  finally show "a * (b + c) = a * b + a * c"
    by blast
qed

end

class comm_semiring_0 = comm_semiring + comm_monoid_add + mult_zero
begin

subclass semiring_0 ..

end

class comm_semiring_0_cancel = comm_semiring + cancel_comm_monoid_add
begin

subclass semiring_0_cancel ..

subclass comm_semiring_0 ..

end

class zero_neq_one = zero + one +
  assumes zero_neq_one [simp]: "0 \<noteq> 1"
begin

lemma one_neq_zero [simp]: "1 \<noteq> 0"
  by (rule not_sym) (rule zero_neq_one)

definition of_bool :: "bool \<Rightarrow> 'a"
  where "of_bool p = (if p then 1 else 0)"

lemma of_bool_eq [simp, code]:
  "of_bool False = 0"
  "of_bool True = 1"
  by (simp_all add: of_bool_def)

lemma of_bool_eq_iff: "of_bool p = of_bool q \<longleftrightarrow> p = q"
  by (simp add: of_bool_def)

lemma split_of_bool [split]: "P (of_bool p) \<longleftrightarrow> (p \<longrightarrow> P 1) \<and> (\<not> p \<longrightarrow> P 0)"
  by (cases p) simp_all

lemma split_of_bool_asm: "P (of_bool p) \<longleftrightarrow> \<not> (p \<and> \<not> P 1 \<or> \<not> p \<and> \<not> P 0)"
  by (cases p) simp_all

end

class semiring_1 = zero_neq_one + semiring_0 + monoid_mult

text \<open>Abstract divisibility\<close>

class dvd = times
begin

definition dvd :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "dvd" 50)
  where "b dvd a \<longleftrightarrow> (\<exists>k. a = b * k)"

lemma dvdI [intro?]: "a = b * k \<Longrightarrow> b dvd a"
  unfolding dvd_def ..

lemma dvdE [elim?]: "b dvd a \<Longrightarrow> (\<And>k. a = b * k \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding dvd_def by blast

end

context comm_monoid_mult
begin

subclass dvd .

lemma dvd_refl [simp]: "a dvd a"
proof
  show "a = a * 1" by simp
qed

lemma dvd_trans [trans]:
  assumes "a dvd b" and "b dvd c"
  shows "a dvd c"
proof -
  from assms obtain v where "b = a * v"
    by (auto elim!: dvdE)
  moreover from assms obtain w where "c = b * w"
    by (auto elim!: dvdE)
  ultimately have "c = a * (v * w)"
    by (simp add: mult.assoc)
  then show ?thesis ..
qed

lemma subset_divisors_dvd: "{c. c dvd a} \<subseteq> {c. c dvd b} \<longleftrightarrow> a dvd b"
  by (auto simp add: subset_iff intro: dvd_trans)

lemma strict_subset_divisors_dvd: "{c. c dvd a} \<subset> {c. c dvd b} \<longleftrightarrow> a dvd b \<and> \<not> b dvd a"
  by (auto simp add: subset_iff intro: dvd_trans)

lemma one_dvd [simp]: "1 dvd a"
  by (auto intro!: dvdI)

lemma dvd_mult [simp]: "a dvd c \<Longrightarrow> a dvd (b * c)"
  by (auto intro!: mult.left_commute dvdI elim!: dvdE)

lemma dvd_mult2 [simp]: "a dvd b \<Longrightarrow> a dvd (b * c)"
  using dvd_mult [of a b c] by (simp add: ac_simps)

lemma dvd_triv_right [simp]: "a dvd b * a"
  by (rule dvd_mult) (rule dvd_refl)

lemma dvd_triv_left [simp]: "a dvd a * b"
  by (rule dvd_mult2) (rule dvd_refl)

lemma mult_dvd_mono:
  assumes "a dvd b"
    and "c dvd d"
  shows "a * c dvd b * d"
proof -
  from \<open>a dvd b\<close> obtain b' where "b = a * b'" ..
  moreover from \<open>c dvd d\<close> obtain d' where "d = c * d'" ..
  ultimately have "b * d = (a * c) * (b' * d')"
    by (simp add: ac_simps)
  then show ?thesis ..
qed

lemma dvd_mult_left: "a * b dvd c \<Longrightarrow> a dvd c"
  by (simp add: dvd_def mult.assoc) blast

lemma dvd_mult_right: "a * b dvd c \<Longrightarrow> b dvd c"
  using dvd_mult_left [of b a c] by (simp add: ac_simps)

end

class comm_semiring_1 = zero_neq_one + comm_semiring_0 + comm_monoid_mult
begin

subclass semiring_1 ..

lemma dvd_0_left_iff [simp]: "0 dvd a \<longleftrightarrow> a = 0"
  by (auto intro: dvd_refl elim!: dvdE)

lemma dvd_0_right [iff]: "a dvd 0"
proof
  show "0 = a * 0" by simp
qed

lemma dvd_0_left: "0 dvd a \<Longrightarrow> a = 0"
  by simp

lemma dvd_add [simp]:
  assumes "a dvd b" and "a dvd c"
  shows "a dvd (b + c)"
proof -
  from \<open>a dvd b\<close> obtain b' where "b = a * b'" ..
  moreover from \<open>a dvd c\<close> obtain c' where "c = a * c'" ..
  ultimately have "b + c = a * (b' + c')"
    by (simp add: distrib_left)
  then show ?thesis ..
qed

end

class semiring_1_cancel = semiring + cancel_comm_monoid_add
  + zero_neq_one + monoid_mult
begin

subclass semiring_0_cancel ..

subclass semiring_1 ..

end

class comm_semiring_1_cancel =
  comm_semiring + cancel_comm_monoid_add + zero_neq_one + comm_monoid_mult +
  assumes right_diff_distrib' [algebra_simps]: "a * (b - c) = a * b - a * c"
begin

subclass semiring_1_cancel ..
subclass comm_semiring_0_cancel ..
subclass comm_semiring_1 ..

lemma left_diff_distrib' [algebra_simps]: "(b - c) * a = b * a - c * a"
  by (simp add: algebra_simps)

lemma dvd_add_times_triv_left_iff [simp]: "a dvd c * a + b \<longleftrightarrow> a dvd b"
proof -
  have "a dvd a * c + b \<longleftrightarrow> a dvd b" (is "?P \<longleftrightarrow> ?Q")
  proof
    assume ?Q
    then show ?P by simp
  next
    assume ?P
    then obtain d where "a * c + b = a * d" ..
    then have "a * c + b - a * c = a * d - a * c" by simp
    then have "b = a * d - a * c" by simp
    then have "b = a * (d - c)" by (simp add: algebra_simps)
    then show ?Q ..
  qed
  then show "a dvd c * a + b \<longleftrightarrow> a dvd b" by (simp add: ac_simps)
qed

lemma dvd_add_times_triv_right_iff [simp]: "a dvd b + c * a \<longleftrightarrow> a dvd b"
  using dvd_add_times_triv_left_iff [of a c b] by (simp add: ac_simps)

lemma dvd_add_triv_left_iff [simp]: "a dvd a + b \<longleftrightarrow> a dvd b"
  using dvd_add_times_triv_left_iff [of a 1 b] by simp

lemma dvd_add_triv_right_iff [simp]: "a dvd b + a \<longleftrightarrow> a dvd b"
  using dvd_add_times_triv_right_iff [of a b 1] by simp

lemma dvd_add_right_iff:
  assumes "a dvd b"
  shows "a dvd b + c \<longleftrightarrow> a dvd c" (is "?P \<longleftrightarrow> ?Q")
proof
  assume ?P
  then obtain d where "b + c = a * d" ..
  moreover from \<open>a dvd b\<close> obtain e where "b = a * e" ..
  ultimately have "a * e + c = a * d" by simp
  then have "a * e + c - a * e = a * d - a * e" by simp
  then have "c = a * d - a * e" by simp
  then have "c = a * (d - e)" by (simp add: algebra_simps)
  then show ?Q ..
next
  assume ?Q
  with assms show ?P by simp
qed

lemma dvd_add_left_iff: "a dvd c \<Longrightarrow> a dvd b + c \<longleftrightarrow> a dvd b"
  using dvd_add_right_iff [of a c b] by (simp add: ac_simps)

end

class ring = semiring + ab_group_add
begin

subclass semiring_0_cancel ..

text \<open>Distribution rules\<close>

lemma minus_mult_left: "- (a * b) = - a * b"
  by (rule minus_unique) (simp add: distrib_right [symmetric])

lemma minus_mult_right: "- (a * b) = a * - b"
  by (rule minus_unique) (simp add: distrib_left [symmetric])

text \<open>Extract signs from products\<close>
lemmas mult_minus_left [simp] = minus_mult_left [symmetric]
lemmas mult_minus_right [simp] = minus_mult_right [symmetric]

lemma minus_mult_minus [simp]: "- a * - b = a * b"
  by simp

lemma minus_mult_commute: "- a * b = a * - b"
  by simp

lemma right_diff_distrib [algebra_simps]: "a * (b - c) = a * b - a * c"
  using distrib_left [of a b "-c "] by simp

lemma left_diff_distrib [algebra_simps]: "(a - b) * c = a * c - b * c"
  using distrib_right [of a "- b" c] by simp

lemmas ring_distribs = distrib_left distrib_right left_diff_distrib right_diff_distrib

lemma eq_add_iff1: "a * e + c = b * e + d \<longleftrightarrow> (a - b) * e + c = d"
  by (simp add: algebra_simps)

lemma eq_add_iff2: "a * e + c = b * e + d \<longleftrightarrow> c = (b - a) * e + d"
  by (simp add: algebra_simps)

end

lemmas ring_distribs = distrib_left distrib_right left_diff_distrib right_diff_distrib

class comm_ring = comm_semiring + ab_group_add
begin

subclass ring ..
subclass comm_semiring_0_cancel ..

lemma square_diff_square_factored: "x * x - y * y = (x + y) * (x - y)"
  by (simp add: algebra_simps)

end

class ring_1 = ring + zero_neq_one + monoid_mult
begin

subclass semiring_1_cancel ..

lemma square_diff_one_factored: "x * x - 1 = (x + 1) * (x - 1)"
  by (simp add: algebra_simps)

end

class comm_ring_1 = comm_ring + zero_neq_one + comm_monoid_mult
begin

subclass ring_1 ..
subclass comm_semiring_1_cancel
  by unfold_locales (simp add: algebra_simps)

lemma dvd_minus_iff [simp]: "x dvd - y \<longleftrightarrow> x dvd y"
proof
  assume "x dvd - y"
  then have "x dvd - 1 * - y" by (rule dvd_mult)
  then show "x dvd y" by simp
next
  assume "x dvd y"
  then have "x dvd - 1 * y" by (rule dvd_mult)
  then show "x dvd - y" by simp
qed

lemma minus_dvd_iff [simp]: "- x dvd y \<longleftrightarrow> x dvd y"
proof
  assume "- x dvd y"
  then obtain k where "y = - x * k" ..
  then have "y = x * - k" by simp
  then show "x dvd y" ..
next
  assume "x dvd y"
  then obtain k where "y = x * k" ..
  then have "y = - x * - k" by simp
  then show "- x dvd y" ..
qed

lemma dvd_diff [simp]: "x dvd y \<Longrightarrow> x dvd z \<Longrightarrow> x dvd (y - z)"
  using dvd_add [of x y "- z"] by simp

end

class semiring_no_zero_divisors = semiring_0 +
  assumes no_zero_divisors: "a \<noteq> 0 \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> a * b \<noteq> 0"
begin

lemma divisors_zero:
  assumes "a * b = 0"
  shows "a = 0 \<or> b = 0"
proof (rule classical)
  assume "\<not> ?thesis"
  then have "a \<noteq> 0" and "b \<noteq> 0" by auto
  with no_zero_divisors have "a * b \<noteq> 0" by blast
  with assms show ?thesis by simp
qed

lemma mult_eq_0_iff [simp]: "a * b = 0 \<longleftrightarrow> a = 0 \<or> b = 0"
proof (cases "a = 0 \<or> b = 0")
  case False
  then have "a \<noteq> 0" and "b \<noteq> 0" by auto
    then show ?thesis using no_zero_divisors by simp
next
  case True
  then show ?thesis by auto
qed

end

class semiring_1_no_zero_divisors = semiring_1 + semiring_no_zero_divisors

class semiring_no_zero_divisors_cancel = semiring_no_zero_divisors +
  assumes mult_cancel_right [simp]: "a * c = b * c \<longleftrightarrow> c = 0 \<or> a = b"
    and mult_cancel_left [simp]: "c * a = c * b \<longleftrightarrow> c = 0 \<or> a = b"
begin

lemma mult_left_cancel: "c \<noteq> 0 \<Longrightarrow> c * a = c * b \<longleftrightarrow> a = b"
  by simp

lemma mult_right_cancel: "c \<noteq> 0 \<Longrightarrow> a * c = b * c \<longleftrightarrow> a = b"
  by simp

end

class ring_no_zero_divisors = ring + semiring_no_zero_divisors
begin

subclass semiring_no_zero_divisors_cancel
proof
  fix a b c
  have "a * c = b * c \<longleftrightarrow> (a - b) * c = 0"
    by (simp add: algebra_simps)
  also have "\<dots> \<longleftrightarrow> c = 0 \<or> a = b"
    by auto
  finally show "a * c = b * c \<longleftrightarrow> c = 0 \<or> a = b" .
  have "c * a = c * b \<longleftrightarrow> c * (a - b) = 0"
    by (simp add: algebra_simps)
  also have "\<dots> \<longleftrightarrow> c = 0 \<or> a = b"
    by auto
  finally show "c * a = c * b \<longleftrightarrow> c = 0 \<or> a = b" .
qed

end

class ring_1_no_zero_divisors = ring_1 + ring_no_zero_divisors
begin

subclass semiring_1_no_zero_divisors ..

lemma square_eq_1_iff: "x * x = 1 \<longleftrightarrow> x = 1 \<or> x = - 1"
proof -
  have "(x - 1) * (x + 1) = x * x - 1"
    by (simp add: algebra_simps)
  then have "x * x = 1 \<longleftrightarrow> (x - 1) * (x + 1) = 0"
    by simp
  then show ?thesis
    by (simp add: eq_neg_iff_add_eq_0)
qed

lemma mult_cancel_right1 [simp]: "c = b * c \<longleftrightarrow> c = 0 \<or> b = 1"
  using mult_cancel_right [of 1 c b] by auto

lemma mult_cancel_right2 [simp]: "a * c = c \<longleftrightarrow> c = 0 \<or> a = 1"
  using mult_cancel_right [of a c 1] by simp

lemma mult_cancel_left1 [simp]: "c = c * b \<longleftrightarrow> c = 0 \<or> b = 1"
  using mult_cancel_left [of c 1 b] by force

lemma mult_cancel_left2 [simp]: "c * a = c \<longleftrightarrow> c = 0 \<or> a = 1"
  using mult_cancel_left [of c a 1] by simp

end

class semidom = comm_semiring_1_cancel + semiring_no_zero_divisors
begin

subclass semiring_1_no_zero_divisors ..

end

class idom = comm_ring_1 + semiring_no_zero_divisors
begin

subclass semidom ..

subclass ring_1_no_zero_divisors ..

lemma dvd_mult_cancel_right [simp]: "a * c dvd b * c \<longleftrightarrow> c = 0 \<or> a dvd b"
proof -
  have "a * c dvd b * c \<longleftrightarrow> (\<exists>k. b * c = (a * k) * c)"
    unfolding dvd_def by (simp add: ac_simps)
  also have "(\<exists>k. b * c = (a * k) * c) \<longleftrightarrow> c = 0 \<or> a dvd b"
    unfolding dvd_def by simp
  finally show ?thesis .
qed

lemma dvd_mult_cancel_left [simp]: "c * a dvd c * b \<longleftrightarrow> c = 0 \<or> a dvd b"
proof -
  have "c * a dvd c * b \<longleftrightarrow> (\<exists>k. b * c = (a * k) * c)"
    unfolding dvd_def by (simp add: ac_simps)
  also have "(\<exists>k. b * c = (a * k) * c) \<longleftrightarrow> c = 0 \<or> a dvd b"
    unfolding dvd_def by simp
  finally show ?thesis .
qed

lemma square_eq_iff: "a * a = b * b \<longleftrightarrow> a = b \<or> a = - b"
proof
  assume "a * a = b * b"
  then have "(a - b) * (a + b) = 0"
    by (simp add: algebra_simps)
  then show "a = b \<or> a = - b"
    by (simp add: eq_neg_iff_add_eq_0)
next
  assume "a = b \<or> a = - b"
  then show "a * a = b * b" by auto
qed

end

class idom_abs_sgn = idom + abs + sgn +
  assumes sgn_mult_abs: "sgn a * \<bar>a\<bar> = a"
    and sgn_sgn [simp]: "sgn (sgn a) = sgn a"
    and abs_abs [simp]: "\<bar>\<bar>a\<bar>\<bar> = \<bar>a\<bar>"
    and abs_0 [simp]: "\<bar>0\<bar> = 0"
    and sgn_0 [simp]: "sgn 0 = 0"
    and sgn_1 [simp]: "sgn 1 = 1"
    and sgn_minus_1: "sgn (- 1) = - 1"
    and sgn_mult: "sgn (a * b) = sgn a * sgn b"
begin

lemma sgn_eq_0_iff:
  "sgn a = 0 \<longleftrightarrow> a = 0"
proof -
  { assume "sgn a = 0"
    then have "sgn a * \<bar>a\<bar> = 0"
      by simp
    then have "a = 0"
      by (simp add: sgn_mult_abs)
  } then show ?thesis
    by auto
qed

lemma abs_eq_0_iff:
  "\<bar>a\<bar> = 0 \<longleftrightarrow> a = 0"
proof -
  { assume "\<bar>a\<bar> = 0"
    then have "sgn a * \<bar>a\<bar> = 0"
      by simp
    then have "a = 0"
      by (simp add: sgn_mult_abs)
  } then show ?thesis
    by auto
qed

lemma abs_mult_sgn:
  "\<bar>a\<bar> * sgn a = a"
  using sgn_mult_abs [of a] by (simp add: ac_simps)

lemma abs_1 [simp]:
  "\<bar>1\<bar> = 1"
  using sgn_mult_abs [of 1] by simp

lemma sgn_abs [simp]:
  "\<bar>sgn a\<bar> = of_bool (a \<noteq> 0)"
  using sgn_mult_abs [of "sgn a"] mult_cancel_left [of "sgn a" "\<bar>sgn a\<bar>" 1]
  by (auto simp add: sgn_eq_0_iff)

lemma abs_sgn [simp]:
  "sgn \<bar>a\<bar> = of_bool (a \<noteq> 0)"
  using sgn_mult_abs [of "\<bar>a\<bar>"] mult_cancel_right [of "sgn \<bar>a\<bar>" "\<bar>a\<bar>" 1]
  by (auto simp add: abs_eq_0_iff)

lemma abs_mult:
  "\<bar>a * b\<bar> = \<bar>a\<bar> * \<bar>b\<bar>"
proof (cases "a = 0 \<or> b = 0")
  case True
  then show ?thesis
    by auto
next
  case False
  then have *: "sgn (a * b) \<noteq> 0"
    by (simp add: sgn_eq_0_iff)
  from abs_mult_sgn [of "a * b"] abs_mult_sgn [of a] abs_mult_sgn [of b]
  have "\<bar>a * b\<bar> * sgn (a * b) = \<bar>a\<bar> * sgn a * \<bar>b\<bar> * sgn b"
    by (simp add: ac_simps)
  then have "\<bar>a * b\<bar> * sgn (a * b) = \<bar>a\<bar> * \<bar>b\<bar> * sgn (a * b)"
    by (simp add: sgn_mult ac_simps)
  with * show ?thesis
    by simp
qed

lemma sgn_minus [simp]:
  "sgn (- a) = - sgn a"
proof -
  from sgn_minus_1 have "sgn (- 1 * a) = - 1 * sgn a"
    by (simp only: sgn_mult)
  then show ?thesis
    by simp
qed

lemma abs_minus [simp]:
  "\<bar>- a\<bar> = \<bar>a\<bar>"
proof -
  have [simp]: "\<bar>- 1\<bar> = 1"
    using sgn_mult_abs [of "- 1"] by simp
  then have "\<bar>- 1 * a\<bar> = 1 * \<bar>a\<bar>"
    by (simp only: abs_mult)
  then show ?thesis
    by simp
qed

end

text \<open>
  The theory of partially ordered rings is taken from the books:
    \<^item> \<^emph>\<open>Lattice Theory\<close> by Garret Birkhoff, American Mathematical Society, 1979
    \<^item> \<^emph>\<open>Partially Ordered Algebraic Systems\<close>, Pergamon Press, 1963

  Most of the used notions can also be looked up in
    \<^item> \<^url>\<open>http://www.mathworld.com\<close> by Eric Weisstein et. al.
    \<^item> \<^emph>\<open>Algebra I\<close> by van der Waerden, Springer
\<close>

text \<open>Syntactic division operator\<close>

class divide =
  fixes divide :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "div" 70)

setup \<open>Sign.add_const_constraint (@{const_name "divide"}, SOME @{typ "'a \<Rightarrow> 'a \<Rightarrow> 'a"})\<close>

context semiring
begin

lemma [field_simps]:
  shows distrib_left_NO_MATCH: "NO_MATCH (x div y) a \<Longrightarrow> a * (b + c) = a * b + a * c"
    and distrib_right_NO_MATCH: "NO_MATCH (x div y) c \<Longrightarrow> (a + b) * c = a * c + b * c"
  by (rule distrib_left distrib_right)+

end

context ring
begin

lemma [field_simps]:
  shows left_diff_distrib_NO_MATCH: "NO_MATCH (x div y) c \<Longrightarrow> (a - b) * c = a * c - b * c"
    and right_diff_distrib_NO_MATCH: "NO_MATCH (x div y) a \<Longrightarrow> a * (b - c) = a * b - a * c"
  by (rule left_diff_distrib right_diff_distrib)+

end

setup \<open>Sign.add_const_constraint (@{const_name "divide"}, SOME @{typ "'a::divide \<Rightarrow> 'a \<Rightarrow> 'a"})\<close>

text \<open>Algebraic classes with division\<close>
  
class semidom_divide = semidom + divide +
  assumes nonzero_mult_div_cancel_right [simp]: "b \<noteq> 0 \<Longrightarrow> (a * b) div b = a"
  assumes div_by_0 [simp]: "a div 0 = 0"
begin

lemma nonzero_mult_div_cancel_left [simp]: "a \<noteq> 0 \<Longrightarrow> (a * b) div a = b"
  using nonzero_mult_div_cancel_right [of a b] by (simp add: ac_simps)

subclass semiring_no_zero_divisors_cancel
proof
  show *: "a * c = b * c \<longleftrightarrow> c = 0 \<or> a = b" for a b c
  proof (cases "c = 0")
    case True
    then show ?thesis by simp
  next
    case False
    have "a = b" if "a * c = b * c"
    proof -
      from that have "a * c div c = b * c div c"
        by simp
      with False show ?thesis
        by simp
    qed
    then show ?thesis by auto
  qed
  show "c * a = c * b \<longleftrightarrow> c = 0 \<or> a = b" for a b c
    using * [of a c b] by (simp add: ac_simps)
qed

lemma div_self [simp]: "a \<noteq> 0 \<Longrightarrow> a div a = 1"
  using nonzero_mult_div_cancel_left [of a 1] by simp

lemma div_0 [simp]: "0 div a = 0"
proof (cases "a = 0")
  case True
  then show ?thesis by simp
next
  case False
  then have "a * 0 div a = 0"
    by (rule nonzero_mult_div_cancel_left)
  then show ?thesis by simp
qed

lemma div_by_1 [simp]: "a div 1 = a"
  using nonzero_mult_div_cancel_left [of 1 a] by simp

end

class idom_divide = idom + semidom_divide

class algebraic_semidom = semidom_divide
begin

text \<open>
  Class @{class algebraic_semidom} enriches a integral domain
  by notions from algebra, like units in a ring.
  It is a separate class to avoid spoiling fields with notions
  which are degenerated there.
\<close>

lemma dvd_times_left_cancel_iff [simp]:
  assumes "a \<noteq> 0"
  shows "a * b dvd a * c \<longleftrightarrow> b dvd c"
    (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then obtain d where "a * c = a * b * d" ..
  with assms have "c = b * d" by (simp add: ac_simps)
  then show ?rhs ..
next
  assume ?rhs
  then obtain d where "c = b * d" ..
  then have "a * c = a * b * d" by (simp add: ac_simps)
  then show ?lhs ..
qed

lemma dvd_times_right_cancel_iff [simp]:
  assumes "a \<noteq> 0"
  shows "b * a dvd c * a \<longleftrightarrow> b dvd c"
  using dvd_times_left_cancel_iff [of a b c] assms by (simp add: ac_simps)

lemma div_dvd_iff_mult:
  assumes "b \<noteq> 0" and "b dvd a"
  shows "a div b dvd c \<longleftrightarrow> a dvd c * b"
proof -
  from \<open>b dvd a\<close> obtain d where "a = b * d" ..
  with \<open>b \<noteq> 0\<close> show ?thesis by (simp add: ac_simps)
qed

lemma dvd_div_iff_mult:
  assumes "c \<noteq> 0" and "c dvd b"
  shows "a dvd b div c \<longleftrightarrow> a * c dvd b"
proof -
  from \<open>c dvd b\<close> obtain d where "b = c * d" ..
  with \<open>c \<noteq> 0\<close> show ?thesis by (simp add: mult.commute [of a])
qed

lemma div_dvd_div [simp]:
  assumes "a dvd b" and "a dvd c"
  shows "b div a dvd c div a \<longleftrightarrow> b dvd c"
proof (cases "a = 0")
  case True
  with assms show ?thesis by simp
next
  case False
  moreover from assms obtain k l where "b = a * k" and "c = a * l"
    by (auto elim!: dvdE)
  ultimately show ?thesis by simp
qed

lemma div_add [simp]:
  assumes "c dvd a" and "c dvd b"
  shows "(a + b) div c = a div c + b div c"
proof (cases "c = 0")
  case True
  then show ?thesis by simp
next
  case False
  moreover from assms obtain k l where "a = c * k" and "b = c * l"
    by (auto elim!: dvdE)
  moreover have "c * k + c * l = c * (k + l)"
    by (simp add: algebra_simps)
  ultimately show ?thesis
    by simp
qed

lemma div_mult_div_if_dvd:
  assumes "b dvd a" and "d dvd c"
  shows "(a div b) * (c div d) = (a * c) div (b * d)"
proof (cases "b = 0 \<or> c = 0")
  case True
  with assms show ?thesis by auto
next
  case False
  moreover from assms obtain k l where "a = b * k" and "c = d * l"
    by (auto elim!: dvdE)
  moreover have "b * k * (d * l) div (b * d) = (b * d) * (k * l) div (b * d)"
    by (simp add: ac_simps)
  ultimately show ?thesis by simp
qed

lemma dvd_div_eq_mult:
  assumes "a \<noteq> 0" and "a dvd b"
  shows "b div a = c \<longleftrightarrow> b = c * a"
    (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?rhs
  then show ?lhs by (simp add: assms)
next
  assume ?lhs
  then have "b div a * a = c * a" by simp
  moreover from assms have "b div a * a = b"
    by (auto elim!: dvdE simp add: ac_simps)
  ultimately show ?rhs by simp
qed

lemma dvd_div_mult_self [simp]: "a dvd b \<Longrightarrow> b div a * a = b"
  by (cases "a = 0") (auto elim: dvdE simp add: ac_simps)

lemma dvd_mult_div_cancel [simp]: "a dvd b \<Longrightarrow> a * (b div a) = b"
  using dvd_div_mult_self [of a b] by (simp add: ac_simps)

lemma div_mult_swap:
  assumes "c dvd b"
  shows "a * (b div c) = (a * b) div c"
proof (cases "c = 0")
  case True
  then show ?thesis by simp
next
  case False
  from assms obtain d where "b = c * d" ..
  moreover from False have "a * divide (d * c) c = ((a * d) * c) div c"
    by simp
  ultimately show ?thesis by (simp add: ac_simps)
qed

lemma dvd_div_mult: "c dvd b \<Longrightarrow> b div c * a = (b * a) div c"
  using div_mult_swap [of c b a] by (simp add: ac_simps)

lemma dvd_div_mult2_eq:
  assumes "b * c dvd a"
  shows "a div (b * c) = a div b div c"
proof -
  from assms obtain k where "a = b * c * k" ..
  then show ?thesis
    by (cases "b = 0 \<or> c = 0") (auto, simp add: ac_simps)
qed

lemma dvd_div_div_eq_mult:
  assumes "a \<noteq> 0" "c \<noteq> 0" and "a dvd b" "c dvd d"
  shows "b div a = d div c \<longleftrightarrow> b * c = a * d"
    (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  from assms have "a * c \<noteq> 0" by simp
  then have "?lhs \<longleftrightarrow> b div a * (a * c) = d div c * (a * c)"
    by simp
  also have "\<dots> \<longleftrightarrow> (a * (b div a)) * c = (c * (d div c)) * a"
    by (simp add: ac_simps)
  also have "\<dots> \<longleftrightarrow> (a * b div a) * c = (c * d div c) * a"
    using assms by (simp add: div_mult_swap)
  also have "\<dots> \<longleftrightarrow> ?rhs"
    using assms by (simp add: ac_simps)
  finally show ?thesis .
qed

lemma dvd_mult_imp_div:
  assumes "a * c dvd b"
  shows "a dvd b div c"
proof (cases "c = 0")
  case True then show ?thesis by simp
next
  case False
  from \<open>a * c dvd b\<close> obtain d where "b = a * c * d" ..
  with False show ?thesis
    by (simp add: mult.commute [of a] mult.assoc)
qed


text \<open>Units: invertible elements in a ring\<close>

abbreviation is_unit :: "'a \<Rightarrow> bool"
  where "is_unit a \<equiv> a dvd 1"

lemma not_is_unit_0 [simp]: "\<not> is_unit 0"
  by simp

lemma unit_imp_dvd [dest]: "is_unit b \<Longrightarrow> b dvd a"
  by (rule dvd_trans [of _ 1]) simp_all

lemma unit_dvdE:
  assumes "is_unit a"
  obtains c where "a \<noteq> 0" and "b = a * c"
proof -
  from assms have "a dvd b" by auto
  then obtain c where "b = a * c" ..
  moreover from assms have "a \<noteq> 0" by auto
  ultimately show thesis using that by blast
qed

lemma dvd_unit_imp_unit: "a dvd b \<Longrightarrow> is_unit b \<Longrightarrow> is_unit a"
  by (rule dvd_trans)

lemma unit_div_1_unit [simp, intro]:
  assumes "is_unit a"
  shows "is_unit (1 div a)"
proof -
  from assms have "1 = 1 div a * a" by simp
  then show "is_unit (1 div a)" by (rule dvdI)
qed

lemma is_unitE [elim?]:
  assumes "is_unit a"
  obtains b where "a \<noteq> 0" and "b \<noteq> 0"
    and "is_unit b" and "1 div a = b" and "1 div b = a"
    and "a * b = 1" and "c div a = c * b"
proof (rule that)
  define b where "b = 1 div a"
  then show "1 div a = b" by simp
  from assms b_def show "is_unit b" by simp
  with assms show "a \<noteq> 0" and "b \<noteq> 0" by auto
  from assms b_def show "a * b = 1" by simp
  then have "1 = a * b" ..
  with b_def \<open>b \<noteq> 0\<close> show "1 div b = a" by simp
  from assms have "a dvd c" ..
  then obtain d where "c = a * d" ..
  with \<open>a \<noteq> 0\<close> \<open>a * b = 1\<close> show "c div a = c * b"
    by (simp add: mult.assoc mult.left_commute [of a])
qed

lemma unit_prod [intro]: "is_unit a \<Longrightarrow> is_unit b \<Longrightarrow> is_unit (a * b)"
  by (subst mult_1_left [of 1, symmetric]) (rule mult_dvd_mono)

lemma is_unit_mult_iff: "is_unit (a * b) \<longleftrightarrow> is_unit a \<and> is_unit b"
  by (auto dest: dvd_mult_left dvd_mult_right)

lemma unit_div [intro]: "is_unit a \<Longrightarrow> is_unit b \<Longrightarrow> is_unit (a div b)"
  by (erule is_unitE [of b a]) (simp add: ac_simps unit_prod)

lemma mult_unit_dvd_iff:
  assumes "is_unit b"
  shows "a * b dvd c \<longleftrightarrow> a dvd c"
proof
  assume "a * b dvd c"
  with assms show "a dvd c"
    by (simp add: dvd_mult_left)
next
  assume "a dvd c"
  then obtain k where "c = a * k" ..
  with assms have "c = (a * b) * (1 div b * k)"
    by (simp add: mult_ac)
  then show "a * b dvd c" by (rule dvdI)
qed

lemma mult_unit_dvd_iff': "is_unit a \<Longrightarrow> (a * b) dvd c \<longleftrightarrow> b dvd c"
  using mult_unit_dvd_iff [of a b c] by (simp add: ac_simps)

lemma dvd_mult_unit_iff:
  assumes "is_unit b"
  shows "a dvd c * b \<longleftrightarrow> a dvd c"
proof
  assume "a dvd c * b"
  with assms have "c * b dvd c * (b * (1 div b))"
    by (subst mult_assoc [symmetric]) simp
  also from assms have "b * (1 div b) = 1"
    by (rule is_unitE) simp
  finally have "c * b dvd c" by simp
  with \<open>a dvd c * b\<close> show "a dvd c" by (rule dvd_trans)
next
  assume "a dvd c"
  then show "a dvd c * b" by simp
qed

lemma dvd_mult_unit_iff': "is_unit b \<Longrightarrow> a dvd b * c \<longleftrightarrow> a dvd c"
  using dvd_mult_unit_iff [of b a c] by (simp add: ac_simps)

lemma div_unit_dvd_iff: "is_unit b \<Longrightarrow> a div b dvd c \<longleftrightarrow> a dvd c"
  by (erule is_unitE [of _ a]) (auto simp add: mult_unit_dvd_iff)

lemma dvd_div_unit_iff: "is_unit b \<Longrightarrow> a dvd c div b \<longleftrightarrow> a dvd c"
  by (erule is_unitE [of _ c]) (simp add: dvd_mult_unit_iff)

lemmas unit_dvd_iff = mult_unit_dvd_iff mult_unit_dvd_iff'
  dvd_mult_unit_iff dvd_mult_unit_iff' 
  div_unit_dvd_iff dvd_div_unit_iff (* FIXME consider named_theorems *)

lemma unit_mult_div_div [simp]: "is_unit a \<Longrightarrow> b * (1 div a) = b div a"
  by (erule is_unitE [of _ b]) simp

lemma unit_div_mult_self [simp]: "is_unit a \<Longrightarrow> b div a * a = b"
  by (rule dvd_div_mult_self) auto

lemma unit_div_1_div_1 [simp]: "is_unit a \<Longrightarrow> 1 div (1 div a) = a"
  by (erule is_unitE) simp

lemma unit_div_mult_swap: "is_unit c \<Longrightarrow> a * (b div c) = (a * b) div c"
  by (erule unit_dvdE [of _ b]) (simp add: mult.left_commute [of _ c])

lemma unit_div_commute: "is_unit b \<Longrightarrow> (a div b) * c = (a * c) div b"
  using unit_div_mult_swap [of b c a] by (simp add: ac_simps)

lemma unit_eq_div1: "is_unit b \<Longrightarrow> a div b = c \<longleftrightarrow> a = c * b"
  by (auto elim: is_unitE)

lemma unit_eq_div2: "is_unit b \<Longrightarrow> a = c div b \<longleftrightarrow> a * b = c"
  using unit_eq_div1 [of b c a] by auto

lemma unit_mult_left_cancel: "is_unit a \<Longrightarrow> a * b = a * c \<longleftrightarrow> b = c"
  using mult_cancel_left [of a b c] by auto

lemma unit_mult_right_cancel: "is_unit a \<Longrightarrow> b * a = c * a \<longleftrightarrow> b = c"
  using unit_mult_left_cancel [of a b c] by (auto simp add: ac_simps)

lemma unit_div_cancel:
  assumes "is_unit a"
  shows "b div a = c div a \<longleftrightarrow> b = c"
proof -
  from assms have "is_unit (1 div a)" by simp
  then have "b * (1 div a) = c * (1 div a) \<longleftrightarrow> b = c"
    by (rule unit_mult_right_cancel)
  with assms show ?thesis by simp
qed

lemma is_unit_div_mult2_eq:
  assumes "is_unit b" and "is_unit c"
  shows "a div (b * c) = a div b div c"
proof -
  from assms have "is_unit (b * c)"
    by (simp add: unit_prod)
  then have "b * c dvd a"
    by (rule unit_imp_dvd)
  then show ?thesis
    by (rule dvd_div_mult2_eq)
qed

lemmas unit_simps = mult_unit_dvd_iff div_unit_dvd_iff dvd_mult_unit_iff
  dvd_div_unit_iff unit_div_mult_swap unit_div_commute
  unit_mult_left_cancel unit_mult_right_cancel unit_div_cancel
  unit_eq_div1 unit_eq_div2

lemma is_unit_div_mult_cancel_left:
  assumes "a \<noteq> 0" and "is_unit b"
  shows "a div (a * b) = 1 div b"
proof -
  from assms have "a div (a * b) = a div a div b"
    by (simp add: mult_unit_dvd_iff dvd_div_mult2_eq)
  with assms show ?thesis by simp
qed

lemma is_unit_div_mult_cancel_right:
  assumes "a \<noteq> 0" and "is_unit b"
  shows "a div (b * a) = 1 div b"
  using assms is_unit_div_mult_cancel_left [of a b] by (simp add: ac_simps)

end

class normalization_semidom = algebraic_semidom +
  fixes normalize :: "'a \<Rightarrow> 'a"
    and unit_factor :: "'a \<Rightarrow> 'a"
  assumes unit_factor_mult_normalize [simp]: "unit_factor a * normalize a = a"
    and normalize_0 [simp]: "normalize 0 = 0"
    and unit_factor_0 [simp]: "unit_factor 0 = 0"
    and is_unit_normalize: "is_unit a  \<Longrightarrow> normalize a = 1"
    and unit_factor_is_unit [iff]: "a \<noteq> 0 \<Longrightarrow> is_unit (unit_factor a)"
    and unit_factor_mult: "unit_factor (a * b) = unit_factor a * unit_factor b"
begin

text \<open>
  Class @{class normalization_semidom} cultivates the idea that each integral
  domain can be split into equivalence classes whose representants are
  associated, i.e. divide each other. @{const normalize} specifies a canonical
  representant for each equivalence class. The rationale behind this is that
  it is easier to reason about equality than equivalences, hence we prefer to
  think about equality of normalized values rather than associated elements.
\<close>

lemma unit_factor_dvd [simp]: "a \<noteq> 0 \<Longrightarrow> unit_factor a dvd b"
  by (rule unit_imp_dvd) simp

lemma unit_factor_self [simp]: "unit_factor a dvd a"
  by (cases "a = 0") simp_all

lemma normalize_mult_unit_factor [simp]: "normalize a * unit_factor a = a"
  using unit_factor_mult_normalize [of a] by (simp add: ac_simps)

lemma normalize_eq_0_iff [simp]: "normalize a = 0 \<longleftrightarrow> a = 0"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  moreover have "unit_factor a * normalize a = a" by simp
  ultimately show ?rhs by simp
next
  assume ?rhs
  then show ?lhs by simp
qed

lemma unit_factor_eq_0_iff [simp]: "unit_factor a = 0 \<longleftrightarrow> a = 0"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  moreover have "unit_factor a * normalize a = a" by simp
  ultimately show ?rhs by simp
next
  assume ?rhs
  then show ?lhs by simp
qed

lemma is_unit_unit_factor:
  assumes "is_unit a"
  shows "unit_factor a = a"
proof -
  from assms have "normalize a = 1" by (rule is_unit_normalize)
  moreover from unit_factor_mult_normalize have "unit_factor a * normalize a = a" .
  ultimately show ?thesis by simp
qed

lemma unit_factor_1 [simp]: "unit_factor 1 = 1"
  by (rule is_unit_unit_factor) simp

lemma normalize_1 [simp]: "normalize 1 = 1"
  by (rule is_unit_normalize) simp

lemma normalize_1_iff: "normalize a = 1 \<longleftrightarrow> is_unit a"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?rhs
  then show ?lhs by (rule is_unit_normalize)
next
  assume ?lhs
  then have "unit_factor a * normalize a = unit_factor a * 1"
    by simp
  then have "unit_factor a = a"
    by simp
  moreover
  from \<open>?lhs\<close> have "a \<noteq> 0" by auto
  then have "is_unit (unit_factor a)" by simp
  ultimately show ?rhs by simp
qed

lemma div_normalize [simp]: "a div normalize a = unit_factor a"
proof (cases "a = 0")
  case True
  then show ?thesis by simp
next
  case False
  then have "normalize a \<noteq> 0" by simp
  with nonzero_mult_div_cancel_right
  have "unit_factor a * normalize a div normalize a = unit_factor a" by blast
  then show ?thesis by simp
qed

lemma div_unit_factor [simp]: "a div unit_factor a = normalize a"
proof (cases "a = 0")
  case True
  then show ?thesis by simp
next
  case False
  then have "unit_factor a \<noteq> 0" by simp
  with nonzero_mult_div_cancel_left
  have "unit_factor a * normalize a div unit_factor a = normalize a"
    by blast
  then show ?thesis by simp
qed

lemma normalize_div [simp]: "normalize a div a = 1 div unit_factor a"
proof (cases "a = 0")
  case True
  then show ?thesis by simp
next
  case False
  have "normalize a div a = normalize a div (unit_factor a * normalize a)"
    by simp
  also have "\<dots> = 1 div unit_factor a"
    using False by (subst is_unit_div_mult_cancel_right) simp_all
  finally show ?thesis .
qed

lemma mult_one_div_unit_factor [simp]: "a * (1 div unit_factor b) = a div unit_factor b"
  by (cases "b = 0") simp_all

lemma inv_unit_factor_eq_0_iff [simp]:
  "1 div unit_factor a = 0 \<longleftrightarrow> a = 0"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then have "a * (1 div unit_factor a) = a * 0"
    by simp
  then show ?rhs
    by simp
next
  assume ?rhs
  then show ?lhs by simp
qed

lemma normalize_mult: "normalize (a * b) = normalize a * normalize b"
proof (cases "a = 0 \<or> b = 0")
  case True
  then show ?thesis by auto
next
  case False
  have "unit_factor (a * b) * normalize (a * b) = a * b"
    by (rule unit_factor_mult_normalize)
  then have "normalize (a * b) = a * b div unit_factor (a * b)"
    by simp
  also have "\<dots> = a * b div unit_factor (b * a)"
    by (simp add: ac_simps)
  also have "\<dots> = a * b div unit_factor b div unit_factor a"
    using False by (simp add: unit_factor_mult is_unit_div_mult2_eq [symmetric])
  also have "\<dots> = a * (b div unit_factor b) div unit_factor a"
    using False by (subst unit_div_mult_swap) simp_all
  also have "\<dots> = normalize a * normalize b"
    using False
    by (simp add: mult.commute [of a] mult.commute [of "normalize a"] unit_div_mult_swap [symmetric])
  finally show ?thesis .
qed

lemma unit_factor_idem [simp]: "unit_factor (unit_factor a) = unit_factor a"
  by (cases "a = 0") (auto intro: is_unit_unit_factor)

lemma normalize_unit_factor [simp]: "a \<noteq> 0 \<Longrightarrow> normalize (unit_factor a) = 1"
  by (rule is_unit_normalize) simp

lemma normalize_idem [simp]: "normalize (normalize a) = normalize a"
proof (cases "a = 0")
  case True
  then show ?thesis by simp
next
  case False
  have "normalize a = normalize (unit_factor a * normalize a)"
    by simp
  also have "\<dots> = normalize (unit_factor a) * normalize (normalize a)"
    by (simp only: normalize_mult)
  finally show ?thesis
    using False by simp_all
qed

lemma unit_factor_normalize [simp]:
  assumes "a \<noteq> 0"
  shows "unit_factor (normalize a) = 1"
proof -
  from assms have *: "normalize a \<noteq> 0"
    by simp
  have "unit_factor (normalize a) * normalize (normalize a) = normalize a"
    by (simp only: unit_factor_mult_normalize)
  then have "unit_factor (normalize a) * normalize a = normalize a"
    by simp
  with * have "unit_factor (normalize a) * normalize a div normalize a = normalize a div normalize a"
    by simp
  with * show ?thesis
    by simp
qed

lemma dvd_unit_factor_div:
  assumes "b dvd a"
  shows "unit_factor (a div b) = unit_factor a div unit_factor b"
proof -
  from assms have "a = a div b * b"
    by simp
  then have "unit_factor a = unit_factor (a div b * b)"
    by simp
  then show ?thesis
    by (cases "b = 0") (simp_all add: unit_factor_mult)
qed

lemma dvd_normalize_div:
  assumes "b dvd a"
  shows "normalize (a div b) = normalize a div normalize b"
proof -
  from assms have "a = a div b * b"
    by simp
  then have "normalize a = normalize (a div b * b)"
    by simp
  then show ?thesis
    by (cases "b = 0") (simp_all add: normalize_mult)
qed

lemma normalize_dvd_iff [simp]: "normalize a dvd b \<longleftrightarrow> a dvd b"
proof -
  have "normalize a dvd b \<longleftrightarrow> unit_factor a * normalize a dvd b"
    using mult_unit_dvd_iff [of "unit_factor a" "normalize a" b]
      by (cases "a = 0") simp_all
  then show ?thesis by simp
qed

lemma dvd_normalize_iff [simp]: "a dvd normalize b \<longleftrightarrow> a dvd b"
proof -
  have "a dvd normalize  b \<longleftrightarrow> a dvd normalize b * unit_factor b"
    using dvd_mult_unit_iff [of "unit_factor b" a "normalize b"]
      by (cases "b = 0") simp_all
  then show ?thesis by simp
qed

text \<open>
  We avoid an explicit definition of associated elements but prefer explicit
  normalisation instead. In theory we could define an abbreviation like @{prop
  "associated a b \<longleftrightarrow> normalize a = normalize b"} but this is counterproductive
  without suggestive infix syntax, which we do not want to sacrifice for this
  purpose here.
\<close>

lemma associatedI:
  assumes "a dvd b" and "b dvd a"
  shows "normalize a = normalize b"
proof (cases "a = 0 \<or> b = 0")
  case True
  with assms show ?thesis by auto
next
  case False
  from \<open>a dvd b\<close> obtain c where b: "b = a * c" ..
  moreover from \<open>b dvd a\<close> obtain d where a: "a = b * d" ..
  ultimately have "b * 1 = b * (c * d)"
    by (simp add: ac_simps)
  with False have "1 = c * d"
    unfolding mult_cancel_left by simp
  then have "is_unit c" and "is_unit d"
    by auto
  with a b show ?thesis
    by (simp add: normalize_mult is_unit_normalize)
qed

lemma associatedD1: "normalize a = normalize b \<Longrightarrow> a dvd b"
  using dvd_normalize_iff [of _ b, symmetric] normalize_dvd_iff [of a _, symmetric]
  by simp

lemma associatedD2: "normalize a = normalize b \<Longrightarrow> b dvd a"
  using dvd_normalize_iff [of _ a, symmetric] normalize_dvd_iff [of b _, symmetric]
  by simp

lemma associated_unit: "normalize a = normalize b \<Longrightarrow> is_unit a \<Longrightarrow> is_unit b"
  using dvd_unit_imp_unit by (auto dest!: associatedD1 associatedD2)

lemma associated_iff_dvd: "normalize a = normalize b \<longleftrightarrow> a dvd b \<and> b dvd a"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?rhs
  then show ?lhs by (auto intro!: associatedI)
next
  assume ?lhs
  then have "unit_factor a * normalize a = unit_factor a * normalize b"
    by simp
  then have *: "normalize b * unit_factor a = a"
    by (simp add: ac_simps)
  show ?rhs
  proof (cases "a = 0 \<or> b = 0")
    case True
    with \<open>?lhs\<close> show ?thesis by auto
  next
    case False
    then have "b dvd normalize b * unit_factor a" and "normalize b * unit_factor a dvd b"
      by (simp_all add: mult_unit_dvd_iff dvd_mult_unit_iff)
    with * show ?thesis by simp
  qed
qed

lemma associated_eqI:
  assumes "a dvd b" and "b dvd a"
  assumes "normalize a = a" and "normalize b = b"
  shows "a = b"
proof -
  from assms have "normalize a = normalize b"
    unfolding associated_iff_dvd by simp
  with \<open>normalize a = a\<close> have "a = normalize b"
    by simp
  with \<open>normalize b = b\<close> show "a = b"
    by simp
qed

end


text \<open>Syntactic division remainder operator\<close>

class modulo = dvd + divide +
  fixes modulo :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "mod" 70)

text \<open>Arbitrary quotient and remainder partitions\<close>

class semiring_modulo = comm_semiring_1_cancel + divide + modulo +
  assumes div_mult_mod_eq: "a div b * b + a mod b = a"
begin

lemma mod_div_decomp:
  fixes a b
  obtains q r where "q = a div b" and "r = a mod b"
    and "a = q * b + r"
proof -
  from div_mult_mod_eq have "a = a div b * b + a mod b" by simp
  moreover have "a div b = a div b" ..
  moreover have "a mod b = a mod b" ..
  note that ultimately show thesis by blast
qed

lemma mult_div_mod_eq: "b * (a div b) + a mod b = a"
  using div_mult_mod_eq [of a b] by (simp add: ac_simps)

lemma mod_div_mult_eq: "a mod b + a div b * b = a"
  using div_mult_mod_eq [of a b] by (simp add: ac_simps)

lemma mod_mult_div_eq: "a mod b + b * (a div b) = a"
  using div_mult_mod_eq [of a b] by (simp add: ac_simps)

lemma minus_div_mult_eq_mod: "a - a div b * b = a mod b"
  by (rule add_implies_diff [symmetric]) (fact mod_div_mult_eq)

lemma minus_mult_div_eq_mod: "a - b * (a div b) = a mod b"
  by (rule add_implies_diff [symmetric]) (fact mod_mult_div_eq)

lemma minus_mod_eq_div_mult: "a - a mod b = a div b * b"
  by (rule add_implies_diff [symmetric]) (fact div_mult_mod_eq)

lemma minus_mod_eq_mult_div: "a - a mod b = b * (a div b)"
  by (rule add_implies_diff [symmetric]) (fact mult_div_mod_eq)

end


class ordered_semiring = semiring + ordered_comm_monoid_add +
  assumes mult_left_mono: "a \<le> b \<Longrightarrow> 0 \<le> c \<Longrightarrow> c * a \<le> c * b"
  assumes mult_right_mono: "a \<le> b \<Longrightarrow> 0 \<le> c \<Longrightarrow> a * c \<le> b * c"
begin

lemma mult_mono: "a \<le> b \<Longrightarrow> c \<le> d \<Longrightarrow> 0 \<le> b \<Longrightarrow> 0 \<le> c \<Longrightarrow> a * c \<le> b * d"
  apply (erule (1) mult_right_mono [THEN order_trans])
  apply (erule (1) mult_left_mono)
  done

lemma mult_mono': "a \<le> b \<Longrightarrow> c \<le> d \<Longrightarrow> 0 \<le> a \<Longrightarrow> 0 \<le> c \<Longrightarrow> a * c \<le> b * d"
  by (rule mult_mono) (fast intro: order_trans)+

end

class ordered_semiring_0 = semiring_0 + ordered_semiring
begin

lemma mult_nonneg_nonneg [simp]: "0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> 0 \<le> a * b"
  using mult_left_mono [of 0 b a] by simp

lemma mult_nonneg_nonpos: "0 \<le> a \<Longrightarrow> b \<le> 0 \<Longrightarrow> a * b \<le> 0"
  using mult_left_mono [of b 0 a] by simp

lemma mult_nonpos_nonneg: "a \<le> 0 \<Longrightarrow> 0 \<le> b \<Longrightarrow> a * b \<le> 0"
  using mult_right_mono [of a 0 b] by simp

text \<open>Legacy -- use @{thm [source] mult_nonpos_nonneg}.\<close>
lemma mult_nonneg_nonpos2: "0 \<le> a \<Longrightarrow> b \<le> 0 \<Longrightarrow> b * a \<le> 0"
  by (drule mult_right_mono [of b 0]) auto

lemma split_mult_neg_le: "(0 \<le> a \<and> b \<le> 0) \<or> (a \<le> 0 \<and> 0 \<le> b) \<Longrightarrow> a * b \<le> 0"
  by (auto simp add: mult_nonneg_nonpos mult_nonneg_nonpos2)

end

class ordered_cancel_semiring = ordered_semiring + cancel_comm_monoid_add
begin

subclass semiring_0_cancel ..

subclass ordered_semiring_0 ..

end

class linordered_semiring = ordered_semiring + linordered_cancel_ab_semigroup_add
begin

subclass ordered_cancel_semiring ..

subclass ordered_cancel_comm_monoid_add ..

subclass ordered_ab_semigroup_monoid_add_imp_le ..

lemma mult_left_less_imp_less: "c * a < c * b \<Longrightarrow> 0 \<le> c \<Longrightarrow> a < b"
  by (force simp add: mult_left_mono not_le [symmetric])

lemma mult_right_less_imp_less: "a * c < b * c \<Longrightarrow> 0 \<le> c \<Longrightarrow> a < b"
  by (force simp add: mult_right_mono not_le [symmetric])

end

class linordered_semiring_1 = linordered_semiring + semiring_1
begin

lemma convex_bound_le:
  assumes "x \<le> a" "y \<le> a" "0 \<le> u" "0 \<le> v" "u + v = 1"
  shows "u * x + v * y \<le> a"
proof-
  from assms have "u * x + v * y \<le> u * a + v * a"
    by (simp add: add_mono mult_left_mono)
  with assms show ?thesis
    unfolding distrib_right[symmetric] by simp
qed

end

class linordered_semiring_strict = semiring + comm_monoid_add + linordered_cancel_ab_semigroup_add +
  assumes mult_strict_left_mono: "a < b \<Longrightarrow> 0 < c \<Longrightarrow> c * a < c * b"
  assumes mult_strict_right_mono: "a < b \<Longrightarrow> 0 < c \<Longrightarrow> a * c < b * c"
begin

subclass semiring_0_cancel ..

subclass linordered_semiring
proof
  fix a b c :: 'a
  assume *: "a \<le> b" "0 \<le> c"
  then show "c * a \<le> c * b"
    unfolding le_less
    using mult_strict_left_mono by (cases "c = 0") auto
  from * show "a * c \<le> b * c"
    unfolding le_less
    using mult_strict_right_mono by (cases "c = 0") auto
qed

lemma mult_left_le_imp_le: "c * a \<le> c * b \<Longrightarrow> 0 < c \<Longrightarrow> a \<le> b"
  by (auto simp add: mult_strict_left_mono _not_less [symmetric])

lemma mult_right_le_imp_le: "a * c \<le> b * c \<Longrightarrow> 0 < c \<Longrightarrow> a \<le> b"
  by (auto simp add: mult_strict_right_mono not_less [symmetric])

lemma mult_pos_pos[simp]: "0 < a \<Longrightarrow> 0 < b \<Longrightarrow> 0 < a * b"
  using mult_strict_left_mono [of 0 b a] by simp

lemma mult_pos_neg: "0 < a \<Longrightarrow> b < 0 \<Longrightarrow> a * b < 0"
  using mult_strict_left_mono [of b 0 a] by simp

lemma mult_neg_pos: "a < 0 \<Longrightarrow> 0 < b \<Longrightarrow> a * b < 0"
  using mult_strict_right_mono [of a 0 b] by simp

text \<open>Legacy -- use @{thm [source] mult_neg_pos}.\<close>
lemma mult_pos_neg2: "0 < a \<Longrightarrow> b < 0 \<Longrightarrow> b * a < 0"
  by (drule mult_strict_right_mono [of b 0]) auto

lemma zero_less_mult_pos: "0 < a * b \<Longrightarrow> 0 < a \<Longrightarrow> 0 < b"
  apply (cases "b \<le> 0")
   apply (auto simp add: le_less not_less)
  apply (drule_tac mult_pos_neg [of a b])
   apply (auto dest: less_not_sym)
  done

lemma zero_less_mult_pos2: "0 < b * a \<Longrightarrow> 0 < a \<Longrightarrow> 0 < b"
  apply (cases "b \<le> 0")
   apply (auto simp add: le_less not_less)
  apply (drule_tac mult_pos_neg2 [of a b])
   apply (auto dest: less_not_sym)
  done

text \<open>Strict monotonicity in both arguments\<close>
lemma mult_strict_mono:
  assumes "a < b" and "c < d" and "0 < b" and "0 \<le> c"
  shows "a * c < b * d"
  using assms
  apply (cases "c = 0")
   apply simp
  apply (erule mult_strict_right_mono [THEN less_trans])
   apply (auto simp add: le_less)
  apply (erule (1) mult_strict_left_mono)
  done

text \<open>This weaker variant has more natural premises\<close>
lemma mult_strict_mono':
  assumes "a < b" and "c < d" and "0 \<le> a" and "0 \<le> c"
  shows "a * c < b * d"
  by (rule mult_strict_mono) (insert assms, auto)

lemma mult_less_le_imp_less:
  assumes "a < b" and "c \<le> d" and "0 \<le> a" and "0 < c"
  shows "a * c < b * d"
  using assms
  apply (subgoal_tac "a * c < b * c")
   apply (erule less_le_trans)
   apply (erule mult_left_mono)
   apply simp
  apply (erule (1) mult_strict_right_mono)
  done

lemma mult_le_less_imp_less:
  assumes "a \<le> b" and "c < d" and "0 < a" and "0 \<le> c"
  shows "a * c < b * d"
  using assms
  apply (subgoal_tac "a * c \<le> b * c")
   apply (erule le_less_trans)
   apply (erule mult_strict_left_mono)
   apply simp
  apply (erule (1) mult_right_mono)
  done

end

class linordered_semiring_1_strict = linordered_semiring_strict + semiring_1
begin

subclass linordered_semiring_1 ..

lemma convex_bound_lt:
  assumes "x < a" "y < a" "0 \<le> u" "0 \<le> v" "u + v = 1"
  shows "u * x + v * y < a"
proof -
  from assms have "u * x + v * y < u * a + v * a"
    by (cases "u = 0") (auto intro!: add_less_le_mono mult_strict_left_mono mult_left_mono)
  with assms show ?thesis
    unfolding distrib_right[symmetric] by simp
qed

end

class ordered_comm_semiring = comm_semiring_0 + ordered_ab_semigroup_add +
  assumes comm_mult_left_mono: "a \<le> b \<Longrightarrow> 0 \<le> c \<Longrightarrow> c * a \<le> c * b"
begin

subclass ordered_semiring
proof
  fix a b c :: 'a
  assume "a \<le> b" "0 \<le> c"
  then show "c * a \<le> c * b" by (rule comm_mult_left_mono)
  then show "a * c \<le> b * c" by (simp only: mult.commute)
qed

end

class ordered_cancel_comm_semiring = ordered_comm_semiring + cancel_comm_monoid_add
begin

subclass comm_semiring_0_cancel ..
subclass ordered_comm_semiring ..
subclass ordered_cancel_semiring ..

end

class linordered_comm_semiring_strict = comm_semiring_0 + linordered_cancel_ab_semigroup_add +
  assumes comm_mult_strict_left_mono: "a < b \<Longrightarrow> 0 < c \<Longrightarrow> c * a < c * b"
begin

subclass linordered_semiring_strict
proof
  fix a b c :: 'a
  assume "a < b" "0 < c"
  then show "c * a < c * b"
    by (rule comm_mult_strict_left_mono)
  then show "a * c < b * c"
    by (simp only: mult.commute)
qed

subclass ordered_cancel_comm_semiring
proof
  fix a b c :: 'a
  assume "a \<le> b" "0 \<le> c"
  then show "c * a \<le> c * b"
    unfolding le_less
    using mult_strict_left_mono by (cases "c = 0") auto
qed

end

class ordered_ring = ring + ordered_cancel_semiring
begin

subclass ordered_ab_group_add ..

lemma less_add_iff1: "a * e + c < b * e + d \<longleftrightarrow> (a - b) * e + c < d"
  by (simp add: algebra_simps)

lemma less_add_iff2: "a * e + c < b * e + d \<longleftrightarrow> c < (b - a) * e + d"
  by (simp add: algebra_simps)

lemma le_add_iff1: "a * e + c \<le> b * e + d \<longleftrightarrow> (a - b) * e + c \<le> d"
  by (simp add: algebra_simps)

lemma le_add_iff2: "a * e + c \<le> b * e + d \<longleftrightarrow> c \<le> (b - a) * e + d"
  by (simp add: algebra_simps)

lemma mult_left_mono_neg: "b \<le> a \<Longrightarrow> c \<le> 0 \<Longrightarrow> c * a \<le> c * b"
  apply (drule mult_left_mono [of _ _ "- c"])
  apply simp_all
  done

lemma mult_right_mono_neg: "b \<le> a \<Longrightarrow> c \<le> 0 \<Longrightarrow> a * c \<le> b * c"
  apply (drule mult_right_mono [of _ _ "- c"])
  apply simp_all
  done

lemma mult_nonpos_nonpos: "a \<le> 0 \<Longrightarrow> b \<le> 0 \<Longrightarrow> 0 \<le> a * b"
  using mult_right_mono_neg [of a 0 b] by simp

lemma split_mult_pos_le: "(0 \<le> a \<and> 0 \<le> b) \<or> (a \<le> 0 \<and> b \<le> 0) \<Longrightarrow> 0 \<le> a * b"
  by (auto simp add: mult_nonpos_nonpos)

end

class abs_if = minus + uminus + ord + zero + abs +
  assumes abs_if: "\<bar>a\<bar> = (if a < 0 then - a else a)"

class linordered_ring = ring + linordered_semiring + linordered_ab_group_add + abs_if
begin

subclass ordered_ring ..

subclass ordered_ab_group_add_abs
proof
  fix a b
  show "\<bar>a + b\<bar> \<le> \<bar>a\<bar> + \<bar>b\<bar>"
    by (auto simp add: abs_if not_le not_less algebra_simps
        simp del: add.commute dest: add_neg_neg add_nonneg_nonneg)
qed (auto simp: abs_if)

lemma zero_le_square [simp]: "0 \<le> a * a"
  using linear [of 0 a] by (auto simp add: mult_nonpos_nonpos)

lemma not_square_less_zero [simp]: "\<not> (a * a < 0)"
  by (simp add: not_less)

proposition abs_eq_iff: "\<bar>x\<bar> = \<bar>y\<bar> \<longleftrightarrow> x = y \<or> x = -y"
  by (auto simp add: abs_if split: if_split_asm)

lemma sum_squares_ge_zero: "0 \<le> x * x + y * y"
  by (intro add_nonneg_nonneg zero_le_square)

lemma not_sum_squares_lt_zero: "\<not> x * x + y * y < 0"
  by (simp add: not_less sum_squares_ge_zero)

end

class linordered_ring_strict = ring + linordered_semiring_strict
  + ordered_ab_group_add + abs_if
begin

subclass linordered_ring ..

lemma mult_strict_left_mono_neg: "b < a \<Longrightarrow> c < 0 \<Longrightarrow> c * a < c * b"
  using mult_strict_left_mono [of b a "- c"] by simp

lemma mult_strict_right_mono_neg: "b < a \<Longrightarrow> c < 0 \<Longrightarrow> a * c < b * c"
  using mult_strict_right_mono [of b a "- c"] by simp

lemma mult_neg_neg: "a < 0 \<Longrightarrow> b < 0 \<Longrightarrow> 0 < a * b"
  using mult_strict_right_mono_neg [of a 0 b] by simp

subclass ring_no_zero_divisors
proof
  fix a b
  assume "a \<noteq> 0"
  then have a: "a < 0 \<or> 0 < a" by (simp add: neq_iff)
  assume "b \<noteq> 0"
  then have b: "b < 0 \<or> 0 < b" by (simp add: neq_iff)
  have "a * b < 0 \<or> 0 < a * b"
  proof (cases "a < 0")
    case True
    show ?thesis
    proof (cases "b < 0")
      case True
      with \<open>a < 0\<close> show ?thesis by (auto dest: mult_neg_neg)
    next
      case False
      with b have "0 < b" by auto
      with \<open>a < 0\<close> show ?thesis by (auto dest: mult_strict_right_mono)
    qed
  next
    case False
    with a have "0 < a" by auto
    show ?thesis
    proof (cases "b < 0")
      case True
      with \<open>0 < a\<close> show ?thesis
        by (auto dest: mult_strict_right_mono_neg)
    next
      case False
      with b have "0 < b" by auto
      with \<open>0 < a\<close> show ?thesis by auto
    qed
  qed
  then show "a * b \<noteq> 0"
    by (simp add: neq_iff)
qed

lemma zero_less_mult_iff: "0 < a * b \<longleftrightarrow> 0 < a \<and> 0 < b \<or> a < 0 \<and> b < 0"
  by (cases a 0 b 0 rule: linorder_cases[case_product linorder_cases])
     (auto simp add: mult_neg_neg not_less le_less dest: zero_less_mult_pos zero_less_mult_pos2)

lemma zero_le_mult_iff: "0 \<le> a * b \<longleftrightarrow> 0 \<le> a \<and> 0 \<le> b \<or> a \<le> 0 \<and> b \<le> 0"
  by (auto simp add: eq_commute [of 0] le_less not_less zero_less_mult_iff)

lemma mult_less_0_iff: "a * b < 0 \<longleftrightarrow> 0 < a \<and> b < 0 \<or> a < 0 \<and> 0 < b"
  using zero_less_mult_iff [of "- a" b] by auto

lemma mult_le_0_iff: "a * b \<le> 0 \<longleftrightarrow> 0 \<le> a \<and> b \<le> 0 \<or> a \<le> 0 \<and> 0 \<le> b"
  using zero_le_mult_iff [of "- a" b] by auto

text \<open>
  Cancellation laws for @{term "c * a < c * b"} and @{term "a * c < b * c"},
  also with the relations \<open>\<le>\<close> and equality.
\<close>

text \<open>
  These ``disjunction'' versions produce two cases when the comparison is
  an assumption, but effectively four when the comparison is a goal.
\<close>

lemma mult_less_cancel_right_disj: "a * c < b * c \<longleftrightarrow> 0 < c \<and> a < b \<or> c < 0 \<and>  b < a"
  apply (cases "c = 0")
   apply (auto simp add: neq_iff mult_strict_right_mono mult_strict_right_mono_neg)
     apply (auto simp add: not_less not_le [symmetric, of "a*c"] not_le [symmetric, of a])
     apply (erule_tac [!] notE)
     apply (auto simp add: less_imp_le mult_right_mono mult_right_mono_neg)
  done

lemma mult_less_cancel_left_disj: "c * a < c * b \<longleftrightarrow> 0 < c \<and> a < b \<or> c < 0 \<and>  b < a"
  apply (cases "c = 0")
   apply (auto simp add: neq_iff mult_strict_left_mono mult_strict_left_mono_neg)
     apply (auto simp add: not_less not_le [symmetric, of "c * a"] not_le [symmetric, of a])
     apply (erule_tac [!] notE)
     apply (auto simp add: less_imp_le mult_left_mono mult_left_mono_neg)
  done

text \<open>
  The ``conjunction of implication'' lemmas produce two cases when the
  comparison is a goal, but give four when the comparison is an assumption.
\<close>

lemma mult_less_cancel_right: "a * c < b * c \<longleftrightarrow> (0 \<le> c \<longrightarrow> a < b) \<and> (c \<le> 0 \<longrightarrow> b < a)"
  using mult_less_cancel_right_disj [of a c b] by auto

lemma mult_less_cancel_left: "c * a < c * b \<longleftrightarrow> (0 \<le> c \<longrightarrow> a < b) \<and> (c \<le> 0 \<longrightarrow> b < a)"
  using mult_less_cancel_left_disj [of c a b] by auto

lemma mult_le_cancel_right: "a * c \<le> b * c \<longleftrightarrow> (0 < c \<longrightarrow> a \<le> b) \<and> (c < 0 \<longrightarrow> b \<le> a)"
  by (simp add: not_less [symmetric] mult_less_cancel_right_disj)

lemma mult_le_cancel_left: "c * a \<le> c * b \<longleftrightarrow> (0 < c \<longrightarrow> a \<le> b) \<and> (c < 0 \<longrightarrow> b \<le> a)"
  by (simp add: not_less [symmetric] mult_less_cancel_left_disj)

lemma mult_le_cancel_left_pos: "0 < c \<Longrightarrow> c * a \<le> c * b \<longleftrightarrow> a \<le> b"
  by (auto simp: mult_le_cancel_left)

lemma mult_le_cancel_left_neg: "c < 0 \<Longrightarrow> c * a \<le> c * b \<longleftrightarrow> b \<le> a"
  by (auto simp: mult_le_cancel_left)

lemma mult_less_cancel_left_pos: "0 < c \<Longrightarrow> c * a < c * b \<longleftrightarrow> a < b"
  by (auto simp: mult_less_cancel_left)

lemma mult_less_cancel_left_neg: "c < 0 \<Longrightarrow> c * a < c * b \<longleftrightarrow> b < a"
  by (auto simp: mult_less_cancel_left)

end

lemmas mult_sign_intros =
  mult_nonneg_nonneg mult_nonneg_nonpos
  mult_nonpos_nonneg mult_nonpos_nonpos
  mult_pos_pos mult_pos_neg
  mult_neg_pos mult_neg_neg

class ordered_comm_ring = comm_ring + ordered_comm_semiring
begin

subclass ordered_ring ..
subclass ordered_cancel_comm_semiring ..

end

class zero_less_one = order + zero + one +
  assumes zero_less_one [simp]: "0 < 1"

class linordered_nonzero_semiring = ordered_comm_semiring + monoid_mult + linorder + zero_less_one
begin

subclass zero_neq_one
  by standard (insert zero_less_one, blast)

subclass comm_semiring_1
  by standard (rule mult_1_left)

lemma zero_le_one [simp]: "0 \<le> 1"
  by (rule zero_less_one [THEN less_imp_le])

lemma not_one_le_zero [simp]: "\<not> 1 \<le> 0"
  by (simp add: not_le)

lemma not_one_less_zero [simp]: "\<not> 1 < 0"
  by (simp add: not_less)

lemma mult_left_le: "c \<le> 1 \<Longrightarrow> 0 \<le> a \<Longrightarrow> a * c \<le> a"
  using mult_left_mono[of c 1 a] by simp

lemma mult_le_one: "a \<le> 1 \<Longrightarrow> 0 \<le> b \<Longrightarrow> b \<le> 1 \<Longrightarrow> a * b \<le> 1"
  using mult_mono[of a 1 b 1] by simp

lemma zero_less_two: "0 < 1 + 1"
  using add_pos_pos[OF zero_less_one zero_less_one] .

end

class linordered_semidom = semidom + linordered_comm_semiring_strict + zero_less_one +
  assumes le_add_diff_inverse2 [simp]: "b \<le> a \<Longrightarrow> a - b + b = a"
begin

subclass linordered_nonzero_semiring ..

text \<open>Addition is the inverse of subtraction.\<close>

lemma le_add_diff_inverse [simp]: "b \<le> a \<Longrightarrow> b + (a - b) = a"
  by (frule le_add_diff_inverse2) (simp add: add.commute)

lemma add_diff_inverse: "\<not> a < b \<Longrightarrow> b + (a - b) = a"
  by simp

lemma add_le_imp_le_diff: "i + k \<le> n \<Longrightarrow> i \<le> n - k"
  apply (subst add_le_cancel_right [where c=k, symmetric])
  apply (frule le_add_diff_inverse2)
  apply (simp only: add.assoc [symmetric])
  using add_implies_diff
  apply fastforce
  done

lemma add_le_add_imp_diff_le:
  assumes 1: "i + k \<le> n"
    and 2: "n \<le> j + k"
  shows "i + k \<le> n \<Longrightarrow> n \<le> j + k \<Longrightarrow> n - k \<le> j"
proof -
  have "n - (i + k) + (i + k) = n"
    using 1 by simp
  moreover have "n - k = n - k - i + i"
    using 1 by (simp add: add_le_imp_le_diff)
  ultimately show ?thesis
    using 2
    apply (simp add: add.assoc [symmetric])
    apply (rule add_le_imp_le_diff [of _ k "j + k", simplified add_diff_cancel_right'])
    apply (simp add: add.commute diff_diff_add)
    done
qed

lemma less_1_mult: "1 < m \<Longrightarrow> 1 < n \<Longrightarrow> 1 < m * n"
  using mult_strict_mono [of 1 m 1 n] by (simp add: less_trans [OF zero_less_one])

end

class linordered_idom =
  comm_ring_1 + linordered_comm_semiring_strict + ordered_ab_group_add + abs_if + sgn +
  assumes sgn_if: "sgn x = (if x = 0 then 0 else if 0 < x then 1 else - 1)"
begin

subclass linordered_semiring_1_strict ..
subclass linordered_ring_strict ..
subclass ordered_comm_ring ..
subclass idom ..

subclass linordered_semidom
proof
  have "0 \<le> 1 * 1" by (rule zero_le_square)
  then show "0 < 1" by (simp add: le_less)
  show "b \<le> a \<Longrightarrow> a - b + b = a" for a b by simp
qed

subclass idom_abs_sgn
  by standard
    (auto simp add: sgn_if abs_if zero_less_mult_iff)

lemma linorder_neqE_linordered_idom:
  assumes "x \<noteq> y"
  obtains "x < y" | "y < x"
  using assms by (rule neqE)

text \<open>These cancellation simp rules also produce two cases when the comparison is a goal.\<close>

lemma mult_le_cancel_right1: "c \<le> b * c \<longleftrightarrow> (0 < c \<longrightarrow> 1 \<le> b) \<and> (c < 0 \<longrightarrow> b \<le> 1)"
  using mult_le_cancel_right [of 1 c b] by simp

lemma mult_le_cancel_right2: "a * c \<le> c \<longleftrightarrow> (0 < c \<longrightarrow> a \<le> 1) \<and> (c < 0 \<longrightarrow> 1 \<le> a)"
  using mult_le_cancel_right [of a c 1] by simp

lemma mult_le_cancel_left1: "c \<le> c * b \<longleftrightarrow> (0 < c \<longrightarrow> 1 \<le> b) \<and> (c < 0 \<longrightarrow> b \<le> 1)"
  using mult_le_cancel_left [of c 1 b] by simp

lemma mult_le_cancel_left2: "c * a \<le> c \<longleftrightarrow> (0 < c \<longrightarrow> a \<le> 1) \<and> (c < 0 \<longrightarrow> 1 \<le> a)"
  using mult_le_cancel_left [of c a 1] by simp

lemma mult_less_cancel_right1: "c < b * c \<longleftrightarrow> (0 \<le> c \<longrightarrow> 1 < b) \<and> (c \<le> 0 \<longrightarrow> b < 1)"
  using mult_less_cancel_right [of 1 c b] by simp

lemma mult_less_cancel_right2: "a * c < c \<longleftrightarrow> (0 \<le> c \<longrightarrow> a < 1) \<and> (c \<le> 0 \<longrightarrow> 1 < a)"
  using mult_less_cancel_right [of a c 1] by simp

lemma mult_less_cancel_left1: "c < c * b \<longleftrightarrow> (0 \<le> c \<longrightarrow> 1 < b) \<and> (c \<le> 0 \<longrightarrow> b < 1)"
  using mult_less_cancel_left [of c 1 b] by simp

lemma mult_less_cancel_left2: "c * a < c \<longleftrightarrow> (0 \<le> c \<longrightarrow> a < 1) \<and> (c \<le> 0 \<longrightarrow> 1 < a)"
  using mult_less_cancel_left [of c a 1] by simp

lemma sgn_0_0: "sgn a = 0 \<longleftrightarrow> a = 0"
  by (fact sgn_eq_0_iff)

lemma sgn_1_pos: "sgn a = 1 \<longleftrightarrow> a > 0"
  unfolding sgn_if by simp

lemma sgn_1_neg: "sgn a = - 1 \<longleftrightarrow> a < 0"
  unfolding sgn_if by auto

lemma sgn_pos [simp]: "0 < a \<Longrightarrow> sgn a = 1"
  by (simp only: sgn_1_pos)

lemma sgn_neg [simp]: "a < 0 \<Longrightarrow> sgn a = - 1"
  by (simp only: sgn_1_neg)

lemma abs_sgn: "\<bar>k\<bar> = k * sgn k"
  unfolding sgn_if abs_if by auto

lemma sgn_greater [simp]: "0 < sgn a \<longleftrightarrow> 0 < a"
  unfolding sgn_if by auto

lemma sgn_less [simp]: "sgn a < 0 \<longleftrightarrow> a < 0"
  unfolding sgn_if by auto

lemma abs_sgn_eq_1 [simp]:
  "a \<noteq> 0 \<Longrightarrow> \<bar>sgn a\<bar> = 1"
  by simp

lemma abs_sgn_eq: "\<bar>sgn a\<bar> = (if a = 0 then 0 else 1)"
  by (simp add: sgn_if)

lemma abs_dvd_iff [simp]: "\<bar>m\<bar> dvd k \<longleftrightarrow> m dvd k"
  by (simp add: abs_if)

lemma dvd_abs_iff [simp]: "m dvd \<bar>k\<bar> \<longleftrightarrow> m dvd k"
  by (simp add: abs_if)

lemma dvd_if_abs_eq: "\<bar>l\<bar> = \<bar>k\<bar> \<Longrightarrow> l dvd k"
  by (subst abs_dvd_iff [symmetric]) simp

text \<open>
  The following lemmas can be proven in more general structures, but
  are dangerous as simp rules in absence of @{thm neg_equal_zero},
  @{thm neg_less_pos}, @{thm neg_less_eq_nonneg}.
\<close>

lemma equation_minus_iff_1 [simp, no_atp]: "1 = - a \<longleftrightarrow> a = - 1"
  by (fact equation_minus_iff)

lemma minus_equation_iff_1 [simp, no_atp]: "- a = 1 \<longleftrightarrow> a = - 1"
  by (subst minus_equation_iff, auto)

lemma le_minus_iff_1 [simp, no_atp]: "1 \<le> - b \<longleftrightarrow> b \<le> - 1"
  by (fact le_minus_iff)

lemma minus_le_iff_1 [simp, no_atp]: "- a \<le> 1 \<longleftrightarrow> - 1 \<le> a"
  by (fact minus_le_iff)

lemma less_minus_iff_1 [simp, no_atp]: "1 < - b \<longleftrightarrow> b < - 1"
  by (fact less_minus_iff)

lemma minus_less_iff_1 [simp, no_atp]: "- a < 1 \<longleftrightarrow> - 1 < a"
  by (fact minus_less_iff)

end

text \<open>Simprules for comparisons where common factors can be cancelled.\<close>

lemmas mult_compare_simps =
  mult_le_cancel_right mult_le_cancel_left
  mult_le_cancel_right1 mult_le_cancel_right2
  mult_le_cancel_left1 mult_le_cancel_left2
  mult_less_cancel_right mult_less_cancel_left
  mult_less_cancel_right1 mult_less_cancel_right2
  mult_less_cancel_left1 mult_less_cancel_left2
  mult_cancel_right mult_cancel_left
  mult_cancel_right1 mult_cancel_right2
  mult_cancel_left1 mult_cancel_left2


text \<open>Reasoning about inequalities with division\<close>

context linordered_semidom
begin

lemma less_add_one: "a < a + 1"
proof -
  have "a + 0 < a + 1"
    by (blast intro: zero_less_one add_strict_left_mono)
  then show ?thesis by simp
qed

end

context linordered_idom
begin

lemma mult_right_le_one_le: "0 \<le> x \<Longrightarrow> 0 \<le> y \<Longrightarrow> y \<le> 1 \<Longrightarrow> x * y \<le> x"
  by (rule mult_left_le)

lemma mult_left_le_one_le: "0 \<le> x \<Longrightarrow> 0 \<le> y \<Longrightarrow> y \<le> 1 \<Longrightarrow> y * x \<le> x"
  by (auto simp add: mult_le_cancel_right2)

end

text \<open>Absolute Value\<close>

context linordered_idom
begin

lemma mult_sgn_abs: "sgn x * \<bar>x\<bar> = x"
  by (fact sgn_mult_abs)

lemma abs_one: "\<bar>1\<bar> = 1"
  by (fact abs_1)

end

class ordered_ring_abs = ordered_ring + ordered_ab_group_add_abs +
  assumes abs_eq_mult:
    "(0 \<le> a \<or> a \<le> 0) \<and> (0 \<le> b \<or> b \<le> 0) \<Longrightarrow> \<bar>a * b\<bar> = \<bar>a\<bar> * \<bar>b\<bar>"

context linordered_idom
begin

subclass ordered_ring_abs
  by standard (auto simp: abs_if not_less mult_less_0_iff)

lemma abs_mult_self [simp]: "\<bar>a\<bar> * \<bar>a\<bar> = a * a"
  by (simp add: abs_if)

lemma abs_mult_less:
  assumes ac: "\<bar>a\<bar> < c"
    and bd: "\<bar>b\<bar> < d"
  shows "\<bar>a\<bar> * \<bar>b\<bar> < c * d"
proof -
  from ac have "0 < c"
    by (blast intro: le_less_trans abs_ge_zero)
  with bd show ?thesis by (simp add: ac mult_strict_mono)
qed

lemma abs_less_iff: "\<bar>a\<bar> < b \<longleftrightarrow> a < b \<and> - a < b"
  by (simp add: less_le abs_le_iff) (auto simp add: abs_if)

lemma abs_mult_pos: "0 \<le> x \<Longrightarrow> \<bar>y\<bar> * x = \<bar>y * x\<bar>"
  by (simp add: abs_mult)

lemma abs_diff_less_iff: "\<bar>x - a\<bar> < r \<longleftrightarrow> a - r < x \<and> x < a + r"
  by (auto simp add: diff_less_eq ac_simps abs_less_iff)

lemma abs_diff_le_iff: "\<bar>x - a\<bar> \<le> r \<longleftrightarrow> a - r \<le> x \<and> x \<le> a + r"
  by (auto simp add: diff_le_eq ac_simps abs_le_iff)

lemma abs_add_one_gt_zero: "0 < 1 + \<bar>x\<bar>"
  by (auto simp: abs_if not_less intro: zero_less_one add_strict_increasing less_trans)

end

subsection \<open>Dioids\<close>

text \<open>
  Dioids are the alternative extensions of semirings, a semiring can
  either be a ring or a dioid but never both.
\<close>

class dioid = semiring_1 + canonically_ordered_monoid_add
begin

subclass ordered_semiring
  by standard (auto simp: le_iff_add distrib_left distrib_right)

end


hide_fact (open) comm_mult_left_mono comm_mult_strict_left_mono distrib

code_identifier
  code_module Rings \<rightharpoonup> (SML) Arith and (OCaml) Arith and (Haskell) Arith

end
