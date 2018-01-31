(*  Title:      HOL/Binomial.thy
    Author:     Jacques D. Fleuriot
    Author:     Lawrence C Paulson
    Author:     Jeremy Avigad
    Author:     Chaitanya Mangla
    Author:     Manuel Eberl
*)

section \<open>Combinatorial Functions: Factorial Function, Rising Factorials, Binomial Coefficients and Binomial Theorem\<close>

theory Binomial
  imports Main
begin

subsection \<open>Factorial\<close>

context semiring_char_0
begin

definition fact :: "nat \<Rightarrow> 'a"
  where fact_prod: "fact n = of_nat (\<Prod>{1..n})"

lemma fact_prod_Suc: "fact n = of_nat (prod Suc {0..<n})"
  by (cases n)
    (simp_all add: fact_prod prod.atLeast_Suc_atMost_Suc_shift
      atLeastLessThanSuc_atLeastAtMost)

lemma fact_prod_rev: "fact n = of_nat (\<Prod>i = 0..<n. n - i)"
  using prod.atLeast_atMost_rev [of "\<lambda>i. i" 1 n]
  by (cases n)
    (simp_all add: fact_prod_Suc prod.atLeast_Suc_atMost_Suc_shift
      atLeastLessThanSuc_atLeastAtMost)

lemma fact_0 [simp]: "fact 0 = 1"
  by (simp add: fact_prod)

lemma fact_1 [simp]: "fact 1 = 1"
  by (simp add: fact_prod)

lemma fact_Suc_0 [simp]: "fact (Suc 0) = 1"
  by (simp add: fact_prod)

lemma fact_Suc [simp]: "fact (Suc n) = of_nat (Suc n) * fact n"
  by (simp add: fact_prod atLeastAtMostSuc_conv algebra_simps)

lemma fact_2 [simp]: "fact 2 = 2"
  by (simp add: numeral_2_eq_2)

lemma fact_split: "k \<le> n \<Longrightarrow> fact n = of_nat (prod Suc {n - k..<n}) * fact (n - k)"
  by (simp add: fact_prod_Suc prod.union_disjoint [symmetric]
    ivl_disj_un ac_simps of_nat_mult [symmetric])

end

lemma of_nat_fact [simp]: "of_nat (fact n) = fact n"
  by (simp add: fact_prod)

lemma of_int_fact [simp]: "of_int (fact n) = fact n"
  by (simp only: fact_prod of_int_of_nat_eq)

lemma fact_reduce: "n > 0 \<Longrightarrow> fact n = of_nat n * fact (n - 1)"
  by (cases n) auto

lemma fact_nonzero [simp]: "fact n \<noteq> (0::'a::{semiring_char_0,semiring_no_zero_divisors})"
  apply (induct n)
  apply auto
  using of_nat_eq_0_iff
  apply fastforce
  done

lemma fact_mono_nat: "m \<le> n \<Longrightarrow> fact m \<le> (fact n :: nat)"
  by (induct n) (auto simp: le_Suc_eq)

lemma fact_in_Nats: "fact n \<in> \<nat>"
  by (induct n) auto

lemma fact_in_Ints: "fact n \<in> \<int>"
  by (induct n) auto

context
  assumes "SORT_CONSTRAINT('a::linordered_semidom)"
begin

lemma fact_mono: "m \<le> n \<Longrightarrow> fact m \<le> (fact n :: 'a)"
  by (metis of_nat_fact of_nat_le_iff fact_mono_nat)

lemma fact_ge_1 [simp]: "fact n \<ge> (1 :: 'a)"
  by (metis le0 fact_0 fact_mono)

lemma fact_gt_zero [simp]: "fact n > (0 :: 'a)"
  using fact_ge_1 less_le_trans zero_less_one by blast

lemma fact_ge_zero [simp]: "fact n \<ge> (0 :: 'a)"
  by (simp add: less_imp_le)

lemma fact_not_neg [simp]: "\<not> fact n < (0 :: 'a)"
  by (simp add: not_less_iff_gr_or_eq)

lemma fact_le_power: "fact n \<le> (of_nat (n^n) :: 'a)"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then have *: "fact n \<le> (of_nat (Suc n ^ n) ::'a)"
    by (rule order_trans) (simp add: power_mono del: of_nat_power)
  have "fact (Suc n) = (of_nat (Suc n) * fact n ::'a)"
    by (simp add: algebra_simps)
  also have "\<dots> \<le> of_nat (Suc n) * of_nat (Suc n ^ n)"
    by (simp add: * ordered_comm_semiring_class.comm_mult_left_mono del: of_nat_power)
  also have "\<dots> \<le> of_nat (Suc n ^ Suc n)"
    by (metis of_nat_mult order_refl power_Suc)
  finally show ?case .
qed

end

text \<open>Note that @{term "fact 0 = fact 1"}\<close>
lemma fact_less_mono_nat: "0 < m \<Longrightarrow> m < n \<Longrightarrow> fact m < (fact n :: nat)"
  by (induct n) (auto simp: less_Suc_eq)

lemma fact_less_mono: "0 < m \<Longrightarrow> m < n \<Longrightarrow> fact m < (fact n :: 'a::linordered_semidom)"
  by (metis of_nat_fact of_nat_less_iff fact_less_mono_nat)

lemma fact_ge_Suc_0_nat [simp]: "fact n \<ge> Suc 0"
  by (metis One_nat_def fact_ge_1)

lemma dvd_fact: "1 \<le> m \<Longrightarrow> m \<le> n \<Longrightarrow> m dvd fact n"
  by (induct n) (auto simp: dvdI le_Suc_eq)

lemma fact_ge_self: "fact n \<ge> n"
  by (cases "n = 0") (simp_all add: dvd_imp_le dvd_fact)

lemma fact_dvd: "n \<le> m \<Longrightarrow> fact n dvd (fact m :: 'a::{semiring_div,linordered_semidom})"
  by (induct m) (auto simp: le_Suc_eq)

lemma fact_mod: "m \<le> n \<Longrightarrow> fact n mod (fact m :: 'a::{semiring_div,linordered_semidom}) = 0"
  by (auto simp add: fact_dvd)

lemma fact_div_fact:
  assumes "m \<ge> n"
  shows "fact m div fact n = \<Prod>{n + 1..m}"
proof -
  obtain d where "d = m - n"
    by auto
  with assms have "m = n + d"
    by auto
  have "fact (n + d) div (fact n) = \<Prod>{n + 1..n + d}"
  proof (induct d)
    case 0
    show ?case by simp
  next
    case (Suc d')
    have "fact (n + Suc d') div fact n = Suc (n + d') * fact (n + d') div fact n"
      by simp
    also from Suc.hyps have "\<dots> = Suc (n + d') * \<Prod>{n + 1..n + d'}"
      unfolding div_mult1_eq[of _ "fact (n + d')"] by (simp add: fact_mod)
    also have "\<dots> = \<Prod>{n + 1..n + Suc d'}"
      by (simp add: atLeastAtMostSuc_conv)
    finally show ?case .
  qed
  with \<open>m = n + d\<close> show ?thesis by simp
qed

lemma fact_num_eq_if: "fact m = (if m = 0 then 1 else of_nat m * fact (m - 1))"
  by (cases m) auto

lemma fact_div_fact_le_pow:
  assumes "r \<le> n"
  shows "fact n div fact (n - r) \<le> n ^ r"
proof -
  have "r \<le> n \<Longrightarrow> \<Prod>{n - r..n} = (n - r) * \<Prod>{Suc (n - r)..n}" for r
    by (subst prod.insert[symmetric]) (auto simp: atLeastAtMost_insertL)
  with assms show ?thesis
    by (induct r rule: nat.induct) (auto simp add: fact_div_fact Suc_diff_Suc mult_le_mono)
qed

lemma fact_numeral: "fact (numeral k) = numeral k * fact (pred_numeral k)"
  \<comment> \<open>Evaluation for specific numerals\<close>
  by (metis fact_Suc numeral_eq_Suc of_nat_numeral)


subsection \<open>Binomial coefficients\<close>

text \<open>This development is based on the work of Andy Gordon and Florian Kammueller.\<close>

text \<open>Combinatorial definition\<close>

definition binomial :: "nat \<Rightarrow> nat \<Rightarrow> nat"  (infixl "choose" 65)
  where "n choose k = card {K\<in>Pow {0..<n}. card K = k}"

theorem n_subsets:
  assumes "finite A"
  shows "card {B. B \<subseteq> A \<and> card B = k} = card A choose k"
proof -
  from assms obtain f where bij: "bij_betw f {0..<card A} A"
    by (blast dest: ex_bij_betw_nat_finite)
  then have [simp]: "card (f ` C) = card C" if "C \<subseteq> {0..<card A}" for C
    by (meson bij_betw_imp_inj_on bij_betw_subset card_image that)
  from bij have "bij_betw (image f) (Pow {0..<card A}) (Pow A)"
    by (rule bij_betw_Pow)
  then have "inj_on (image f) (Pow {0..<card A})"
    by (rule bij_betw_imp_inj_on)
  moreover have "{K. K \<subseteq> {0..<card A} \<and> card K = k} \<subseteq> Pow {0..<card A}"
    by auto
  ultimately have "inj_on (image f) {K. K \<subseteq> {0..<card A} \<and> card K = k}"
    by (rule inj_on_subset)
  then have "card {K. K \<subseteq> {0..<card A} \<and> card K = k} =
      card (image f ` {K. K \<subseteq> {0..<card A} \<and> card K = k})" (is "_ = card ?C")
    by (simp add: card_image)
  also have "?C = {K. K \<subseteq> f ` {0..<card A} \<and> card K = k}"
    by (auto elim!: subset_imageE)
  also have "f ` {0..<card A} = A"
    by (meson bij bij_betw_def)
  finally show ?thesis
    by (simp add: binomial_def)
qed

text \<open>Recursive characterization\<close>

lemma binomial_n_0 [simp, code]: "n choose 0 = 1"
proof -
  have "{K \<in> Pow {0..<n}. card K = 0} = {{}}"
    by (auto dest: finite_subset)
  then show ?thesis
    by (simp add: binomial_def)
qed

lemma binomial_0_Suc [simp, code]: "0 choose Suc k = 0"
  by (simp add: binomial_def)

lemma binomial_Suc_Suc [simp, code]: "Suc n choose Suc k = (n choose k) + (n choose Suc k)"
proof -
  let ?P = "\<lambda>n k. {K. K \<subseteq> {0..<n} \<and> card K = k}"
  let ?Q = "?P (Suc n) (Suc k)"
  have inj: "inj_on (insert n) (?P n k)"
    by rule (auto; metis atLeastLessThan_iff insert_iff less_irrefl subsetCE)
  have disjoint: "insert n ` ?P n k \<inter> ?P n (Suc k) = {}"
    by auto
  have "?Q = {K\<in>?Q. n \<in> K} \<union> {K\<in>?Q. n \<notin> K}"
    by auto
  also have "{K\<in>?Q. n \<in> K} = insert n ` ?P n k" (is "?A = ?B")
  proof (rule set_eqI)
    fix K
    have K_finite: "finite K" if "K \<subseteq> insert n {0..<n}"
      using that by (rule finite_subset) simp_all
    have Suc_card_K: "Suc (card K - Suc 0) = card K" if "n \<in> K"
      and "finite K"
    proof -
      from \<open>n \<in> K\<close> obtain L where "K = insert n L" and "n \<notin> L"
        by (blast elim: Set.set_insert)
      with that show ?thesis by (simp add: card_insert)
    qed
    show "K \<in> ?A \<longleftrightarrow> K \<in> ?B"
      by (subst in_image_insert_iff)
        (auto simp add: card_insert subset_eq_atLeast0_lessThan_finite
          Diff_subset_conv K_finite Suc_card_K)
  qed
  also have "{K\<in>?Q. n \<notin> K} = ?P n (Suc k)"
    by (auto simp add: atLeast0_lessThan_Suc)
  finally show ?thesis using inj disjoint
    by (simp add: binomial_def card_Un_disjoint card_image)
qed

lemma binomial_eq_0: "n < k \<Longrightarrow> n choose k = 0"
  by (auto simp add: binomial_def dest: subset_eq_atLeast0_lessThan_card)

lemma zero_less_binomial: "k \<le> n \<Longrightarrow> n choose k > 0"
  by (induct n k rule: diff_induct) simp_all

lemma binomial_eq_0_iff [simp]: "n choose k = 0 \<longleftrightarrow> n < k"
  by (metis binomial_eq_0 less_numeral_extra(3) not_less zero_less_binomial)

lemma zero_less_binomial_iff [simp]: "n choose k > 0 \<longleftrightarrow> k \<le> n"
  by (metis binomial_eq_0_iff not_less0 not_less zero_less_binomial)

lemma binomial_n_n [simp]: "n choose n = 1"
  by (induct n) (simp_all add: binomial_eq_0)

lemma binomial_Suc_n [simp]: "Suc n choose n = Suc n"
  by (induct n) simp_all

lemma binomial_1 [simp]: "n choose Suc 0 = n"
  by (induct n) simp_all

lemma choose_reduce_nat:
  "0 < n \<Longrightarrow> 0 < k \<Longrightarrow>
    n choose k = ((n - 1) choose (k - 1)) + ((n - 1) choose k)"
  using binomial_Suc_Suc [of "n - 1" "k - 1"] by simp

lemma Suc_times_binomial_eq: "Suc n * (n choose k) = (Suc n choose Suc k) * Suc k"
  apply (induct n arbitrary: k)
   apply simp
   apply arith
  apply (case_tac k)
   apply (auto simp add: add_mult_distrib add_mult_distrib2 le_Suc_eq binomial_eq_0)
  done

lemma binomial_le_pow2: "n choose k \<le> 2^n"
  apply (induct n arbitrary: k)
   apply (case_tac k)
    apply simp_all
  apply (case_tac k)
   apply auto
  apply (simp add: add_le_mono mult_2)
  done

text \<open>The absorption property.\<close>
lemma Suc_times_binomial: "Suc k * (Suc n choose Suc k) = Suc n * (n choose k)"
  using Suc_times_binomial_eq by auto

text \<open>This is the well-known version of absorption, but it's harder to use
  because of the need to reason about division.\<close>
lemma binomial_Suc_Suc_eq_times: "(Suc n choose Suc k) = (Suc n * (n choose k)) div Suc k"
  by (simp add: Suc_times_binomial_eq del: mult_Suc mult_Suc_right)

text \<open>Another version of absorption, with \<open>-1\<close> instead of \<open>Suc\<close>.\<close>
lemma times_binomial_minus1_eq: "0 < k \<Longrightarrow> k * (n choose k) = n * ((n - 1) choose (k - 1))"
  using Suc_times_binomial_eq [where n = "n - 1" and k = "k - 1"]
  by (auto split: nat_diff_split)


subsection \<open>The binomial theorem (courtesy of Tobias Nipkow):\<close>

text \<open>Avigad's version, generalized to any commutative ring\<close>
theorem binomial_ring: "(a + b :: 'a::{comm_ring_1,power})^n =
  (\<Sum>k=0..n. (of_nat (n choose k)) * a^k * b^(n-k))"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have decomp: "{0..n+1} = {0} \<union> {n + 1} \<union> {1..n}"
    by auto
  have decomp2: "{0..n} = {0} \<union> {1..n}"
    by auto
  have "(a + b)^(n+1) = (a + b) * (\<Sum>k=0..n. of_nat (n choose k) * a^k * b^(n - k))"
    using Suc.hyps by simp
  also have "\<dots> = a * (\<Sum>k=0..n. of_nat (n choose k) * a^k * b^(n-k)) +
      b * (\<Sum>k=0..n. of_nat (n choose k) * a^k * b^(n-k))"
    by (rule distrib_right)
  also have "\<dots> = (\<Sum>k=0..n. of_nat (n choose k) * a^(k+1) * b^(n-k)) +
      (\<Sum>k=0..n. of_nat (n choose k) * a^k * b^(n - k + 1))"
    by (auto simp add: sum_distrib_left ac_simps)
  also have "\<dots> = (\<Sum>k=0..n. of_nat (n choose k) * a^k * b^(n + 1 - k)) +
      (\<Sum>k=1..n+1. of_nat (n choose (k - 1)) * a^k * b^(n + 1 - k))"
    by (simp add:sum_shift_bounds_cl_Suc_ivl Suc_diff_le field_simps del: sum_cl_ivl_Suc)
  also have "\<dots> = a^(n + 1) + b^(n + 1) +
      (\<Sum>k=1..n. of_nat (n choose (k - 1)) * a^k * b^(n + 1 - k)) +
      (\<Sum>k=1..n. of_nat (n choose k) * a^k * b^(n + 1 - k))"
    by (simp add: decomp2)
  also have "\<dots> = a^(n + 1) + b^(n + 1) +
      (\<Sum>k=1..n. of_nat (n + 1 choose k) * a^k * b^(n + 1 - k))"
    by (auto simp add: field_simps sum.distrib [symmetric] choose_reduce_nat)
  also have "\<dots> = (\<Sum>k=0..n+1. of_nat (n + 1 choose k) * a^k * b^(n + 1 - k))"
    using decomp by (simp add: field_simps)
  finally show ?case
    by simp
qed

text \<open>Original version for the naturals.\<close>
corollary binomial: "(a + b :: nat)^n = (\<Sum>k=0..n. (of_nat (n choose k)) * a^k * b^(n - k))"
  using binomial_ring [of "int a" "int b" n]
  by (simp only: of_nat_add [symmetric] of_nat_mult [symmetric] of_nat_power [symmetric]
      of_nat_sum [symmetric] of_nat_eq_iff of_nat_id)

lemma binomial_fact_lemma: "k \<le> n \<Longrightarrow> fact k * fact (n - k) * (n choose k) = fact n"
proof (induct n arbitrary: k rule: nat_less_induct)
  fix n k
  assume H: "\<forall>m<n. \<forall>x\<le>m. fact x * fact (m - x) * (m choose x) = fact m"
  assume kn: "k \<le> n"
  let ?ths = "fact k * fact (n - k) * (n choose k) = fact n"
  consider "n = 0 \<or> k = 0 \<or> n = k" | m h where "n = Suc m" "k = Suc h" "h < m"
    using kn by atomize_elim presburger
  then show "fact k * fact (n - k) * (n choose k) = fact n"
  proof cases
    case 1
    with kn show ?thesis by auto
  next
    case 2
    note n = \<open>n = Suc m\<close>
    note k = \<open>k = Suc h\<close>
    note hm = \<open>h < m\<close>
    have mn: "m < n"
      using n by arith
    have hm': "h \<le> m"
      using hm by arith
    have km: "k \<le> m"
      using hm k n kn by arith
    have "m - h = Suc (m - Suc h)"
      using  k km hm by arith
    with km k have "fact (m - h) = (m - h) * fact (m - k)"
      by simp
    with n k have "fact k * fact (n - k) * (n choose k) =
        k * (fact h * fact (m - h) * (m choose h)) +
        (m - h) * (fact k * fact (m - k) * (m choose k))"
      by (simp add: field_simps)
    also have "\<dots> = (k + (m - h)) * fact m"
      using H[rule_format, OF mn hm'] H[rule_format, OF mn km]
      by (simp add: field_simps)
    finally show ?thesis
      using k n km by simp
  qed
qed

lemma binomial_fact':
  assumes "k \<le> n"
  shows "n choose k = fact n div (fact k * fact (n - k))"
  using binomial_fact_lemma [OF assms]
  by (metis fact_nonzero mult_eq_0_iff nonzero_mult_div_cancel_left)

lemma binomial_fact:
  assumes kn: "k \<le> n"
  shows "(of_nat (n choose k) :: 'a::field_char_0) = fact n / (fact k * fact (n - k))"
  using binomial_fact_lemma[OF kn]
  apply (simp add: field_simps)
  apply (metis mult.commute of_nat_fact of_nat_mult)
  done

lemma fact_binomial:
  assumes "k \<le> n"
  shows "fact k * of_nat (n choose k) = (fact n / fact (n - k) :: 'a::field_char_0)"
  unfolding binomial_fact [OF assms] by (simp add: field_simps)

lemma choose_two: "n choose 2 = n * (n - 1) div 2"
proof (cases "n \<ge> 2")
  case False
  then have "n = 0 \<or> n = 1"
    by auto
  then show ?thesis by auto
next
  case True
  define m where "m = n - 2"
  with True have "n = m + 2"
    by simp
  then have "fact n = n * (n - 1) * fact (n - 2)"
    by (simp add: fact_prod_Suc atLeast0_lessThan_Suc algebra_simps)
  with True show ?thesis
    by (simp add: binomial_fact')
qed

lemma choose_row_sum: "(\<Sum>k=0..n. n choose k) = 2^n"
  using binomial [of 1 "1" n] by (simp add: numeral_2_eq_2)

lemma sum_choose_lower: "(\<Sum>k=0..n. (r+k) choose k) = Suc (r+n) choose n"
  by (induct n) auto

lemma sum_choose_upper: "(\<Sum>k=0..n. k choose m) = Suc n choose Suc m"
  by (induct n) auto

lemma choose_alternating_sum:
  "n > 0 \<Longrightarrow> (\<Sum>i\<le>n. (-1)^i * of_nat (n choose i)) = (0 :: 'a::comm_ring_1)"
  using binomial_ring[of "-1 :: 'a" 1 n]
  by (simp add: atLeast0AtMost mult_of_nat_commute zero_power)

lemma choose_even_sum:
  assumes "n > 0"
  shows "2 * (\<Sum>i\<le>n. if even i then of_nat (n choose i) else 0) = (2 ^ n :: 'a::comm_ring_1)"
proof -
  have "2 ^ n = (\<Sum>i\<le>n. of_nat (n choose i)) + (\<Sum>i\<le>n. (-1) ^ i * of_nat (n choose i) :: 'a)"
    using choose_row_sum[of n]
    by (simp add: choose_alternating_sum assms atLeast0AtMost of_nat_sum[symmetric])
  also have "\<dots> = (\<Sum>i\<le>n. of_nat (n choose i) + (-1) ^ i * of_nat (n choose i))"
    by (simp add: sum.distrib)
  also have "\<dots> = 2 * (\<Sum>i\<le>n. if even i then of_nat (n choose i) else 0)"
    by (subst sum_distrib_left, intro sum.cong) simp_all
  finally show ?thesis ..
qed

lemma choose_odd_sum:
  assumes "n > 0"
  shows "2 * (\<Sum>i\<le>n. if odd i then of_nat (n choose i) else 0) = (2 ^ n :: 'a::comm_ring_1)"
proof -
  have "2 ^ n = (\<Sum>i\<le>n. of_nat (n choose i)) - (\<Sum>i\<le>n. (-1) ^ i * of_nat (n choose i) :: 'a)"
    using choose_row_sum[of n]
    by (simp add: choose_alternating_sum assms atLeast0AtMost of_nat_sum[symmetric])
  also have "\<dots> = (\<Sum>i\<le>n. of_nat (n choose i) - (-1) ^ i * of_nat (n choose i))"
    by (simp add: sum_subtractf)
  also have "\<dots> = 2 * (\<Sum>i\<le>n. if odd i then of_nat (n choose i) else 0)"
    by (subst sum_distrib_left, intro sum.cong) simp_all
  finally show ?thesis ..
qed

lemma choose_row_sum': "(\<Sum>k\<le>n. (n choose k)) = 2 ^ n"
  using choose_row_sum[of n] by (simp add: atLeast0AtMost)

text\<open>NW diagonal sum property\<close>
lemma sum_choose_diagonal:
  assumes "m \<le> n"
  shows "(\<Sum>k=0..m. (n - k) choose (m - k)) = Suc n choose m"
proof -
  have "(\<Sum>k=0..m. (n-k) choose (m - k)) = (\<Sum>k=0..m. (n - m + k) choose k)"
    using sum.atLeast_atMost_rev [of "\<lambda>k. (n - k) choose (m - k)" 0 m] assms
      by simp
  also have "\<dots> = Suc (n - m + m) choose m"
    by (rule sum_choose_lower)
  also have "\<dots> = Suc n choose m"
    using assms by simp
  finally show ?thesis .
qed


subsection \<open>Pochhammer's symbol: generalized rising factorial\<close>

text \<open>See \<^url>\<open>http://en.wikipedia.org/wiki/Pochhammer_symbol\<close>.\<close>

context comm_semiring_1
begin

definition pochhammer :: "'a \<Rightarrow> nat \<Rightarrow> 'a"
  where pochhammer_prod: "pochhammer a n = prod (\<lambda>i. a + of_nat i) {0..<n}"

lemma pochhammer_prod_rev: "pochhammer a n = prod (\<lambda>i. a + of_nat (n - i)) {1..n}"
  using prod.atLeast_lessThan_rev_at_least_Suc_atMost [of "\<lambda>i. a + of_nat i" 0 n]
  by (simp add: pochhammer_prod)

lemma pochhammer_Suc_prod: "pochhammer a (Suc n) = prod (\<lambda>i. a + of_nat i) {0..n}"
  by (simp add: pochhammer_prod atLeastLessThanSuc_atLeastAtMost)

lemma pochhammer_Suc_prod_rev: "pochhammer a (Suc n) = prod (\<lambda>i. a + of_nat (n - i)) {0..n}"
  by (simp add: pochhammer_prod_rev prod.atLeast_Suc_atMost_Suc_shift)

lemma pochhammer_0 [simp]: "pochhammer a 0 = 1"
  by (simp add: pochhammer_prod)

lemma pochhammer_1 [simp]: "pochhammer a 1 = a"
  by (simp add: pochhammer_prod lessThan_Suc)

lemma pochhammer_Suc0 [simp]: "pochhammer a (Suc 0) = a"
  by (simp add: pochhammer_prod lessThan_Suc)

lemma pochhammer_Suc: "pochhammer a (Suc n) = pochhammer a n * (a + of_nat n)"
  by (simp add: pochhammer_prod atLeast0_lessThan_Suc ac_simps)

end

lemma pochhammer_nonneg: 
  fixes x :: "'a :: linordered_semidom"
  shows "x > 0 \<Longrightarrow> pochhammer x n \<ge> 0"
  by (induction n) (auto simp: pochhammer_Suc intro!: mult_nonneg_nonneg add_nonneg_nonneg)

lemma pochhammer_pos: 
  fixes x :: "'a :: linordered_semidom"
  shows "x > 0 \<Longrightarrow> pochhammer x n > 0"
  by (induction n) (auto simp: pochhammer_Suc intro!: mult_pos_pos add_pos_nonneg)

lemma pochhammer_of_nat: "pochhammer (of_nat x) n = of_nat (pochhammer x n)"
  by (simp add: pochhammer_prod)

lemma pochhammer_of_int: "pochhammer (of_int x) n = of_int (pochhammer x n)"
  by (simp add: pochhammer_prod)

lemma pochhammer_rec: "pochhammer a (Suc n) = a * pochhammer (a + 1) n"
  by (simp add: pochhammer_prod prod.atLeast0_lessThan_Suc_shift ac_simps)

lemma pochhammer_rec': "pochhammer z (Suc n) = (z + of_nat n) * pochhammer z n"
  by (simp add: pochhammer_prod prod.atLeast0_lessThan_Suc ac_simps)

lemma pochhammer_fact: "fact n = pochhammer 1 n"
  by (simp add: pochhammer_prod fact_prod_Suc)

lemma pochhammer_of_nat_eq_0_lemma: "k > n \<Longrightarrow> pochhammer (- (of_nat n :: 'a:: idom)) k = 0"
  by (auto simp add: pochhammer_prod)

lemma pochhammer_of_nat_eq_0_lemma':
  assumes kn: "k \<le> n"
  shows "pochhammer (- (of_nat n :: 'a::{idom,ring_char_0})) k \<noteq> 0"
proof (cases k)
  case 0
  then show ?thesis by simp
next
  case (Suc h)
  then show ?thesis
    apply (simp add: pochhammer_Suc_prod)
    using Suc kn
    apply (auto simp add: algebra_simps)
    done
qed

lemma pochhammer_of_nat_eq_0_iff:
  "pochhammer (- (of_nat n :: 'a::{idom,ring_char_0})) k = 0 \<longleftrightarrow> k > n"
  (is "?l = ?r")
  using pochhammer_of_nat_eq_0_lemma[of n k, where ?'a='a]
    pochhammer_of_nat_eq_0_lemma'[of k n, where ?'a = 'a]
  by (auto simp add: not_le[symmetric])

lemma pochhammer_eq_0_iff: "pochhammer a n = (0::'a::field_char_0) \<longleftrightarrow> (\<exists>k < n. a = - of_nat k)"
  by (auto simp add: pochhammer_prod eq_neg_iff_add_eq_0)

lemma pochhammer_eq_0_mono:
  "pochhammer a n = (0::'a::field_char_0) \<Longrightarrow> m \<ge> n \<Longrightarrow> pochhammer a m = 0"
  unfolding pochhammer_eq_0_iff by auto

lemma pochhammer_neq_0_mono:
  "pochhammer a m \<noteq> (0::'a::field_char_0) \<Longrightarrow> m \<ge> n \<Longrightarrow> pochhammer a n \<noteq> 0"
  unfolding pochhammer_eq_0_iff by auto

lemma pochhammer_minus:
  "pochhammer (- b) k = ((- 1) ^ k :: 'a::comm_ring_1) * pochhammer (b - of_nat k + 1) k"
proof (cases k)
  case 0
  then show ?thesis by simp
next
  case (Suc h)
  have eq: "((- 1) ^ Suc h :: 'a) = (\<Prod>i = 0..h. - 1)"
    using prod_constant [where A="{0.. h}" and y="- 1 :: 'a"]
    by auto
  with Suc show ?thesis
    using pochhammer_Suc_prod_rev [of "b - of_nat k + 1"]
    by (auto simp add: pochhammer_Suc_prod prod.distrib [symmetric] eq of_nat_diff)
qed

lemma pochhammer_minus':
  "pochhammer (b - of_nat k + 1) k = ((- 1) ^ k :: 'a::comm_ring_1) * pochhammer (- b) k"
  apply (simp only: pochhammer_minus [where b = b])
  apply (simp only: mult.assoc [symmetric])
  apply (simp only: power_add [symmetric])
  apply simp
  done

lemma pochhammer_same: "pochhammer (- of_nat n) n =
    ((- 1) ^ n :: 'a::{semiring_char_0,comm_ring_1,semiring_no_zero_divisors}) * fact n"
  unfolding pochhammer_minus
  by (simp add: of_nat_diff pochhammer_fact)

lemma pochhammer_product': "pochhammer z (n + m) = pochhammer z n * pochhammer (z + of_nat n) m"
proof (induct n arbitrary: z)
  case 0
  then show ?case by simp
next
  case (Suc n z)
  have "pochhammer z (Suc n) * pochhammer (z + of_nat (Suc n)) m =
      z * (pochhammer (z + 1) n * pochhammer (z + 1 + of_nat n) m)"
    by (simp add: pochhammer_rec ac_simps)
  also note Suc[symmetric]
  also have "z * pochhammer (z + 1) (n + m) = pochhammer z (Suc (n + m))"
    by (subst pochhammer_rec) simp
  finally show ?case
    by simp
qed

lemma pochhammer_product:
  "m \<le> n \<Longrightarrow> pochhammer z n = pochhammer z m * pochhammer (z + of_nat m) (n - m)"
  using pochhammer_product'[of z m "n - m"] by simp

lemma pochhammer_times_pochhammer_half:
  fixes z :: "'a::field_char_0"
  shows "pochhammer z (Suc n) * pochhammer (z + 1/2) (Suc n) = (\<Prod>k=0..2*n+1. z + of_nat k / 2)"
proof (induct n)
  case 0
  then show ?case
    by (simp add: atLeast0_atMost_Suc)
next
  case (Suc n)
  define n' where "n' = Suc n"
  have "pochhammer z (Suc n') * pochhammer (z + 1 / 2) (Suc n') =
      (pochhammer z n' * pochhammer (z + 1 / 2) n') * ((z + of_nat n') * (z + 1/2 + of_nat n'))"
    (is "_ = _ * ?A")
    by (simp_all add: pochhammer_rec' mult_ac)
  also have "?A = (z + of_nat (Suc (2 * n + 1)) / 2) * (z + of_nat (Suc (Suc (2 * n + 1))) / 2)"
    (is "_ = ?B")
    by (simp add: field_simps n'_def)
  also note Suc[folded n'_def]
  also have "(\<Prod>k=0..2 * n + 1. z + of_nat k / 2) * ?B = (\<Prod>k=0..2 * Suc n + 1. z + of_nat k / 2)"
    by (simp add: atLeast0_atMost_Suc)
  finally show ?case
    by (simp add: n'_def)
qed

lemma pochhammer_double:
  fixes z :: "'a::field_char_0"
  shows "pochhammer (2 * z) (2 * n) = of_nat (2^(2*n)) * pochhammer z n * pochhammer (z+1/2) n"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have "pochhammer (2 * z) (2 * (Suc n)) = pochhammer (2 * z) (2 * n) *
      (2 * (z + of_nat n)) * (2 * (z + of_nat n) + 1)"
    by (simp add: pochhammer_rec' ac_simps)
  also note Suc
  also have "of_nat (2 ^ (2 * n)) * pochhammer z n * pochhammer (z + 1/2) n *
        (2 * (z + of_nat n)) * (2 * (z + of_nat n) + 1) =
      of_nat (2 ^ (2 * (Suc n))) * pochhammer z (Suc n) * pochhammer (z + 1/2) (Suc n)"
    by (simp add: field_simps pochhammer_rec')
  finally show ?case .
qed

lemma fact_double:
  "fact (2 * n) = (2 ^ (2 * n) * pochhammer (1 / 2) n * fact n :: 'a::field_char_0)"
  using pochhammer_double[of "1/2::'a" n] by (simp add: pochhammer_fact)

lemma pochhammer_absorb_comp: "(r - of_nat k) * pochhammer (- r) k = r * pochhammer (-r + 1) k"
  (is "?lhs = ?rhs")
  for r :: "'a::comm_ring_1"
proof -
  have "?lhs = - pochhammer (- r) (Suc k)"
    by (subst pochhammer_rec') (simp add: algebra_simps)
  also have "\<dots> = ?rhs"
    by (subst pochhammer_rec) simp
  finally show ?thesis .
qed


subsection \<open>Generalized binomial coefficients\<close>

definition gbinomial :: "'a::{semidom_divide,semiring_char_0} \<Rightarrow> nat \<Rightarrow> 'a"  (infixl "gchoose" 65)
  where gbinomial_prod_rev: "a gchoose n = prod (\<lambda>i. a - of_nat i) {0..<n} div fact n"

lemma gbinomial_0 [simp]:
  "a gchoose 0 = 1"
  "0 gchoose (Suc n) = 0"
  by (simp_all add: gbinomial_prod_rev prod.atLeast0_lessThan_Suc_shift)

lemma gbinomial_Suc: "a gchoose (Suc k) = prod (\<lambda>i. a - of_nat i) {0..k} div fact (Suc k)"
  by (simp add: gbinomial_prod_rev atLeastLessThanSuc_atLeastAtMost)

lemma gbinomial_mult_fact: "fact n * (a gchoose n) = (\<Prod>i = 0..<n. a - of_nat i)"
  for a :: "'a::field_char_0"
  by (simp_all add: gbinomial_prod_rev field_simps)

lemma gbinomial_mult_fact': "(a gchoose n) * fact n = (\<Prod>i = 0..<n. a - of_nat i)"
  for a :: "'a::field_char_0"
  using gbinomial_mult_fact [of n a] by (simp add: ac_simps)

lemma gbinomial_pochhammer: "a gchoose n = (- 1) ^ n * pochhammer (- a) n / fact n"
  for a :: "'a::field_char_0"
  by (cases n)
    (simp_all add: pochhammer_minus,
     simp_all add: gbinomial_prod_rev pochhammer_prod_rev
       power_mult_distrib [symmetric] atLeastLessThanSuc_atLeastAtMost
       prod.atLeast_Suc_atMost_Suc_shift of_nat_diff)

lemma gbinomial_pochhammer': "s gchoose n = pochhammer (s - of_nat n + 1) n / fact n"
  for s :: "'a::field_char_0"
proof -
  have "s gchoose n = ((-1)^n * (-1)^n) * pochhammer (s - of_nat n + 1) n / fact n"
    by (simp add: gbinomial_pochhammer pochhammer_minus mult_ac)
  also have "(-1 :: 'a)^n * (-1)^n = 1"
    by (subst power_add [symmetric]) simp
  finally show ?thesis
    by simp
qed

lemma gbinomial_binomial: "n gchoose k = n choose k"
proof (cases "k \<le> n")
  case False
  then have "n < k"
    by (simp add: not_le)
  then have "0 \<in> (op - n) ` {0..<k}"
    by auto
  then have "prod (op - n) {0..<k} = 0"
    by (auto intro: prod_zero)
  with \<open>n < k\<close> show ?thesis
    by (simp add: binomial_eq_0 gbinomial_prod_rev prod_zero)
next
  case True
  then have "inj_on (op - n) {0..<k}"
    by (auto intro: inj_onI)
  then have "\<Prod>(op - n ` {0..<k}) = prod (op - n) {0..<k}"
    by (auto dest: prod.reindex)
  also have "op - n ` {0..<k} = {Suc (n - k)..n}"
    using True by (auto simp add: image_def Bex_def) presburger  (* FIXME slow *)
  finally have *: "prod (\<lambda>q. n - q) {0..<k} = \<Prod>{Suc (n - k)..n}" ..
  from True have "n choose k = fact n div (fact k * fact (n - k))"
    by (rule binomial_fact')
  with * show ?thesis
    by (simp add: gbinomial_prod_rev mult.commute [of "fact k"] div_mult2_eq fact_div_fact)
qed

lemma of_nat_gbinomial: "of_nat (n gchoose k) = (of_nat n gchoose k :: 'a::field_char_0)"
proof (cases "k \<le> n")
  case False
  then show ?thesis
    by (simp add: not_le gbinomial_binomial binomial_eq_0 gbinomial_prod_rev)
next
  case True
  define m where "m = n - k"
  with True have n: "n = m + k"
    by arith
  from n have "fact n = ((\<Prod>i = 0..<m + k. of_nat (m + k - i) ):: 'a)"
    by (simp add: fact_prod_rev)
  also have "\<dots> = ((\<Prod>i\<in>{0..<k} \<union> {k..<m + k}. of_nat (m + k - i)) :: 'a)"
    by (simp add: ivl_disj_un)
  finally have "fact n = (fact m * (\<Prod>i = 0..<k. of_nat m + of_nat k - of_nat i) :: 'a)"
    using prod_shift_bounds_nat_ivl [of "\<lambda>i. of_nat (m + k - i) :: 'a" 0 k m]
    by (simp add: fact_prod_rev [of m] prod.union_disjoint of_nat_diff)
  then have "fact n / fact (n - k) = ((\<Prod>i = 0..<k. of_nat n - of_nat i) :: 'a)"
    by (simp add: n)
  with True have "fact k * of_nat (n gchoose k) = (fact k * (of_nat n gchoose k) :: 'a)"
    by (simp only: gbinomial_mult_fact [of k "of_nat n"] gbinomial_binomial [of n k] fact_binomial)
  then show ?thesis
    by simp
qed

lemma binomial_gbinomial: "of_nat (n choose k) = (of_nat n gchoose k :: 'a::field_char_0)"
  by (simp add: gbinomial_binomial [symmetric] of_nat_gbinomial)

setup
  \<open>Sign.add_const_constraint (@{const_name gbinomial}, SOME @{typ "'a::field_char_0 \<Rightarrow> nat \<Rightarrow> 'a"})\<close>

lemma gbinomial_1[simp]: "a gchoose 1 = a"
  by (simp add: gbinomial_prod_rev lessThan_Suc)

lemma gbinomial_Suc0[simp]: "a gchoose (Suc 0) = a"
  by (simp add: gbinomial_prod_rev lessThan_Suc)

lemma gbinomial_mult_1:
  fixes a :: "'a::field_char_0"
  shows "a * (a gchoose n) = of_nat n * (a gchoose n) + of_nat (Suc n) * (a gchoose (Suc n))"
  (is "?l = ?r")
proof -
  have "?r = ((- 1) ^n * pochhammer (- a) n / (fact n)) * (of_nat n - (- a + of_nat n))"
    apply (simp only: gbinomial_pochhammer pochhammer_Suc right_diff_distrib power_Suc)
    apply (simp del: of_nat_Suc fact_Suc)
    apply (auto simp add: field_simps simp del: of_nat_Suc)
    done
  also have "\<dots> = ?l"
    by (simp add: field_simps gbinomial_pochhammer)
  finally show ?thesis ..
qed

lemma gbinomial_mult_1':
  "(a gchoose n) * a = of_nat n * (a gchoose n) + of_nat (Suc n) * (a gchoose (Suc n))"
  for a :: "'a::field_char_0"
  by (simp add: mult.commute gbinomial_mult_1)

lemma gbinomial_Suc_Suc: "(a + 1) gchoose (Suc k) = a gchoose k + (a gchoose (Suc k))"
  for a :: "'a::field_char_0"
proof (cases k)
  case 0
  then show ?thesis by simp
next
  case (Suc h)
  have eq0: "(\<Prod>i\<in>{1..k}. (a + 1) - of_nat i) = (\<Prod>i\<in>{0..h}. a - of_nat i)"
    apply (rule prod.reindex_cong [where l = Suc])
      using Suc
      apply (auto simp add: image_Suc_atMost)
    done
  have "fact (Suc k) * (a gchoose k + (a gchoose (Suc k))) =
      (a gchoose Suc h) * (fact (Suc (Suc h))) +
      (a gchoose Suc (Suc h)) * (fact (Suc (Suc h)))"
    by (simp add: Suc field_simps del: fact_Suc)
  also have "\<dots> =
    (a gchoose Suc h) * of_nat (Suc (Suc h) * fact (Suc h)) + (\<Prod>i=0..Suc h. a - of_nat i)"
    apply (simp del: fact_Suc add: gbinomial_mult_fact field_simps mult.left_commute [of _ "2"])
    apply (simp del: fact_Suc add: fact_Suc [of "Suc h"] field_simps gbinomial_mult_fact
      mult.left_commute [of _ "2"] atLeastLessThanSuc_atLeastAtMost)
    done
  also have "\<dots> =
    (fact (Suc h) * (a gchoose Suc h)) * of_nat (Suc (Suc h)) + (\<Prod>i=0..Suc h. a - of_nat i)"
    by (simp only: fact_Suc mult.commute mult.left_commute of_nat_fact of_nat_id of_nat_mult)
  also have "\<dots> =
    of_nat (Suc (Suc h)) * (\<Prod>i=0..h. a - of_nat i) + (\<Prod>i=0..Suc h. a - of_nat i)"
    unfolding gbinomial_mult_fact atLeastLessThanSuc_atLeastAtMost by auto
  also have "\<dots> =
    (\<Prod>i=0..Suc h. a - of_nat i) + (of_nat h * (\<Prod>i=0..h. a - of_nat i) + 2 * (\<Prod>i=0..h. a - of_nat i))"
    by (simp add: field_simps)
  also have "\<dots> =
    ((a gchoose Suc h) * (fact (Suc h)) * of_nat (Suc k)) + (\<Prod>i\<in>{0..Suc h}. a - of_nat i)"
    unfolding gbinomial_mult_fact'
    by (simp add: comm_semiring_class.distrib field_simps Suc atLeastLessThanSuc_atLeastAtMost)
  also have "\<dots> = (\<Prod>i\<in>{0..h}. a - of_nat i) * (a + 1)"
    unfolding gbinomial_mult_fact' atLeast0_atMost_Suc
    by (simp add: field_simps Suc atLeastLessThanSuc_atLeastAtMost)
  also have "\<dots> = (\<Prod>i\<in>{0..k}. (a + 1) - of_nat i)"
    using eq0
    by (simp add: Suc prod.atLeast0_atMost_Suc_shift)
  also have "\<dots> = (fact (Suc k)) * ((a + 1) gchoose (Suc k))"
    by (simp only: gbinomial_mult_fact atLeastLessThanSuc_atLeastAtMost)
  finally show ?thesis
    using fact_nonzero [of "Suc k"] by auto
qed

lemma gbinomial_reduce_nat: "0 < k \<Longrightarrow> a gchoose k = (a - 1) gchoose (k - 1) + ((a - 1) gchoose k)"
  for a :: "'a::field_char_0"
  by (metis Suc_pred' diff_add_cancel gbinomial_Suc_Suc)

lemma gchoose_row_sum_weighted:
  "(\<Sum>k = 0..m. (r gchoose k) * (r/2 - of_nat k)) = of_nat(Suc m) / 2 * (r gchoose (Suc m))"
  for r :: "'a::field_char_0"
  by (induct m) (simp_all add: field_simps distrib gbinomial_mult_1)

lemma binomial_symmetric:
  assumes kn: "k \<le> n"
  shows "n choose k = n choose (n - k)"
proof -
  have kn': "n - k \<le> n"
    using kn by arith
  from binomial_fact_lemma[OF kn] binomial_fact_lemma[OF kn']
  have "fact k * fact (n - k) * (n choose k) = fact (n - k) * fact (n - (n - k)) * (n choose (n - k))"
    by simp
  then show ?thesis
    using kn by simp
qed

lemma choose_rising_sum:
  "(\<Sum>j\<le>m. ((n + j) choose n)) = ((n + m + 1) choose (n + 1))"
  "(\<Sum>j\<le>m. ((n + j) choose n)) = ((n + m + 1) choose m)"
proof -
  show "(\<Sum>j\<le>m. ((n + j) choose n)) = ((n + m + 1) choose (n + 1))"
    by (induct m) simp_all
  also have "\<dots> = (n + m + 1) choose m"
    by (subst binomial_symmetric) simp_all
  finally show "(\<Sum>j\<le>m. ((n + j) choose n)) = (n + m + 1) choose m" .
qed

lemma choose_linear_sum: "(\<Sum>i\<le>n. i * (n choose i)) = n * 2 ^ (n - 1)"
proof (cases n)
  case 0
  then show ?thesis by simp
next
  case (Suc m)
  have "(\<Sum>i\<le>n. i * (n choose i)) = (\<Sum>i\<le>Suc m. i * (Suc m choose i))"
    by (simp add: Suc)
  also have "\<dots> = Suc m * 2 ^ m"
    by (simp only: sum_atMost_Suc_shift Suc_times_binomial sum_distrib_left[symmetric])
       (simp add: choose_row_sum')
  finally show ?thesis
    using Suc by simp
qed

lemma choose_alternating_linear_sum:
  assumes "n \<noteq> 1"
  shows "(\<Sum>i\<le>n. (-1)^i * of_nat i * of_nat (n choose i) :: 'a::comm_ring_1) = 0"
proof (cases n)
  case 0
  then show ?thesis by simp
next
  case (Suc m)
  with assms have "m > 0"
    by simp
  have "(\<Sum>i\<le>n. (-1) ^ i * of_nat i * of_nat (n choose i) :: 'a) =
      (\<Sum>i\<le>Suc m. (-1) ^ i * of_nat i * of_nat (Suc m choose i))"
    by (simp add: Suc)
  also have "\<dots> = (\<Sum>i\<le>m. (-1) ^ (Suc i) * of_nat (Suc i * (Suc m choose Suc i)))"
    by (simp only: sum_atMost_Suc_shift sum_distrib_left[symmetric] mult_ac of_nat_mult) simp
  also have "\<dots> = - of_nat (Suc m) * (\<Sum>i\<le>m. (-1) ^ i * of_nat (m choose i))"
    by (subst sum_distrib_left, rule sum.cong[OF refl], subst Suc_times_binomial)
       (simp add: algebra_simps)
  also have "(\<Sum>i\<le>m. (-1 :: 'a) ^ i * of_nat ((m choose i))) = 0"
    using choose_alternating_sum[OF \<open>m > 0\<close>] by simp
  finally show ?thesis
    by simp
qed

lemma vandermonde: "(\<Sum>k\<le>r. (m choose k) * (n choose (r - k))) = (m + n) choose r"
proof (induct n arbitrary: r)
  case 0
  have "(\<Sum>k\<le>r. (m choose k) * (0 choose (r - k))) = (\<Sum>k\<le>r. if k = r then (m choose k) else 0)"
    by (intro sum.cong) simp_all
  also have "\<dots> = m choose r"
    by (simp add: sum.delta)
  finally show ?case
    by simp
next
  case (Suc n r)
  show ?case
    by (cases r) (simp_all add: Suc [symmetric] algebra_simps sum.distrib Suc_diff_le)
qed

lemma choose_square_sum: "(\<Sum>k\<le>n. (n choose k)^2) = ((2*n) choose n)"
  using vandermonde[of n n n]
  by (simp add: power2_eq_square mult_2 binomial_symmetric [symmetric])

lemma pochhammer_binomial_sum:
  fixes a b :: "'a::comm_ring_1"
  shows "pochhammer (a + b) n = (\<Sum>k\<le>n. of_nat (n choose k) * pochhammer a k * pochhammer b (n - k))"
proof (induction n arbitrary: a b)
  case 0
  then show ?case by simp
next
  case (Suc n a b)
  have "(\<Sum>k\<le>Suc n. of_nat (Suc n choose k) * pochhammer a k * pochhammer b (Suc n - k)) =
      (\<Sum>i\<le>n. of_nat (n choose i) * pochhammer a (Suc i) * pochhammer b (n - i)) +
      ((\<Sum>i\<le>n. of_nat (n choose Suc i) * pochhammer a (Suc i) * pochhammer b (n - i)) +
      pochhammer b (Suc n))"
    by (subst sum_atMost_Suc_shift) (simp add: ring_distribs sum.distrib)
  also have "(\<Sum>i\<le>n. of_nat (n choose i) * pochhammer a (Suc i) * pochhammer b (n - i)) =
      a * pochhammer ((a + 1) + b) n"
    by (subst Suc) (simp add: sum_distrib_left pochhammer_rec mult_ac)
  also have "(\<Sum>i\<le>n. of_nat (n choose Suc i) * pochhammer a (Suc i) * pochhammer b (n - i)) +
        pochhammer b (Suc n) =
      (\<Sum>i=0..Suc n. of_nat (n choose i) * pochhammer a i * pochhammer b (Suc n - i))"
    apply (subst sum_head_Suc)
    apply simp
    apply (subst sum_shift_bounds_cl_Suc_ivl)
    apply (simp add: atLeast0AtMost)
    done
  also have "\<dots> = (\<Sum>i\<le>n. of_nat (n choose i) * pochhammer a i * pochhammer b (Suc n - i))"
    using Suc by (intro sum.mono_neutral_right) (auto simp: not_le binomial_eq_0)
  also have "\<dots> = (\<Sum>i\<le>n. of_nat (n choose i) * pochhammer a i * pochhammer b (Suc (n - i)))"
    by (intro sum.cong) (simp_all add: Suc_diff_le)
  also have "\<dots> = b * pochhammer (a + (b + 1)) n"
    by (subst Suc) (simp add: sum_distrib_left mult_ac pochhammer_rec)
  also have "a * pochhammer ((a + 1) + b) n + b * pochhammer (a + (b + 1)) n =
      pochhammer (a + b) (Suc n)"
    by (simp add: pochhammer_rec algebra_simps)
  finally show ?case ..
qed

text \<open>Contributed by Manuel Eberl, generalised by LCP.
  Alternative definition of the binomial coefficient as @{term "\<Prod>i<k. (n - i) / (k - i)"}.\<close>
lemma gbinomial_altdef_of_nat: "x gchoose k = (\<Prod>i = 0..<k. (x - of_nat i) / of_nat (k - i) :: 'a)"
  for k :: nat and x :: "'a::field_char_0"
  by (simp add: prod_dividef gbinomial_prod_rev fact_prod_rev)

lemma gbinomial_ge_n_over_k_pow_k:
  fixes k :: nat
    and x :: "'a::linordered_field"
  assumes "of_nat k \<le> x"
  shows "(x / of_nat k :: 'a) ^ k \<le> x gchoose k"
proof -
  have x: "0 \<le> x"
    using assms of_nat_0_le_iff order_trans by blast
  have "(x / of_nat k :: 'a) ^ k = (\<Prod>i = 0..<k. x / of_nat k :: 'a)"
    by (simp add: prod_constant)
  also have "\<dots> \<le> x gchoose k" (* FIXME *)
    unfolding gbinomial_altdef_of_nat
    apply (safe intro!: prod_mono)
    apply simp_all
    prefer 2
    subgoal premises for i
    proof -
      from assms have "x * of_nat i \<ge> of_nat (i * k)"
        by (metis mult.commute mult_le_cancel_right of_nat_less_0_iff of_nat_mult)
      then have "x * of_nat k - x * of_nat i \<le> x * of_nat k - of_nat (i * k)"
        by arith
      then have "x * of_nat (k - i) \<le> (x - of_nat i) * of_nat k"
        using \<open>i < k\<close> by (simp add: algebra_simps zero_less_mult_iff of_nat_diff)
      then have "x * of_nat (k - i) \<le> (x - of_nat i) * (of_nat k :: 'a)"
        by (simp only: of_nat_mult[symmetric] of_nat_le_iff)
      with assms show ?thesis
        using \<open>i < k\<close> by (simp add: field_simps)
    qed
    apply (simp add: x zero_le_divide_iff)
    done
  finally show ?thesis .
qed

lemma gbinomial_negated_upper: "(a gchoose b) = (-1) ^ b * ((of_nat b - a - 1) gchoose b)"
  by (simp add: gbinomial_pochhammer pochhammer_minus algebra_simps)

lemma gbinomial_minus: "((-a) gchoose b) = (-1) ^ b * ((a + of_nat b - 1) gchoose b)"
  by (subst gbinomial_negated_upper) (simp add: add_ac)

lemma Suc_times_gbinomial: "of_nat (Suc b) * ((a + 1) gchoose (Suc b)) = (a + 1) * (a gchoose b)"
proof (cases b)
  case 0
  then show ?thesis by simp
next
  case (Suc b)
  then have "((a + 1) gchoose (Suc (Suc b))) = (\<Prod>i = 0..Suc b. a + (1 - of_nat i)) / fact (b + 2)"
    by (simp add: field_simps gbinomial_prod_rev atLeastLessThanSuc_atLeastAtMost)
  also have "(\<Prod>i = 0..Suc b. a + (1 - of_nat i)) = (a + 1) * (\<Prod>i = 0..b. a - of_nat i)"
    by (simp add: prod.atLeast0_atMost_Suc_shift)
  also have "\<dots> / fact (b + 2) = (a + 1) / of_nat (Suc (Suc b)) * (a gchoose Suc b)"
    by (simp_all add: gbinomial_prod_rev atLeastLessThanSuc_atLeastAtMost)
  finally show ?thesis by (simp add: Suc field_simps del: of_nat_Suc)
qed

lemma gbinomial_factors: "((a + 1) gchoose (Suc b)) = (a + 1) / of_nat (Suc b) * (a gchoose b)"
proof (cases b)
  case 0
  then show ?thesis by simp
next
  case (Suc b)
  then have "((a + 1) gchoose (Suc (Suc b))) = (\<Prod>i = 0 .. Suc b. a + (1 - of_nat i)) / fact (b + 2)"
    by (simp add: field_simps gbinomial_prod_rev atLeastLessThanSuc_atLeastAtMost)
  also have "(\<Prod>i = 0 .. Suc b. a + (1 - of_nat i)) = (a + 1) * (\<Prod>i = 0..b. a - of_nat i)"
    by (simp add: prod.atLeast0_atMost_Suc_shift)
  also have "\<dots> / fact (b + 2) = (a + 1) / of_nat (Suc (Suc b)) * (a gchoose Suc b)"
    by (simp_all add: gbinomial_prod_rev atLeastLessThanSuc_atLeastAtMost atLeast0AtMost)
  finally show ?thesis
    by (simp add: Suc)
qed

lemma gbinomial_rec: "((r + 1) gchoose (Suc k)) = (r gchoose k) * ((r + 1) / of_nat (Suc k))"
  using gbinomial_mult_1[of r k]
  by (subst gbinomial_Suc_Suc) (simp add: field_simps del: of_nat_Suc, simp add: algebra_simps)

lemma gbinomial_of_nat_symmetric: "k \<le> n \<Longrightarrow> (of_nat n) gchoose k = (of_nat n) gchoose (n - k)"
  using binomial_symmetric[of k n] by (simp add: binomial_gbinomial [symmetric])


text \<open>The absorption identity (equation 5.5 \cite[p.~157]{GKP}):
\[
{r \choose k} = \frac{r}{k}{r - 1 \choose k - 1},\quad \textnormal{integer } k \neq 0.
\]\<close>
lemma gbinomial_absorption': "k > 0 \<Longrightarrow> r gchoose k = (r / of_nat k) * (r - 1 gchoose (k - 1))"
  using gbinomial_rec[of "r - 1" "k - 1"]
  by (simp_all add: gbinomial_rec field_simps del: of_nat_Suc)

text \<open>The absorption identity is written in the following form to avoid
division by $k$ (the lower index) and therefore remove the $k \neq 0$
restriction\cite[p.~157]{GKP}:
\[
k{r \choose k} = r{r - 1 \choose k - 1}, \quad \textnormal{integer } k.
\]\<close>
lemma gbinomial_absorption: "of_nat (Suc k) * (r gchoose Suc k) = r * ((r - 1) gchoose k)"
  using gbinomial_absorption'[of "Suc k" r] by (simp add: field_simps del: of_nat_Suc)

text \<open>The absorption identity for natural number binomial coefficients:\<close>
lemma binomial_absorption: "Suc k * (n choose Suc k) = n * ((n - 1) choose k)"
  by (cases n) (simp_all add: binomial_eq_0 Suc_times_binomial del: binomial_Suc_Suc mult_Suc)

text \<open>The absorption companion identity for natural number coefficients,
  following the proof by GKP \cite[p.~157]{GKP}:\<close>
lemma binomial_absorb_comp: "(n - k) * (n choose k) = n * ((n - 1) choose k)"
  (is "?lhs = ?rhs")
proof (cases "n \<le> k")
  case True
  then show ?thesis by auto
next
  case False
  then have "?rhs = Suc ((n - 1) - k) * (n choose Suc ((n - 1) - k))"
    using binomial_symmetric[of k "n - 1"] binomial_absorption[of "(n - 1) - k" n]
    by simp
  also have "Suc ((n - 1) - k) = n - k"
    using False by simp
  also have "n choose \<dots> = n choose k"
    using False by (intro binomial_symmetric [symmetric]) simp_all
  finally show ?thesis ..
qed

text \<open>The generalised absorption companion identity:\<close>
lemma gbinomial_absorb_comp: "(r - of_nat k) * (r gchoose k) = r * ((r - 1) gchoose k)"
  using pochhammer_absorb_comp[of r k] by (simp add: gbinomial_pochhammer)

lemma gbinomial_addition_formula:
  "r gchoose (Suc k) = ((r - 1) gchoose (Suc k)) + ((r - 1) gchoose k)"
  using gbinomial_Suc_Suc[of "r - 1" k] by (simp add: algebra_simps)

lemma binomial_addition_formula:
  "0 < n \<Longrightarrow> n choose (Suc k) = ((n - 1) choose (Suc k)) + ((n - 1) choose k)"
  by (subst choose_reduce_nat) simp_all

text \<open>
  Equation 5.9 of the reference material \cite[p.~159]{GKP} is a useful
  summation formula, operating on both indices:
  \[
   \sum\limits_{k \leq n}{r + k \choose k} = {r + n + 1 \choose n},
   \quad \textnormal{integer } n.
  \]
\<close>
lemma gbinomial_parallel_sum: "(\<Sum>k\<le>n. (r + of_nat k) gchoose k) = (r + of_nat n + 1) gchoose n"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc m)
  then show ?case
    using gbinomial_Suc_Suc[of "(r + of_nat m + 1)" m]
    by (simp add: add_ac)
qed


subsubsection \<open>Summation on the upper index\<close>

text \<open>
  Another summation formula is equation 5.10 of the reference material \cite[p.~160]{GKP},
  aptly named \emph{summation on the upper index}:\[\sum_{0 \leq k \leq n} {k \choose m} =
  {n + 1 \choose m + 1}, \quad \textnormal{integers } m, n \geq 0.\]
\<close>
lemma gbinomial_sum_up_index:
  "(\<Sum>k = 0..n. (of_nat k gchoose m) :: 'a::field_char_0) = (of_nat n + 1) gchoose (m + 1)"
proof (induct n)
  case 0
  show ?case
    using gbinomial_Suc_Suc[of 0 m]
    by (cases m) auto
next
  case (Suc n)
  then show ?case
    using gbinomial_Suc_Suc[of "of_nat (Suc n) :: 'a" m]
    by (simp add: add_ac)
qed

lemma gbinomial_index_swap:
  "((-1) ^ m) * ((- (of_nat n) - 1) gchoose m) = ((-1) ^ n) * ((- (of_nat m) - 1) gchoose n)"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = (of_nat (m + n) gchoose m)"
    by (subst gbinomial_negated_upper) (simp add: power_mult_distrib [symmetric])
  also have "\<dots> = (of_nat (m + n) gchoose n)"
    by (subst gbinomial_of_nat_symmetric) simp_all
  also have "\<dots> = ?rhs"
    by (subst gbinomial_negated_upper) simp
  finally show ?thesis .
qed

lemma gbinomial_sum_lower_neg: "(\<Sum>k\<le>m. (r gchoose k) * (- 1) ^ k) = (- 1) ^ m * (r - 1 gchoose m)"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = (\<Sum>k\<le>m. -(r + 1) + of_nat k gchoose k)"
    by (intro sum.cong[OF refl]) (subst gbinomial_negated_upper, simp add: power_mult_distrib)
  also have "\<dots>  = - r + of_nat m gchoose m"
    by (subst gbinomial_parallel_sum) simp
  also have "\<dots> = ?rhs"
    by (subst gbinomial_negated_upper) (simp add: power_mult_distrib)
  finally show ?thesis .
qed

lemma gbinomial_partial_row_sum:
  "(\<Sum>k\<le>m. (r gchoose k) * ((r / 2) - of_nat k)) = ((of_nat m + 1)/2) * (r gchoose (m + 1))"
proof (induct m)
  case 0
  then show ?case by simp
next
  case (Suc mm)
  then have "(\<Sum>k\<le>Suc mm. (r gchoose k) * (r / 2 - of_nat k)) =
      (r - of_nat (Suc mm)) * (r gchoose Suc mm) / 2"
    by (simp add: field_simps)
  also have "\<dots> = r * (r - 1 gchoose Suc mm) / 2"
    by (subst gbinomial_absorb_comp) (rule refl)
  also have "\<dots> = (of_nat (Suc mm) + 1) / 2 * (r gchoose (Suc mm + 1))"
    by (subst gbinomial_absorption [symmetric]) simp
  finally show ?case .
qed

lemma sum_bounds_lt_plus1: "(\<Sum>k<mm. f (Suc k)) = (\<Sum>k=1..mm. f k)"
  by (induct mm) simp_all

lemma gbinomial_partial_sum_poly:
  "(\<Sum>k\<le>m. (of_nat m + r gchoose k) * x^k * y^(m-k)) =
    (\<Sum>k\<le>m. (-r gchoose k) * (-x)^k * (x + y)^(m-k))"
  (is "?lhs m = ?rhs m")
proof (induction m)
  case 0
  then show ?case by simp
next
  case (Suc mm)
  define G where "G i k = (of_nat i + r gchoose k) * x^k * y^(i - k)" for i k
  define S where "S = ?lhs"
  have SG_def: "S = (\<lambda>i. (\<Sum>k\<le>i. (G i k)))"
    unfolding S_def G_def ..

  have "S (Suc mm) = G (Suc mm) 0 + (\<Sum>k=Suc 0..Suc mm. G (Suc mm) k)"
    using SG_def by (simp add: sum_head_Suc atLeast0AtMost [symmetric])
  also have "(\<Sum>k=Suc 0..Suc mm. G (Suc mm) k) = (\<Sum>k=0..mm. G (Suc mm) (Suc k))"
    by (subst sum_shift_bounds_cl_Suc_ivl) simp
  also have "\<dots> = (\<Sum>k=0..mm. ((of_nat mm + r gchoose (Suc k)) +
      (of_nat mm + r gchoose k)) * x^(Suc k) * y^(mm - k))"
    unfolding G_def by (subst gbinomial_addition_formula) simp
  also have "\<dots> = (\<Sum>k=0..mm. (of_nat mm + r gchoose (Suc k)) * x^(Suc k) * y^(mm - k)) +
      (\<Sum>k=0..mm. (of_nat mm + r gchoose k) * x^(Suc k) * y^(mm - k))"
    by (subst sum.distrib [symmetric]) (simp add: algebra_simps)
  also have "(\<Sum>k=0..mm. (of_nat mm + r gchoose (Suc k)) * x^(Suc k) * y^(mm - k)) =
      (\<Sum>k<Suc mm. (of_nat mm + r gchoose (Suc k)) * x^(Suc k) * y^(mm - k))"
    by (simp only: atLeast0AtMost lessThan_Suc_atMost)
  also have "\<dots> = (\<Sum>k<mm. (of_nat mm + r gchoose Suc k) * x^(Suc k) * y^(mm-k)) +
      (of_nat mm + r gchoose (Suc mm)) * x^(Suc mm)"
    (is "_ = ?A + ?B")
    by (subst sum_lessThan_Suc) simp
  also have "?A = (\<Sum>k=1..mm. (of_nat mm + r gchoose k) * x^k * y^(mm - k + 1))"
  proof (subst sum_bounds_lt_plus1 [symmetric], intro sum.cong[OF refl], clarify)
    fix k
    assume "k < mm"
    then have "mm - k = mm - Suc k + 1"
      by linarith
    then show "(of_nat mm + r gchoose Suc k) * x ^ Suc k * y ^ (mm - k) =
        (of_nat mm + r gchoose Suc k) * x ^ Suc k * y ^ (mm - Suc k + 1)"
      by (simp only:)
  qed
  also have "\<dots> + ?B = y * (\<Sum>k=1..mm. (G mm k)) + (of_nat mm + r gchoose (Suc mm)) * x^(Suc mm)"
    unfolding G_def by (subst sum_distrib_left) (simp add: algebra_simps)
  also have "(\<Sum>k=0..mm. (of_nat mm + r gchoose k) * x^(Suc k) * y^(mm - k)) = x * (S mm)"
    unfolding S_def by (subst sum_distrib_left) (simp add: atLeast0AtMost algebra_simps)
  also have "(G (Suc mm) 0) = y * (G mm 0)"
    by (simp add: G_def)
  finally have "S (Suc mm) =
      y * (G mm 0 + (\<Sum>k=1..mm. (G mm k))) + (of_nat mm + r gchoose (Suc mm)) * x^(Suc mm) + x * (S mm)"
    by (simp add: ring_distribs)
  also have "G mm 0 + (\<Sum>k=1..mm. (G mm k)) = S mm"
    by (simp add: sum_head_Suc[symmetric] SG_def atLeast0AtMost)
  finally have "S (Suc mm) = (x + y) * (S mm) + (of_nat mm + r gchoose (Suc mm)) * x^(Suc mm)"
    by (simp add: algebra_simps)
  also have "(of_nat mm + r gchoose (Suc mm)) = (-1) ^ (Suc mm) * (- r gchoose (Suc mm))"
    by (subst gbinomial_negated_upper) simp
  also have "(-1) ^ Suc mm * (- r gchoose Suc mm) * x ^ Suc mm =
      (- r gchoose (Suc mm)) * (-x) ^ Suc mm"
    by (simp add: power_minus[of x])
  also have "(x + y) * S mm + \<dots> = (x + y) * ?rhs mm + (- r gchoose (Suc mm)) * (- x)^Suc mm"
    unfolding S_def by (subst Suc.IH) simp
  also have "(x + y) * ?rhs mm = (\<Sum>n\<le>mm. ((- r gchoose n) * (- x) ^ n * (x + y) ^ (Suc mm - n)))"
    by (subst sum_distrib_left, rule sum.cong) (simp_all add: Suc_diff_le)
  also have "\<dots> + (-r gchoose (Suc mm)) * (-x)^Suc mm =
      (\<Sum>n\<le>Suc mm. (- r gchoose n) * (- x) ^ n * (x + y) ^ (Suc mm - n))"
    by simp
  finally show ?case
    by (simp only: S_def)
qed

lemma gbinomial_partial_sum_poly_xpos:
  "(\<Sum>k\<le>m. (of_nat m + r gchoose k) * x^k * y^(m-k)) =
     (\<Sum>k\<le>m. (of_nat k + r - 1 gchoose k) * x^k * (x + y)^(m-k))"
  apply (subst gbinomial_partial_sum_poly)
  apply (subst gbinomial_negated_upper)
  apply (intro sum.cong, rule refl)
  apply (simp add: power_mult_distrib [symmetric])
  done

lemma binomial_r_part_sum: "(\<Sum>k\<le>m. (2 * m + 1 choose k)) = 2 ^ (2 * m)"
proof -
  have "2 * 2^(2*m) = (\<Sum>k = 0..(2 * m + 1). (2 * m + 1 choose k))"
    using choose_row_sum[where n="2 * m + 1"] by simp
  also have "(\<Sum>k = 0..(2 * m + 1). (2 * m + 1 choose k)) =
      (\<Sum>k = 0..m. (2 * m + 1 choose k)) +
      (\<Sum>k = m+1..2*m+1. (2 * m + 1 choose k))"
    using sum_ub_add_nat[of 0 m "\<lambda>k. 2 * m + 1 choose k" "m+1"]
    by (simp add: mult_2)
  also have "(\<Sum>k = m+1..2*m+1. (2 * m + 1 choose k)) =
      (\<Sum>k = 0..m. (2 * m + 1 choose (k + (m + 1))))"
    by (subst sum_shift_bounds_cl_nat_ivl [symmetric]) (simp add: mult_2)
  also have "\<dots> = (\<Sum>k = 0..m. (2 * m + 1 choose (m - k)))"
    by (intro sum.cong[OF refl], subst binomial_symmetric) simp_all
  also have "\<dots> = (\<Sum>k = 0..m. (2 * m + 1 choose k))"
    using sum.atLeast_atMost_rev [of "\<lambda>k. 2 * m + 1 choose (m - k)" 0 m]
    by simp
  also have "\<dots> + \<dots> = 2 * \<dots>"
    by simp
  finally show ?thesis
    by (subst (asm) mult_cancel1) (simp add: atLeast0AtMost)
qed

lemma gbinomial_r_part_sum: "(\<Sum>k\<le>m. (2 * (of_nat m) + 1 gchoose k)) = 2 ^ (2 * m)"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = of_nat (\<Sum>k\<le>m. (2 * m + 1) choose k)"
    by (simp add: binomial_gbinomial add_ac)
  also have "\<dots> = of_nat (2 ^ (2 * m))"
    by (subst binomial_r_part_sum) (rule refl)
  finally show ?thesis by simp
qed

lemma gbinomial_sum_nat_pow2:
  "(\<Sum>k\<le>m. (of_nat (m + k) gchoose k :: 'a::field_char_0) / 2 ^ k) = 2 ^ m"
  (is "?lhs = ?rhs")
proof -
  have "2 ^ m * 2 ^ m = (2 ^ (2*m) :: 'a)"
    by (induct m) simp_all
  also have "\<dots> = (\<Sum>k\<le>m. (2 * (of_nat m) + 1 gchoose k))"
    using gbinomial_r_part_sum ..
  also have "\<dots> = (\<Sum>k\<le>m. (of_nat (m + k) gchoose k) * 2 ^ (m - k))"
    using gbinomial_partial_sum_poly_xpos[where x="1" and y="1" and r="of_nat m + 1" and m="m"]
    by (simp add: add_ac)
  also have "\<dots> = 2 ^ m * (\<Sum>k\<le>m. (of_nat (m + k) gchoose k) / 2 ^ k)"
    by (subst sum_distrib_left) (simp add: algebra_simps power_diff)
  finally show ?thesis
    by (subst (asm) mult_left_cancel) simp_all
qed

lemma gbinomial_trinomial_revision:
  assumes "k \<le> m"
  shows "(r gchoose m) * (of_nat m gchoose k) = (r gchoose k) * (r - of_nat k gchoose (m - k))"
proof -
  have "(r gchoose m) * (of_nat m gchoose k) = (r gchoose m) * fact m / (fact k * fact (m - k))"
    using assms by (simp add: binomial_gbinomial [symmetric] binomial_fact)
  also have "\<dots> = (r gchoose k) * (r - of_nat k gchoose (m - k))"
    using assms by (simp add: gbinomial_pochhammer power_diff pochhammer_product)
  finally show ?thesis .
qed

text \<open>Versions of the theorems above for the natural-number version of "choose"\<close>
lemma binomial_altdef_of_nat:
  "k \<le> n \<Longrightarrow> of_nat (n choose k) = (\<Prod>i = 0..<k. of_nat (n - i) / of_nat (k - i) :: 'a)"
  for n k :: nat and x :: "'a::field_char_0"
  by (simp add: gbinomial_altdef_of_nat binomial_gbinomial of_nat_diff)

lemma binomial_ge_n_over_k_pow_k: "k \<le> n \<Longrightarrow> (of_nat n / of_nat k :: 'a) ^ k \<le> of_nat (n choose k)"
  for k n :: nat and x :: "'a::linordered_field"
  by (simp add: gbinomial_ge_n_over_k_pow_k binomial_gbinomial of_nat_diff)

lemma binomial_le_pow:
  assumes "r \<le> n"
  shows "n choose r \<le> n ^ r"
proof -
  have "n choose r \<le> fact n div fact (n - r)"
    using assms by (subst binomial_fact_lemma[symmetric]) auto
  with fact_div_fact_le_pow [OF assms] show ?thesis
    by auto
qed

lemma binomial_altdef_nat: "k \<le> n \<Longrightarrow> n choose k = fact n div (fact k * fact (n - k))"
  for k n :: nat
  by (subst binomial_fact_lemma [symmetric]) auto

lemma choose_dvd:
  "k \<le> n \<Longrightarrow> fact k * fact (n - k) dvd (fact n :: 'a::{semiring_div,linordered_semidom})"
  unfolding dvd_def
  apply (rule exI [where x="of_nat (n choose k)"])
  using binomial_fact_lemma [of k n, THEN arg_cong [where f = of_nat and 'b='a]]
  apply auto
  done

lemma fact_fact_dvd_fact:
  "fact k * fact n dvd (fact (k + n) :: 'a::{semiring_div,linordered_semidom})"
  by (metis add.commute add_diff_cancel_left' choose_dvd le_add2)

lemma choose_mult_lemma:
  "((m + r + k) choose (m + k)) * ((m + k) choose k) = ((m + r + k) choose k) * ((m + r) choose m)"
  (is "?lhs = _")
proof -
  have "?lhs =
      fact (m + r + k) div (fact (m + k) * fact (m + r - m)) * (fact (m + k) div (fact k * fact m))"
    by (simp add: binomial_altdef_nat)
  also have "\<dots> = fact (m + r + k) div (fact r * (fact k * fact m))"
    apply (subst div_mult_div_if_dvd)
    apply (auto simp: algebra_simps fact_fact_dvd_fact)
    apply (metis add.assoc add.commute fact_fact_dvd_fact)
    done
  also have "\<dots> = (fact (m + r + k) * fact (m + r)) div (fact r * (fact k * fact m) * fact (m + r))"
    apply (subst div_mult_div_if_dvd [symmetric])
    apply (auto simp add: algebra_simps)
    apply (metis fact_fact_dvd_fact dvd_trans nat_mult_dvd_cancel_disj)
    done
  also have "\<dots> =
      (fact (m + r + k) div (fact k * fact (m + r)) * (fact (m + r) div (fact r * fact m)))"
    apply (subst div_mult_div_if_dvd)
    apply (auto simp: fact_fact_dvd_fact algebra_simps)
    done
  finally show ?thesis
    by (simp add: binomial_altdef_nat mult.commute)
qed

text \<open>The "Subset of a Subset" identity.\<close>
lemma choose_mult:
  "k \<le> m \<Longrightarrow> m \<le> n \<Longrightarrow> (n choose m) * (m choose k) = (n choose k) * ((n - k) choose (m - k))"
  using choose_mult_lemma [of "m-k" "n-m" k] by simp


subsection \<open>More on Binomial Coefficients\<close>

lemma choose_one: "n choose 1 = n" for n :: nat
  by simp

lemma card_UNION:
  assumes "finite A"
    and "\<forall>k \<in> A. finite k"
  shows "card (\<Union>A) = nat (\<Sum>I | I \<subseteq> A \<and> I \<noteq> {}. (- 1) ^ (card I + 1) * int (card (\<Inter>I)))"
  (is "?lhs = ?rhs")
proof -
  have "?rhs = nat (\<Sum>I | I \<subseteq> A \<and> I \<noteq> {}. (- 1) ^ (card I + 1) * (\<Sum>_\<in>\<Inter>I. 1))"
    by simp
  also have "\<dots> = nat (\<Sum>I | I \<subseteq> A \<and> I \<noteq> {}. (\<Sum>_\<in>\<Inter>I. (- 1) ^ (card I + 1)))"
    (is "_ = nat ?rhs")
    by (subst sum_distrib_left) simp
  also have "?rhs = (\<Sum>(I, _)\<in>Sigma {I. I \<subseteq> A \<and> I \<noteq> {}} Inter. (- 1) ^ (card I + 1))"
    using assms by (subst sum.Sigma) auto
  also have "\<dots> = (\<Sum>(x, I)\<in>(SIGMA x:UNIV. {I. I \<subseteq> A \<and> I \<noteq> {} \<and> x \<in> \<Inter>I}). (- 1) ^ (card I + 1))"
    by (rule sum.reindex_cong [where l = "\<lambda>(x, y). (y, x)"]) (auto intro: inj_onI simp add: split_beta)
  also have "\<dots> = (\<Sum>(x, I)\<in>(SIGMA x:\<Union>A. {I. I \<subseteq> A \<and> I \<noteq> {} \<and> x \<in> \<Inter>I}). (- 1) ^ (card I + 1))"
    using assms
    by (auto intro!: sum.mono_neutral_cong_right finite_SigmaI2 intro: finite_subset[where B="\<Union>A"])
  also have "\<dots> = (\<Sum>x\<in>\<Union>A. (\<Sum>I|I \<subseteq> A \<and> I \<noteq> {} \<and> x \<in> \<Inter>I. (- 1) ^ (card I + 1)))"
    using assms by (subst sum.Sigma) auto
  also have "\<dots> = (\<Sum>_\<in>\<Union>A. 1)" (is "sum ?lhs _ = _")
  proof (rule sum.cong[OF refl])
    fix x
    assume x: "x \<in> \<Union>A"
    define K where "K = {X \<in> A. x \<in> X}"
    with \<open>finite A\<close> have K: "finite K"
      by auto
    let ?I = "\<lambda>i. {I. I \<subseteq> A \<and> card I = i \<and> x \<in> \<Inter>I}"
    have "inj_on snd (SIGMA i:{1..card A}. ?I i)"
      using assms by (auto intro!: inj_onI)
    moreover have [symmetric]: "snd ` (SIGMA i:{1..card A}. ?I i) = {I. I \<subseteq> A \<and> I \<noteq> {} \<and> x \<in> \<Inter>I}"
      using assms
      by (auto intro!: rev_image_eqI[where x="(card a, a)" for a]
        simp add: card_gt_0_iff[folded Suc_le_eq]
        dest: finite_subset intro: card_mono)
    ultimately have "?lhs x = (\<Sum>(i, I)\<in>(SIGMA i:{1..card A}. ?I i). (- 1) ^ (i + 1))"
      by (rule sum.reindex_cong [where l = snd]) fastforce
    also have "\<dots> = (\<Sum>i=1..card A. (\<Sum>I|I \<subseteq> A \<and> card I = i \<and> x \<in> \<Inter>I. (- 1) ^ (i + 1)))"
      using assms by (subst sum.Sigma) auto
    also have "\<dots> = (\<Sum>i=1..card A. (- 1) ^ (i + 1) * (\<Sum>I|I \<subseteq> A \<and> card I = i \<and> x \<in> \<Inter>I. 1))"
      by (subst sum_distrib_left) simp
    also have "\<dots> = (\<Sum>i=1..card K. (- 1) ^ (i + 1) * (\<Sum>I|I \<subseteq> K \<and> card I = i. 1))"
      (is "_ = ?rhs")
    proof (rule sum.mono_neutral_cong_right[rule_format])
      show "finite {1..card A}"
        by simp
      show "{1..card K} \<subseteq> {1..card A}"
        using \<open>finite A\<close> by (auto simp add: K_def intro: card_mono)
    next
      fix i
      assume "i \<in> {1..card A} - {1..card K}"
      then have i: "i \<le> card A" "card K < i"
        by auto
      have "{I. I \<subseteq> A \<and> card I = i \<and> x \<in> \<Inter>I} = {I. I \<subseteq> K \<and> card I = i}"
        by (auto simp add: K_def)
      also have "\<dots> = {}"
        using \<open>finite A\<close> i by (auto simp add: K_def dest: card_mono[rotated 1])
      finally show "(- 1) ^ (i + 1) * (\<Sum>I | I \<subseteq> A \<and> card I = i \<and> x \<in> \<Inter>I. 1 :: int) = 0"
        by (simp only:) simp
    next
      fix i
      have "(\<Sum>I | I \<subseteq> A \<and> card I = i \<and> x \<in> \<Inter>I. 1) = (\<Sum>I | I \<subseteq> K \<and> card I = i. 1 :: int)"
        (is "?lhs = ?rhs")
        by (rule sum.cong) (auto simp add: K_def)
      then show "(- 1) ^ (i + 1) * ?lhs = (- 1) ^ (i + 1) * ?rhs"
        by simp
    qed
    also have "{I. I \<subseteq> K \<and> card I = 0} = {{}}"
      using assms by (auto simp add: card_eq_0_iff K_def dest: finite_subset)
    then have "?rhs = (\<Sum>i = 0..card K. (- 1) ^ (i + 1) * (\<Sum>I | I \<subseteq> K \<and> card I = i. 1 :: int)) + 1"
      by (subst (2) sum_head_Suc) simp_all
    also have "\<dots> = (\<Sum>i = 0..card K. (- 1) * ((- 1) ^ i * int (card K choose i))) + 1"
      using K by (subst n_subsets[symmetric]) simp_all
    also have "\<dots> = - (\<Sum>i = 0..card K. (- 1) ^ i * int (card K choose i)) + 1"
      by (subst sum_distrib_left[symmetric]) simp
    also have "\<dots> =  - ((-1 + 1) ^ card K) + 1"
      by (subst binomial_ring) (simp add: ac_simps)
    also have "\<dots> = 1"
      using x K by (auto simp add: K_def card_gt_0_iff)
    finally show "?lhs x = 1" .
  qed
  also have "nat \<dots> = card (\<Union>A)"
    by simp
  finally show ?thesis ..
qed

text \<open>The number of nat lists of length \<open>m\<close> summing to \<open>N\<close> is @{term "(N + m - 1) choose N"}:\<close>
lemma card_length_sum_list_rec:
  assumes "m \<ge> 1"
  shows "card {l::nat list. length l = m \<and> sum_list l = N} =
      card {l. length l = (m - 1) \<and> sum_list l = N} +
      card {l. length l = m \<and> sum_list l + 1 = N}"
    (is "card ?C = card ?A + card ?B")
proof -
  let ?A' = "{l. length l = m \<and> sum_list l = N \<and> hd l = 0}"
  let ?B' = "{l. length l = m \<and> sum_list l = N \<and> hd l \<noteq> 0}"
  let ?f = "\<lambda>l. 0 # l"
  let ?g = "\<lambda>l. (hd l + 1) # tl l"
  have 1: "xs \<noteq> [] \<Longrightarrow> x = hd xs \<Longrightarrow> x # tl xs = xs" for x xs
    by simp
  have 2: "xs \<noteq> [] \<Longrightarrow> sum_list(tl xs) = sum_list xs - hd xs" for xs :: "nat list"
    by (auto simp add: neq_Nil_conv)
  have f: "bij_betw ?f ?A ?A'"
    apply (rule bij_betw_byWitness[where f' = tl])
    using assms
    apply (auto simp: 2 length_0_conv[symmetric] 1 simp del: length_0_conv)
    done
  have 3: "xs \<noteq> [] \<Longrightarrow> hd xs + (sum_list xs - hd xs) = sum_list xs" for xs :: "nat list"
    by (metis 1 sum_list_simps(2) 2)
  have g: "bij_betw ?g ?B ?B'"
    apply (rule bij_betw_byWitness[where f' = "\<lambda>l. (hd l - 1) # tl l"])
    using assms
    by (auto simp: 2 length_0_conv[symmetric] intro!: 3
        simp del: length_greater_0_conv length_0_conv)
  have fin: "finite {xs. size xs = M \<and> set xs \<subseteq> {0..<N}}" for M N :: nat
    using finite_lists_length_eq[OF finite_atLeastLessThan] conj_commute by auto
  have fin_A: "finite ?A" using fin[of _ "N+1"]
    by (intro finite_subset[where ?A = "?A" and ?B = "{xs. size xs = m - 1 \<and> set xs \<subseteq> {0..<N+1}}"])
      (auto simp: member_le_sum_list_nat less_Suc_eq_le)
  have fin_B: "finite ?B"
    by (intro finite_subset[where ?A = "?B" and ?B = "{xs. size xs = m \<and> set xs \<subseteq> {0..<N}}"])
      (auto simp: member_le_sum_list_nat less_Suc_eq_le fin)
  have uni: "?C = ?A' \<union> ?B'"
    by auto
  have disj: "?A' \<inter> ?B' = {}"
    by auto
  have "card ?C = card(?A' \<union> ?B')"
    using uni by simp
  also have "\<dots> = card ?A + card ?B"
    using card_Un_disjoint[OF _ _ disj] bij_betw_finite[OF f] bij_betw_finite[OF g]
      bij_betw_same_card[OF f] bij_betw_same_card[OF g] fin_A fin_B
    by presburger
  finally show ?thesis .
qed

lemma card_length_sum_list: "card {l::nat list. size l = m \<and> sum_list l = N} = (N + m - 1) choose N"
  \<comment> "by Holden Lee, tidied by Tobias Nipkow"
proof (cases m)
  case 0
  then show ?thesis
    by (cases N) (auto cong: conj_cong)
next
  case (Suc m')
  have m: "m \<ge> 1"
    by (simp add: Suc)
  then show ?thesis
  proof (induct "N + m - 1" arbitrary: N m)
    case 0  \<comment> "In the base case, the only solution is [0]."
    have [simp]: "{l::nat list. length l = Suc 0 \<and> (\<forall>n\<in>set l. n = 0)} = {[0]}"
      by (auto simp: length_Suc_conv)
    have "m = 1 \<and> N = 0"
      using 0 by linarith
    then show ?case
      by simp
  next
    case (Suc k)
    have c1: "card {l::nat list. size l = (m - 1) \<and> sum_list l =  N} = (N + (m - 1) - 1) choose N"
    proof (cases "m = 1")
      case True
      with Suc.hyps have "N \<ge> 1"
        by auto
      with True show ?thesis
        by (simp add: binomial_eq_0)
    next
      case False
      then show ?thesis
        using Suc by fastforce
    qed
    from Suc have c2: "card {l::nat list. size l = m \<and> sum_list l + 1 = N} =
      (if N > 0 then ((N - 1) + m - 1) choose (N - 1) else 0)"
    proof -
      have *: "n > 0 \<Longrightarrow> Suc m = n \<longleftrightarrow> m = n - 1" for m n
        by arith
      from Suc have "N > 0 \<Longrightarrow>
        card {l::nat list. size l = m \<and> sum_list l + 1 = N} =
          ((N - 1) + m - 1) choose (N - 1)"
        by (simp add: *)
      then show ?thesis
        by auto
    qed
    from Suc.prems have "(card {l::nat list. size l = (m - 1) \<and> sum_list l = N} +
          card {l::nat list. size l = m \<and> sum_list l + 1 = N}) = (N + m - 1) choose N"
      by (auto simp: c1 c2 choose_reduce_nat[of "N + m - 1" N] simp del: One_nat_def)
    then show ?case
      using card_length_sum_list_rec[OF Suc.prems] by auto
  qed
qed

lemma Suc_times_binomial_add: "Suc a * (Suc (a + b) choose Suc a) = Suc b * (Suc (a + b) choose a)"
  \<comment> \<open>by Lukas Bulwahn\<close>
proof -
  have dvd: "Suc a * (fact a * fact b) dvd fact (Suc (a + b))" for a b
    using fact_fact_dvd_fact[of "Suc a" "b", where 'a=nat]
    by (simp only: fact_Suc add_Suc[symmetric] of_nat_id mult.assoc)
  have "Suc a * (fact (Suc (a + b)) div (Suc a * fact a * fact b)) =
      Suc a * fact (Suc (a + b)) div (Suc a * (fact a * fact b))"
    by (subst div_mult_swap[symmetric]; simp only: mult.assoc dvd)
  also have "\<dots> = Suc b * fact (Suc (a + b)) div (Suc b * (fact a * fact b))"
    by (simp only: div_mult_mult1)
  also have "\<dots> = Suc b * (fact (Suc (a + b)) div (Suc b * (fact a * fact b)))"
    using dvd[of b a] by (subst div_mult_swap[symmetric]; simp only: ac_simps dvd)
  finally show ?thesis
    by (subst (1 2) binomial_altdef_nat)
      (simp_all only: ac_simps diff_Suc_Suc Suc_diff_le diff_add_inverse fact_Suc of_nat_id)
qed


subsection \<open>Misc\<close>

lemma fact_code [code]:
  "fact n = (of_nat (fold_atLeastAtMost_nat (op *) 2 n 1) :: 'a::semiring_char_0)"
proof -
  have "fact n = (of_nat (\<Prod>{1..n}) :: 'a)"
    by (simp add: fact_prod)
  also have "\<Prod>{1..n} = \<Prod>{2..n}"
    by (intro prod.mono_neutral_right) auto
  also have "\<dots> = fold_atLeastAtMost_nat (op *) 2 n 1"
    by (simp add: prod_atLeastAtMost_code)
  finally show ?thesis .
qed

lemma pochhammer_code [code]:
  "pochhammer a n =
    (if n = 0 then 1
     else fold_atLeastAtMost_nat (\<lambda>n acc. (a + of_nat n) * acc) 0 (n - 1) 1)"
  by (cases n)
    (simp_all add: pochhammer_prod prod_atLeastAtMost_code [symmetric]
      atLeastLessThanSuc_atLeastAtMost)

lemma gbinomial_code [code]:
  "a gchoose n =
    (if n = 0 then 1
     else fold_atLeastAtMost_nat (\<lambda>n acc. (a - of_nat n) * acc) 0 (n - 1) 1 / fact n)"
  by (cases n)
    (simp_all add: gbinomial_prod_rev prod_atLeastAtMost_code [symmetric]
      atLeastLessThanSuc_atLeastAtMost)

(* FIXME *)
(*TODO: This code equation breaks Scala code generation in HOL-Codegenerator_Test. We have to figure out why and how to prevent that. *)

(*
lemma binomial_code [code]:
  "(n choose k) =
      (if k > n then 0
       else if 2 * k > n then (n choose (n - k))
       else (fold_atLeastAtMost_nat (op * ) (n-k+1) n 1 div fact k))"
proof -
  {
    assume "k \<le> n"
    then have "{1..n} = {1..n-k} \<union> {n-k+1..n}" by auto
    then have "(fact n :: nat) = fact (n-k) * \<Prod>{n-k+1..n}"
      by (simp add: prod.union_disjoint fact_altdef_nat)
  }
  then show ?thesis by (auto simp: binomial_altdef_nat mult_ac prod_atLeastAtMost_code)
qed
*)

end
