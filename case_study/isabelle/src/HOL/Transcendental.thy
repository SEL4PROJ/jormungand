(*  Title:      HOL/Transcendental.thy
    Author:     Jacques D. Fleuriot, University of Cambridge, University of Edinburgh
    Author:     Lawrence C Paulson
    Author:     Jeremy Avigad
*)

section \<open>Power Series, Transcendental Functions etc.\<close>

theory Transcendental
imports Binomial Series Deriv NthRoot
begin

text \<open>A fact theorem on reals.\<close>

lemma square_fact_le_2_fact: "fact n * fact n \<le> (fact (2 * n) :: real)"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have "(fact (Suc n)) * (fact (Suc n)) = of_nat (Suc n) * of_nat (Suc n) * (fact n * fact n :: real)"
    by (simp add: field_simps)
  also have "\<dots> \<le> of_nat (Suc n) * of_nat (Suc n) * fact (2 * n)"
    by (rule mult_left_mono [OF Suc]) simp
  also have "\<dots> \<le> of_nat (Suc (Suc (2 * n))) * of_nat (Suc (2 * n)) * fact (2 * n)"
    by (rule mult_right_mono)+ (auto simp: field_simps)
  also have "\<dots> = fact (2 * Suc n)" by (simp add: field_simps)
  finally show ?case .
qed

lemma fact_in_Reals: "fact n \<in> \<real>"
  by (induction n) auto

lemma of_real_fact [simp]: "of_real (fact n) = fact n"
  by (metis of_nat_fact of_real_of_nat_eq)

lemma pochhammer_of_real: "pochhammer (of_real x) n = of_real (pochhammer x n)"
  by (simp add: pochhammer_prod)

lemma norm_fact [simp]: "norm (fact n :: 'a::real_normed_algebra_1) = fact n"
proof -
  have "(fact n :: 'a) = of_real (fact n)"
    by simp
  also have "norm \<dots> = fact n"
    by (subst norm_of_real) simp
  finally show ?thesis .
qed

lemma root_test_convergence:
  fixes f :: "nat \<Rightarrow> 'a::banach"
  assumes f: "(\<lambda>n. root n (norm (f n))) \<longlonglongrightarrow> x" \<comment> "could be weakened to lim sup"
    and "x < 1"
  shows "summable f"
proof -
  have "0 \<le> x"
    by (rule LIMSEQ_le[OF tendsto_const f]) (auto intro!: exI[of _ 1])
  from \<open>x < 1\<close> obtain z where z: "x < z" "z < 1"
    by (metis dense)
  from f \<open>x < z\<close> have "eventually (\<lambda>n. root n (norm (f n)) < z) sequentially"
    by (rule order_tendstoD)
  then have "eventually (\<lambda>n. norm (f n) \<le> z^n) sequentially"
    using eventually_ge_at_top
  proof eventually_elim
    fix n
    assume less: "root n (norm (f n)) < z" and n: "1 \<le> n"
    from power_strict_mono[OF less, of n] n show "norm (f n) \<le> z ^ n"
      by simp
  qed
  then show "summable f"
    unfolding eventually_sequentially
    using z \<open>0 \<le> x\<close> by (auto intro!: summable_comparison_test[OF _  summable_geometric])
qed

subsection \<open>More facts about binomial coefficients\<close>

text \<open>
  These facts could have been proven before, but having real numbers 
  makes the proofs a lot easier.
\<close>

lemma central_binomial_odd:
  "odd n \<Longrightarrow> n choose (Suc (n div 2)) = n choose (n div 2)"
proof -
  assume "odd n"
  hence "Suc (n div 2) \<le> n" by presburger
  hence "n choose (Suc (n div 2)) = n choose (n - Suc (n div 2))"
    by (rule binomial_symmetric)
  also from \<open>odd n\<close> have "n - Suc (n div 2) = n div 2" by presburger
  finally show ?thesis .
qed

lemma binomial_less_binomial_Suc:
  assumes k: "k < n div 2"
  shows   "n choose k < n choose (Suc k)"
proof -
  from k have k': "k \<le> n" "Suc k \<le> n" by simp_all
  from k' have "real (n choose k) = fact n / (fact k * fact (n - k))"
    by (simp add: binomial_fact)
  also from k' have "n - k = Suc (n - Suc k)" by simp
  also from k' have "fact \<dots> = (real n - real k) * fact (n - Suc k)"
    by (subst fact_Suc) (simp_all add: of_nat_diff)
  also from k have "fact k = fact (Suc k) / (real k + 1)" by (simp add: field_simps)
  also have "fact n / (fact (Suc k) / (real k + 1) * ((real n - real k) * fact (n - Suc k))) =
               (n choose (Suc k)) * ((real k + 1) / (real n - real k))"
    using k by (simp add: divide_simps binomial_fact)
  also from assms have "(real k + 1) / (real n - real k) < 1" by simp
  finally show ?thesis using k by (simp add: mult_less_cancel_left)
qed

lemma binomial_strict_mono:
  assumes "k < k'" "2*k' \<le> n"
  shows   "n choose k < n choose k'"
proof -
  from assms have "k \<le> k' - 1" by simp
  thus ?thesis
  proof (induction rule: inc_induct)
    case base
    with assms binomial_less_binomial_Suc[of "k' - 1" n] 
      show ?case by simp
  next
    case (step k)
    from step.prems step.hyps assms have "n choose k < n choose (Suc k)" 
      by (intro binomial_less_binomial_Suc) simp_all
    also have "\<dots> < n choose k'" by (rule step.IH)
    finally show ?case .
  qed
qed

lemma binomial_mono:
  assumes "k \<le> k'" "2*k' \<le> n"
  shows   "n choose k \<le> n choose k'"
  using assms binomial_strict_mono[of k k' n] by (cases "k = k'") simp_all

lemma binomial_strict_antimono:
  assumes "k < k'" "2 * k \<ge> n" "k' \<le> n"
  shows   "n choose k > n choose k'"
proof -
  from assms have "n choose (n - k) > n choose (n - k')"
    by (intro binomial_strict_mono) (simp_all add: algebra_simps)
  with assms show ?thesis by (simp add: binomial_symmetric [symmetric])
qed

lemma binomial_antimono:
  assumes "k \<le> k'" "k \<ge> n div 2" "k' \<le> n"
  shows   "n choose k \<ge> n choose k'"
proof (cases "k = k'")
  case False
  note not_eq = False
  show ?thesis
  proof (cases "k = n div 2 \<and> odd n")
    case False
    with assms(2) have "2*k \<ge> n" by presburger
    with not_eq assms binomial_strict_antimono[of k k' n] 
      show ?thesis by simp
  next
    case True
    have "n choose k' \<le> n choose (Suc (n div 2))"
    proof (cases "k' = Suc (n div 2)") 
      case False
      with assms True not_eq have "Suc (n div 2) < k'" by simp
      with assms binomial_strict_antimono[of "Suc (n div 2)" k' n] True
        show ?thesis by auto
    qed simp_all
    also from True have "\<dots> = n choose k" by (simp add: central_binomial_odd)
    finally show ?thesis .
  qed
qed simp_all

lemma binomial_maximum: "n choose k \<le> n choose (n div 2)"
proof -
  have "k \<le> n div 2 \<longleftrightarrow> 2*k \<le> n" by linarith
  consider "2*k \<le> n" | "2*k \<ge> n" "k \<le> n" | "k > n" by linarith
  thus ?thesis
  proof cases
    case 1
    thus ?thesis by (intro binomial_mono) linarith+
  next
    case 2
    thus ?thesis by (intro binomial_antimono) simp_all
  qed (simp_all add: binomial_eq_0)
qed

lemma binomial_maximum': "(2*n) choose k \<le> (2*n) choose n"
  using binomial_maximum[of "2*n"] by simp

lemma central_binomial_lower_bound:
  assumes "n > 0"
  shows   "4^n / (2*real n) \<le> real ((2*n) choose n)"
proof -
  from binomial[of 1 1 "2*n"]
    have "4 ^ n = (\<Sum>k=0..2*n. (2*n) choose k)"
    by (simp add: power_mult power2_eq_square One_nat_def [symmetric] del: One_nat_def)
  also have "{0..2*n} = {0<..<2*n} \<union> {0,2*n}" by auto
  also have "(\<Sum>k\<in>\<dots>. (2*n) choose k) = 
               (\<Sum>k\<in>{0<..<2*n}. (2*n) choose k) + (\<Sum>k\<in>{0,2*n}. (2*n) choose k)"
    by (subst sum.union_disjoint) auto
  also have "(\<Sum>k\<in>{0,2*n}. (2*n) choose k) \<le> (\<Sum>k\<le>1. (n choose k)\<^sup>2)" 
    by (cases n) simp_all
  also from assms have "\<dots> \<le> (\<Sum>k\<le>n. (n choose k)\<^sup>2)"
    by (intro sum_mono3) auto
  also have "\<dots> = (2*n) choose n" by (rule choose_square_sum)
  also have "(\<Sum>k\<in>{0<..<2*n}. (2*n) choose k) \<le> (\<Sum>k\<in>{0<..<2*n}. (2*n) choose n)"
    by (intro sum_mono binomial_maximum')
  also have "\<dots> = card {0<..<2*n} * ((2*n) choose n)" by simp
  also have "card {0<..<2*n} \<le> 2*n - 1" by (cases n) simp_all
  also have "(2 * n - 1) * (2 * n choose n) + (2 * n choose n) = ((2*n) choose n) * (2*n)"
    using assms by (simp add: algebra_simps)
  finally have "4 ^ n \<le> (2 * n choose n) * (2 * n)" by simp_all
  hence "real (4 ^ n) \<le> real ((2 * n choose n) * (2 * n))"
    by (subst of_nat_le_iff)
  with assms show ?thesis by (simp add: field_simps)
qed


subsection \<open>Properties of Power Series\<close>

lemma powser_zero [simp]: "(\<Sum>n. f n * 0 ^ n) = f 0"
  for f :: "nat \<Rightarrow> 'a::real_normed_algebra_1"
proof -
  have "(\<Sum>n<1. f n * 0 ^ n) = (\<Sum>n. f n * 0 ^ n)"
    by (subst suminf_finite[where N="{0}"]) (auto simp: power_0_left)
  then show ?thesis by simp
qed

lemma powser_sums_zero: "(\<lambda>n. a n * 0^n) sums a 0"
  for a :: "nat \<Rightarrow> 'a::real_normed_div_algebra"
  using sums_finite [of "{0}" "\<lambda>n. a n * 0 ^ n"]
  by simp

lemma powser_sums_zero_iff [simp]: "(\<lambda>n. a n * 0^n) sums x \<longleftrightarrow> a 0 = x"
  for a :: "nat \<Rightarrow> 'a::real_normed_div_algebra"
  using powser_sums_zero sums_unique2 by blast

text \<open>
  Power series has a circle or radius of convergence: if it sums for \<open>x\<close>,
  then it sums absolutely for \<open>z\<close> with @{term "\<bar>z\<bar> < \<bar>x\<bar>"}.\<close>

lemma powser_insidea:
  fixes x z :: "'a::real_normed_div_algebra"
  assumes 1: "summable (\<lambda>n. f n * x^n)"
    and 2: "norm z < norm x"
  shows "summable (\<lambda>n. norm (f n * z ^ n))"
proof -
  from 2 have x_neq_0: "x \<noteq> 0" by clarsimp
  from 1 have "(\<lambda>n. f n * x^n) \<longlonglongrightarrow> 0"
    by (rule summable_LIMSEQ_zero)
  then have "convergent (\<lambda>n. f n * x^n)"
    by (rule convergentI)
  then have "Cauchy (\<lambda>n. f n * x^n)"
    by (rule convergent_Cauchy)
  then have "Bseq (\<lambda>n. f n * x^n)"
    by (rule Cauchy_Bseq)
  then obtain K where 3: "0 < K" and 4: "\<forall>n. norm (f n * x^n) \<le> K"
    by (auto simp add: Bseq_def)
  have "\<exists>N. \<forall>n\<ge>N. norm (norm (f n * z ^ n)) \<le> K * norm (z ^ n) * inverse (norm (x^n))"
  proof (intro exI allI impI)
    fix n :: nat
    assume "0 \<le> n"
    have "norm (norm (f n * z ^ n)) * norm (x^n) =
          norm (f n * x^n) * norm (z ^ n)"
      by (simp add: norm_mult abs_mult)
    also have "\<dots> \<le> K * norm (z ^ n)"
      by (simp only: mult_right_mono 4 norm_ge_zero)
    also have "\<dots> = K * norm (z ^ n) * (inverse (norm (x^n)) * norm (x^n))"
      by (simp add: x_neq_0)
    also have "\<dots> = K * norm (z ^ n) * inverse (norm (x^n)) * norm (x^n)"
      by (simp only: mult.assoc)
    finally show "norm (norm (f n * z ^ n)) \<le> K * norm (z ^ n) * inverse (norm (x^n))"
      by (simp add: mult_le_cancel_right x_neq_0)
  qed
  moreover have "summable (\<lambda>n. K * norm (z ^ n) * inverse (norm (x^n)))"
  proof -
    from 2 have "norm (norm (z * inverse x)) < 1"
      using x_neq_0
      by (simp add: norm_mult nonzero_norm_inverse divide_inverse [where 'a=real, symmetric])
    then have "summable (\<lambda>n. norm (z * inverse x) ^ n)"
      by (rule summable_geometric)
    then have "summable (\<lambda>n. K * norm (z * inverse x) ^ n)"
      by (rule summable_mult)
    then show "summable (\<lambda>n. K * norm (z ^ n) * inverse (norm (x^n)))"
      using x_neq_0
      by (simp add: norm_mult nonzero_norm_inverse power_mult_distrib
          power_inverse norm_power mult.assoc)
  qed
  ultimately show "summable (\<lambda>n. norm (f n * z ^ n))"
    by (rule summable_comparison_test)
qed

lemma powser_inside:
  fixes f :: "nat \<Rightarrow> 'a::{real_normed_div_algebra,banach}"
  shows
    "summable (\<lambda>n. f n * (x^n)) \<Longrightarrow> norm z < norm x \<Longrightarrow>
      summable (\<lambda>n. f n * (z ^ n))"
  by (rule powser_insidea [THEN summable_norm_cancel])

lemma powser_times_n_limit_0:
  fixes x :: "'a::{real_normed_div_algebra,banach}"
  assumes "norm x < 1"
    shows "(\<lambda>n. of_nat n * x ^ n) \<longlonglongrightarrow> 0"
proof -
  have "norm x / (1 - norm x) \<ge> 0"
    using assms by (auto simp: divide_simps)
  moreover obtain N where N: "norm x / (1 - norm x) < of_int N"
    using ex_le_of_int by (meson ex_less_of_int)
  ultimately have N0: "N>0"
    by auto
  then have *: "real_of_int (N + 1) * norm x / real_of_int N < 1"
    using N assms by (auto simp: field_simps)
  have **: "real_of_int N * (norm x * (real_of_nat (Suc n) * norm (x ^ n))) \<le>
      real_of_nat n * (norm x * ((1 + N) * norm (x ^ n)))" if "N \<le> int n" for n :: nat
  proof -
    from that have "real_of_int N * real_of_nat (Suc n) \<le> real_of_nat n * real_of_int (1 + N)"
      by (simp add: algebra_simps)
    then have "(real_of_int N * real_of_nat (Suc n)) * (norm x * norm (x ^ n)) \<le>
        (real_of_nat n *  (1 + N)) * (norm x * norm (x ^ n))"
      using N0 mult_mono by fastforce
    then show ?thesis
      by (simp add: algebra_simps)
  qed
  show ?thesis using *
    by (rule summable_LIMSEQ_zero [OF summable_ratio_test, where N1="nat N"])
      (simp add: N0 norm_mult field_simps ** del: of_nat_Suc of_int_add)
qed

corollary lim_n_over_pown:
  fixes x :: "'a::{real_normed_field,banach}"
  shows "1 < norm x \<Longrightarrow> ((\<lambda>n. of_nat n / x^n) \<longlongrightarrow> 0) sequentially"
  using powser_times_n_limit_0 [of "inverse x"]
  by (simp add: norm_divide divide_simps)

lemma sum_split_even_odd:
  fixes f :: "nat \<Rightarrow> real"
  shows "(\<Sum>i<2 * n. if even i then f i else g i) = (\<Sum>i<n. f (2 * i)) + (\<Sum>i<n. g (2 * i + 1))"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have "(\<Sum>i<2 * Suc n. if even i then f i else g i) =
    (\<Sum>i<n. f (2 * i)) + (\<Sum>i<n. g (2 * i + 1)) + (f (2 * n) + g (2 * n + 1))"
    using Suc.hyps unfolding One_nat_def by auto
  also have "\<dots> = (\<Sum>i<Suc n. f (2 * i)) + (\<Sum>i<Suc n. g (2 * i + 1))"
    by auto
  finally show ?case .
qed

lemma sums_if':
  fixes g :: "nat \<Rightarrow> real"
  assumes "g sums x"
  shows "(\<lambda> n. if even n then 0 else g ((n - 1) div 2)) sums x"
  unfolding sums_def
proof (rule LIMSEQ_I)
  fix r :: real
  assume "0 < r"
  from \<open>g sums x\<close>[unfolded sums_def, THEN LIMSEQ_D, OF this]
  obtain no where no_eq: "\<And>n. n \<ge> no \<Longrightarrow> (norm (sum g {..<n} - x) < r)"
    by blast

  let ?SUM = "\<lambda> m. \<Sum>i<m. if even i then 0 else g ((i - 1) div 2)"
  have "(norm (?SUM m - x) < r)" if "m \<ge> 2 * no" for m
  proof -
    from that have "m div 2 \<ge> no" by auto
    have sum_eq: "?SUM (2 * (m div 2)) = sum g {..< m div 2}"
      using sum_split_even_odd by auto
    then have "(norm (?SUM (2 * (m div 2)) - x) < r)"
      using no_eq unfolding sum_eq using \<open>m div 2 \<ge> no\<close> by auto
    moreover
    have "?SUM (2 * (m div 2)) = ?SUM m"
    proof (cases "even m")
      case True
      then show ?thesis
        by (auto simp add: even_two_times_div_two)
    next
      case False
      then have eq: "Suc (2 * (m div 2)) = m" by simp
      then have "even (2 * (m div 2))" using \<open>odd m\<close> by auto
      have "?SUM m = ?SUM (Suc (2 * (m div 2)))" unfolding eq ..
      also have "\<dots> = ?SUM (2 * (m div 2))" using \<open>even (2 * (m div 2))\<close> by auto
      finally show ?thesis by auto
    qed
    ultimately show ?thesis by auto
  qed
  then show "\<exists>no. \<forall> m \<ge> no. norm (?SUM m - x) < r"
    by blast
qed

lemma sums_if:
  fixes g :: "nat \<Rightarrow> real"
  assumes "g sums x" and "f sums y"
  shows "(\<lambda> n. if even n then f (n div 2) else g ((n - 1) div 2)) sums (x + y)"
proof -
  let ?s = "\<lambda> n. if even n then 0 else f ((n - 1) div 2)"
  have if_sum: "(if B then (0 :: real) else E) + (if B then T else 0) = (if B then T else E)"
    for B T E
    by (cases B) auto
  have g_sums: "(\<lambda> n. if even n then 0 else g ((n - 1) div 2)) sums x"
    using sums_if'[OF \<open>g sums x\<close>] .
  have if_eq: "\<And>B T E. (if \<not> B then T else E) = (if B then E else T)"
    by auto
  have "?s sums y" using sums_if'[OF \<open>f sums y\<close>] .
  from this[unfolded sums_def, THEN LIMSEQ_Suc]
  have "(\<lambda>n. if even n then f (n div 2) else 0) sums y"
    by (simp add: lessThan_Suc_eq_insert_0 sum_atLeast1_atMost_eq image_Suc_lessThan
        if_eq sums_def cong del: if_weak_cong)
  from sums_add[OF g_sums this] show ?thesis
    by (simp only: if_sum)
qed

subsection \<open>Alternating series test / Leibniz formula\<close>
(* FIXME: generalise these results from the reals via type classes? *)

lemma sums_alternating_upper_lower:
  fixes a :: "nat \<Rightarrow> real"
  assumes mono: "\<And>n. a (Suc n) \<le> a n"
    and a_pos: "\<And>n. 0 \<le> a n"
    and "a \<longlonglongrightarrow> 0"
  shows "\<exists>l. ((\<forall>n. (\<Sum>i<2*n. (- 1)^i*a i) \<le> l) \<and> (\<lambda> n. \<Sum>i<2*n. (- 1)^i*a i) \<longlonglongrightarrow> l) \<and>
             ((\<forall>n. l \<le> (\<Sum>i<2*n + 1. (- 1)^i*a i)) \<and> (\<lambda> n. \<Sum>i<2*n + 1. (- 1)^i*a i) \<longlonglongrightarrow> l)"
  (is "\<exists>l. ((\<forall>n. ?f n \<le> l) \<and> _) \<and> ((\<forall>n. l \<le> ?g n) \<and> _)")
proof (rule nested_sequence_unique)
  have fg_diff: "\<And>n. ?f n - ?g n = - a (2 * n)" by auto

  show "\<forall>n. ?f n \<le> ?f (Suc n)"
  proof
    show "?f n \<le> ?f (Suc n)" for n
      using mono[of "2*n"] by auto
  qed
  show "\<forall>n. ?g (Suc n) \<le> ?g n"
  proof
    show "?g (Suc n) \<le> ?g n" for n
      using mono[of "Suc (2*n)"] by auto
  qed
  show "\<forall>n. ?f n \<le> ?g n"
  proof
    show "?f n \<le> ?g n" for n
      using fg_diff a_pos by auto
  qed
  show "(\<lambda>n. ?f n - ?g n) \<longlonglongrightarrow> 0"
    unfolding fg_diff
  proof (rule LIMSEQ_I)
    fix r :: real
    assume "0 < r"
    with \<open>a \<longlonglongrightarrow> 0\<close>[THEN LIMSEQ_D] obtain N where "\<And> n. n \<ge> N \<Longrightarrow> norm (a n - 0) < r"
      by auto
    then have "\<forall>n \<ge> N. norm (- a (2 * n) - 0) < r"
      by auto
    then show "\<exists>N. \<forall>n \<ge> N. norm (- a (2 * n) - 0) < r"
      by auto
  qed
qed

lemma summable_Leibniz':
  fixes a :: "nat \<Rightarrow> real"
  assumes a_zero: "a \<longlonglongrightarrow> 0"
    and a_pos: "\<And>n. 0 \<le> a n"
    and a_monotone: "\<And>n. a (Suc n) \<le> a n"
  shows summable: "summable (\<lambda> n. (-1)^n * a n)"
    and "\<And>n. (\<Sum>i<2*n. (-1)^i*a i) \<le> (\<Sum>i. (-1)^i*a i)"
    and "(\<lambda>n. \<Sum>i<2*n. (-1)^i*a i) \<longlonglongrightarrow> (\<Sum>i. (-1)^i*a i)"
    and "\<And>n. (\<Sum>i. (-1)^i*a i) \<le> (\<Sum>i<2*n+1. (-1)^i*a i)"
    and "(\<lambda>n. \<Sum>i<2*n+1. (-1)^i*a i) \<longlonglongrightarrow> (\<Sum>i. (-1)^i*a i)"
proof -
  let ?S = "\<lambda>n. (-1)^n * a n"
  let ?P = "\<lambda>n. \<Sum>i<n. ?S i"
  let ?f = "\<lambda>n. ?P (2 * n)"
  let ?g = "\<lambda>n. ?P (2 * n + 1)"
  obtain l :: real
    where below_l: "\<forall> n. ?f n \<le> l"
      and "?f \<longlonglongrightarrow> l"
      and above_l: "\<forall> n. l \<le> ?g n"
      and "?g \<longlonglongrightarrow> l"
    using sums_alternating_upper_lower[OF a_monotone a_pos a_zero] by blast

  let ?Sa = "\<lambda>m. \<Sum>n<m. ?S n"
  have "?Sa \<longlonglongrightarrow> l"
  proof (rule LIMSEQ_I)
    fix r :: real
    assume "0 < r"
    with \<open>?f \<longlonglongrightarrow> l\<close>[THEN LIMSEQ_D]
    obtain f_no where f: "\<And>n. n \<ge> f_no \<Longrightarrow> norm (?f n - l) < r"
      by auto
    from \<open>0 < r\<close> \<open>?g \<longlonglongrightarrow> l\<close>[THEN LIMSEQ_D]
    obtain g_no where g: "\<And>n. n \<ge> g_no \<Longrightarrow> norm (?g n - l) < r"
      by auto
    have "norm (?Sa n - l) < r" if "n \<ge> (max (2 * f_no) (2 * g_no))" for n
    proof -
      from that have "n \<ge> 2 * f_no" and "n \<ge> 2 * g_no" by auto
      show ?thesis
      proof (cases "even n")
        case True
        then have n_eq: "2 * (n div 2) = n"
          by (simp add: even_two_times_div_two)
        with \<open>n \<ge> 2 * f_no\<close> have "n div 2 \<ge> f_no"
          by auto
        from f[OF this] show ?thesis
          unfolding n_eq atLeastLessThanSuc_atLeastAtMost .
      next
        case False
        then have "even (n - 1)" by simp
        then have n_eq: "2 * ((n - 1) div 2) = n - 1"
          by (simp add: even_two_times_div_two)
        then have range_eq: "n - 1 + 1 = n"
          using odd_pos[OF False] by auto
        from n_eq \<open>n \<ge> 2 * g_no\<close> have "(n - 1) div 2 \<ge> g_no"
          by auto
        from g[OF this] show ?thesis
          by (simp only: n_eq range_eq)
      qed
    qed
    then show "\<exists>no. \<forall>n \<ge> no. norm (?Sa n - l) < r" by blast
  qed
  then have sums_l: "(\<lambda>i. (-1)^i * a i) sums l"
    by (simp only: sums_def)
  then show "summable ?S"
    by (auto simp: summable_def)

  have "l = suminf ?S" by (rule sums_unique[OF sums_l])

  fix n
  show "suminf ?S \<le> ?g n"
    unfolding sums_unique[OF sums_l, symmetric] using above_l by auto
  show "?f n \<le> suminf ?S"
    unfolding sums_unique[OF sums_l, symmetric] using below_l by auto
  show "?g \<longlonglongrightarrow> suminf ?S"
    using \<open>?g \<longlonglongrightarrow> l\<close> \<open>l = suminf ?S\<close> by auto
  show "?f \<longlonglongrightarrow> suminf ?S"
    using \<open>?f \<longlonglongrightarrow> l\<close> \<open>l = suminf ?S\<close> by auto
qed

theorem summable_Leibniz:
  fixes a :: "nat \<Rightarrow> real"
  assumes a_zero: "a \<longlonglongrightarrow> 0"
    and "monoseq a"
  shows "summable (\<lambda> n. (-1)^n * a n)" (is "?summable")
    and "0 < a 0 \<longrightarrow>
      (\<forall>n. (\<Sum>i. (- 1)^i*a i) \<in> { \<Sum>i<2*n. (- 1)^i * a i .. \<Sum>i<2*n+1. (- 1)^i * a i})" (is "?pos")
    and "a 0 < 0 \<longrightarrow>
      (\<forall>n. (\<Sum>i. (- 1)^i*a i) \<in> { \<Sum>i<2*n+1. (- 1)^i * a i .. \<Sum>i<2*n. (- 1)^i * a i})" (is "?neg")
    and "(\<lambda>n. \<Sum>i<2*n. (- 1)^i*a i) \<longlonglongrightarrow> (\<Sum>i. (- 1)^i*a i)" (is "?f")
    and "(\<lambda>n. \<Sum>i<2*n+1. (- 1)^i*a i) \<longlonglongrightarrow> (\<Sum>i. (- 1)^i*a i)" (is "?g")
proof -
  have "?summable \<and> ?pos \<and> ?neg \<and> ?f \<and> ?g"
  proof (cases "(\<forall>n. 0 \<le> a n) \<and> (\<forall>m. \<forall>n\<ge>m. a n \<le> a m)")
    case True
    then have ord: "\<And>n m. m \<le> n \<Longrightarrow> a n \<le> a m"
      and ge0: "\<And>n. 0 \<le> a n"
      by auto
    have mono: "a (Suc n) \<le> a n" for n
      using ord[where n="Suc n" and m=n] by auto
    note leibniz = summable_Leibniz'[OF \<open>a \<longlonglongrightarrow> 0\<close> ge0]
    from leibniz[OF mono]
    show ?thesis using \<open>0 \<le> a 0\<close> by auto
  next
    let ?a = "\<lambda>n. - a n"
    case False
    with monoseq_le[OF \<open>monoseq a\<close> \<open>a \<longlonglongrightarrow> 0\<close>]
    have "(\<forall> n. a n \<le> 0) \<and> (\<forall>m. \<forall>n\<ge>m. a m \<le> a n)" by auto
    then have ord: "\<And>n m. m \<le> n \<Longrightarrow> ?a n \<le> ?a m" and ge0: "\<And> n. 0 \<le> ?a n"
      by auto
    have monotone: "?a (Suc n) \<le> ?a n" for n
      using ord[where n="Suc n" and m=n] by auto
    note leibniz =
      summable_Leibniz'[OF _ ge0, of "\<lambda>x. x",
        OF tendsto_minus[OF \<open>a \<longlonglongrightarrow> 0\<close>, unfolded minus_zero] monotone]
    have "summable (\<lambda> n. (-1)^n * ?a n)"
      using leibniz(1) by auto
    then obtain l where "(\<lambda> n. (-1)^n * ?a n) sums l"
      unfolding summable_def by auto
    from this[THEN sums_minus] have "(\<lambda> n. (-1)^n * a n) sums -l"
      by auto
    then have ?summable by (auto simp: summable_def)
    moreover
    have "\<bar>- a - - b\<bar> = \<bar>a - b\<bar>" for a b :: real
      unfolding minus_diff_minus by auto

    from suminf_minus[OF leibniz(1), unfolded mult_minus_right minus_minus]
    have move_minus: "(\<Sum>n. - ((- 1) ^ n * a n)) = - (\<Sum>n. (- 1) ^ n * a n)"
      by auto

    have ?pos using \<open>0 \<le> ?a 0\<close> by auto
    moreover have ?neg
      using leibniz(2,4)
      unfolding mult_minus_right sum_negf move_minus neg_le_iff_le
      by auto
    moreover have ?f and ?g
      using leibniz(3,5)[unfolded mult_minus_right sum_negf move_minus, THEN tendsto_minus_cancel]
      by auto
    ultimately show ?thesis by auto
  qed
  then show ?summable and ?pos and ?neg and ?f and ?g
    by safe
qed


subsection \<open>Term-by-Term Differentiability of Power Series\<close>

definition diffs :: "(nat \<Rightarrow> 'a::ring_1) \<Rightarrow> nat \<Rightarrow> 'a"
  where "diffs c = (\<lambda>n. of_nat (Suc n) * c (Suc n))"

text \<open>Lemma about distributing negation over it.\<close>
lemma diffs_minus: "diffs (\<lambda>n. - c n) = (\<lambda>n. - diffs c n)"
  by (simp add: diffs_def)

lemma diffs_equiv:
  fixes x :: "'a::{real_normed_vector,ring_1}"
  shows "summable (\<lambda>n. diffs c n * x^n) \<Longrightarrow>
    (\<lambda>n. of_nat n * c n * x^(n - Suc 0)) sums (\<Sum>n. diffs c n * x^n)"
  unfolding diffs_def
  by (simp add: summable_sums sums_Suc_imp)

lemma lemma_termdiff1:
  fixes z :: "'a :: {monoid_mult,comm_ring}"
  shows "(\<Sum>p<m. (((z + h) ^ (m - p)) * (z ^ p)) - (z ^ m)) =
    (\<Sum>p<m. (z ^ p) * (((z + h) ^ (m - p)) - (z ^ (m - p))))"
  by (auto simp add: algebra_simps power_add [symmetric])

lemma sumr_diff_mult_const2: "sum f {..<n} - of_nat n * r = (\<Sum>i<n. f i - r)"
  for r :: "'a::ring_1"
  by (simp add: sum_subtractf)

lemma lemma_realpow_rev_sumr:
  "(\<Sum>p<Suc n. (x ^ p) * (y ^ (n - p))) = (\<Sum>p<Suc n. (x ^ (n - p)) * (y ^ p))"
  by (subst nat_diff_sum_reindex[symmetric]) simp

lemma lemma_termdiff2:
  fixes h :: "'a::field"
  assumes h: "h \<noteq> 0"
  shows "((z + h) ^ n - z ^ n) / h - of_nat n * z ^ (n - Suc 0) =
    h * (\<Sum>p< n - Suc 0. \<Sum>q< n - Suc 0 - p. (z + h) ^ q * z ^ (n - 2 - q))"
    (is "?lhs = ?rhs")
  apply (subgoal_tac "h * ?lhs = h * ?rhs")
   apply (simp add: h)
  apply (simp add: right_diff_distrib diff_divide_distrib h)
  apply (simp add: mult.assoc [symmetric])
  apply (cases n)
  apply simp
  apply (simp add: diff_power_eq_sum h right_diff_distrib [symmetric] mult.assoc
      del: power_Suc sum_lessThan_Suc of_nat_Suc)
  apply (subst lemma_realpow_rev_sumr)
  apply (subst sumr_diff_mult_const2)
  apply simp
  apply (simp only: lemma_termdiff1 sum_distrib_left)
  apply (rule sum.cong [OF refl])
  apply (simp add: less_iff_Suc_add)
  apply clarify
  apply (simp add: sum_distrib_left diff_power_eq_sum ac_simps
      del: sum_lessThan_Suc power_Suc)
  apply (subst mult.assoc [symmetric], subst power_add [symmetric])
  apply (simp add: ac_simps)
  done

lemma real_sum_nat_ivl_bounded2:
  fixes K :: "'a::linordered_semidom"
  assumes f: "\<And>p::nat. p < n \<Longrightarrow> f p \<le> K"
    and K: "0 \<le> K"
  shows "sum f {..<n-k} \<le> of_nat n * K"
  apply (rule order_trans [OF sum_mono])
   apply (rule f)
   apply simp
  apply (simp add: mult_right_mono K)
  done

lemma lemma_termdiff3:
  fixes h z :: "'a::real_normed_field"
  assumes 1: "h \<noteq> 0"
    and 2: "norm z \<le> K"
    and 3: "norm (z + h) \<le> K"
  shows "norm (((z + h) ^ n - z ^ n) / h - of_nat n * z ^ (n - Suc 0)) \<le>
    of_nat n * of_nat (n - Suc 0) * K ^ (n - 2) * norm h"
proof -
  have "norm (((z + h) ^ n - z ^ n) / h - of_nat n * z ^ (n - Suc 0)) =
    norm (\<Sum>p<n - Suc 0. \<Sum>q<n - Suc 0 - p. (z + h) ^ q * z ^ (n - 2 - q)) * norm h"
    by (metis (lifting, no_types) lemma_termdiff2 [OF 1] mult.commute norm_mult)
  also have "\<dots> \<le> of_nat n * (of_nat (n - Suc 0) * K ^ (n - 2)) * norm h"
  proof (rule mult_right_mono [OF _ norm_ge_zero])
    from norm_ge_zero 2 have K: "0 \<le> K"
      by (rule order_trans)
    have le_Kn: "\<And>i j n. i + j = n \<Longrightarrow> norm ((z + h) ^ i * z ^ j) \<le> K ^ n"
      apply (erule subst)
      apply (simp only: norm_mult norm_power power_add)
      apply (intro mult_mono power_mono 2 3 norm_ge_zero zero_le_power K)
      done
    show "norm (\<Sum>p<n - Suc 0. \<Sum>q<n - Suc 0 - p. (z + h) ^ q * z ^ (n - 2 - q)) \<le>
        of_nat n * (of_nat (n - Suc 0) * K ^ (n - 2))"
      apply (intro
          order_trans [OF norm_sum]
          real_sum_nat_ivl_bounded2
          mult_nonneg_nonneg
          of_nat_0_le_iff
          zero_le_power K)
      apply (rule le_Kn)
      apply simp
      done
  qed
  also have "\<dots> = of_nat n * of_nat (n - Suc 0) * K ^ (n - 2) * norm h"
    by (simp only: mult.assoc)
  finally show ?thesis .
qed

lemma lemma_termdiff4:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
    and k :: real
  assumes k: "0 < k"
    and le: "\<And>h. h \<noteq> 0 \<Longrightarrow> norm h < k \<Longrightarrow> norm (f h) \<le> K * norm h"
  shows "f \<midarrow>0\<rightarrow> 0"
proof (rule tendsto_norm_zero_cancel)
  show "(\<lambda>h. norm (f h)) \<midarrow>0\<rightarrow> 0"
  proof (rule real_tendsto_sandwich)
    show "eventually (\<lambda>h. 0 \<le> norm (f h)) (at 0)"
      by simp
    show "eventually (\<lambda>h. norm (f h) \<le> K * norm h) (at 0)"
      using k by (auto simp add: eventually_at dist_norm le)
    show "(\<lambda>h. 0) \<midarrow>(0::'a)\<rightarrow> (0::real)"
      by (rule tendsto_const)
    have "(\<lambda>h. K * norm h) \<midarrow>(0::'a)\<rightarrow> K * norm (0::'a)"
      by (intro tendsto_intros)
    then show "(\<lambda>h. K * norm h) \<midarrow>(0::'a)\<rightarrow> 0"
      by simp
  qed
qed

lemma lemma_termdiff5:
  fixes g :: "'a::real_normed_vector \<Rightarrow> nat \<Rightarrow> 'b::banach"
    and k :: real
  assumes k: "0 < k"
    and f: "summable f"
    and le: "\<And>h n. h \<noteq> 0 \<Longrightarrow> norm h < k \<Longrightarrow> norm (g h n) \<le> f n * norm h"
  shows "(\<lambda>h. suminf (g h)) \<midarrow>0\<rightarrow> 0"
proof (rule lemma_termdiff4 [OF k])
  fix h :: 'a
  assume "h \<noteq> 0" and "norm h < k"
  then have 1: "\<forall>n. norm (g h n) \<le> f n * norm h"
    by (simp add: le)
  then have "\<exists>N. \<forall>n\<ge>N. norm (norm (g h n)) \<le> f n * norm h"
    by simp
  moreover from f have 2: "summable (\<lambda>n. f n * norm h)"
    by (rule summable_mult2)
  ultimately have 3: "summable (\<lambda>n. norm (g h n))"
    by (rule summable_comparison_test)
  then have "norm (suminf (g h)) \<le> (\<Sum>n. norm (g h n))"
    by (rule summable_norm)
  also from 1 3 2 have "(\<Sum>n. norm (g h n)) \<le> (\<Sum>n. f n * norm h)"
    by (rule suminf_le)
  also from f have "(\<Sum>n. f n * norm h) = suminf f * norm h"
    by (rule suminf_mult2 [symmetric])
  finally show "norm (suminf (g h)) \<le> suminf f * norm h" .
qed


(* FIXME: Long proofs *)

lemma termdiffs_aux:
  fixes x :: "'a::{real_normed_field,banach}"
  assumes 1: "summable (\<lambda>n. diffs (diffs c) n * K ^ n)"
    and 2: "norm x < norm K"
  shows "(\<lambda>h. \<Sum>n. c n * (((x + h) ^ n - x^n) / h - of_nat n * x ^ (n - Suc 0))) \<midarrow>0\<rightarrow> 0"
proof -
  from dense [OF 2] obtain r where r1: "norm x < r" and r2: "r < norm K"
    by fast
  from norm_ge_zero r1 have r: "0 < r"
    by (rule order_le_less_trans)
  then have r_neq_0: "r \<noteq> 0" by simp
  show ?thesis
  proof (rule lemma_termdiff5)
    show "0 < r - norm x"
      using r1 by simp
    from r r2 have "norm (of_real r::'a) < norm K"
      by simp
    with 1 have "summable (\<lambda>n. norm (diffs (diffs c) n * (of_real r ^ n)))"
      by (rule powser_insidea)
    then have "summable (\<lambda>n. diffs (diffs (\<lambda>n. norm (c n))) n * r ^ n)"
      using r by (simp add: diffs_def norm_mult norm_power del: of_nat_Suc)
    then have "summable (\<lambda>n. of_nat n * diffs (\<lambda>n. norm (c n)) n * r ^ (n - Suc 0))"
      by (rule diffs_equiv [THEN sums_summable])
    also have "(\<lambda>n. of_nat n * diffs (\<lambda>n. norm (c n)) n * r ^ (n - Suc 0)) =
      (\<lambda>n. diffs (\<lambda>m. of_nat (m - Suc 0) * norm (c m) * inverse r) n * (r ^ n))"
      apply (rule ext)
      apply (simp add: diffs_def)
      apply (case_tac n)
       apply (simp_all add: r_neq_0)
      done
    finally have "summable
      (\<lambda>n. of_nat n * (of_nat (n - Suc 0) * norm (c n) * inverse r) * r ^ (n - Suc 0))"
      by (rule diffs_equiv [THEN sums_summable])
    also have
      "(\<lambda>n. of_nat n * (of_nat (n - Suc 0) * norm (c n) * inverse r) * r ^ (n - Suc 0)) =
       (\<lambda>n. norm (c n) * of_nat n * of_nat (n - Suc 0) * r ^ (n - 2))"
      apply (rule ext)
      apply (case_tac n)
       apply simp
      apply (rename_tac nat)
      apply (case_tac nat)
       apply simp
      apply (simp add: r_neq_0)
      done
    finally show "summable (\<lambda>n. norm (c n) * of_nat n * of_nat (n - Suc 0) * r ^ (n - 2))" .
  next
    fix h :: 'a
    fix n :: nat
    assume h: "h \<noteq> 0"
    assume "norm h < r - norm x"
    then have "norm x + norm h < r" by simp
    with norm_triangle_ineq have xh: "norm (x + h) < r"
      by (rule order_le_less_trans)
    show "norm (c n * (((x + h) ^ n - x^n) / h - of_nat n * x ^ (n - Suc 0))) \<le>
      norm (c n) * of_nat n * of_nat (n - Suc 0) * r ^ (n - 2) * norm h"
      apply (simp only: norm_mult mult.assoc)
      apply (rule mult_left_mono [OF _ norm_ge_zero])
      apply (simp add: mult.assoc [symmetric])
      apply (metis h lemma_termdiff3 less_eq_real_def r1 xh)
      done
  qed
qed

lemma termdiffs:
  fixes K x :: "'a::{real_normed_field,banach}"
  assumes 1: "summable (\<lambda>n. c n * K ^ n)"
    and 2: "summable (\<lambda>n. (diffs c) n * K ^ n)"
    and 3: "summable (\<lambda>n. (diffs (diffs c)) n * K ^ n)"
    and 4: "norm x < norm K"
  shows "DERIV (\<lambda>x. \<Sum>n. c n * x^n) x :> (\<Sum>n. (diffs c) n * x^n)"
  unfolding DERIV_def
proof (rule LIM_zero_cancel)
  show "(\<lambda>h. (suminf (\<lambda>n. c n * (x + h) ^ n) - suminf (\<lambda>n. c n * x^n)) / h
            - suminf (\<lambda>n. diffs c n * x^n)) \<midarrow>0\<rightarrow> 0"
  proof (rule LIM_equal2)
    show "0 < norm K - norm x"
      using 4 by (simp add: less_diff_eq)
  next
    fix h :: 'a
    assume "norm (h - 0) < norm K - norm x"
    then have "norm x + norm h < norm K" by simp
    then have 5: "norm (x + h) < norm K"
      by (rule norm_triangle_ineq [THEN order_le_less_trans])
    have "summable (\<lambda>n. c n * x^n)"
      and "summable (\<lambda>n. c n * (x + h) ^ n)"
      and "summable (\<lambda>n. diffs c n * x^n)"
      using 1 2 4 5 by (auto elim: powser_inside)
    then have "((\<Sum>n. c n * (x + h) ^ n) - (\<Sum>n. c n * x^n)) / h - (\<Sum>n. diffs c n * x^n) =
          (\<Sum>n. (c n * (x + h) ^ n - c n * x^n) / h - of_nat n * c n * x ^ (n - Suc 0))"
      by (intro sums_unique sums_diff sums_divide diffs_equiv summable_sums)
    then show "((\<Sum>n. c n * (x + h) ^ n) - (\<Sum>n. c n * x^n)) / h - (\<Sum>n. diffs c n * x^n) =
          (\<Sum>n. c n * (((x + h) ^ n - x^n) / h - of_nat n * x ^ (n - Suc 0)))"
      by (simp add: algebra_simps)
  next
    show "(\<lambda>h. \<Sum>n. c n * (((x + h) ^ n - x^n) / h - of_nat n * x ^ (n - Suc 0))) \<midarrow>0\<rightarrow> 0"
      by (rule termdiffs_aux [OF 3 4])
  qed
qed

subsection \<open>The Derivative of a Power Series Has the Same Radius of Convergence\<close>

lemma termdiff_converges:
  fixes x :: "'a::{real_normed_field,banach}"
  assumes K: "norm x < K"
    and sm: "\<And>x. norm x < K \<Longrightarrow> summable(\<lambda>n. c n * x ^ n)"
  shows "summable (\<lambda>n. diffs c n * x ^ n)"
proof (cases "x = 0")
  case True
  then show ?thesis
    using powser_sums_zero sums_summable by auto
next
  case False
  then have "K > 0"
    using K less_trans zero_less_norm_iff by blast
  then obtain r :: real where r: "norm x < norm r" "norm r < K" "r > 0"
    using K False
    by (auto simp: field_simps abs_less_iff add_pos_pos intro: that [of "(norm x + K) / 2"])
  have "(\<lambda>n. of_nat n * (x / of_real r) ^ n) \<longlonglongrightarrow> 0"
    using r by (simp add: norm_divide powser_times_n_limit_0 [of "x / of_real r"])
  then obtain N where N: "\<And>n. n\<ge>N \<Longrightarrow> real_of_nat n * norm x ^ n < r ^ n"
    using r unfolding LIMSEQ_iff
    apply (drule_tac x=1 in spec)
    apply (auto simp: norm_divide norm_mult norm_power field_simps)
    done
  have "summable (\<lambda>n. (of_nat n * c n) * x ^ n)"
    apply (rule summable_comparison_test' [of "\<lambda>n. norm(c n * (of_real r) ^ n)" N])
     apply (rule powser_insidea [OF sm [of "of_real ((r+K)/2)"]])
    using N r norm_of_real [of "r + K", where 'a = 'a]
      apply (auto simp add: norm_divide norm_mult norm_power field_simps)
    apply (fastforce simp: less_eq_real_def)
    done
  then have "summable (\<lambda>n. (of_nat (Suc n) * c(Suc n)) * x ^ Suc n)"
    using summable_iff_shift [of "\<lambda>n. of_nat n * c n * x ^ n" 1]
    by simp
  then have "summable (\<lambda>n. (of_nat (Suc n) * c(Suc n)) * x ^ n)"
    using False summable_mult2 [of "\<lambda>n. (of_nat (Suc n) * c(Suc n) * x ^ n) * x" "inverse x"]
    by (simp add: mult.assoc) (auto simp: ac_simps)
  then show ?thesis
    by (simp add: diffs_def)
qed

lemma termdiff_converges_all:
  fixes x :: "'a::{real_normed_field,banach}"
  assumes "\<And>x. summable (\<lambda>n. c n * x^n)"
  shows "summable (\<lambda>n. diffs c n * x^n)"
  apply (rule termdiff_converges [where K = "1 + norm x"])
  using assms
   apply auto
  done

lemma termdiffs_strong:
  fixes K x :: "'a::{real_normed_field,banach}"
  assumes sm: "summable (\<lambda>n. c n * K ^ n)"
    and K: "norm x < norm K"
  shows "DERIV (\<lambda>x. \<Sum>n. c n * x^n) x :> (\<Sum>n. diffs c n * x^n)"
proof -
  have K2: "norm ((of_real (norm K) + of_real (norm x)) / 2 :: 'a) < norm K"
    using K
    apply (auto simp: norm_divide field_simps)
    apply (rule le_less_trans [of _ "of_real (norm K) + of_real (norm x)"])
     apply (auto simp: mult_2_right norm_triangle_mono)
    done
  then have [simp]: "norm ((of_real (norm K) + of_real (norm x)) :: 'a) < norm K * 2"
    by simp
  have "summable (\<lambda>n. c n * (of_real (norm x + norm K) / 2) ^ n)"
    by (metis K2 summable_norm_cancel [OF powser_insidea [OF sm]] add.commute of_real_add)
  moreover have "\<And>x. norm x < norm K \<Longrightarrow> summable (\<lambda>n. diffs c n * x ^ n)"
    by (blast intro: sm termdiff_converges powser_inside)
  moreover have "\<And>x. norm x < norm K \<Longrightarrow> summable (\<lambda>n. diffs(diffs c) n * x ^ n)"
    by (blast intro: sm termdiff_converges powser_inside)
  ultimately show ?thesis
    apply (rule termdiffs [where K = "of_real (norm x + norm K) / 2"])
      apply (auto simp: field_simps)
    using K
    apply (simp_all add: of_real_add [symmetric] del: of_real_add)
    done
qed

lemma termdiffs_strong_converges_everywhere:
  fixes K x :: "'a::{real_normed_field,banach}"
  assumes "\<And>y. summable (\<lambda>n. c n * y ^ n)"
  shows "((\<lambda>x. \<Sum>n. c n * x^n) has_field_derivative (\<Sum>n. diffs c n * x^n)) (at x)"
  using termdiffs_strong[OF assms[of "of_real (norm x + 1)"], of x]
  by (force simp del: of_real_add)

lemma termdiffs_strong':
  fixes z :: "'a :: {real_normed_field,banach}"
  assumes "\<And>z. norm z < K \<Longrightarrow> summable (\<lambda>n. c n * z ^ n)"
  assumes "norm z < K"
  shows   "((\<lambda>z. \<Sum>n. c n * z^n) has_field_derivative (\<Sum>n. diffs c n * z^n)) (at z)"
proof (rule termdiffs_strong)
  define L :: real where "L =  (norm z + K) / 2"
  have "0 \<le> norm z" by simp
  also note \<open>norm z < K\<close>
  finally have K: "K \<ge> 0" by simp
  from assms K have L: "L \<ge> 0" "norm z < L" "L < K" by (simp_all add: L_def)
  from L show "norm z < norm (of_real L :: 'a)" by simp
  from L show "summable (\<lambda>n. c n * of_real L ^ n)" by (intro assms(1)) simp_all
qed

lemma termdiffs_sums_strong:
  fixes z :: "'a :: {banach,real_normed_field}"
  assumes sums: "\<And>z. norm z < K \<Longrightarrow> (\<lambda>n. c n * z ^ n) sums f z"
  assumes deriv: "(f has_field_derivative f') (at z)"
  assumes norm: "norm z < K"
  shows   "(\<lambda>n. diffs c n * z ^ n) sums f'"
proof -
  have summable: "summable (\<lambda>n. diffs c n * z^n)"
    by (intro termdiff_converges[OF norm] sums_summable[OF sums])
  from norm have "eventually (\<lambda>z. z \<in> norm -` {..<K}) (nhds z)"
    by (intro eventually_nhds_in_open open_vimage) 
       (simp_all add: continuous_on_norm continuous_on_id)
  hence eq: "eventually (\<lambda>z. (\<Sum>n. c n * z^n) = f z) (nhds z)"
    by eventually_elim (insert sums, simp add: sums_iff)

  have "((\<lambda>z. \<Sum>n. c n * z^n) has_field_derivative (\<Sum>n. diffs c n * z^n)) (at z)"
    by (intro termdiffs_strong'[OF _ norm] sums_summable[OF sums])
  hence "(f has_field_derivative (\<Sum>n. diffs c n * z^n)) (at z)"
    by (subst (asm) DERIV_cong_ev[OF refl eq refl])
  from this and deriv have "(\<Sum>n. diffs c n * z^n) = f'" by (rule DERIV_unique)
  with summable show ?thesis by (simp add: sums_iff)
qed

lemma isCont_powser:
  fixes K x :: "'a::{real_normed_field,banach}"
  assumes "summable (\<lambda>n. c n * K ^ n)"
  assumes "norm x < norm K"
  shows "isCont (\<lambda>x. \<Sum>n. c n * x^n) x"
  using termdiffs_strong[OF assms] by (blast intro!: DERIV_isCont)

lemmas isCont_powser' = isCont_o2[OF _ isCont_powser]

lemma isCont_powser_converges_everywhere:
  fixes K x :: "'a::{real_normed_field,banach}"
  assumes "\<And>y. summable (\<lambda>n. c n * y ^ n)"
  shows "isCont (\<lambda>x. \<Sum>n. c n * x^n) x"
  using termdiffs_strong[OF assms[of "of_real (norm x + 1)"], of x]
  by (force intro!: DERIV_isCont simp del: of_real_add)

lemma powser_limit_0:
  fixes a :: "nat \<Rightarrow> 'a::{real_normed_field,banach}"
  assumes s: "0 < s"
    and sm: "\<And>x. norm x < s \<Longrightarrow> (\<lambda>n. a n * x ^ n) sums (f x)"
  shows "(f \<longlongrightarrow> a 0) (at 0)"
proof -
  have "summable (\<lambda>n. a n * (of_real s / 2) ^ n)"
    apply (rule sums_summable [where l = "f (of_real s / 2)", OF sm])
    using s
    apply (auto simp: norm_divide)
    done
  then have "((\<lambda>x. \<Sum>n. a n * x ^ n) has_field_derivative (\<Sum>n. diffs a n * 0 ^ n)) (at 0)"
    apply (rule termdiffs_strong)
    using s
    apply (auto simp: norm_divide)
    done
  then have "isCont (\<lambda>x. \<Sum>n. a n * x ^ n) 0"
    by (blast intro: DERIV_continuous)
  then have "((\<lambda>x. \<Sum>n. a n * x ^ n) \<longlongrightarrow> a 0) (at 0)"
    by (simp add: continuous_within)
  then show ?thesis
    apply (rule Lim_transform)
    apply (auto simp add: LIM_eq)
    apply (rule_tac x="s" in exI)
    using s
    apply (auto simp: sm [THEN sums_unique])
    done
qed

lemma powser_limit_0_strong:
  fixes a :: "nat \<Rightarrow> 'a::{real_normed_field,banach}"
  assumes s: "0 < s"
    and sm: "\<And>x. x \<noteq> 0 \<Longrightarrow> norm x < s \<Longrightarrow> (\<lambda>n. a n * x ^ n) sums (f x)"
  shows "(f \<longlongrightarrow> a 0) (at 0)"
proof -
  have *: "((\<lambda>x. if x = 0 then a 0 else f x) \<longlongrightarrow> a 0) (at 0)"
    apply (rule powser_limit_0 [OF s])
    apply (case_tac "x = 0")
     apply (auto simp add: powser_sums_zero sm)
    done
  show ?thesis
    apply (subst LIM_equal [where g = "(\<lambda>x. if x = 0 then a 0 else f x)"])
     apply (simp_all add: *)
    done
qed


subsection \<open>Derivability of power series\<close>

lemma DERIV_series':
  fixes f :: "real \<Rightarrow> nat \<Rightarrow> real"
  assumes DERIV_f: "\<And> n. DERIV (\<lambda> x. f x n) x0 :> (f' x0 n)"
    and allf_summable: "\<And> x. x \<in> {a <..< b} \<Longrightarrow> summable (f x)"
    and x0_in_I: "x0 \<in> {a <..< b}"
    and "summable (f' x0)"
    and "summable L"
    and L_def: "\<And>n x y. x \<in> {a <..< b} \<Longrightarrow> y \<in> {a <..< b} \<Longrightarrow> \<bar>f x n - f y n\<bar> \<le> L n * \<bar>x - y\<bar>"
  shows "DERIV (\<lambda> x. suminf (f x)) x0 :> (suminf (f' x0))"
  unfolding DERIV_def
proof (rule LIM_I)
  fix r :: real
  assume "0 < r" then have "0 < r/3" by auto

  obtain N_L where N_L: "\<And> n. N_L \<le> n \<Longrightarrow> \<bar> \<Sum> i. L (i + n) \<bar> < r/3"
    using suminf_exist_split[OF \<open>0 < r/3\<close> \<open>summable L\<close>] by auto

  obtain N_f' where N_f': "\<And> n. N_f' \<le> n \<Longrightarrow> \<bar> \<Sum> i. f' x0 (i + n) \<bar> < r/3"
    using suminf_exist_split[OF \<open>0 < r/3\<close> \<open>summable (f' x0)\<close>] by auto

  let ?N = "Suc (max N_L N_f')"
  have "\<bar> \<Sum> i. f' x0 (i + ?N) \<bar> < r/3" (is "?f'_part < r/3")
    and L_estimate: "\<bar> \<Sum> i. L (i + ?N) \<bar> < r/3"
    using N_L[of "?N"] and N_f' [of "?N"] by auto

  let ?diff = "\<lambda>i x. (f (x0 + x) i - f x0 i) / x"

  let ?r = "r / (3 * real ?N)"
  from \<open>0 < r\<close> have "0 < ?r" by simp

  let ?s = "\<lambda>n. SOME s. 0 < s \<and> (\<forall> x. x \<noteq> 0 \<and> \<bar> x \<bar> < s \<longrightarrow> \<bar> ?diff n x - f' x0 n \<bar> < ?r)"
  define S' where "S' = Min (?s ` {..< ?N })"

  have "0 < S'"
    unfolding S'_def
  proof (rule iffD2[OF Min_gr_iff])
    show "\<forall>x \<in> (?s ` {..< ?N }). 0 < x"
    proof
      fix x
      assume "x \<in> ?s ` {..<?N}"
      then obtain n where "x = ?s n" and "n \<in> {..<?N}"
        using image_iff[THEN iffD1] by blast
      from DERIV_D[OF DERIV_f[where n=n], THEN LIM_D, OF \<open>0 < ?r\<close>, unfolded real_norm_def]
      obtain s where s_bound: "0 < s \<and> (\<forall>x. x \<noteq> 0 \<and> \<bar>x\<bar> < s \<longrightarrow> \<bar>?diff n x - f' x0 n\<bar> < ?r)"
        by auto
      have "0 < ?s n"
        by (rule someI2[where a=s]) (auto simp add: s_bound simp del: of_nat_Suc)
      then show "0 < x" by (simp only: \<open>x = ?s n\<close>)
    qed
  qed auto

  define S where "S = min (min (x0 - a) (b - x0)) S'"
  then have "0 < S" and S_a: "S \<le> x0 - a" and S_b: "S \<le> b - x0"
    and "S \<le> S'" using x0_in_I and \<open>0 < S'\<close>
    by auto

  have "\<bar>(suminf (f (x0 + x)) - suminf (f x0)) / x - suminf (f' x0)\<bar> < r"
    if "x \<noteq> 0" and "\<bar>x\<bar> < S" for x
  proof -
    from that have x_in_I: "x0 + x \<in> {a <..< b}"
      using S_a S_b by auto

    note diff_smbl = summable_diff[OF allf_summable[OF x_in_I] allf_summable[OF x0_in_I]]
    note div_smbl = summable_divide[OF diff_smbl]
    note all_smbl = summable_diff[OF div_smbl \<open>summable (f' x0)\<close>]
    note ign = summable_ignore_initial_segment[where k="?N"]
    note diff_shft_smbl = summable_diff[OF ign[OF allf_summable[OF x_in_I]] ign[OF allf_summable[OF x0_in_I]]]
    note div_shft_smbl = summable_divide[OF diff_shft_smbl]
    note all_shft_smbl = summable_diff[OF div_smbl ign[OF \<open>summable (f' x0)\<close>]]

    have 1: "\<bar>(\<bar>?diff (n + ?N) x\<bar>)\<bar> \<le> L (n + ?N)" for n
    proof -
      have "\<bar>?diff (n + ?N) x\<bar> \<le> L (n + ?N) * \<bar>(x0 + x) - x0\<bar> / \<bar>x\<bar>"
        using divide_right_mono[OF L_def[OF x_in_I x0_in_I] abs_ge_zero]
        by (simp only: abs_divide)
      with \<open>x \<noteq> 0\<close> show ?thesis by auto
    qed
    note 2 = summable_rabs_comparison_test[OF _ ign[OF \<open>summable L\<close>]]
    from 1 have "\<bar> \<Sum> i. ?diff (i + ?N) x \<bar> \<le> (\<Sum> i. L (i + ?N))"
      by (metis (lifting) abs_idempotent
          order_trans[OF summable_rabs[OF 2] suminf_le[OF _ 2 ign[OF \<open>summable L\<close>]]])
    then have "\<bar>\<Sum>i. ?diff (i + ?N) x\<bar> \<le> r / 3" (is "?L_part \<le> r/3")
      using L_estimate by auto

    have "\<bar>\<Sum>n<?N. ?diff n x - f' x0 n\<bar> \<le> (\<Sum>n<?N. \<bar>?diff n x - f' x0 n\<bar>)" ..
    also have "\<dots> < (\<Sum>n<?N. ?r)"
    proof (rule sum_strict_mono)
      fix n
      assume "n \<in> {..< ?N}"
      have "\<bar>x\<bar> < S" using \<open>\<bar>x\<bar> < S\<close> .
      also have "S \<le> S'" using \<open>S \<le> S'\<close> .
      also have "S' \<le> ?s n"
        unfolding S'_def
      proof (rule Min_le_iff[THEN iffD2])
        have "?s n \<in> (?s ` {..<?N}) \<and> ?s n \<le> ?s n"
          using \<open>n \<in> {..< ?N}\<close> by auto
        then show "\<exists> a \<in> (?s ` {..<?N}). a \<le> ?s n"
          by blast
      qed auto
      finally have "\<bar>x\<bar> < ?s n" .

      from DERIV_D[OF DERIV_f[where n=n], THEN LIM_D, OF \<open>0 < ?r\<close>,
          unfolded real_norm_def diff_0_right, unfolded some_eq_ex[symmetric], THEN conjunct2]
      have "\<forall>x. x \<noteq> 0 \<and> \<bar>x\<bar> < ?s n \<longrightarrow> \<bar>?diff n x - f' x0 n\<bar> < ?r" .
      with \<open>x \<noteq> 0\<close> and \<open>\<bar>x\<bar> < ?s n\<close> show "\<bar>?diff n x - f' x0 n\<bar> < ?r"
        by blast
    qed auto
    also have "\<dots> = of_nat (card {..<?N}) * ?r"
      by (rule sum_constant)
    also have "\<dots> = real ?N * ?r"
      by simp
    also have "\<dots> = r/3"
      by (auto simp del: of_nat_Suc)
    finally have "\<bar>\<Sum>n<?N. ?diff n x - f' x0 n \<bar> < r / 3" (is "?diff_part < r / 3") .

    from suminf_diff[OF allf_summable[OF x_in_I] allf_summable[OF x0_in_I]]
    have "\<bar>(suminf (f (x0 + x)) - (suminf (f x0))) / x - suminf (f' x0)\<bar> =
        \<bar>\<Sum>n. ?diff n x - f' x0 n\<bar>"
      unfolding suminf_diff[OF div_smbl \<open>summable (f' x0)\<close>, symmetric]
      using suminf_divide[OF diff_smbl, symmetric] by auto
    also have "\<dots> \<le> ?diff_part + \<bar>(\<Sum>n. ?diff (n + ?N) x) - (\<Sum> n. f' x0 (n + ?N))\<bar>"
      unfolding suminf_split_initial_segment[OF all_smbl, where k="?N"]
      unfolding suminf_diff[OF div_shft_smbl ign[OF \<open>summable (f' x0)\<close>]]
      apply (subst (5) add.commute)
      apply (rule abs_triangle_ineq)
      done
    also have "\<dots> \<le> ?diff_part + ?L_part + ?f'_part"
      using abs_triangle_ineq4 by auto
    also have "\<dots> < r /3 + r/3 + r/3"
      using \<open>?diff_part < r/3\<close> \<open>?L_part \<le> r/3\<close> and \<open>?f'_part < r/3\<close>
      by (rule add_strict_mono [OF add_less_le_mono])
    finally show ?thesis
      by auto
  qed
  then show "\<exists>s > 0. \<forall> x. x \<noteq> 0 \<and> norm (x - 0) < s \<longrightarrow>
      norm (((\<Sum>n. f (x0 + x) n) - (\<Sum>n. f x0 n)) / x - (\<Sum>n. f' x0 n)) < r"
    using \<open>0 < S\<close> by auto
qed

lemma DERIV_power_series':
  fixes f :: "nat \<Rightarrow> real"
  assumes converges: "\<And>x. x \<in> {-R <..< R} \<Longrightarrow> summable (\<lambda>n. f n * real (Suc n) * x^n)"
    and x0_in_I: "x0 \<in> {-R <..< R}"
    and "0 < R"
  shows "DERIV (\<lambda>x. (\<Sum>n. f n * x^(Suc n))) x0 :> (\<Sum>n. f n * real (Suc n) * x0^n)"
    (is "DERIV (\<lambda>x. suminf (?f x)) x0 :> suminf (?f' x0)")
proof -
  have for_subinterval: "DERIV (\<lambda>x. suminf (?f x)) x0 :> suminf (?f' x0)"
    if "0 < R'" and "R' < R" and "-R' < x0" and "x0 < R'" for R'
  proof -
    from that have "x0 \<in> {-R' <..< R'}" and "R' \<in> {-R <..< R}" and "x0 \<in> {-R <..< R}"
      by auto
    show ?thesis
    proof (rule DERIV_series')
      show "summable (\<lambda> n. \<bar>f n * real (Suc n) * R'^n\<bar>)"
      proof -
        have "(R' + R) / 2 < R" and "0 < (R' + R) / 2"
          using \<open>0 < R'\<close> \<open>0 < R\<close> \<open>R' < R\<close> by (auto simp: field_simps)
        then have in_Rball: "(R' + R) / 2 \<in> {-R <..< R}"
          using \<open>R' < R\<close> by auto
        have "norm R' < norm ((R' + R) / 2)"
          using \<open>0 < R'\<close> \<open>0 < R\<close> \<open>R' < R\<close> by (auto simp: field_simps)
        from powser_insidea[OF converges[OF in_Rball] this] show ?thesis
          by auto
      qed
    next
      fix n x y
      assume "x \<in> {-R' <..< R'}" and "y \<in> {-R' <..< R'}"
      show "\<bar>?f x n - ?f y n\<bar> \<le> \<bar>f n * real (Suc n) * R'^n\<bar> * \<bar>x-y\<bar>"
      proof -
        have "\<bar>f n * x ^ (Suc n) - f n * y ^ (Suc n)\<bar> =
          (\<bar>f n\<bar> * \<bar>x-y\<bar>) * \<bar>\<Sum>p<Suc n. x ^ p * y ^ (n - p)\<bar>"
          unfolding right_diff_distrib[symmetric] diff_power_eq_sum abs_mult
          by auto
        also have "\<dots> \<le> (\<bar>f n\<bar> * \<bar>x-y\<bar>) * (\<bar>real (Suc n)\<bar> * \<bar>R' ^ n\<bar>)"
        proof (rule mult_left_mono)
          have "\<bar>\<Sum>p<Suc n. x ^ p * y ^ (n - p)\<bar> \<le> (\<Sum>p<Suc n. \<bar>x ^ p * y ^ (n - p)\<bar>)"
            by (rule sum_abs)
          also have "\<dots> \<le> (\<Sum>p<Suc n. R' ^ n)"
          proof (rule sum_mono)
            fix p
            assume "p \<in> {..<Suc n}"
            then have "p \<le> n" by auto
            have "\<bar>x^n\<bar> \<le> R'^n" if  "x \<in> {-R'<..<R'}" for n and x :: real
            proof -
              from that have "\<bar>x\<bar> \<le> R'" by auto
              then show ?thesis
                unfolding power_abs by (rule power_mono) auto
            qed
            from mult_mono[OF this[OF \<open>x \<in> {-R'<..<R'}\<close>, of p] this[OF \<open>y \<in> {-R'<..<R'}\<close>, of "n-p"]]
              and \<open>0 < R'\<close>
            have "\<bar>x^p * y^(n - p)\<bar> \<le> R'^p * R'^(n - p)"
              unfolding abs_mult by auto
            then show "\<bar>x^p * y^(n - p)\<bar> \<le> R'^n"
              unfolding power_add[symmetric] using \<open>p \<le> n\<close> by auto
          qed
          also have "\<dots> = real (Suc n) * R' ^ n"
            unfolding sum_constant card_atLeastLessThan by auto
          finally show "\<bar>\<Sum>p<Suc n. x ^ p * y ^ (n - p)\<bar> \<le> \<bar>real (Suc n)\<bar> * \<bar>R' ^ n\<bar>"
            unfolding abs_of_nonneg[OF zero_le_power[OF less_imp_le[OF \<open>0 < R'\<close>]]]
            by linarith
          show "0 \<le> \<bar>f n\<bar> * \<bar>x - y\<bar>"
            unfolding abs_mult[symmetric] by auto
        qed
        also have "\<dots> = \<bar>f n * real (Suc n) * R' ^ n\<bar> * \<bar>x - y\<bar>"
          unfolding abs_mult mult.assoc[symmetric] by algebra
        finally show ?thesis .
      qed
    next
      show "DERIV (\<lambda>x. ?f x n) x0 :> ?f' x0 n" for n
        by (auto intro!: derivative_eq_intros simp del: power_Suc)
    next
      fix x
      assume "x \<in> {-R' <..< R'}"
      then have "R' \<in> {-R <..< R}" and "norm x < norm R'"
        using assms \<open>R' < R\<close> by auto
      have "summable (\<lambda>n. f n * x^n)"
      proof (rule summable_comparison_test, intro exI allI impI)
        fix n
        have le: "\<bar>f n\<bar> * 1 \<le> \<bar>f n\<bar> * real (Suc n)"
          by (rule mult_left_mono) auto
        show "norm (f n * x^n) \<le> norm (f n * real (Suc n) * x^n)"
          unfolding real_norm_def abs_mult
          using le mult_right_mono by fastforce
      qed (rule powser_insidea[OF converges[OF \<open>R' \<in> {-R <..< R}\<close>] \<open>norm x < norm R'\<close>])
      from this[THEN summable_mult2[where c=x], simplified mult.assoc, simplified mult.commute]
      show "summable (?f x)" by auto
    next
      show "summable (?f' x0)"
        using converges[OF \<open>x0 \<in> {-R <..< R}\<close>] .
      show "x0 \<in> {-R' <..< R'}"
        using \<open>x0 \<in> {-R' <..< R'}\<close> .
    qed
  qed
  let ?R = "(R + \<bar>x0\<bar>) / 2"
  have "\<bar>x0\<bar> < ?R"
    using assms by (auto simp: field_simps)
  then have "- ?R < x0"
  proof (cases "x0 < 0")
    case True
    then have "- x0 < ?R"
      using \<open>\<bar>x0\<bar> < ?R\<close> by auto
    then show ?thesis
      unfolding neg_less_iff_less[symmetric, of "- x0"] by auto
  next
    case False
    have "- ?R < 0" using assms by auto
    also have "\<dots> \<le> x0" using False by auto
    finally show ?thesis .
  qed
  then have "0 < ?R" "?R < R" "- ?R < x0" and "x0 < ?R"
    using assms by (auto simp: field_simps)
  from for_subinterval[OF this] show ?thesis .
qed

lemma geometric_deriv_sums:
  fixes z :: "'a :: {real_normed_field,banach}"
  assumes "norm z < 1"
  shows   "(\<lambda>n. of_nat (Suc n) * z ^ n) sums (1 / (1 - z)^2)"
proof -
  have "(\<lambda>n. diffs (\<lambda>n. 1) n * z^n) sums (1 / (1 - z)^2)"
  proof (rule termdiffs_sums_strong)
    fix z :: 'a assume "norm z < 1"
    thus "(\<lambda>n. 1 * z^n) sums (1 / (1 - z))" by (simp add: geometric_sums)
  qed (insert assms, auto intro!: derivative_eq_intros simp: power2_eq_square)
  thus ?thesis unfolding diffs_def by simp
qed

lemma isCont_pochhammer [continuous_intros]: "isCont (\<lambda>z. pochhammer z n) z"
  for z :: "'a::real_normed_field"
  by (induct n) (auto simp: pochhammer_rec')

lemma continuous_on_pochhammer [continuous_intros]: "continuous_on A (\<lambda>z. pochhammer z n)"
  for A :: "'a::real_normed_field set"
  by (intro continuous_at_imp_continuous_on ballI isCont_pochhammer)


subsection \<open>Exponential Function\<close>

definition exp :: "'a \<Rightarrow> 'a::{real_normed_algebra_1,banach}"
  where "exp = (\<lambda>x. \<Sum>n. x^n /\<^sub>R fact n)"

lemma summable_exp_generic:
  fixes x :: "'a::{real_normed_algebra_1,banach}"
  defines S_def: "S \<equiv> \<lambda>n. x^n /\<^sub>R fact n"
  shows "summable S"
proof -
  have S_Suc: "\<And>n. S (Suc n) = (x * S n) /\<^sub>R (Suc n)"
    unfolding S_def by (simp del: mult_Suc)
  obtain r :: real where r0: "0 < r" and r1: "r < 1"
    using dense [OF zero_less_one] by fast
  obtain N :: nat where N: "norm x < real N * r"
    using ex_less_of_nat_mult r0 by auto
  from r1 show ?thesis
  proof (rule summable_ratio_test [rule_format])
    fix n :: nat
    assume n: "N \<le> n"
    have "norm x \<le> real N * r"
      using N by (rule order_less_imp_le)
    also have "real N * r \<le> real (Suc n) * r"
      using r0 n by (simp add: mult_right_mono)
    finally have "norm x * norm (S n) \<le> real (Suc n) * r * norm (S n)"
      using norm_ge_zero by (rule mult_right_mono)
    then have "norm (x * S n) \<le> real (Suc n) * r * norm (S n)"
      by (rule order_trans [OF norm_mult_ineq])
    then have "norm (x * S n) / real (Suc n) \<le> r * norm (S n)"
      by (simp add: pos_divide_le_eq ac_simps)
    then show "norm (S (Suc n)) \<le> r * norm (S n)"
      by (simp add: S_Suc inverse_eq_divide)
  qed
qed

lemma summable_norm_exp: "summable (\<lambda>n. norm (x^n /\<^sub>R fact n))"
  for x :: "'a::{real_normed_algebra_1,banach}"
proof (rule summable_norm_comparison_test [OF exI, rule_format])
  show "summable (\<lambda>n. norm x^n /\<^sub>R fact n)"
    by (rule summable_exp_generic)
  show "norm (x^n /\<^sub>R fact n) \<le> norm x^n /\<^sub>R fact n" for n
    by (simp add: norm_power_ineq)
qed

lemma summable_exp: "summable (\<lambda>n. inverse (fact n) * x^n)"
  for x :: "'a::{real_normed_field,banach}"
  using summable_exp_generic [where x=x]
  by (simp add: scaleR_conv_of_real nonzero_of_real_inverse)

lemma exp_converges: "(\<lambda>n. x^n /\<^sub>R fact n) sums exp x"
  unfolding exp_def by (rule summable_exp_generic [THEN summable_sums])

lemma exp_fdiffs:
  "diffs (\<lambda>n. inverse (fact n)) = (\<lambda>n. inverse (fact n :: 'a::{real_normed_field,banach}))"
  by (simp add: diffs_def mult_ac nonzero_inverse_mult_distrib nonzero_of_real_inverse
      del: mult_Suc of_nat_Suc)

lemma diffs_of_real: "diffs (\<lambda>n. of_real (f n)) = (\<lambda>n. of_real (diffs f n))"
  by (simp add: diffs_def)

lemma DERIV_exp [simp]: "DERIV exp x :> exp x"
  unfolding exp_def scaleR_conv_of_real
  apply (rule DERIV_cong)
   apply (rule termdiffs [where K="of_real (1 + norm x)"])
      apply (simp_all only: diffs_of_real scaleR_conv_of_real exp_fdiffs)
     apply (rule exp_converges [THEN sums_summable, unfolded scaleR_conv_of_real])+
  apply (simp del: of_real_add)
  done

declare DERIV_exp[THEN DERIV_chain2, derivative_intros]
  and DERIV_exp[THEN DERIV_chain2, unfolded has_field_derivative_def, derivative_intros]

lemma norm_exp: "norm (exp x) \<le> exp (norm x)"
proof -
  from summable_norm[OF summable_norm_exp, of x]
  have "norm (exp x) \<le> (\<Sum>n. inverse (fact n) * norm (x^n))"
    by (simp add: exp_def)
  also have "\<dots> \<le> exp (norm x)"
    using summable_exp_generic[of "norm x"] summable_norm_exp[of x]
    by (auto simp: exp_def intro!: suminf_le norm_power_ineq)
  finally show ?thesis .
qed

lemma isCont_exp: "isCont exp x"
  for x :: "'a::{real_normed_field,banach}"
  by (rule DERIV_exp [THEN DERIV_isCont])

lemma isCont_exp' [simp]: "isCont f a \<Longrightarrow> isCont (\<lambda>x. exp (f x)) a"
  for f :: "_ \<Rightarrow>'a::{real_normed_field,banach}"
  by (rule isCont_o2 [OF _ isCont_exp])

lemma tendsto_exp [tendsto_intros]: "(f \<longlongrightarrow> a) F \<Longrightarrow> ((\<lambda>x. exp (f x)) \<longlongrightarrow> exp a) F"
  for f:: "_ \<Rightarrow>'a::{real_normed_field,banach}"
  by (rule isCont_tendsto_compose [OF isCont_exp])

lemma continuous_exp [continuous_intros]: "continuous F f \<Longrightarrow> continuous F (\<lambda>x. exp (f x))"
  for f :: "_ \<Rightarrow>'a::{real_normed_field,banach}"
  unfolding continuous_def by (rule tendsto_exp)

lemma continuous_on_exp [continuous_intros]: "continuous_on s f \<Longrightarrow> continuous_on s (\<lambda>x. exp (f x))"
  for f :: "_ \<Rightarrow>'a::{real_normed_field,banach}"
  unfolding continuous_on_def by (auto intro: tendsto_exp)


subsubsection \<open>Properties of the Exponential Function\<close>

lemma exp_zero [simp]: "exp 0 = 1"
  unfolding exp_def by (simp add: scaleR_conv_of_real)

lemma exp_series_add_commuting:
  fixes x y :: "'a::{real_normed_algebra_1,banach}"
  defines S_def: "S \<equiv> \<lambda>x n. x^n /\<^sub>R fact n"
  assumes comm: "x * y = y * x"
  shows "S (x + y) n = (\<Sum>i\<le>n. S x i * S y (n - i))"
proof (induct n)
  case 0
  show ?case
    unfolding S_def by simp
next
  case (Suc n)
  have S_Suc: "\<And>x n. S x (Suc n) = (x * S x n) /\<^sub>R real (Suc n)"
    unfolding S_def by (simp del: mult_Suc)
  then have times_S: "\<And>x n. x * S x n = real (Suc n) *\<^sub>R S x (Suc n)"
    by simp
  have S_comm: "\<And>n. S x n * y = y * S x n"
    by (simp add: power_commuting_commutes comm S_def)

  have "real (Suc n) *\<^sub>R S (x + y) (Suc n) = (x + y) * S (x + y) n"
    by (simp only: times_S)
  also have "\<dots> = (x + y) * (\<Sum>i\<le>n. S x i * S y (n - i))"
    by (simp only: Suc)
  also have "\<dots> = x * (\<Sum>i\<le>n. S x i * S y (n - i)) + y * (\<Sum>i\<le>n. S x i * S y (n - i))"
    by (rule distrib_right)
  also have "\<dots> = (\<Sum>i\<le>n. x * S x i * S y (n - i)) + (\<Sum>i\<le>n. S x i * y * S y (n - i))"
    by (simp add: sum_distrib_left ac_simps S_comm)
  also have "\<dots> = (\<Sum>i\<le>n. x * S x i * S y (n - i)) + (\<Sum>i\<le>n. S x i * (y * S y (n - i)))"
    by (simp add: ac_simps)
  also have "\<dots> = (\<Sum>i\<le>n. real (Suc i) *\<^sub>R (S x (Suc i) * S y (n - i))) +
      (\<Sum>i\<le>n. real (Suc n - i) *\<^sub>R (S x i * S y (Suc n - i)))"
    by (simp add: times_S Suc_diff_le)
  also have "(\<Sum>i\<le>n. real (Suc i) *\<^sub>R (S x (Suc i) * S y (n - i))) =
      (\<Sum>i\<le>Suc n. real i *\<^sub>R (S x i * S y (Suc n - i)))"
    by (subst sum_atMost_Suc_shift) simp
  also have "(\<Sum>i\<le>n. real (Suc n - i) *\<^sub>R (S x i * S y (Suc n - i))) =
      (\<Sum>i\<le>Suc n. real (Suc n - i) *\<^sub>R (S x i * S y (Suc n - i)))"
    by simp
  also have "(\<Sum>i\<le>Suc n. real i *\<^sub>R (S x i * S y (Suc n - i))) +
        (\<Sum>i\<le>Suc n. real (Suc n - i) *\<^sub>R (S x i * S y (Suc n - i))) =
      (\<Sum>i\<le>Suc n. real (Suc n) *\<^sub>R (S x i * S y (Suc n - i)))"
    by (simp only: sum.distrib [symmetric] scaleR_left_distrib [symmetric]
        of_nat_add [symmetric]) simp
  also have "\<dots> = real (Suc n) *\<^sub>R (\<Sum>i\<le>Suc n. S x i * S y (Suc n - i))"
    by (simp only: scaleR_right.sum)
  finally show "S (x + y) (Suc n) = (\<Sum>i\<le>Suc n. S x i * S y (Suc n - i))"
    by (simp del: sum_cl_ivl_Suc)
qed

lemma exp_add_commuting: "x * y = y * x \<Longrightarrow> exp (x + y) = exp x * exp y"
  by (simp only: exp_def Cauchy_product summable_norm_exp exp_series_add_commuting)

lemma exp_times_arg_commute: "exp A * A = A * exp A"
  by (simp add: exp_def suminf_mult[symmetric] summable_exp_generic power_commutes suminf_mult2)

lemma exp_add: "exp (x + y) = exp x * exp y"
  for x y :: "'a::{real_normed_field,banach}"
  by (rule exp_add_commuting) (simp add: ac_simps)

lemma exp_double: "exp(2 * z) = exp z ^ 2"
  by (simp add: exp_add_commuting mult_2 power2_eq_square)

lemmas mult_exp_exp = exp_add [symmetric]

lemma exp_of_real: "exp (of_real x) = of_real (exp x)"
  unfolding exp_def
  apply (subst suminf_of_real)
   apply (rule summable_exp_generic)
  apply (simp add: scaleR_conv_of_real)
  done

corollary exp_in_Reals [simp]: "z \<in> \<real> \<Longrightarrow> exp z \<in> \<real>"
  by (metis Reals_cases Reals_of_real exp_of_real)

lemma exp_not_eq_zero [simp]: "exp x \<noteq> 0"
proof
  have "exp x * exp (- x) = 1"
    by (simp add: exp_add_commuting[symmetric])
  also assume "exp x = 0"
  finally show False by simp
qed

lemma exp_minus_inverse: "exp x * exp (- x) = 1"
  by (simp add: exp_add_commuting[symmetric])

lemma exp_minus: "exp (- x) = inverse (exp x)"
  for x :: "'a::{real_normed_field,banach}"
  by (intro inverse_unique [symmetric] exp_minus_inverse)

lemma exp_diff: "exp (x - y) = exp x / exp y"
  for x :: "'a::{real_normed_field,banach}"
  using exp_add [of x "- y"] by (simp add: exp_minus divide_inverse)

lemma exp_of_nat_mult: "exp (of_nat n * x) = exp x ^ n"
  for x :: "'a::{real_normed_field,banach}"
  by (induct n) (auto simp add: distrib_left exp_add mult.commute)

corollary exp_real_of_nat_mult: "exp (real n * x) = exp x ^ n"
  by (simp add: exp_of_nat_mult)

lemma exp_sum: "finite I \<Longrightarrow> exp (sum f I) = prod (\<lambda>x. exp (f x)) I"
  by (induct I rule: finite_induct) (auto simp: exp_add_commuting mult.commute)

lemma exp_divide_power_eq:
  fixes x :: "'a::{real_normed_field,banach}"
  assumes "n > 0"
  shows "exp (x / of_nat n) ^ n = exp x"
  using assms
proof (induction n arbitrary: x)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases "n = 0")
    case True
    then show ?thesis by simp
  next
    case False
    then have [simp]: "x * of_nat n / (1 + of_nat n) / of_nat n = x / (1 + of_nat n)"
      by simp
    have [simp]: "x / (1 + of_nat n) + x * of_nat n / (1 + of_nat n) = x"
      apply (simp add: divide_simps)
      using of_nat_eq_0_iff apply (fastforce simp: distrib_left)
      done
    show ?thesis
      using Suc.IH [of "x * of_nat n / (1 + of_nat n)"] False
      by (simp add: exp_add [symmetric])
  qed
qed


subsubsection \<open>Properties of the Exponential Function on Reals\<close>

text \<open>Comparisons of @{term "exp x"} with zero.\<close>

text \<open>Proof: because every exponential can be seen as a square.\<close>
lemma exp_ge_zero [simp]: "0 \<le> exp x"
  for x :: real
proof -
  have "0 \<le> exp (x/2) * exp (x/2)"
    by simp
  then show ?thesis
    by (simp add: exp_add [symmetric])
qed

lemma exp_gt_zero [simp]: "0 < exp x"
  for x :: real
  by (simp add: order_less_le)

lemma not_exp_less_zero [simp]: "\<not> exp x < 0"
  for x :: real
  by (simp add: not_less)

lemma not_exp_le_zero [simp]: "\<not> exp x \<le> 0"
  for x :: real
  by (simp add: not_le)

lemma abs_exp_cancel [simp]: "\<bar>exp x\<bar> = exp x"
  for x :: real
  by simp

text \<open>Strict monotonicity of exponential.\<close>

lemma exp_ge_add_one_self_aux:
  fixes x :: real
  assumes "0 \<le> x"
  shows "1 + x \<le> exp x"
  using order_le_imp_less_or_eq [OF assms]
proof
  assume "0 < x"
  have "1 + x \<le> (\<Sum>n<2. inverse (fact n) * x^n)"
    by (auto simp add: numeral_2_eq_2)
  also have "\<dots> \<le> (\<Sum>n. inverse (fact n) * x^n)"
    apply (rule sum_le_suminf [OF summable_exp])
    using \<open>0 < x\<close>
    apply (auto  simp add:  zero_le_mult_iff)
    done
  finally show "1 + x \<le> exp x"
    by (simp add: exp_def)
next
  assume "0 = x"
  then show "1 + x \<le> exp x"
    by auto
qed

lemma exp_gt_one: "0 < x \<Longrightarrow> 1 < exp x"
  for x :: real
proof -
  assume x: "0 < x"
  then have "1 < 1 + x" by simp
  also from x have "1 + x \<le> exp x"
    by (simp add: exp_ge_add_one_self_aux)
  finally show ?thesis .
qed

lemma exp_less_mono:
  fixes x y :: real
  assumes "x < y"
  shows "exp x < exp y"
proof -
  from \<open>x < y\<close> have "0 < y - x" by simp
  then have "1 < exp (y - x)" by (rule exp_gt_one)
  then have "1 < exp y / exp x" by (simp only: exp_diff)
  then show "exp x < exp y" by simp
qed

lemma exp_less_cancel: "exp x < exp y \<Longrightarrow> x < y"
  for x y :: real
  unfolding linorder_not_le [symmetric]
  by (auto simp add: order_le_less exp_less_mono)

lemma exp_less_cancel_iff [iff]: "exp x < exp y \<longleftrightarrow> x < y"
  for x y :: real
  by (auto intro: exp_less_mono exp_less_cancel)

lemma exp_le_cancel_iff [iff]: "exp x \<le> exp y \<longleftrightarrow> x \<le> y"
  for x y :: real
  by (auto simp add: linorder_not_less [symmetric])

lemma exp_inj_iff [iff]: "exp x = exp y \<longleftrightarrow> x = y"
  for x y :: real
  by (simp add: order_eq_iff)

text \<open>Comparisons of @{term "exp x"} with one.\<close>

lemma one_less_exp_iff [simp]: "1 < exp x \<longleftrightarrow> 0 < x"
  for x :: real
  using exp_less_cancel_iff [where x = 0 and y = x] by simp

lemma exp_less_one_iff [simp]: "exp x < 1 \<longleftrightarrow> x < 0"
  for x :: real
  using exp_less_cancel_iff [where x = x and y = 0] by simp

lemma one_le_exp_iff [simp]: "1 \<le> exp x \<longleftrightarrow> 0 \<le> x"
  for x :: real
  using exp_le_cancel_iff [where x = 0 and y = x] by simp

lemma exp_le_one_iff [simp]: "exp x \<le> 1 \<longleftrightarrow> x \<le> 0"
  for x :: real
  using exp_le_cancel_iff [where x = x and y = 0] by simp

lemma exp_eq_one_iff [simp]: "exp x = 1 \<longleftrightarrow> x = 0"
  for x :: real
  using exp_inj_iff [where x = x and y = 0] by simp

lemma lemma_exp_total: "1 \<le> y \<Longrightarrow> \<exists>x. 0 \<le> x \<and> x \<le> y - 1 \<and> exp x = y"
  for y :: real
proof (rule IVT)
  assume "1 \<le> y"
  then have "0 \<le> y - 1" by simp
  then have "1 + (y - 1) \<le> exp (y - 1)"
    by (rule exp_ge_add_one_self_aux)
  then show "y \<le> exp (y - 1)" by simp
qed (simp_all add: le_diff_eq)

lemma exp_total: "0 < y \<Longrightarrow> \<exists>x. exp x = y"
  for y :: real
proof (rule linorder_le_cases [of 1 y])
  assume "1 \<le> y"
  then show "\<exists>x. exp x = y"
    by (fast dest: lemma_exp_total)
next
  assume "0 < y" and "y \<le> 1"
  then have "1 \<le> inverse y"
    by (simp add: one_le_inverse_iff)
  then obtain x where "exp x = inverse y"
    by (fast dest: lemma_exp_total)
  then have "exp (- x) = y"
    by (simp add: exp_minus)
  then show "\<exists>x. exp x = y" ..
qed


subsection \<open>Natural Logarithm\<close>

class ln = real_normed_algebra_1 + banach +
  fixes ln :: "'a \<Rightarrow> 'a"
  assumes ln_one [simp]: "ln 1 = 0"

definition powr :: "'a \<Rightarrow> 'a \<Rightarrow> 'a::ln"  (infixr "powr" 80)
  \<comment> \<open>exponentation via ln and exp\<close>
  where  [code del]: "x powr a \<equiv> if x = 0 then 0 else exp (a * ln x)"

lemma powr_0 [simp]: "0 powr z = 0"
  by (simp add: powr_def)


instantiation real :: ln
begin

definition ln_real :: "real \<Rightarrow> real"
  where "ln_real x = (THE u. exp u = x)"

instance
  by intro_classes (simp add: ln_real_def)

end

lemma powr_eq_0_iff [simp]: "w powr z = 0 \<longleftrightarrow> w = 0"
  by (simp add: powr_def)

lemma ln_exp [simp]: "ln (exp x) = x"
  for x :: real
  by (simp add: ln_real_def)

lemma exp_ln [simp]: "0 < x \<Longrightarrow> exp (ln x) = x"
  for x :: real
  by (auto dest: exp_total)

lemma exp_ln_iff [simp]: "exp (ln x) = x \<longleftrightarrow> 0 < x"
  for x :: real
  by (metis exp_gt_zero exp_ln)

lemma ln_unique: "exp y = x \<Longrightarrow> ln x = y"
  for x :: real
  by (erule subst) (rule ln_exp)

lemma ln_mult: "0 < x \<Longrightarrow> 0 < y \<Longrightarrow> ln (x * y) = ln x + ln y"
  for x :: real
  by (rule ln_unique) (simp add: exp_add)

lemma ln_prod: "finite I \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> f i > 0) \<Longrightarrow> ln (prod f I) = sum (\<lambda>x. ln(f x)) I"
  for f :: "'a \<Rightarrow> real"
  by (induct I rule: finite_induct) (auto simp: ln_mult prod_pos)

lemma ln_inverse: "0 < x \<Longrightarrow> ln (inverse x) = - ln x"
  for x :: real
  by (rule ln_unique) (simp add: exp_minus)

lemma ln_div: "0 < x \<Longrightarrow> 0 < y \<Longrightarrow> ln (x / y) = ln x - ln y"
  for x :: real
  by (rule ln_unique) (simp add: exp_diff)

lemma ln_realpow: "0 < x \<Longrightarrow> ln (x^n) = real n * ln x"
  by (rule ln_unique) (simp add: exp_real_of_nat_mult)

lemma ln_less_cancel_iff [simp]: "0 < x \<Longrightarrow> 0 < y \<Longrightarrow> ln x < ln y \<longleftrightarrow> x < y"
  for x :: real
  by (subst exp_less_cancel_iff [symmetric]) simp

lemma ln_le_cancel_iff [simp]: "0 < x \<Longrightarrow> 0 < y \<Longrightarrow> ln x \<le> ln y \<longleftrightarrow> x \<le> y"
  for x :: real
  by (simp add: linorder_not_less [symmetric])

lemma ln_inj_iff [simp]: "0 < x \<Longrightarrow> 0 < y \<Longrightarrow> ln x = ln y \<longleftrightarrow> x = y"
  for x :: real
  by (simp add: order_eq_iff)

lemma ln_add_one_self_le_self [simp]: "0 \<le> x \<Longrightarrow> ln (1 + x) \<le> x"
  for x :: real
  by (rule exp_le_cancel_iff [THEN iffD1]) (simp add: exp_ge_add_one_self_aux)

lemma ln_less_self [simp]: "0 < x \<Longrightarrow> ln x < x"
  for x :: real
  by (rule order_less_le_trans [where y = "ln (1 + x)"]) simp_all

lemma ln_ge_zero [simp]: "1 \<le> x \<Longrightarrow> 0 \<le> ln x"
  for x :: real
  using ln_le_cancel_iff [of 1 x] by simp

lemma ln_ge_zero_imp_ge_one: "0 \<le> ln x \<Longrightarrow> 0 < x \<Longrightarrow> 1 \<le> x"
  for x :: real
  using ln_le_cancel_iff [of 1 x] by simp

lemma ln_ge_zero_iff [simp]: "0 < x \<Longrightarrow> 0 \<le> ln x \<longleftrightarrow> 1 \<le> x"
  for x :: real
  using ln_le_cancel_iff [of 1 x] by simp

lemma ln_less_zero_iff [simp]: "0 < x \<Longrightarrow> ln x < 0 \<longleftrightarrow> x < 1"
  for x :: real
  using ln_less_cancel_iff [of x 1] by simp

lemma ln_gt_zero: "1 < x \<Longrightarrow> 0 < ln x"
  for x :: real
  using ln_less_cancel_iff [of 1 x] by simp

lemma ln_gt_zero_imp_gt_one: "0 < ln x \<Longrightarrow> 0 < x \<Longrightarrow> 1 < x"
  for x :: real
  using ln_less_cancel_iff [of 1 x] by simp

lemma ln_gt_zero_iff [simp]: "0 < x \<Longrightarrow> 0 < ln x \<longleftrightarrow> 1 < x"
  for x :: real
  using ln_less_cancel_iff [of 1 x] by simp

lemma ln_eq_zero_iff [simp]: "0 < x \<Longrightarrow> ln x = 0 \<longleftrightarrow> x = 1"
  for x :: real
  using ln_inj_iff [of x 1] by simp

lemma ln_less_zero: "0 < x \<Longrightarrow> x < 1 \<Longrightarrow> ln x < 0"
  for x :: real
  by simp

lemma ln_neg_is_const: "x \<le> 0 \<Longrightarrow> ln x = (THE x. False)"
  for x :: real
  by (auto simp: ln_real_def intro!: arg_cong[where f = The])

lemma isCont_ln:
  fixes x :: real
  assumes "x \<noteq> 0"
  shows "isCont ln x"
proof (cases "0 < x")
  case True
  then have "isCont ln (exp (ln x))"
    by (intro isCont_inv_fun[where d = "\<bar>x\<bar>" and f = exp]) auto
  with True show ?thesis
    by simp
next
  case False
  with \<open>x \<noteq> 0\<close> show "isCont ln x"
    unfolding isCont_def
    by (subst filterlim_cong[OF _ refl, of _ "nhds (ln 0)" _ "\<lambda>_. ln 0"])
       (auto simp: ln_neg_is_const not_less eventually_at dist_real_def
         intro!: exI[of _ "\<bar>x\<bar>"])
qed

lemma tendsto_ln [tendsto_intros]: "(f \<longlongrightarrow> a) F \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> ((\<lambda>x. ln (f x)) \<longlongrightarrow> ln a) F"
  for a :: real
  by (rule isCont_tendsto_compose [OF isCont_ln])

lemma continuous_ln:
  "continuous F f \<Longrightarrow> f (Lim F (\<lambda>x. x)) \<noteq> 0 \<Longrightarrow> continuous F (\<lambda>x. ln (f x :: real))"
  unfolding continuous_def by (rule tendsto_ln)

lemma isCont_ln' [continuous_intros]:
  "continuous (at x) f \<Longrightarrow> f x \<noteq> 0 \<Longrightarrow> continuous (at x) (\<lambda>x. ln (f x :: real))"
  unfolding continuous_at by (rule tendsto_ln)

lemma continuous_within_ln [continuous_intros]:
  "continuous (at x within s) f \<Longrightarrow> f x \<noteq> 0 \<Longrightarrow> continuous (at x within s) (\<lambda>x. ln (f x :: real))"
  unfolding continuous_within by (rule tendsto_ln)

lemma continuous_on_ln [continuous_intros]:
  "continuous_on s f \<Longrightarrow> (\<forall>x\<in>s. f x \<noteq> 0) \<Longrightarrow> continuous_on s (\<lambda>x. ln (f x :: real))"
  unfolding continuous_on_def by (auto intro: tendsto_ln)

lemma DERIV_ln: "0 < x \<Longrightarrow> DERIV ln x :> inverse x"
  for x :: real
  by (rule DERIV_inverse_function [where f=exp and a=0 and b="x+1"])
    (auto intro: DERIV_cong [OF DERIV_exp exp_ln] isCont_ln)

lemma DERIV_ln_divide: "0 < x \<Longrightarrow> DERIV ln x :> 1 / x"
  for x :: real
  by (rule DERIV_ln[THEN DERIV_cong]) (simp_all add: divide_inverse)

declare DERIV_ln_divide[THEN DERIV_chain2, derivative_intros]
  and DERIV_ln_divide[THEN DERIV_chain2, unfolded has_field_derivative_def, derivative_intros]

lemma ln_series:
  assumes "0 < x" and "x < 2"
  shows "ln x = (\<Sum> n. (-1)^n * (1 / real (n + 1)) * (x - 1)^(Suc n))"
    (is "ln x = suminf (?f (x - 1))")
proof -
  let ?f' = "\<lambda>x n. (-1)^n * (x - 1)^n"

  have "ln x - suminf (?f (x - 1)) = ln 1 - suminf (?f (1 - 1))"
  proof (rule DERIV_isconst3 [where x = x])
    fix x :: real
    assume "x \<in> {0 <..< 2}"
    then have "0 < x" and "x < 2" by auto
    have "norm (1 - x) < 1"
      using \<open>0 < x\<close> and \<open>x < 2\<close> by auto
    have "1 / x = 1 / (1 - (1 - x))" by auto
    also have "\<dots> = (\<Sum> n. (1 - x)^n)"
      using geometric_sums[OF \<open>norm (1 - x) < 1\<close>] by (rule sums_unique)
    also have "\<dots> = suminf (?f' x)"
      unfolding power_mult_distrib[symmetric]
      by (rule arg_cong[where f=suminf], rule arg_cong[where f="op ^"], auto)
    finally have "DERIV ln x :> suminf (?f' x)"
      using DERIV_ln[OF \<open>0 < x\<close>] unfolding divide_inverse by auto
    moreover
    have repos: "\<And> h x :: real. h - 1 + x = h + x - 1" by auto
    have "DERIV (\<lambda>x. suminf (?f x)) (x - 1) :>
      (\<Sum>n. (-1)^n * (1 / real (n + 1)) * real (Suc n) * (x - 1) ^ n)"
    proof (rule DERIV_power_series')
      show "x - 1 \<in> {- 1<..<1}" and "(0 :: real) < 1"
        using \<open>0 < x\<close> \<open>x < 2\<close> by auto
    next
      fix x :: real
      assume "x \<in> {- 1<..<1}"
      then have "norm (-x) < 1" by auto
      show "summable (\<lambda>n. (- 1) ^ n * (1 / real (n + 1)) * real (Suc n) * x^n)"
        unfolding One_nat_def
        by (auto simp add: power_mult_distrib[symmetric] summable_geometric[OF \<open>norm (-x) < 1\<close>])
    qed
    then have "DERIV (\<lambda>x. suminf (?f x)) (x - 1) :> suminf (?f' x)"
      unfolding One_nat_def by auto
    then have "DERIV (\<lambda>x. suminf (?f (x - 1))) x :> suminf (?f' x)"
      unfolding DERIV_def repos .
    ultimately have "DERIV (\<lambda>x. ln x - suminf (?f (x - 1))) x :> suminf (?f' x) - suminf (?f' x)"
      by (rule DERIV_diff)
    then show "DERIV (\<lambda>x. ln x - suminf (?f (x - 1))) x :> 0" by auto
  qed (auto simp add: assms)
  then show ?thesis by auto
qed

lemma exp_first_terms:
  fixes x :: "'a::{real_normed_algebra_1,banach}"
  shows "exp x = (\<Sum>n<k. inverse(fact n) *\<^sub>R (x ^ n)) + (\<Sum>n. inverse(fact (n + k)) *\<^sub>R (x ^ (n + k)))"
proof -
  have "exp x = suminf (\<lambda>n. inverse(fact n) *\<^sub>R (x^n))"
    by (simp add: exp_def)
  also from summable_exp_generic have "\<dots> = (\<Sum> n. inverse(fact(n+k)) *\<^sub>R (x ^ (n + k))) +
    (\<Sum> n::nat<k. inverse(fact n) *\<^sub>R (x^n))" (is "_ = _ + ?a")
    by (rule suminf_split_initial_segment)
  finally show ?thesis by simp
qed

lemma exp_first_term: "exp x = 1 + (\<Sum>n. inverse (fact (Suc n)) *\<^sub>R (x ^ Suc n))"
  for x :: "'a::{real_normed_algebra_1,banach}"
  using exp_first_terms[of x 1] by simp

lemma exp_first_two_terms: "exp x = 1 + x + (\<Sum>n. inverse (fact (n + 2)) *\<^sub>R (x ^ (n + 2)))"
  for x :: "'a::{real_normed_algebra_1,banach}"
  using exp_first_terms[of x 2] by (simp add: eval_nat_numeral)

lemma exp_bound:
  fixes x :: real
  assumes a: "0 \<le> x"
    and b: "x \<le> 1"
  shows "exp x \<le> 1 + x + x\<^sup>2"
proof -
  have aux1: "inverse (fact (n + 2)) * x ^ (n + 2) \<le> (x\<^sup>2/2) * ((1/2)^n)" for n :: nat
  proof -
    have "(2::nat) * 2 ^ n \<le> fact (n + 2)"
      by (induct n) simp_all
    then have "real ((2::nat) * 2 ^ n) \<le> real_of_nat (fact (n + 2))"
      by (simp only: of_nat_le_iff)
    then have "((2::real) * 2 ^ n) \<le> fact (n + 2)"
      unfolding of_nat_fact by simp
    then have "inverse (fact (n + 2)) \<le> inverse ((2::real) * 2 ^ n)"
      by (rule le_imp_inverse_le) simp
    then have "inverse (fact (n + 2)) \<le> 1/(2::real) * (1/2)^n"
      by (simp add: power_inverse [symmetric])
    then have "inverse (fact (n + 2)) * (x^n * x\<^sup>2) \<le> 1/2 * (1/2)^n * (1 * x\<^sup>2)"
      by (rule mult_mono) (rule mult_mono, simp_all add: power_le_one a b)
    then show ?thesis
      unfolding power_add by (simp add: ac_simps del: fact_Suc)
  qed
  have "(\<lambda>n. x\<^sup>2 / 2 * (1 / 2) ^ n) sums (x\<^sup>2 / 2 * (1 / (1 - 1 / 2)))"
    by (intro sums_mult geometric_sums) simp
  then have aux2: "(\<lambda>n. x\<^sup>2 / 2 * (1 / 2) ^ n) sums x\<^sup>2"
    by simp
  have "suminf (\<lambda>n. inverse(fact (n+2)) * (x ^ (n + 2))) \<le> x\<^sup>2"
  proof -
    have "suminf (\<lambda>n. inverse(fact (n+2)) * (x ^ (n + 2))) \<le> suminf (\<lambda>n. (x\<^sup>2/2) * ((1/2)^n))"
      apply (rule suminf_le)
        apply (rule allI)
        apply (rule aux1)
       apply (rule summable_exp [THEN summable_ignore_initial_segment])
      apply (rule sums_summable)
      apply (rule aux2)
      done
    also have "\<dots> = x\<^sup>2"
      by (rule sums_unique [THEN sym]) (rule aux2)
    finally show ?thesis .
  qed
  then show ?thesis
    unfolding exp_first_two_terms by auto
qed

corollary exp_half_le2: "exp(1/2) \<le> (2::real)"
  using exp_bound [of "1/2"]
  by (simp add: field_simps)

corollary exp_le: "exp 1 \<le> (3::real)"
  using exp_bound [of 1]
  by (simp add: field_simps)

lemma exp_bound_half: "norm z \<le> 1/2 \<Longrightarrow> norm (exp z) \<le> 2"
  by (blast intro: order_trans intro!: exp_half_le2 norm_exp)

lemma exp_bound_lemma:
  assumes "norm z \<le> 1/2"
  shows "norm (exp z) \<le> 1 + 2 * norm z"
proof -
  have *: "(norm z)\<^sup>2 \<le> norm z * 1"
    unfolding power2_eq_square
    apply (rule mult_left_mono)
    using assms
     apply auto
    done
  show ?thesis
    apply (rule order_trans [OF norm_exp])
    apply (rule order_trans [OF exp_bound])
    using assms *
      apply auto
    done
qed

lemma real_exp_bound_lemma: "0 \<le> x \<Longrightarrow> x \<le> 1/2 \<Longrightarrow> exp x \<le> 1 + 2 * x"
  for x :: real
  using exp_bound_lemma [of x] by simp

lemma ln_one_minus_pos_upper_bound:
  fixes x :: real
  assumes a: "0 \<le> x" and b: "x < 1"
  shows "ln (1 - x) \<le> - x"
proof -
  have "(1 - x) * (1 + x + x\<^sup>2) = 1 - x^3"
    by (simp add: algebra_simps power2_eq_square power3_eq_cube)
  also have "\<dots> \<le> 1"
    by (auto simp add: a)
  finally have "(1 - x) * (1 + x + x\<^sup>2) \<le> 1" .
  moreover have c: "0 < 1 + x + x\<^sup>2"
    by (simp add: add_pos_nonneg a)
  ultimately have "1 - x \<le> 1 / (1 + x + x\<^sup>2)"
    by (elim mult_imp_le_div_pos)
  also have "\<dots> \<le> 1 / exp x"
    by (metis a abs_one b exp_bound exp_gt_zero frac_le less_eq_real_def real_sqrt_abs
        real_sqrt_pow2_iff real_sqrt_power)
  also have "\<dots> = exp (- x)"
    by (auto simp add: exp_minus divide_inverse)
  finally have "1 - x \<le> exp (- x)" .
  also have "1 - x = exp (ln (1 - x))"
    by (metis b diff_0 exp_ln_iff less_iff_diff_less_0 minus_diff_eq)
  finally have "exp (ln (1 - x)) \<le> exp (- x)" .
  then show ?thesis
    by (auto simp only: exp_le_cancel_iff)
qed

lemma exp_ge_add_one_self [simp]: "1 + x \<le> exp x"
  for x :: real
  apply (cases "0 \<le> x")
   apply (erule exp_ge_add_one_self_aux)
  apply (cases "x \<le> -1")
   apply (subgoal_tac "1 + x \<le> 0")
    apply (erule order_trans)
    apply simp
   apply simp
  apply (subgoal_tac "1 + x = exp (ln (1 + x))")
   apply (erule ssubst)
   apply (subst exp_le_cancel_iff)
   apply (subgoal_tac "ln (1 - (- x)) \<le> - (- x)")
    apply simp
   apply (rule ln_one_minus_pos_upper_bound)
    apply auto
  done

lemma ln_one_plus_pos_lower_bound:
  fixes x :: real
  assumes a: "0 \<le> x" and b: "x \<le> 1"
  shows "x - x\<^sup>2 \<le> ln (1 + x)"
proof -
  have "exp (x - x\<^sup>2) = exp x / exp (x\<^sup>2)"
    by (rule exp_diff)
  also have "\<dots> \<le> (1 + x + x\<^sup>2) / exp (x \<^sup>2)"
    by (metis a b divide_right_mono exp_bound exp_ge_zero)
  also have "\<dots> \<le> (1 + x + x\<^sup>2) / (1 + x\<^sup>2)"
    by (simp add: a divide_left_mono add_pos_nonneg)
  also from a have "\<dots> \<le> 1 + x"
    by (simp add: field_simps add_strict_increasing zero_le_mult_iff)
  finally have "exp (x - x\<^sup>2) \<le> 1 + x" .
  also have "\<dots> = exp (ln (1 + x))"
  proof -
    from a have "0 < 1 + x" by auto
    then show ?thesis
      by (auto simp only: exp_ln_iff [THEN sym])
  qed
  finally have "exp (x - x\<^sup>2) \<le> exp (ln (1 + x))" .
  then show ?thesis
    by (metis exp_le_cancel_iff)
qed

lemma ln_one_minus_pos_lower_bound:
  fixes x :: real
  assumes a: "0 \<le> x" and b: "x \<le> 1 / 2"
  shows "- x - 2 * x\<^sup>2 \<le> ln (1 - x)"
proof -
  from b have c: "x < 1" by auto
  then have "ln (1 - x) = - ln (1 + x / (1 - x))"
    apply (subst ln_inverse [symmetric])
     apply (simp add: field_simps)
    apply (rule arg_cong [where f=ln])
    apply (simp add: field_simps)
    done
  also have "- (x / (1 - x)) \<le> \<dots>"
  proof -
    have "ln (1 + x / (1 - x)) \<le> x / (1 - x)"
      using a c by (intro ln_add_one_self_le_self) auto
    then show ?thesis
      by auto
  qed
  also have "- (x / (1 - x)) = - x / (1 - x)"
    by auto
  finally have d: "- x / (1 - x) \<le> ln (1 - x)" .
  have "0 < 1 - x" using a b by simp
  then have e: "- x - 2 * x\<^sup>2 \<le> - x / (1 - x)"
    using mult_right_le_one_le[of "x * x" "2 * x"] a b
    by (simp add: field_simps power2_eq_square)
  from e d show "- x - 2 * x\<^sup>2 \<le> ln (1 - x)"
    by (rule order_trans)
qed

lemma ln_add_one_self_le_self2:
  fixes x :: real
  shows "-1 < x \<Longrightarrow> ln (1 + x) \<le> x"
  apply (subgoal_tac "ln (1 + x) \<le> ln (exp x)")
   apply simp
  apply (subst ln_le_cancel_iff)
    apply auto
  done

lemma abs_ln_one_plus_x_minus_x_bound_nonneg:
  fixes x :: real
  assumes x: "0 \<le> x" and x1: "x \<le> 1"
  shows "\<bar>ln (1 + x) - x\<bar> \<le> x\<^sup>2"
proof -
  from x have "ln (1 + x) \<le> x"
    by (rule ln_add_one_self_le_self)
  then have "ln (1 + x) - x \<le> 0"
    by simp
  then have "\<bar>ln(1 + x) - x\<bar> = - (ln(1 + x) - x)"
    by (rule abs_of_nonpos)
  also have "\<dots> = x - ln (1 + x)"
    by simp
  also have "\<dots> \<le> x\<^sup>2"
  proof -
    from x x1 have "x - x\<^sup>2 \<le> ln (1 + x)"
      by (intro ln_one_plus_pos_lower_bound)
    then show ?thesis
      by simp
  qed
  finally show ?thesis .
qed

lemma abs_ln_one_plus_x_minus_x_bound_nonpos:
  fixes x :: real
  assumes a: "-(1 / 2) \<le> x" and b: "x \<le> 0"
  shows "\<bar>ln (1 + x) - x\<bar> \<le> 2 * x\<^sup>2"
proof -
  have "\<bar>ln (1 + x) - x\<bar> = x - ln (1 - (- x))"
    apply (subst abs_of_nonpos)
     apply simp
     apply (rule ln_add_one_self_le_self2)
    using a apply auto
    done
  also have "\<dots> \<le> 2 * x\<^sup>2"
    apply (subgoal_tac "- (-x) - 2 * (-x)\<^sup>2 \<le> ln (1 - (- x))")
     apply (simp add: algebra_simps)
    apply (rule ln_one_minus_pos_lower_bound)
    using a b apply auto
    done
  finally show ?thesis .
qed

lemma abs_ln_one_plus_x_minus_x_bound:
  fixes x :: real
  shows "\<bar>x\<bar> \<le> 1 / 2 \<Longrightarrow> \<bar>ln (1 + x) - x\<bar> \<le> 2 * x\<^sup>2"
  apply (cases "0 \<le> x")
   apply (rule order_trans)
    apply (rule abs_ln_one_plus_x_minus_x_bound_nonneg)
     apply auto
  apply (rule abs_ln_one_plus_x_minus_x_bound_nonpos)
   apply auto
  done

lemma ln_x_over_x_mono:
  fixes x :: real
  assumes x: "exp 1 \<le> x" "x \<le> y"
  shows "ln y / y \<le> ln x / x"
proof -
  note x
  moreover have "0 < exp (1::real)" by simp
  ultimately have a: "0 < x" and b: "0 < y"
    by (fast intro: less_le_trans order_trans)+
  have "x * ln y - x * ln x = x * (ln y - ln x)"
    by (simp add: algebra_simps)
  also have "\<dots> = x * ln (y / x)"
    by (simp only: ln_div a b)
  also have "y / x = (x + (y - x)) / x"
    by simp
  also have "\<dots> = 1 + (y - x) / x"
    using x a by (simp add: field_simps)
  also have "x * ln (1 + (y - x) / x) \<le> x * ((y - x) / x)"
    using x a
    by (intro mult_left_mono ln_add_one_self_le_self) simp_all
  also have "\<dots> = y - x"
    using a by simp
  also have "\<dots> = (y - x) * ln (exp 1)" by simp
  also have "\<dots> \<le> (y - x) * ln x"
    apply (rule mult_left_mono)
     apply (subst ln_le_cancel_iff)
       apply fact
      apply (rule a)
     apply (rule x)
    using x apply simp
    done
  also have "\<dots> = y * ln x - x * ln x"
    by (rule left_diff_distrib)
  finally have "x * ln y \<le> y * ln x"
    by arith
  then have "ln y \<le> (y * ln x) / x"
    using a by (simp add: field_simps)
  also have "\<dots> = y * (ln x / x)" by simp
  finally show ?thesis
    using b by (simp add: field_simps)
qed

lemma ln_le_minus_one: "0 < x \<Longrightarrow> ln x \<le> x - 1"
  for x :: real
  using exp_ge_add_one_self[of "ln x"] by simp

corollary ln_diff_le: "0 < x \<Longrightarrow> 0 < y \<Longrightarrow> ln x - ln y \<le> (x - y) / y"
  for x :: real
  by (simp add: ln_div [symmetric] diff_divide_distrib ln_le_minus_one)

lemma ln_eq_minus_one:
  fixes x :: real
  assumes "0 < x" "ln x = x - 1"
  shows "x = 1"
proof -
  let ?l = "\<lambda>y. ln y - y + 1"
  have D: "\<And>x::real. 0 < x \<Longrightarrow> DERIV ?l x :> (1 / x - 1)"
    by (auto intro!: derivative_eq_intros)

  show ?thesis
  proof (cases rule: linorder_cases)
    assume "x < 1"
    from dense[OF \<open>x < 1\<close>] obtain a where "x < a" "a < 1" by blast
    from \<open>x < a\<close> have "?l x < ?l a"
    proof (rule DERIV_pos_imp_increasing, safe)
      fix y
      assume "x \<le> y" "y \<le> a"
      with \<open>0 < x\<close> \<open>a < 1\<close> have "0 < 1 / y - 1" "0 < y"
        by (auto simp: field_simps)
      with D show "\<exists>z. DERIV ?l y :> z \<and> 0 < z" by blast
    qed
    also have "\<dots> \<le> 0"
      using ln_le_minus_one \<open>0 < x\<close> \<open>x < a\<close> by (auto simp: field_simps)
    finally show "x = 1" using assms by auto
  next
    assume "1 < x"
    from dense[OF this] obtain a where "1 < a" "a < x" by blast
    from \<open>a < x\<close> have "?l x < ?l a"
    proof (rule DERIV_neg_imp_decreasing, safe)
      fix y
      assume "a \<le> y" "y \<le> x"
      with \<open>1 < a\<close> have "1 / y - 1 < 0" "0 < y"
        by (auto simp: field_simps)
      with D show "\<exists>z. DERIV ?l y :> z \<and> z < 0"
        by blast
    qed
    also have "\<dots> \<le> 0"
      using ln_le_minus_one \<open>1 < a\<close> by (auto simp: field_simps)
    finally show "x = 1" using assms by auto
  next
    assume "x = 1"
    then show ?thesis by simp
  qed
qed

lemma ln_x_over_x_tendsto_0: "((\<lambda>x::real. ln x / x) \<longlongrightarrow> 0) at_top"
proof (rule lhospital_at_top_at_top[where f' = inverse and g' = "\<lambda>_. 1"])
  from eventually_gt_at_top[of "0::real"]
  show "\<forall>\<^sub>F x in at_top. (ln has_real_derivative inverse x) (at x)"
    by eventually_elim (auto intro!: derivative_eq_intros simp: field_simps)
qed (use tendsto_inverse_0 in
      \<open>auto simp: filterlim_ident dest!: tendsto_mono[OF at_top_le_at_infinity]\<close>)

lemma exp_ge_one_plus_x_over_n_power_n:
  assumes "x \<ge> - real n" "n > 0"
  shows "(1 + x / of_nat n) ^ n \<le> exp x"
proof (cases "x = - of_nat n")
  case False
  from assms False have "(1 + x / of_nat n) ^ n = exp (of_nat n * ln (1 + x / of_nat n))"
    by (subst exp_of_nat_mult, subst exp_ln) (simp_all add: field_simps)
  also from assms False have "ln (1 + x / real n) \<le> x / real n"
    by (intro ln_add_one_self_le_self2) (simp_all add: field_simps)
  with assms have "exp (of_nat n * ln (1 + x / of_nat n)) \<le> exp x"
    by (simp add: field_simps)
  finally show ?thesis .
next
  case True
  then show ?thesis by (simp add: zero_power)
qed

lemma exp_ge_one_minus_x_over_n_power_n:
  assumes "x \<le> real n" "n > 0"
  shows "(1 - x / of_nat n) ^ n \<le> exp (-x)"
  using exp_ge_one_plus_x_over_n_power_n[of n "-x"] assms by simp

lemma exp_at_bot: "(exp \<longlongrightarrow> (0::real)) at_bot"
  unfolding tendsto_Zfun_iff
proof (rule ZfunI, simp add: eventually_at_bot_dense)
  fix r :: real
  assume "0 < r"
  have "exp x < r" if "x < ln r" for x
  proof -
    from that have "exp x < exp (ln r)"
      by simp
    with \<open>0 < r\<close> show ?thesis
      by simp
  qed
  then show "\<exists>k. \<forall>n<k. exp n < r" by auto
qed

lemma exp_at_top: "LIM x at_top. exp x :: real :> at_top"
  by (rule filterlim_at_top_at_top[where Q="\<lambda>x. True" and P="\<lambda>x. 0 < x" and g="ln"])
    (auto intro: eventually_gt_at_top)

lemma lim_exp_minus_1: "((\<lambda>z::'a. (exp(z) - 1) / z) \<longlongrightarrow> 1) (at 0)"
  for x :: "'a::{real_normed_field,banach}"
proof -
  have "((\<lambda>z::'a. exp(z) - 1) has_field_derivative 1) (at 0)"
    by (intro derivative_eq_intros | simp)+
  then show ?thesis
    by (simp add: Deriv.DERIV_iff2)
qed

lemma ln_at_0: "LIM x at_right 0. ln (x::real) :> at_bot"
  by (rule filterlim_at_bot_at_right[where Q="\<lambda>x. 0 < x" and P="\<lambda>x. True" and g="exp"])
     (auto simp: eventually_at_filter)

lemma ln_at_top: "LIM x at_top. ln (x::real) :> at_top"
  by (rule filterlim_at_top_at_top[where Q="\<lambda>x. 0 < x" and P="\<lambda>x. True" and g="exp"])
     (auto intro: eventually_gt_at_top)

lemma filtermap_ln_at_top: "filtermap (ln::real \<Rightarrow> real) at_top = at_top"
  by (intro filtermap_fun_inverse[of exp] exp_at_top ln_at_top) auto

lemma filtermap_exp_at_top: "filtermap (exp::real \<Rightarrow> real) at_top = at_top"
  by (intro filtermap_fun_inverse[of ln] exp_at_top ln_at_top)
     (auto simp: eventually_at_top_dense)

lemma tendsto_power_div_exp_0: "((\<lambda>x. x ^ k / exp x) \<longlongrightarrow> (0::real)) at_top"
proof (induct k)
  case 0
  show "((\<lambda>x. x ^ 0 / exp x) \<longlongrightarrow> (0::real)) at_top"
    by (simp add: inverse_eq_divide[symmetric])
       (metis filterlim_compose[OF tendsto_inverse_0] exp_at_top filterlim_mono
         at_top_le_at_infinity order_refl)
next
  case (Suc k)
  show ?case
  proof (rule lhospital_at_top_at_top)
    show "eventually (\<lambda>x. DERIV (\<lambda>x. x ^ Suc k) x :> (real (Suc k) * x^k)) at_top"
      by eventually_elim (intro derivative_eq_intros, auto)
    show "eventually (\<lambda>x. DERIV exp x :> exp x) at_top"
      by eventually_elim auto
    show "eventually (\<lambda>x. exp x \<noteq> 0) at_top"
      by auto
    from tendsto_mult[OF tendsto_const Suc, of "real (Suc k)"]
    show "((\<lambda>x. real (Suc k) * x ^ k / exp x) \<longlongrightarrow> 0) at_top"
      by simp
  qed (rule exp_at_top)
qed

definition log :: "real \<Rightarrow> real \<Rightarrow> real"
  \<comment> \<open>logarithm of @{term x} to base @{term a}\<close>
  where "log a x = ln x / ln a"

lemma tendsto_log [tendsto_intros]:
  "(f \<longlongrightarrow> a) F \<Longrightarrow> (g \<longlongrightarrow> b) F \<Longrightarrow> 0 < a \<Longrightarrow> a \<noteq> 1 \<Longrightarrow> 0 < b \<Longrightarrow>
    ((\<lambda>x. log (f x) (g x)) \<longlongrightarrow> log a b) F"
  unfolding log_def by (intro tendsto_intros) auto

lemma continuous_log:
  assumes "continuous F f"
    and "continuous F g"
    and "0 < f (Lim F (\<lambda>x. x))"
    and "f (Lim F (\<lambda>x. x)) \<noteq> 1"
    and "0 < g (Lim F (\<lambda>x. x))"
  shows "continuous F (\<lambda>x. log (f x) (g x))"
  using assms unfolding continuous_def by (rule tendsto_log)

lemma continuous_at_within_log[continuous_intros]:
  assumes "continuous (at a within s) f"
    and "continuous (at a within s) g"
    and "0 < f a"
    and "f a \<noteq> 1"
    and "0 < g a"
  shows "continuous (at a within s) (\<lambda>x. log (f x) (g x))"
  using assms unfolding continuous_within by (rule tendsto_log)

lemma isCont_log[continuous_intros, simp]:
  assumes "isCont f a" "isCont g a" "0 < f a" "f a \<noteq> 1" "0 < g a"
  shows "isCont (\<lambda>x. log (f x) (g x)) a"
  using assms unfolding continuous_at by (rule tendsto_log)

lemma continuous_on_log[continuous_intros]:
  assumes "continuous_on s f" "continuous_on s g"
    and "\<forall>x\<in>s. 0 < f x" "\<forall>x\<in>s. f x \<noteq> 1" "\<forall>x\<in>s. 0 < g x"
  shows "continuous_on s (\<lambda>x. log (f x) (g x))"
  using assms unfolding continuous_on_def by (fast intro: tendsto_log)

lemma powr_one_eq_one [simp]: "1 powr a = 1"
  by (simp add: powr_def)

lemma powr_zero_eq_one [simp]: "x powr 0 = (if x = 0 then 0 else 1)"
  by (simp add: powr_def)

lemma powr_one_gt_zero_iff [simp]: "x powr 1 = x \<longleftrightarrow> 0 \<le> x"
  for x :: real
  by (auto simp: powr_def)
declare powr_one_gt_zero_iff [THEN iffD2, simp]

lemma powr_mult: "0 \<le> x \<Longrightarrow> 0 \<le> y \<Longrightarrow> (x * y) powr a = (x powr a) * (y powr a)"
  for a x y :: real
  by (simp add: powr_def exp_add [symmetric] ln_mult distrib_left)

lemma powr_ge_pzero [simp]: "0 \<le> x powr y"
  for x y :: real
  by (simp add: powr_def)

lemma powr_divide: "0 < x \<Longrightarrow> 0 < y \<Longrightarrow> (x / y) powr a = (x powr a) / (y powr a)"
  for a b x :: real
  apply (simp add: divide_inverse positive_imp_inverse_positive powr_mult)
  apply (simp add: powr_def exp_minus [symmetric] exp_add [symmetric] ln_inverse)
  done

lemma powr_divide2: "x powr a / x powr b = x powr (a - b)"
  for a b x :: real
  apply (simp add: powr_def)
  apply (subst exp_diff [THEN sym])
  apply (simp add: left_diff_distrib)
  done

lemma powr_add: "x powr (a + b) = (x powr a) * (x powr b)"
  for a b x :: real
  by (simp add: powr_def exp_add [symmetric] distrib_right)

lemma powr_mult_base: "0 < x \<Longrightarrow>x * x powr y = x powr (1 + y)"
  for x :: real
  by (auto simp: powr_add)

lemma powr_powr: "(x powr a) powr b = x powr (a * b)"
  for a b x :: real
  by (simp add: powr_def)

lemma powr_powr_swap: "(x powr a) powr b = (x powr b) powr a"
  for a b x :: real
  by (simp add: powr_powr mult.commute)

lemma powr_minus: "x powr (- a) = inverse (x powr a)"
  for x a :: real
  by (simp add: powr_def exp_minus [symmetric])

lemma powr_minus_divide: "x powr (- a) = 1/(x powr a)"
  for x a :: real
  by (simp add: divide_inverse powr_minus)

lemma divide_powr_uminus: "a / b powr c = a * b powr (- c)"
  for a b c :: real
  by (simp add: powr_minus_divide)

lemma powr_less_mono: "a < b \<Longrightarrow> 1 < x \<Longrightarrow> x powr a < x powr b"
  for a b x :: real
  by (simp add: powr_def)

lemma powr_less_cancel: "x powr a < x powr b \<Longrightarrow> 1 < x \<Longrightarrow> a < b"
  for a b x :: real
  by (simp add: powr_def)

lemma powr_less_cancel_iff [simp]: "1 < x \<Longrightarrow> x powr a < x powr b \<longleftrightarrow> a < b"
  for a b x :: real
  by (blast intro: powr_less_cancel powr_less_mono)

lemma powr_le_cancel_iff [simp]: "1 < x \<Longrightarrow> x powr a \<le> x powr b \<longleftrightarrow> a \<le> b"
  for a b x :: real
  by (simp add: linorder_not_less [symmetric])

lemma log_ln: "ln x = log (exp(1)) x"
  by (simp add: log_def)

lemma DERIV_log:
  assumes "x > 0"
  shows "DERIV (\<lambda>y. log b y) x :> 1 / (ln b * x)"
proof -
  define lb where "lb = 1 / ln b"
  moreover have "DERIV (\<lambda>y. lb * ln y) x :> lb / x"
    using \<open>x > 0\<close> by (auto intro!: derivative_eq_intros)
  ultimately show ?thesis
    by (simp add: log_def)
qed

lemmas DERIV_log[THEN DERIV_chain2, derivative_intros]
  and DERIV_log[THEN DERIV_chain2, unfolded has_field_derivative_def, derivative_intros]

lemma powr_log_cancel [simp]: "0 < a \<Longrightarrow> a \<noteq> 1 \<Longrightarrow> 0 < x \<Longrightarrow> a powr (log a x) = x"
  by (simp add: powr_def log_def)

lemma log_powr_cancel [simp]: "0 < a \<Longrightarrow> a \<noteq> 1 \<Longrightarrow> log a (a powr y) = y"
  by (simp add: log_def powr_def)

lemma log_mult:
  "0 < a \<Longrightarrow> a \<noteq> 1 \<Longrightarrow> 0 < x \<Longrightarrow> 0 < y \<Longrightarrow>
    log a (x * y) = log a x + log a y"
  by (simp add: log_def ln_mult divide_inverse distrib_right)

lemma log_eq_div_ln_mult_log:
  "0 < a \<Longrightarrow> a \<noteq> 1 \<Longrightarrow> 0 < b \<Longrightarrow> b \<noteq> 1 \<Longrightarrow> 0 < x \<Longrightarrow>
    log a x = (ln b/ln a) * log b x"
  by (simp add: log_def divide_inverse)

text\<open>Base 10 logarithms\<close>
lemma log_base_10_eq1: "0 < x \<Longrightarrow> log 10 x = (ln (exp 1) / ln 10) * ln x"
  by (simp add: log_def)

lemma log_base_10_eq2: "0 < x \<Longrightarrow> log 10 x = (log 10 (exp 1)) * ln x"
  by (simp add: log_def)

lemma log_one [simp]: "log a 1 = 0"
  by (simp add: log_def)

lemma log_eq_one [simp]: "0 < a \<Longrightarrow> a \<noteq> 1 \<Longrightarrow> log a a = 1"
  by (simp add: log_def)

lemma log_inverse: "0 < a \<Longrightarrow> a \<noteq> 1 \<Longrightarrow> 0 < x \<Longrightarrow> log a (inverse x) = - log a x"
  apply (rule add_left_cancel [THEN iffD1, where a1 = "log a x"])
  apply (simp add: log_mult [symmetric])
  done

lemma log_divide: "0 < a \<Longrightarrow> a \<noteq> 1 \<Longrightarrow> 0 < x \<Longrightarrow> 0 < y \<Longrightarrow> log a (x/y) = log a x - log a y"
  by (simp add: log_mult divide_inverse log_inverse)

lemma powr_gt_zero [simp]: "0 < x powr a \<longleftrightarrow> x \<noteq> 0"
  for a x :: real
  by (simp add: powr_def)

lemma log_add_eq_powr: "0 < b \<Longrightarrow> b \<noteq> 1 \<Longrightarrow> 0 < x \<Longrightarrow> log b x + y = log b (x * b powr y)"
  and add_log_eq_powr: "0 < b \<Longrightarrow> b \<noteq> 1 \<Longrightarrow> 0 < x \<Longrightarrow> y + log b x = log b (b powr y * x)"
  and log_minus_eq_powr: "0 < b \<Longrightarrow> b \<noteq> 1 \<Longrightarrow> 0 < x \<Longrightarrow> log b x - y = log b (x * b powr -y)"
  and minus_log_eq_powr: "0 < b \<Longrightarrow> b \<noteq> 1 \<Longrightarrow> 0 < x \<Longrightarrow> y - log b x = log b (b powr y / x)"
  by (simp_all add: log_mult log_divide)

lemma log_less_cancel_iff [simp]: "1 < a \<Longrightarrow> 0 < x \<Longrightarrow> 0 < y \<Longrightarrow> log a x < log a y \<longleftrightarrow> x < y"
  apply safe
   apply (rule_tac [2] powr_less_cancel)
    apply (drule_tac a = "log a x" in powr_less_mono)
     apply auto
  done

lemma log_inj:
  assumes "1 < b"
  shows "inj_on (log b) {0 <..}"
proof (rule inj_onI, simp)
  fix x y
  assume pos: "0 < x" "0 < y" and *: "log b x = log b y"
  show "x = y"
  proof (cases rule: linorder_cases)
    assume "x = y"
    then show ?thesis by simp
  next
    assume "x < y"
    then have "log b x < log b y"
      using log_less_cancel_iff[OF \<open>1 < b\<close>] pos by simp
    then show ?thesis using * by simp
  next
    assume "y < x"
    then have "log b y < log b x"
      using log_less_cancel_iff[OF \<open>1 < b\<close>] pos by simp
    then show ?thesis using * by simp
  qed
qed

lemma log_le_cancel_iff [simp]: "1 < a \<Longrightarrow> 0 < x \<Longrightarrow> 0 < y \<Longrightarrow> log a x \<le> log a y \<longleftrightarrow> x \<le> y"
  by (simp add: linorder_not_less [symmetric])

lemma zero_less_log_cancel_iff[simp]: "1 < a \<Longrightarrow> 0 < x \<Longrightarrow> 0 < log a x \<longleftrightarrow> 1 < x"
  using log_less_cancel_iff[of a 1 x] by simp

lemma zero_le_log_cancel_iff[simp]: "1 < a \<Longrightarrow> 0 < x \<Longrightarrow> 0 \<le> log a x \<longleftrightarrow> 1 \<le> x"
  using log_le_cancel_iff[of a 1 x] by simp

lemma log_less_zero_cancel_iff[simp]: "1 < a \<Longrightarrow> 0 < x \<Longrightarrow> log a x < 0 \<longleftrightarrow> x < 1"
  using log_less_cancel_iff[of a x 1] by simp

lemma log_le_zero_cancel_iff[simp]: "1 < a \<Longrightarrow> 0 < x \<Longrightarrow> log a x \<le> 0 \<longleftrightarrow> x \<le> 1"
  using log_le_cancel_iff[of a x 1] by simp

lemma one_less_log_cancel_iff[simp]: "1 < a \<Longrightarrow> 0 < x \<Longrightarrow> 1 < log a x \<longleftrightarrow> a < x"
  using log_less_cancel_iff[of a a x] by simp

lemma one_le_log_cancel_iff[simp]: "1 < a \<Longrightarrow> 0 < x \<Longrightarrow> 1 \<le> log a x \<longleftrightarrow> a \<le> x"
  using log_le_cancel_iff[of a a x] by simp

lemma log_less_one_cancel_iff[simp]: "1 < a \<Longrightarrow> 0 < x \<Longrightarrow> log a x < 1 \<longleftrightarrow> x < a"
  using log_less_cancel_iff[of a x a] by simp

lemma log_le_one_cancel_iff[simp]: "1 < a \<Longrightarrow> 0 < x \<Longrightarrow> log a x \<le> 1 \<longleftrightarrow> x \<le> a"
  using log_le_cancel_iff[of a x a] by simp

lemma le_log_iff:
  fixes b x y :: real
  assumes "1 < b" "x > 0"
  shows "y \<le> log b x \<longleftrightarrow> b powr y \<le> x"
  using assms
  apply auto
   apply (metis (no_types, hide_lams) less_irrefl less_le_trans linear powr_le_cancel_iff
      powr_log_cancel zero_less_one)
  apply (metis not_less order.trans order_refl powr_le_cancel_iff powr_log_cancel zero_le_one)
  done

lemma less_log_iff:
  assumes "1 < b" "x > 0"
  shows "y < log b x \<longleftrightarrow> b powr y < x"
  by (metis assms dual_order.strict_trans less_irrefl powr_less_cancel_iff
    powr_log_cancel zero_less_one)

lemma
  assumes "1 < b" "x > 0"
  shows log_less_iff: "log b x < y \<longleftrightarrow> x < b powr y"
    and log_le_iff: "log b x \<le> y \<longleftrightarrow> x \<le> b powr y"
  using le_log_iff[OF assms, of y] less_log_iff[OF assms, of y]
  by auto

lemmas powr_le_iff = le_log_iff[symmetric]
  and powr_less_iff = le_log_iff[symmetric]
  and less_powr_iff = log_less_iff[symmetric]
  and le_powr_iff = log_le_iff[symmetric]

lemma floor_log_eq_powr_iff: "x > 0 \<Longrightarrow> b > 1 \<Longrightarrow> \<lfloor>log b x\<rfloor> = k \<longleftrightarrow> b powr k \<le> x \<and> x < b powr (k + 1)"
  by (auto simp add: floor_eq_iff powr_le_iff less_powr_iff)

lemma powr_realpow: "0 < x \<Longrightarrow> x powr (real n) = x^n"
  by (induct n) (simp_all add: ac_simps powr_add)

lemma powr_numeral: "0 < x \<Longrightarrow> x powr (numeral n :: real) = x ^ (numeral n)"
  by (metis of_nat_numeral powr_realpow)

lemma powr_real_of_int:
  "x > 0 \<Longrightarrow> x powr real_of_int n = (if n \<ge> 0 then x ^ nat n else inverse (x ^ nat (- n)))"
  using powr_realpow[of x "nat n"] powr_realpow[of x "nat (-n)"]
  by (auto simp: field_simps powr_minus)

lemma powr2_sqrt[simp]: "0 < x \<Longrightarrow> sqrt x powr 2 = x"
  by (simp add: powr_numeral)

lemma powr_realpow2: "0 \<le> x \<Longrightarrow> 0 < n \<Longrightarrow> x^n = (if (x = 0) then 0 else x powr (real n))"
  apply (cases "x = 0")
   apply simp_all
  apply (rule powr_realpow [THEN sym])
  apply simp
  done

lemma powr_int:
  assumes "x > 0"
  shows "x powr i = (if i \<ge> 0 then x ^ nat i else 1 / x ^ nat (-i))"
proof (cases "i < 0")
  case True
  have r: "x powr i = 1 / x powr (- i)"
    by (simp add: powr_minus field_simps)
  show ?thesis using \<open>i < 0\<close> \<open>x > 0\<close>
    by (simp add: r field_simps powr_realpow[symmetric])
next
  case False
  then show ?thesis
    by (simp add: assms powr_realpow[symmetric])
qed

lemma compute_powr[code]:
  fixes i :: real
  shows "b powr i =
    (if b \<le> 0 then Code.abort (STR ''op powr with nonpositive base'') (\<lambda>_. b powr i)
     else if \<lfloor>i\<rfloor> = i then (if 0 \<le> i then b ^ nat \<lfloor>i\<rfloor> else 1 / b ^ nat \<lfloor>- i\<rfloor>)
     else Code.abort (STR ''op powr with non-integer exponent'') (\<lambda>_. b powr i))"
  by (auto simp: powr_int)

lemma powr_one: "0 \<le> x \<Longrightarrow> x powr 1 = x"
  for x :: real
  using powr_realpow [of x 1] by simp

lemma powr_neg_one: "0 < x \<Longrightarrow> x powr - 1 = 1 / x"
  for x :: real
  using powr_int [of x "- 1"] by simp

lemma powr_neg_numeral: "0 < x \<Longrightarrow> x powr - numeral n = 1 / x ^ numeral n"
  for x :: real
  using powr_int [of x "- numeral n"] by simp

lemma root_powr_inverse: "0 < n \<Longrightarrow> 0 < x \<Longrightarrow> root n x = x powr (1/n)"
  by (rule real_root_pos_unique) (auto simp: powr_realpow[symmetric] powr_powr)

lemma ln_powr: "x \<noteq> 0 \<Longrightarrow> ln (x powr y) = y * ln x"
  for x :: real
  by (simp add: powr_def)

lemma ln_root: "n > 0 \<Longrightarrow> b > 0 \<Longrightarrow> ln (root n b) =  ln b / n"
  by (simp add: root_powr_inverse ln_powr)

lemma ln_sqrt: "0 < x \<Longrightarrow> ln (sqrt x) = ln x / 2"
  by (simp add: ln_powr powr_numeral ln_powr[symmetric] mult.commute)

lemma log_root: "n > 0 \<Longrightarrow> a > 0 \<Longrightarrow> log b (root n a) =  log b a / n"
  by (simp add: log_def ln_root)

lemma log_powr: "x \<noteq> 0 \<Longrightarrow> log b (x powr y) = y * log b x"
  by (simp add: log_def ln_powr)

lemma log_nat_power: "0 < x \<Longrightarrow> log b (x^n) = real n * log b x"
  by (simp add: log_powr powr_realpow [symmetric])

lemma le_log_of_power:
  assumes "1 < b" "b ^ n \<le> m"
  shows "n \<le> log b m"
proof -
   from assms have "0 < m"
     by (metis less_trans zero_less_power less_le_trans zero_less_one)
   have "n = log b (b ^ n)"
     using assms(1) by (simp add: log_nat_power)
   also have "\<dots> \<le> log b m"
     using assms \<open>0 < m\<close> by simp
   finally show ?thesis .
qed

lemma le_log2_of_power: "2 ^ n \<le> m \<Longrightarrow> n \<le> log 2 m"
  for m n :: nat
  using le_log_of_power[of 2] by simp

lemma log_base_change: "0 < a \<Longrightarrow> a \<noteq> 1 \<Longrightarrow> log b x = log a x / log a b"
  by (simp add: log_def)

lemma log_base_pow: "0 < a \<Longrightarrow> log (a ^ n) x = log a x / n"
  by (simp add: log_def ln_realpow)

lemma log_base_powr: "a \<noteq> 0 \<Longrightarrow> log (a powr b) x = log a x / b"
  by (simp add: log_def ln_powr)

lemma log_base_root: "n > 0 \<Longrightarrow> b > 0 \<Longrightarrow> log (root n b) x = n * (log b x)"
  by (simp add: log_def ln_root)

lemma ln_bound: "1 \<le> x \<Longrightarrow> ln x \<le> x"
  for x :: real
  apply (subgoal_tac "ln (1 + (x - 1)) \<le> x - 1")
   apply simp
  apply (rule ln_add_one_self_le_self)
  apply simp
  done

lemma powr_mono: "a \<le> b \<Longrightarrow> 1 \<le> x \<Longrightarrow> x powr a \<le> x powr b"
  for x :: real
  apply (cases "x = 1")
   apply simp
  apply (cases "a = b")
   apply simp
  apply (rule order_less_imp_le)
  apply (rule powr_less_mono)
   apply auto
  done

lemma ge_one_powr_ge_zero: "1 \<le> x \<Longrightarrow> 0 \<le> a \<Longrightarrow> 1 \<le> x powr a"
  for x :: real
  using powr_mono by fastforce

lemma powr_less_mono2: "0 < a \<Longrightarrow> 0 \<le> x \<Longrightarrow> x < y \<Longrightarrow> x powr a < y powr a"
  for x :: real
  by (simp add: powr_def)

lemma powr_less_mono2_neg: "a < 0 \<Longrightarrow> 0 < x \<Longrightarrow> x < y \<Longrightarrow> y powr a < x powr a"
  for x :: real
  by (simp add: powr_def)

lemma powr_mono2: "0 \<le> a \<Longrightarrow> 0 \<le> x \<Longrightarrow> x \<le> y \<Longrightarrow> x powr a \<le> y powr a"
  for x :: real
  apply (case_tac "a = 0")
   apply simp
  apply (case_tac "x = y")
   apply simp
  apply (metis dual_order.strict_iff_order powr_less_mono2)
  done

lemma powr_mono2':
  fixes a x y :: real
  assumes "a \<le> 0" "x > 0" "x \<le> y"
  shows "x powr a \<ge> y powr a"
proof -
  from assms have "x powr - a \<le> y powr - a"
    by (intro powr_mono2) simp_all
  with assms show ?thesis
    by (auto simp add: powr_minus field_simps)
qed

lemma powr_inj: "0 < a \<Longrightarrow> a \<noteq> 1 \<Longrightarrow> a powr x = a powr y \<longleftrightarrow> x = y"
  for x :: real
  unfolding powr_def exp_inj_iff by simp

lemma powr_half_sqrt: "0 \<le> x \<Longrightarrow> x powr (1/2) = sqrt x"
  by (simp add: powr_def root_powr_inverse sqrt_def)

lemma ln_powr_bound: "1 \<le> x \<Longrightarrow> 0 < a \<Longrightarrow> ln x \<le> (x powr a) / a"
  for x :: real
  by (metis exp_gt_zero linear ln_eq_zero_iff ln_exp ln_less_self ln_powr mult.commute
      mult_imp_le_div_pos not_less powr_gt_zero)

lemma ln_powr_bound2:
  fixes x :: real
  assumes "1 < x" and "0 < a"
  shows "(ln x) powr a \<le> (a powr a) * x"
proof -
  from assms have "ln x \<le> (x powr (1 / a)) / (1 / a)"
    by (metis less_eq_real_def ln_powr_bound zero_less_divide_1_iff)
  also have "\<dots> = a * (x powr (1 / a))"
    by simp
  finally have "(ln x) powr a \<le> (a * (x powr (1 / a))) powr a"
    by (metis assms less_imp_le ln_gt_zero powr_mono2)
  also have "\<dots> = (a powr a) * ((x powr (1 / a)) powr a)"
    using assms powr_mult by auto
  also have "(x powr (1 / a)) powr a = x powr ((1 / a) * a)"
    by (rule powr_powr)
  also have "\<dots> = x" using assms
    by auto
  finally show ?thesis .
qed

lemma tendsto_powr:
  fixes a b :: real
  assumes f: "(f \<longlongrightarrow> a) F"
    and g: "(g \<longlongrightarrow> b) F"
    and a: "a \<noteq> 0"
  shows "((\<lambda>x. f x powr g x) \<longlongrightarrow> a powr b) F"
  unfolding powr_def
proof (rule filterlim_If)
  from f show "((\<lambda>x. 0) \<longlongrightarrow> (if a = 0 then 0 else exp (b * ln a))) (inf F (principal {x. f x = 0}))"
    by simp (auto simp: filterlim_iff eventually_inf_principal elim: eventually_mono dest: t1_space_nhds)
  from f g a show "((\<lambda>x. exp (g x * ln (f x))) \<longlongrightarrow> (if a = 0 then 0 else exp (b * ln a)))
      (inf F (principal {x. f x \<noteq> 0}))"
    by (auto intro!: tendsto_intros intro: tendsto_mono inf_le1)
qed

lemma tendsto_powr'[tendsto_intros]:
  fixes a :: real
  assumes f: "(f \<longlongrightarrow> a) F"
    and g: "(g \<longlongrightarrow> b) F"
    and a: "a \<noteq> 0 \<or> (b > 0 \<and> eventually (\<lambda>x. f x \<ge> 0) F)"
  shows "((\<lambda>x. f x powr g x) \<longlongrightarrow> a powr b) F"
proof -
  from a consider "a \<noteq> 0" | "a = 0" "b > 0" "eventually (\<lambda>x. f x \<ge> 0) F"
    by auto
  then show ?thesis
  proof cases
    case 1
    with f g show ?thesis by (rule tendsto_powr)
  next
    case 2
    have "((\<lambda>x. if f x = 0 then 0 else exp (g x * ln (f x))) \<longlongrightarrow> 0) F"
    proof (intro filterlim_If)
      have "filterlim f (principal {0<..}) (inf F (principal {z. f z \<noteq> 0}))"
        using \<open>eventually (\<lambda>x. f x \<ge> 0) F\<close>
        by (auto simp add: filterlim_iff eventually_inf_principal
            eventually_principal elim: eventually_mono)
      moreover have "filterlim f (nhds a) (inf F (principal {z. f z \<noteq> 0}))"
        by (rule tendsto_mono[OF _ f]) simp_all
      ultimately have f: "filterlim f (at_right 0) (inf F (principal {x. f x \<noteq> 0}))"
        by (simp add: at_within_def filterlim_inf \<open>a = 0\<close>)
      have g: "(g \<longlongrightarrow> b) (inf F (principal {z. f z \<noteq> 0}))"
        by (rule tendsto_mono[OF _ g]) simp_all
      show "((\<lambda>x. exp (g x * ln (f x))) \<longlongrightarrow> 0) (inf F (principal {x. f x \<noteq> 0}))"
        by (rule filterlim_compose[OF exp_at_bot] filterlim_tendsto_pos_mult_at_bot
                 filterlim_compose[OF ln_at_0] f g \<open>b > 0\<close>)+
    qed simp_all
    with \<open>a = 0\<close> show ?thesis
      by (simp add: powr_def)
  qed
qed

lemma continuous_powr:
  assumes "continuous F f"
    and "continuous F g"
    and "f (Lim F (\<lambda>x. x)) \<noteq> 0"
  shows "continuous F (\<lambda>x. (f x) powr (g x :: real))"
  using assms unfolding continuous_def by (rule tendsto_powr)

lemma continuous_at_within_powr[continuous_intros]:
  fixes f g :: "_ \<Rightarrow> real"
  assumes "continuous (at a within s) f"
    and "continuous (at a within s) g"
    and "f a \<noteq> 0"
  shows "continuous (at a within s) (\<lambda>x. (f x) powr (g x))"
  using assms unfolding continuous_within by (rule tendsto_powr)

lemma isCont_powr[continuous_intros, simp]:
  fixes f g :: "_ \<Rightarrow> real"
  assumes "isCont f a" "isCont g a" "f a \<noteq> 0"
  shows "isCont (\<lambda>x. (f x) powr g x) a"
  using assms unfolding continuous_at by (rule tendsto_powr)

lemma continuous_on_powr[continuous_intros]:
  fixes f g :: "_ \<Rightarrow> real"
  assumes "continuous_on s f" "continuous_on s g" and "\<forall>x\<in>s. f x \<noteq> 0"
  shows "continuous_on s (\<lambda>x. (f x) powr (g x))"
  using assms unfolding continuous_on_def by (fast intro: tendsto_powr)

lemma tendsto_powr2:
  fixes a :: real
  assumes f: "(f \<longlongrightarrow> a) F"
    and g: "(g \<longlongrightarrow> b) F"
    and "\<forall>\<^sub>F x in F. 0 \<le> f x"
    and b: "0 < b"
  shows "((\<lambda>x. f x powr g x) \<longlongrightarrow> a powr b) F"
  using tendsto_powr'[of f a F g b] assms by auto

lemma DERIV_powr:
  fixes r :: real
  assumes g: "DERIV g x :> m"
    and pos: "g x > 0"
    and f: "DERIV f x :> r"
  shows "DERIV (\<lambda>x. g x powr f x) x :> (g x powr f x) * (r * ln (g x) + m * f x / g x)"
proof -
  have "DERIV (\<lambda>x. exp (f x * ln (g x))) x :> (g x powr f x) * (r * ln (g x) + m * f x / g x)"
    using pos
    by (auto intro!: derivative_eq_intros g pos f simp: powr_def field_simps exp_diff)
  then show ?thesis
  proof (rule DERIV_cong_ev[OF refl _ refl, THEN iffD1, rotated])
    from DERIV_isCont[OF g] pos have "\<forall>\<^sub>F x in at x. 0 < g x"
      unfolding isCont_def by (rule order_tendstoD(1))
    with pos show "\<forall>\<^sub>F x in nhds x. exp (f x * ln (g x)) = g x powr f x"
      by (auto simp: eventually_at_filter powr_def elim: eventually_mono)
  qed
qed

lemma DERIV_fun_powr:
  fixes r :: real
  assumes g: "DERIV g x :> m"
    and pos: "g x > 0"
  shows "DERIV (\<lambda>x. (g x) powr r) x :> r * (g x) powr (r - of_nat 1) * m"
  using DERIV_powr[OF g pos DERIV_const, of r] pos
  by (simp add: powr_divide2[symmetric] field_simps)

lemma has_real_derivative_powr:
  assumes "z > 0"
  shows "((\<lambda>z. z powr r) has_real_derivative r * z powr (r - 1)) (at z)"
proof (subst DERIV_cong_ev[OF refl _ refl])
  from assms have "eventually (\<lambda>z. z \<noteq> 0) (nhds z)"
    by (intro t1_space_nhds) auto
  then show "eventually (\<lambda>z. z powr r = exp (r * ln z)) (nhds z)"
    unfolding powr_def by eventually_elim simp
  from assms show "((\<lambda>z. exp (r * ln z)) has_real_derivative r * z powr (r - 1)) (at z)"
    by (auto intro!: derivative_eq_intros simp: powr_def field_simps exp_diff)
qed

declare has_real_derivative_powr[THEN DERIV_chain2, derivative_intros]

lemma tendsto_zero_powrI:
  assumes "(f \<longlongrightarrow> (0::real)) F" "(g \<longlongrightarrow> b) F" "\<forall>\<^sub>F x in F. 0 \<le> f x" "0 < b"
  shows "((\<lambda>x. f x powr g x) \<longlongrightarrow> 0) F"
  using tendsto_powr2[OF assms] by simp

lemma continuous_on_powr':
  fixes f g :: "_ \<Rightarrow> real"
  assumes "continuous_on s f" "continuous_on s g"
    and "\<forall>x\<in>s. f x \<ge> 0 \<and> (f x = 0 \<longrightarrow> g x > 0)"
  shows "continuous_on s (\<lambda>x. (f x) powr (g x))"
  unfolding continuous_on_def
proof
  fix x
  assume x: "x \<in> s"
  from assms x show "((\<lambda>x. f x powr g x) \<longlongrightarrow> f x powr g x) (at x within s)"
  proof (cases "f x = 0")
    case True
    from assms(3) have "eventually (\<lambda>x. f x \<ge> 0) (at x within s)"
      by (auto simp: at_within_def eventually_inf_principal)
    with True x assms show ?thesis
      by (auto intro!: tendsto_zero_powrI[of f _ g "g x"] simp: continuous_on_def)
  next
    case False
    with assms x show ?thesis
      by (auto intro!: tendsto_powr' simp: continuous_on_def)
  qed
qed

lemma tendsto_neg_powr:
  assumes "s < 0"
    and f: "LIM x F. f x :> at_top"
  shows "((\<lambda>x. f x powr s) \<longlongrightarrow> (0::real)) F"
proof -
  have "((\<lambda>x. exp (s * ln (f x))) \<longlongrightarrow> (0::real)) F" (is "?X")
    by (auto intro!: filterlim_compose[OF exp_at_bot] filterlim_compose[OF ln_at_top]
        filterlim_tendsto_neg_mult_at_bot assms)
  also have "?X \<longleftrightarrow> ((\<lambda>x. f x powr s) \<longlongrightarrow> (0::real)) F"
    using f filterlim_at_top_dense[of f F]
    by (intro filterlim_cong[OF refl refl]) (auto simp: neq_iff powr_def elim: eventually_mono)
  finally show ?thesis .
qed

lemma tendsto_exp_limit_at_right: "((\<lambda>y. (1 + x * y) powr (1 / y)) \<longlongrightarrow> exp x) (at_right 0)"
  for x :: real
proof (cases "x = 0")
  case True
  then show ?thesis by simp
next
  case False
  have "((\<lambda>y. ln (1 + x * y)::real) has_real_derivative 1 * x) (at 0)"
    by (auto intro!: derivative_eq_intros)
  then have "((\<lambda>y. ln (1 + x * y) / y) \<longlongrightarrow> x) (at 0)"
    by (auto simp add: has_field_derivative_def field_has_derivative_at)
  then have *: "((\<lambda>y. exp (ln (1 + x * y) / y)) \<longlongrightarrow> exp x) (at 0)"
    by (rule tendsto_intros)
  then show ?thesis
  proof (rule filterlim_mono_eventually)
    show "eventually (\<lambda>xa. exp (ln (1 + x * xa) / xa) = (1 + x * xa) powr (1 / xa)) (at_right 0)"
      unfolding eventually_at_right[OF zero_less_one]
      using False
      apply (intro exI[of _ "1 / \<bar>x\<bar>"])
      apply (auto simp: field_simps powr_def abs_if)
      apply (metis add_less_same_cancel1 mult_less_0_iff not_less_iff_gr_or_eq zero_less_one)
      done
  qed (simp_all add: at_eq_sup_left_right)
qed

lemma tendsto_exp_limit_at_top: "((\<lambda>y. (1 + x / y) powr y) \<longlongrightarrow> exp x) at_top"
  for x :: real
  apply (subst filterlim_at_top_to_right)
  apply (simp add: inverse_eq_divide)
  apply (rule tendsto_exp_limit_at_right)
  done

lemma tendsto_exp_limit_sequentially: "(\<lambda>n. (1 + x / n) ^ n) \<longlonglongrightarrow> exp x"
  for x :: real
proof (rule filterlim_mono_eventually)
  from reals_Archimedean2 [of "\<bar>x\<bar>"] obtain n :: nat where *: "real n > \<bar>x\<bar>" ..
  then have "eventually (\<lambda>n :: nat. 0 < 1 + x / real n) at_top"
    apply (intro eventually_sequentiallyI [of n])
    apply (cases "x \<ge> 0")
     apply (rule add_pos_nonneg)
      apply (auto intro: divide_nonneg_nonneg)
    apply (subgoal_tac "x / real xa > - 1")
     apply (auto simp add: field_simps)
    done
  then show "eventually (\<lambda>n. (1 + x / n) powr n = (1 + x / n) ^ n) at_top"
    by (rule eventually_mono) (erule powr_realpow)
  show "(\<lambda>n. (1 + x / real n) powr real n) \<longlonglongrightarrow> exp x"
    by (rule filterlim_compose [OF tendsto_exp_limit_at_top filterlim_real_sequentially])
qed auto


subsection \<open>Sine and Cosine\<close>

definition sin_coeff :: "nat \<Rightarrow> real"
  where "sin_coeff = (\<lambda>n. if even n then 0 else (- 1) ^ ((n - Suc 0) div 2) / (fact n))"

definition cos_coeff :: "nat \<Rightarrow> real"
  where "cos_coeff = (\<lambda>n. if even n then ((- 1) ^ (n div 2)) / (fact n) else 0)"

definition sin :: "'a \<Rightarrow> 'a::{real_normed_algebra_1,banach}"
  where "sin = (\<lambda>x. \<Sum>n. sin_coeff n *\<^sub>R x^n)"

definition cos :: "'a \<Rightarrow> 'a::{real_normed_algebra_1,banach}"
  where "cos = (\<lambda>x. \<Sum>n. cos_coeff n *\<^sub>R x^n)"

lemma sin_coeff_0 [simp]: "sin_coeff 0 = 0"
  unfolding sin_coeff_def by simp

lemma cos_coeff_0 [simp]: "cos_coeff 0 = 1"
  unfolding cos_coeff_def by simp

lemma sin_coeff_Suc: "sin_coeff (Suc n) = cos_coeff n / real (Suc n)"
  unfolding cos_coeff_def sin_coeff_def
  by (simp del: mult_Suc)

lemma cos_coeff_Suc: "cos_coeff (Suc n) = - sin_coeff n / real (Suc n)"
  unfolding cos_coeff_def sin_coeff_def
  by (simp del: mult_Suc) (auto elim: oddE)

lemma summable_norm_sin: "summable (\<lambda>n. norm (sin_coeff n *\<^sub>R x^n))"
  for x :: "'a::{real_normed_algebra_1,banach}"
  unfolding sin_coeff_def
  apply (rule summable_comparison_test [OF _ summable_norm_exp [where x=x]])
  apply (auto simp: divide_inverse abs_mult power_abs [symmetric] zero_le_mult_iff)
  done

lemma summable_norm_cos: "summable (\<lambda>n. norm (cos_coeff n *\<^sub>R x^n))"
  for x :: "'a::{real_normed_algebra_1,banach}"
  unfolding cos_coeff_def
  apply (rule summable_comparison_test [OF _ summable_norm_exp [where x=x]])
  apply (auto simp: divide_inverse abs_mult power_abs [symmetric] zero_le_mult_iff)
  done

lemma sin_converges: "(\<lambda>n. sin_coeff n *\<^sub>R x^n) sums sin x"
  unfolding sin_def
  by (metis (full_types) summable_norm_cancel summable_norm_sin summable_sums)

lemma cos_converges: "(\<lambda>n. cos_coeff n *\<^sub>R x^n) sums cos x"
  unfolding cos_def
  by (metis (full_types) summable_norm_cancel summable_norm_cos summable_sums)

lemma sin_of_real: "sin (of_real x) = of_real (sin x)"
  for x :: real
proof -
  have "(\<lambda>n. of_real (sin_coeff n *\<^sub>R  x^n)) = (\<lambda>n. sin_coeff n *\<^sub>R  (of_real x)^n)"
  proof
    show "of_real (sin_coeff n *\<^sub>R  x^n) = sin_coeff n *\<^sub>R of_real x^n" for n
      by (simp add: scaleR_conv_of_real)
  qed
  also have "\<dots> sums (sin (of_real x))"
    by (rule sin_converges)
  finally have "(\<lambda>n. of_real (sin_coeff n *\<^sub>R x^n)) sums (sin (of_real x))" .
  then show ?thesis
    using sums_unique2 sums_of_real [OF sin_converges]
    by blast
qed

corollary sin_in_Reals [simp]: "z \<in> \<real> \<Longrightarrow> sin z \<in> \<real>"
  by (metis Reals_cases Reals_of_real sin_of_real)

lemma cos_of_real: "cos (of_real x) = of_real (cos x)"
  for x :: real
proof -
  have "(\<lambda>n. of_real (cos_coeff n *\<^sub>R  x^n)) = (\<lambda>n. cos_coeff n *\<^sub>R  (of_real x)^n)"
  proof
    show "of_real (cos_coeff n *\<^sub>R  x^n) = cos_coeff n *\<^sub>R of_real x^n" for n
      by (simp add: scaleR_conv_of_real)
  qed
  also have "\<dots> sums (cos (of_real x))"
    by (rule cos_converges)
  finally have "(\<lambda>n. of_real (cos_coeff n *\<^sub>R x^n)) sums (cos (of_real x))" .
  then show ?thesis
    using sums_unique2 sums_of_real [OF cos_converges]
    by blast
qed

corollary cos_in_Reals [simp]: "z \<in> \<real> \<Longrightarrow> cos z \<in> \<real>"
  by (metis Reals_cases Reals_of_real cos_of_real)

lemma diffs_sin_coeff: "diffs sin_coeff = cos_coeff"
  by (simp add: diffs_def sin_coeff_Suc del: of_nat_Suc)

lemma diffs_cos_coeff: "diffs cos_coeff = (\<lambda>n. - sin_coeff n)"
  by (simp add: diffs_def cos_coeff_Suc del: of_nat_Suc)

text \<open>Now at last we can get the derivatives of exp, sin and cos.\<close>

lemma DERIV_sin [simp]: "DERIV sin x :> cos x"
  for x :: "'a::{real_normed_field,banach}"
  unfolding sin_def cos_def scaleR_conv_of_real
  apply (rule DERIV_cong)
   apply (rule termdiffs [where K="of_real (norm x) + 1 :: 'a"])
      apply (simp_all add: norm_less_p1 diffs_of_real diffs_sin_coeff diffs_cos_coeff
              summable_minus_iff scaleR_conv_of_real [symmetric]
              summable_norm_sin [THEN summable_norm_cancel]
              summable_norm_cos [THEN summable_norm_cancel])
  done

declare DERIV_sin[THEN DERIV_chain2, derivative_intros]
  and DERIV_sin[THEN DERIV_chain2, unfolded has_field_derivative_def, derivative_intros]

lemma DERIV_cos [simp]: "DERIV cos x :> - sin x"
  for x :: "'a::{real_normed_field,banach}"
  unfolding sin_def cos_def scaleR_conv_of_real
  apply (rule DERIV_cong)
   apply (rule termdiffs [where K="of_real (norm x) + 1 :: 'a"])
      apply (simp_all add: norm_less_p1 diffs_of_real diffs_minus suminf_minus
              diffs_sin_coeff diffs_cos_coeff
              summable_minus_iff scaleR_conv_of_real [symmetric]
              summable_norm_sin [THEN summable_norm_cancel]
              summable_norm_cos [THEN summable_norm_cancel])
  done

declare DERIV_cos[THEN DERIV_chain2, derivative_intros]
  and DERIV_cos[THEN DERIV_chain2, unfolded has_field_derivative_def, derivative_intros]

lemma isCont_sin: "isCont sin x"
  for x :: "'a::{real_normed_field,banach}"
  by (rule DERIV_sin [THEN DERIV_isCont])

lemma isCont_cos: "isCont cos x"
  for x :: "'a::{real_normed_field,banach}"
  by (rule DERIV_cos [THEN DERIV_isCont])

lemma isCont_sin' [simp]: "isCont f a \<Longrightarrow> isCont (\<lambda>x. sin (f x)) a"
  for f :: "_ \<Rightarrow> 'a::{real_normed_field,banach}"
  by (rule isCont_o2 [OF _ isCont_sin])

(* FIXME a context for f would be better *)

lemma isCont_cos' [simp]: "isCont f a \<Longrightarrow> isCont (\<lambda>x. cos (f x)) a"
  for f :: "_ \<Rightarrow> 'a::{real_normed_field,banach}"
  by (rule isCont_o2 [OF _ isCont_cos])

lemma tendsto_sin [tendsto_intros]: "(f \<longlongrightarrow> a) F \<Longrightarrow> ((\<lambda>x. sin (f x)) \<longlongrightarrow> sin a) F"
  for f :: "_ \<Rightarrow> 'a::{real_normed_field,banach}"
  by (rule isCont_tendsto_compose [OF isCont_sin])

lemma tendsto_cos [tendsto_intros]: "(f \<longlongrightarrow> a) F \<Longrightarrow> ((\<lambda>x. cos (f x)) \<longlongrightarrow> cos a) F"
  for f :: "_ \<Rightarrow> 'a::{real_normed_field,banach}"
  by (rule isCont_tendsto_compose [OF isCont_cos])

lemma continuous_sin [continuous_intros]: "continuous F f \<Longrightarrow> continuous F (\<lambda>x. sin (f x))"
  for f :: "_ \<Rightarrow> 'a::{real_normed_field,banach}"
  unfolding continuous_def by (rule tendsto_sin)

lemma continuous_on_sin [continuous_intros]: "continuous_on s f \<Longrightarrow> continuous_on s (\<lambda>x. sin (f x))"
  for f :: "_ \<Rightarrow> 'a::{real_normed_field,banach}"
  unfolding continuous_on_def by (auto intro: tendsto_sin)

lemma continuous_within_sin: "continuous (at z within s) sin"
  for z :: "'a::{real_normed_field,banach}"
  by (simp add: continuous_within tendsto_sin)

lemma continuous_cos [continuous_intros]: "continuous F f \<Longrightarrow> continuous F (\<lambda>x. cos (f x))"
  for f :: "_ \<Rightarrow> 'a::{real_normed_field,banach}"
  unfolding continuous_def by (rule tendsto_cos)

lemma continuous_on_cos [continuous_intros]: "continuous_on s f \<Longrightarrow> continuous_on s (\<lambda>x. cos (f x))"
  for f :: "_ \<Rightarrow> 'a::{real_normed_field,banach}"
  unfolding continuous_on_def by (auto intro: tendsto_cos)

lemma continuous_within_cos: "continuous (at z within s) cos"
  for z :: "'a::{real_normed_field,banach}"
  by (simp add: continuous_within tendsto_cos)


subsection \<open>Properties of Sine and Cosine\<close>

lemma sin_zero [simp]: "sin 0 = 0"
  by (simp add: sin_def sin_coeff_def scaleR_conv_of_real)

lemma cos_zero [simp]: "cos 0 = 1"
  by (simp add: cos_def cos_coeff_def scaleR_conv_of_real)

lemma DERIV_fun_sin: "DERIV g x :> m \<Longrightarrow> DERIV (\<lambda>x. sin (g x)) x :> cos (g x) * m"
  by (auto intro!: derivative_intros)

lemma DERIV_fun_cos: "DERIV g x :> m \<Longrightarrow> DERIV (\<lambda>x. cos(g x)) x :> - sin (g x) * m"
  by (auto intro!: derivative_eq_intros)


subsection \<open>Deriving the Addition Formulas\<close>

text \<open>The product of two cosine series.\<close>
lemma cos_x_cos_y:
  fixes x :: "'a::{real_normed_field,banach}"
  shows
    "(\<lambda>p. \<Sum>n\<le>p.
        if even p \<and> even n
        then ((-1) ^ (p div 2) * (p choose n) / (fact p)) *\<^sub>R (x^n) * y^(p-n) else 0)
      sums (cos x * cos y)"
proof -
  have "(cos_coeff n * cos_coeff (p - n)) *\<^sub>R (x^n * y^(p - n)) =
    (if even p \<and> even n then ((-1) ^ (p div 2) * (p choose n) / (fact p)) *\<^sub>R (x^n) * y^(p - n)
     else 0)"
    if "n \<le> p" for n p :: nat
  proof -
    from that have *: "even n \<Longrightarrow> even p \<Longrightarrow>
        (-1) ^ (n div 2) * (-1) ^ ((p - n) div 2) = (-1 :: real) ^ (p div 2)"
      by (metis div_add power_add le_add_diff_inverse odd_add)
    with that show ?thesis
      by (auto simp: algebra_simps cos_coeff_def binomial_fact)
  qed
  then have "(\<lambda>p. \<Sum>n\<le>p. if even p \<and> even n
                  then ((-1) ^ (p div 2) * (p choose n) / (fact p)) *\<^sub>R (x^n) * y^(p-n) else 0) =
             (\<lambda>p. \<Sum>n\<le>p. (cos_coeff n * cos_coeff (p - n)) *\<^sub>R (x^n * y^(p-n)))"
    by simp
  also have "\<dots> = (\<lambda>p. \<Sum>n\<le>p. (cos_coeff n *\<^sub>R x^n) * (cos_coeff (p - n) *\<^sub>R y^(p-n)))"
    by (simp add: algebra_simps)
  also have "\<dots> sums (cos x * cos y)"
    using summable_norm_cos
    by (auto simp: cos_def scaleR_conv_of_real intro!: Cauchy_product_sums)
  finally show ?thesis .
qed

text \<open>The product of two sine series.\<close>
lemma sin_x_sin_y:
  fixes x :: "'a::{real_normed_field,banach}"
  shows
    "(\<lambda>p. \<Sum>n\<le>p.
        if even p \<and> odd n
        then - ((-1) ^ (p div 2) * (p choose n) / (fact p)) *\<^sub>R (x^n) * y^(p-n)
        else 0)
      sums (sin x * sin y)"
proof -
  have "(sin_coeff n * sin_coeff (p - n)) *\<^sub>R (x^n * y^(p-n)) =
    (if even p \<and> odd n
     then -((-1) ^ (p div 2) * (p choose n) / (fact p)) *\<^sub>R (x^n) * y^(p-n)
     else 0)"
    if "n \<le> p" for n p :: nat
  proof -
    have "(-1) ^ ((n - Suc 0) div 2) * (-1) ^ ((p - Suc n) div 2) = - ((-1 :: real) ^ (p div 2))"
      if np: "odd n" "even p"
    proof -
      from \<open>n \<le> p\<close> np have *: "n - Suc 0 + (p - Suc n) = p - Suc (Suc 0)" "Suc (Suc 0) \<le> p"
        by arith+
      have "(p - Suc (Suc 0)) div 2 = p div 2 - Suc 0"
        by simp
      with \<open>n \<le> p\<close> np * show ?thesis
        apply (simp add: power_add [symmetric] div_add [symmetric] del: div_add)
        apply (metis (no_types) One_nat_def Suc_1 le_div_geq minus_minus
            mult.left_neutral mult_minus_left power.simps(2) zero_less_Suc)
        done
    qed
    then show ?thesis
      using \<open>n\<le>p\<close> by (auto simp: algebra_simps sin_coeff_def binomial_fact)
  qed
  then have "(\<lambda>p. \<Sum>n\<le>p. if even p \<and> odd n
               then - ((-1) ^ (p div 2) * (p choose n) / (fact p)) *\<^sub>R (x^n) * y^(p-n) else 0) =
             (\<lambda>p. \<Sum>n\<le>p. (sin_coeff n * sin_coeff (p - n)) *\<^sub>R (x^n * y^(p-n)))"
    by simp
  also have "\<dots> = (\<lambda>p. \<Sum>n\<le>p. (sin_coeff n *\<^sub>R x^n) * (sin_coeff (p - n) *\<^sub>R y^(p-n)))"
    by (simp add: algebra_simps)
  also have "\<dots> sums (sin x * sin y)"
    using summable_norm_sin
    by (auto simp: sin_def scaleR_conv_of_real intro!: Cauchy_product_sums)
  finally show ?thesis .
qed

lemma sums_cos_x_plus_y:
  fixes x :: "'a::{real_normed_field,banach}"
  shows
    "(\<lambda>p. \<Sum>n\<le>p.
        if even p
        then ((-1) ^ (p div 2) * (p choose n) / (fact p)) *\<^sub>R (x^n) * y^(p-n)
        else 0)
      sums cos (x + y)"
proof -
  have
    "(\<Sum>n\<le>p.
      if even p then ((-1) ^ (p div 2) * (p choose n) / (fact p)) *\<^sub>R (x^n) * y^(p-n)
      else 0) = cos_coeff p *\<^sub>R ((x + y) ^ p)"
    for p :: nat
  proof -
    have
      "(\<Sum>n\<le>p. if even p then ((-1) ^ (p div 2) * (p choose n) / (fact p)) *\<^sub>R (x^n) * y^(p-n) else 0) =
       (if even p then \<Sum>n\<le>p. ((-1) ^ (p div 2) * (p choose n) / (fact p)) *\<^sub>R (x^n) * y^(p-n) else 0)"
      by simp
    also have "\<dots> =
       (if even p
        then of_real ((-1) ^ (p div 2) / (fact p)) * (\<Sum>n\<le>p. (p choose n) *\<^sub>R (x^n) * y^(p-n))
        else 0)"
      by (auto simp: sum_distrib_left field_simps scaleR_conv_of_real nonzero_of_real_divide)
    also have "\<dots> = cos_coeff p *\<^sub>R ((x + y) ^ p)"
      by (simp add: cos_coeff_def binomial_ring [of x y]  scaleR_conv_of_real atLeast0AtMost)
    finally show ?thesis .
  qed
  then have
    "(\<lambda>p. \<Sum>n\<le>p.
        if even p
        then ((-1) ^ (p div 2) * (p choose n) / (fact p)) *\<^sub>R (x^n) * y^(p-n)
        else 0) = (\<lambda>p. cos_coeff p *\<^sub>R ((x+y)^p))"
    by simp
   also have "\<dots> sums cos (x + y)"
    by (rule cos_converges)
   finally show ?thesis .
qed

theorem cos_add:
  fixes x :: "'a::{real_normed_field,banach}"
  shows "cos (x + y) = cos x * cos y - sin x * sin y"
proof -
  have
    "(if even p \<and> even n
      then ((- 1) ^ (p div 2) * int (p choose n) / (fact p)) *\<^sub>R (x^n) * y^(p-n) else 0) -
     (if even p \<and> odd n
      then - ((- 1) ^ (p div 2) * int (p choose n) / (fact p)) *\<^sub>R (x^n) * y^(p-n) else 0) =
     (if even p then ((-1) ^ (p div 2) * (p choose n) / (fact p)) *\<^sub>R (x^n) * y^(p-n) else 0)"
    if "n \<le> p" for n p :: nat
    by simp
  then have
    "(\<lambda>p. \<Sum>n\<le>p. (if even p then ((-1) ^ (p div 2) * (p choose n) / (fact p)) *\<^sub>R (x^n) * y^(p-n) else 0))
      sums (cos x * cos y - sin x * sin y)"
    using sums_diff [OF cos_x_cos_y [of x y] sin_x_sin_y [of x y]]
    by (simp add: sum_subtractf [symmetric])
  then show ?thesis
    by (blast intro: sums_cos_x_plus_y sums_unique2)
qed

lemma sin_minus_converges: "(\<lambda>n. - (sin_coeff n *\<^sub>R (-x)^n)) sums sin x"
proof -
  have [simp]: "\<And>n. - (sin_coeff n *\<^sub>R (-x)^n) = (sin_coeff n *\<^sub>R x^n)"
    by (auto simp: sin_coeff_def elim!: oddE)
  show ?thesis
    by (simp add: sin_def summable_norm_sin [THEN summable_norm_cancel, THEN summable_sums])
qed

lemma sin_minus [simp]: "sin (- x) = - sin x"
  for x :: "'a::{real_normed_algebra_1,banach}"
  using sin_minus_converges [of x]
  by (auto simp: sin_def summable_norm_sin [THEN summable_norm_cancel]
      suminf_minus sums_iff equation_minus_iff)

lemma cos_minus_converges: "(\<lambda>n. (cos_coeff n *\<^sub>R (-x)^n)) sums cos x"
proof -
  have [simp]: "\<And>n. (cos_coeff n *\<^sub>R (-x)^n) = (cos_coeff n *\<^sub>R x^n)"
    by (auto simp: Transcendental.cos_coeff_def elim!: evenE)
  show ?thesis
    by (simp add: cos_def summable_norm_cos [THEN summable_norm_cancel, THEN summable_sums])
qed

lemma cos_minus [simp]: "cos (-x) = cos x"
  for x :: "'a::{real_normed_algebra_1,banach}"
  using cos_minus_converges [of x]
  by (simp add: cos_def summable_norm_cos [THEN summable_norm_cancel]
      suminf_minus sums_iff equation_minus_iff)

lemma sin_cos_squared_add [simp]: "(sin x)\<^sup>2 + (cos x)\<^sup>2 = 1"
  for x :: "'a::{real_normed_field,banach}"
  using cos_add [of x "-x"]
  by (simp add: power2_eq_square algebra_simps)

lemma sin_cos_squared_add2 [simp]: "(cos x)\<^sup>2 + (sin x)\<^sup>2 = 1"
  for x :: "'a::{real_normed_field,banach}"
  by (subst add.commute, rule sin_cos_squared_add)

lemma sin_cos_squared_add3 [simp]: "cos x * cos x + sin x * sin x = 1"
  for x :: "'a::{real_normed_field,banach}"
  using sin_cos_squared_add2 [unfolded power2_eq_square] .

lemma sin_squared_eq: "(sin x)\<^sup>2 = 1 - (cos x)\<^sup>2"
  for x :: "'a::{real_normed_field,banach}"
  unfolding eq_diff_eq by (rule sin_cos_squared_add)

lemma cos_squared_eq: "(cos x)\<^sup>2 = 1 - (sin x)\<^sup>2"
  for x :: "'a::{real_normed_field,banach}"
  unfolding eq_diff_eq by (rule sin_cos_squared_add2)

lemma abs_sin_le_one [simp]: "\<bar>sin x\<bar> \<le> 1"
  for x :: real
  by (rule power2_le_imp_le) (simp_all add: sin_squared_eq)

lemma sin_ge_minus_one [simp]: "- 1 \<le> sin x"
  for x :: real
  using abs_sin_le_one [of x] by (simp add: abs_le_iff)

lemma sin_le_one [simp]: "sin x \<le> 1"
  for x :: real
  using abs_sin_le_one [of x] by (simp add: abs_le_iff)

lemma abs_cos_le_one [simp]: "\<bar>cos x\<bar> \<le> 1"
  for x :: real
  by (rule power2_le_imp_le) (simp_all add: cos_squared_eq)

lemma cos_ge_minus_one [simp]: "- 1 \<le> cos x"
  for x :: real
  using abs_cos_le_one [of x] by (simp add: abs_le_iff)

lemma cos_le_one [simp]: "cos x \<le> 1"
  for x :: real
  using abs_cos_le_one [of x] by (simp add: abs_le_iff)

lemma cos_diff: "cos (x - y) = cos x * cos y + sin x * sin y"
  for x :: "'a::{real_normed_field,banach}"
  using cos_add [of x "- y"] by simp

lemma cos_double: "cos(2*x) = (cos x)\<^sup>2 - (sin x)\<^sup>2"
  for x :: "'a::{real_normed_field,banach}"
  using cos_add [where x=x and y=x] by (simp add: power2_eq_square)

lemma sin_cos_le1: "\<bar>sin x * sin y + cos x * cos y\<bar> \<le> 1"
  for x :: real
  using cos_diff [of x y] by (metis abs_cos_le_one add.commute)

lemma DERIV_fun_pow: "DERIV g x :> m \<Longrightarrow> DERIV (\<lambda>x. (g x) ^ n) x :> real n * (g x) ^ (n - 1) * m"
  by (auto intro!: derivative_eq_intros simp:)

lemma DERIV_fun_exp: "DERIV g x :> m \<Longrightarrow> DERIV (\<lambda>x. exp (g x)) x :> exp (g x) * m"
  by (auto intro!: derivative_intros)


subsection \<open>The Constant Pi\<close>

definition pi :: real
  where "pi = 2 * (THE x. 0 \<le> x \<and> x \<le> 2 \<and> cos x = 0)"

text \<open>Show that there's a least positive @{term x} with @{term "cos x = 0"};
   hence define pi.\<close>

lemma sin_paired: "(\<lambda>n. (- 1) ^ n / (fact (2 * n + 1)) * x ^ (2 * n + 1)) sums  sin x"
  for x :: real
proof -
  have "(\<lambda>n. \<Sum>k = n*2..<n * 2 + 2. sin_coeff k * x ^ k) sums sin x"
    by (rule sums_group) (use sin_converges [of x, unfolded scaleR_conv_of_real] in auto)
  then show ?thesis
    by (simp add: sin_coeff_def ac_simps)
qed

lemma sin_gt_zero_02:
  fixes x :: real
  assumes "0 < x" and "x < 2"
  shows "0 < sin x"
proof -
  let ?f = "\<lambda>n::nat. \<Sum>k = n*2..<n*2+2. (- 1) ^ k / (fact (2*k+1)) * x^(2*k+1)"
  have pos: "\<forall>n. 0 < ?f n"
  proof
    fix n :: nat
    let ?k2 = "real (Suc (Suc (4 * n)))"
    let ?k3 = "real (Suc (Suc (Suc (4 * n))))"
    have "x * x < ?k2 * ?k3"
      using assms by (intro mult_strict_mono', simp_all)
    then have "x * x * x * x ^ (n * 4) < ?k2 * ?k3 * x * x ^ (n * 4)"
      by (intro mult_strict_right_mono zero_less_power \<open>0 < x\<close>)
    then show "0 < ?f n"
      by (simp add: divide_simps mult_ac del: mult_Suc)
qed
  have sums: "?f sums sin x"
    by (rule sin_paired [THEN sums_group]) simp
  show "0 < sin x"
    unfolding sums_unique [OF sums]
    using sums_summable [OF sums] pos
    by (rule suminf_pos)
qed

lemma cos_double_less_one: "0 < x \<Longrightarrow> x < 2 \<Longrightarrow> cos (2 * x) < 1"
  for x :: real
  using sin_gt_zero_02 [where x = x] by (auto simp: cos_squared_eq cos_double)

lemma cos_paired: "(\<lambda>n. (- 1) ^ n / (fact (2 * n)) * x ^ (2 * n)) sums cos x"
  for x :: real
proof -
  have "(\<lambda>n. \<Sum>k = n * 2..<n * 2 + 2. cos_coeff k * x ^ k) sums cos x"
    by (rule sums_group) (use cos_converges [of x, unfolded scaleR_conv_of_real] in auto)
  then show ?thesis
    by (simp add: cos_coeff_def ac_simps)
qed

lemmas realpow_num_eq_if = power_eq_if

lemma sumr_pos_lt_pair:
  fixes f :: "nat \<Rightarrow> real"
  shows "summable f \<Longrightarrow>
    (\<And>d. 0 < f (k + (Suc(Suc 0) * d)) + f (k + ((Suc (Suc 0) * d) + 1))) \<Longrightarrow>
    sum f {..<k} < suminf f"
  apply (simp only: One_nat_def)
  apply (subst suminf_split_initial_segment [where k=k])
   apply assumption
  apply simp
  apply (drule_tac k=k in summable_ignore_initial_segment)
  apply (drule_tac k="Suc (Suc 0)" in sums_group [OF summable_sums])
   apply simp
  apply simp
  apply (metis (no_types, lifting) add.commute suminf_pos summable_def sums_unique)
  done

lemma cos_two_less_zero [simp]: "cos 2 < (0::real)"
proof -
  note fact_Suc [simp del]
  from sums_minus [OF cos_paired]
  have *: "(\<lambda>n. - ((- 1) ^ n * 2 ^ (2 * n) / fact (2 * n))) sums - cos (2::real)"
    by simp
  then have sm: "summable (\<lambda>n. - ((- 1::real) ^ n * 2 ^ (2 * n) / (fact (2 * n))))"
    by (rule sums_summable)
  have "0 < (\<Sum>n<Suc (Suc (Suc 0)). - ((- 1::real) ^ n * 2 ^ (2 * n) / (fact (2 * n))))"
    by (simp add: fact_num_eq_if realpow_num_eq_if)
  moreover have "(\<Sum>n<Suc (Suc (Suc 0)). - ((- 1::real) ^ n  * 2 ^ (2 * n) / (fact (2 * n)))) <
    (\<Sum>n. - ((- 1) ^ n * 2 ^ (2 * n) / (fact (2 * n))))"
  proof -
    {
      fix d
      let ?six4d = "Suc (Suc (Suc (Suc (Suc (Suc (4 * d))))))"
      have "(4::real) * (fact (?six4d)) < (Suc (Suc (?six4d)) * fact (Suc (?six4d)))"
        unfolding of_nat_mult by (rule mult_strict_mono) (simp_all add: fact_less_mono)
      then have "(4::real) * (fact (?six4d)) < (fact (Suc (Suc (?six4d))))"
        by (simp only: fact_Suc [of "Suc (?six4d)"] of_nat_mult of_nat_fact)
      then have "(4::real) * inverse (fact (Suc (Suc (?six4d)))) < inverse (fact (?six4d))"
        by (simp add: inverse_eq_divide less_divide_eq)
    }
    then show ?thesis
      by (force intro!: sumr_pos_lt_pair [OF sm] simp add: divide_inverse algebra_simps)
  qed
  ultimately have "0 < (\<Sum>n. - ((- 1::real) ^ n * 2 ^ (2 * n) / (fact (2 * n))))"
    by (rule order_less_trans)
  moreover from * have "- cos 2 = (\<Sum>n. - ((- 1::real) ^ n * 2 ^ (2 * n) / (fact (2 * n))))"
    by (rule sums_unique)
  ultimately have "(0::real) < - cos 2" by simp
  then show ?thesis by simp
qed

lemmas cos_two_neq_zero [simp] = cos_two_less_zero [THEN less_imp_neq]
lemmas cos_two_le_zero [simp] = cos_two_less_zero [THEN order_less_imp_le]

lemma cos_is_zero: "\<exists>!x::real. 0 \<le> x \<and> x \<le> 2 \<and> cos x = 0"
proof (rule ex_ex1I)
  show "\<exists>x::real. 0 \<le> x \<and> x \<le> 2 \<and> cos x = 0"
    by (rule IVT2) simp_all
next
  fix x y :: real
  assume x: "0 \<le> x \<and> x \<le> 2 \<and> cos x = 0"
  assume y: "0 \<le> y \<and> y \<le> 2 \<and> cos y = 0"
  have [simp]: "\<forall>x::real. cos differentiable (at x)"
    unfolding real_differentiable_def by (auto intro: DERIV_cos)
  from x y less_linear [of x y] show "x = y"
    apply auto
     apply (drule_tac f = cos in Rolle)
        apply (drule_tac [5] f = cos in Rolle)
           apply (auto dest!: DERIV_cos [THEN DERIV_unique])
     apply (metis order_less_le_trans less_le sin_gt_zero_02)
    apply (metis order_less_le_trans less_le sin_gt_zero_02)
    done
qed

lemma pi_half: "pi/2 = (THE x. 0 \<le> x \<and> x \<le> 2 \<and> cos x = 0)"
  by (simp add: pi_def)

lemma cos_pi_half [simp]: "cos (pi / 2) = 0"
  by (simp add: pi_half cos_is_zero [THEN theI'])

lemma cos_of_real_pi_half [simp]: "cos ((of_real pi / 2) :: 'a) = 0"
  if "SORT_CONSTRAINT('a::{real_field,banach,real_normed_algebra_1})"
  by (metis cos_pi_half cos_of_real eq_numeral_simps(4)
      nonzero_of_real_divide of_real_0 of_real_numeral)

lemma pi_half_gt_zero [simp]: "0 < pi / 2"
  apply (rule order_le_neq_trans)
   apply (simp add: pi_half cos_is_zero [THEN theI'])
  apply (metis cos_pi_half cos_zero zero_neq_one)
  done

lemmas pi_half_neq_zero [simp] = pi_half_gt_zero [THEN less_imp_neq, symmetric]
lemmas pi_half_ge_zero [simp] = pi_half_gt_zero [THEN order_less_imp_le]

lemma pi_half_less_two [simp]: "pi / 2 < 2"
  apply (rule order_le_neq_trans)
   apply (simp add: pi_half cos_is_zero [THEN theI'])
  apply (metis cos_pi_half cos_two_neq_zero)
  done

lemmas pi_half_neq_two [simp] = pi_half_less_two [THEN less_imp_neq]
lemmas pi_half_le_two [simp] =  pi_half_less_two [THEN order_less_imp_le]

lemma pi_gt_zero [simp]: "0 < pi"
  using pi_half_gt_zero by simp

lemma pi_ge_zero [simp]: "0 \<le> pi"
  by (rule pi_gt_zero [THEN order_less_imp_le])

lemma pi_neq_zero [simp]: "pi \<noteq> 0"
  by (rule pi_gt_zero [THEN less_imp_neq, symmetric])

lemma pi_not_less_zero [simp]: "\<not> pi < 0"
  by (simp add: linorder_not_less)

lemma minus_pi_half_less_zero: "-(pi/2) < 0"
  by simp

lemma m2pi_less_pi: "- (2*pi) < pi"
  by simp

lemma sin_pi_half [simp]: "sin(pi/2) = 1"
  using sin_cos_squared_add2 [where x = "pi/2"]
  using sin_gt_zero_02 [OF pi_half_gt_zero pi_half_less_two]
  by (simp add: power2_eq_1_iff)

lemma sin_of_real_pi_half [simp]: "sin ((of_real pi / 2) :: 'a) = 1"
  if "SORT_CONSTRAINT('a::{real_field,banach,real_normed_algebra_1})"
  using sin_pi_half
  by (metis sin_pi_half eq_numeral_simps(4) nonzero_of_real_divide of_real_1 of_real_numeral sin_of_real)

lemma sin_cos_eq: "sin x = cos (of_real pi / 2 - x)"
  for x :: "'a::{real_normed_field,banach}"
  by (simp add: cos_diff)

lemma minus_sin_cos_eq: "- sin x = cos (x + of_real pi / 2)"
  for x :: "'a::{real_normed_field,banach}"
  by (simp add: cos_add nonzero_of_real_divide)

lemma cos_sin_eq: "cos x = sin (of_real pi / 2 - x)"
  for x :: "'a::{real_normed_field,banach}"
  using sin_cos_eq [of "of_real pi / 2 - x"] by simp

lemma sin_add: "sin (x + y) = sin x * cos y + cos x * sin y"
  for x :: "'a::{real_normed_field,banach}"
  using cos_add [of "of_real pi / 2 - x" "-y"]
  by (simp add: cos_sin_eq) (simp add: sin_cos_eq)

lemma sin_diff: "sin (x - y) = sin x * cos y - cos x * sin y"
  for x :: "'a::{real_normed_field,banach}"
  using sin_add [of x "- y"] by simp

lemma sin_double: "sin(2 * x) = 2 * sin x * cos x"
  for x :: "'a::{real_normed_field,banach}"
  using sin_add [where x=x and y=x] by simp

lemma cos_of_real_pi [simp]: "cos (of_real pi) = -1"
  using cos_add [where x = "pi/2" and y = "pi/2"]
  by (simp add: cos_of_real)

lemma sin_of_real_pi [simp]: "sin (of_real pi) = 0"
  using sin_add [where x = "pi/2" and y = "pi/2"]
  by (simp add: sin_of_real)

lemma cos_pi [simp]: "cos pi = -1"
  using cos_add [where x = "pi/2" and y = "pi/2"] by simp

lemma sin_pi [simp]: "sin pi = 0"
  using sin_add [where x = "pi/2" and y = "pi/2"] by simp

lemma sin_periodic_pi [simp]: "sin (x + pi) = - sin x"
  by (simp add: sin_add)

lemma sin_periodic_pi2 [simp]: "sin (pi + x) = - sin x"
  by (simp add: sin_add)

lemma cos_periodic_pi [simp]: "cos (x + pi) = - cos x"
  by (simp add: cos_add)

lemma cos_periodic_pi2 [simp]: "cos (pi + x) = - cos x"
  by (simp add: cos_add)

lemma sin_periodic [simp]: "sin (x + 2 * pi) = sin x"
  by (simp add: sin_add sin_double cos_double)

lemma cos_periodic [simp]: "cos (x + 2 * pi) = cos x"
  by (simp add: cos_add sin_double cos_double)

lemma cos_npi [simp]: "cos (real n * pi) = (- 1) ^ n"
  by (induct n) (auto simp: distrib_right)

lemma cos_npi2 [simp]: "cos (pi * real n) = (- 1) ^ n"
  by (metis cos_npi mult.commute)

lemma sin_npi [simp]: "sin (real n * pi) = 0"
  for n :: nat
  by (induct n) (auto simp: distrib_right)

lemma sin_npi2 [simp]: "sin (pi * real n) = 0"
  for n :: nat
  by (simp add: mult.commute [of pi])

lemma cos_two_pi [simp]: "cos (2 * pi) = 1"
  by (simp add: cos_double)

lemma sin_two_pi [simp]: "sin (2 * pi) = 0"
  by (simp add: sin_double)

lemma sin_times_sin: "sin w * sin z = (cos (w - z) - cos (w + z)) / 2"
  for w :: "'a::{real_normed_field,banach}"
  by (simp add: cos_diff cos_add)

lemma sin_times_cos: "sin w * cos z = (sin (w + z) + sin (w - z)) / 2"
  for w :: "'a::{real_normed_field,banach}"
  by (simp add: sin_diff sin_add)

lemma cos_times_sin: "cos w * sin z = (sin (w + z) - sin (w - z)) / 2"
  for w :: "'a::{real_normed_field,banach}"
  by (simp add: sin_diff sin_add)

lemma cos_times_cos: "cos w * cos z = (cos (w - z) + cos (w + z)) / 2"
  for w :: "'a::{real_normed_field,banach}"
  by (simp add: cos_diff cos_add)

lemma sin_plus_sin: "sin w + sin z = 2 * sin ((w + z) / 2) * cos ((w - z) / 2)"
  for w :: "'a::{real_normed_field,banach,field}"  (* FIXME field should not be necessary *)
  apply (simp add: mult.assoc sin_times_cos)
  apply (simp add: field_simps)
  done

lemma sin_diff_sin: "sin w - sin z = 2 * sin ((w - z) / 2) * cos ((w + z) / 2)"
  for w :: "'a::{real_normed_field,banach,field}"
  apply (simp add: mult.assoc sin_times_cos)
  apply (simp add: field_simps)
  done

lemma cos_plus_cos: "cos w + cos z = 2 * cos ((w + z) / 2) * cos ((w - z) / 2)"
  for w :: "'a::{real_normed_field,banach,field}"
  apply (simp add: mult.assoc cos_times_cos)
  apply (simp add: field_simps)
  done

lemma cos_diff_cos: "cos w - cos z = 2 * sin ((w + z) / 2) * sin ((z - w) / 2)"
  for w :: "'a::{real_normed_field,banach,field}"
  apply (simp add: mult.assoc sin_times_sin)
  apply (simp add: field_simps)
  done

lemma cos_double_cos: "cos (2 * z) = 2 * cos z ^ 2 - 1"
  for z :: "'a::{real_normed_field,banach}"
  by (simp add: cos_double sin_squared_eq)

lemma cos_double_sin: "cos (2 * z) = 1 - 2 * sin z ^ 2"
  for z :: "'a::{real_normed_field,banach}"
  by (simp add: cos_double sin_squared_eq)

lemma sin_pi_minus [simp]: "sin (pi - x) = sin x"
  by (metis sin_minus sin_periodic_pi minus_minus uminus_add_conv_diff)

lemma cos_pi_minus [simp]: "cos (pi - x) = - (cos x)"
  by (metis cos_minus cos_periodic_pi uminus_add_conv_diff)

lemma sin_minus_pi [simp]: "sin (x - pi) = - (sin x)"
  by (simp add: sin_diff)

lemma cos_minus_pi [simp]: "cos (x - pi) = - (cos x)"
  by (simp add: cos_diff)

lemma sin_2pi_minus [simp]: "sin (2 * pi - x) = - (sin x)"
  by (metis sin_periodic_pi2 add_diff_eq mult_2 sin_pi_minus)

lemma cos_2pi_minus [simp]: "cos (2 * pi - x) = cos x"
  by (metis (no_types, hide_lams) cos_add cos_minus cos_two_pi sin_minus sin_two_pi
      diff_0_right minus_diff_eq mult_1 mult_zero_left uminus_add_conv_diff)

lemma sin_gt_zero2: "0 < x \<Longrightarrow> x < pi/2 \<Longrightarrow> 0 < sin x"
  by (metis sin_gt_zero_02 order_less_trans pi_half_less_two)

lemma sin_less_zero:
  assumes "- pi/2 < x" and "x < 0"
  shows "sin x < 0"
proof -
  have "0 < sin (- x)"
    using assms by (simp only: sin_gt_zero2)
  then show ?thesis by simp
qed

lemma pi_less_4: "pi < 4"
  using pi_half_less_two by auto

lemma cos_gt_zero: "0 < x \<Longrightarrow> x < pi/2 \<Longrightarrow> 0 < cos x"
  by (simp add: cos_sin_eq sin_gt_zero2)

lemma cos_gt_zero_pi: "-(pi/2) < x \<Longrightarrow> x < pi/2 \<Longrightarrow> 0 < cos x"
  using cos_gt_zero [of x] cos_gt_zero [of "-x"]
  by (cases rule: linorder_cases [of x 0]) auto

lemma cos_ge_zero: "-(pi/2) \<le> x \<Longrightarrow> x \<le> pi/2 \<Longrightarrow> 0 \<le> cos x"
  by (auto simp: order_le_less cos_gt_zero_pi)
    (metis cos_pi_half eq_divide_eq eq_numeral_simps(4))

lemma sin_gt_zero: "0 < x \<Longrightarrow> x < pi \<Longrightarrow> 0 < sin x"
  by (simp add: sin_cos_eq cos_gt_zero_pi)

lemma sin_lt_zero: "pi < x \<Longrightarrow> x < 2 * pi \<Longrightarrow> sin x < 0"
  using sin_gt_zero [of "x - pi"]
  by (simp add: sin_diff)

lemma pi_ge_two: "2 \<le> pi"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then have "pi < 2" by auto
  have "\<exists>y > pi. y < 2 \<and> y < 2 * pi"
  proof (cases "2 < 2 * pi")
    case True
    with dense[OF \<open>pi < 2\<close>] show ?thesis by auto
  next
    case False
    have "pi < 2 * pi" by auto
    from dense[OF this] and False show ?thesis by auto
  qed
  then obtain y where "pi < y" and "y < 2" and "y < 2 * pi"
    by blast
  then have "0 < sin y"
    using sin_gt_zero_02 by auto
  moreover have "sin y < 0"
    using sin_gt_zero[of "y - pi"] \<open>pi < y\<close> and \<open>y < 2 * pi\<close> sin_periodic_pi[of "y - pi"]
    by auto
  ultimately show False by auto
qed

lemma sin_ge_zero: "0 \<le> x \<Longrightarrow> x \<le> pi \<Longrightarrow> 0 \<le> sin x"
  by (auto simp: order_le_less sin_gt_zero)

lemma sin_le_zero: "pi \<le> x \<Longrightarrow> x < 2 * pi \<Longrightarrow> sin x \<le> 0"
  using sin_ge_zero [of "x - pi"] by (simp add: sin_diff)

lemma sin_pi_divide_n_ge_0 [simp]:
  assumes "n \<noteq> 0"
  shows "0 \<le> sin (pi / real n)"
  by (rule sin_ge_zero) (use assms in \<open>simp_all add: divide_simps\<close>)

lemma sin_pi_divide_n_gt_0:
  assumes "2 \<le> n"
  shows "0 < sin (pi / real n)"
  by (rule sin_gt_zero) (use assms in \<open>simp_all add: divide_simps\<close>)

(* FIXME: This proof is almost identical to lemma \<open>cos_is_zero\<close>.
   It should be possible to factor out some of the common parts. *)
lemma cos_total:
  assumes y: "- 1 \<le> y" "y \<le> 1"
  shows "\<exists>!x. 0 \<le> x \<and> x \<le> pi \<and> cos x = y"
proof (rule ex_ex1I)
  show "\<exists>x. 0 \<le> x \<and> x \<le> pi \<and> cos x = y"
    by (rule IVT2) (simp_all add: y)
next
  fix a b
  assume a: "0 \<le> a \<and> a \<le> pi \<and> cos a = y"
  assume b: "0 \<le> b \<and> b \<le> pi \<and> cos b = y"
  have [simp]: "\<forall>x::real. cos differentiable (at x)"
    unfolding real_differentiable_def by (auto intro: DERIV_cos)
  from a b less_linear [of a b] show "a = b"
    apply auto
     apply (drule_tac f = cos in Rolle)
        apply (drule_tac [5] f = cos in Rolle)
           apply (auto dest!: DERIV_cos [THEN DERIV_unique])
     apply (metis order_less_le_trans less_le sin_gt_zero)
    apply (metis order_less_le_trans less_le sin_gt_zero)
    done
qed

lemma sin_total:
  assumes y: "-1 \<le> y" "y \<le> 1"
  shows "\<exists>!x. - (pi/2) \<le> x \<and> x \<le> pi/2 \<and> sin x = y"
proof -
  from cos_total [OF y]
  obtain x where x: "0 \<le> x" "x \<le> pi" "cos x = y"
    and uniq: "\<And>x'. 0 \<le> x' \<Longrightarrow> x' \<le> pi \<Longrightarrow> cos x' = y \<Longrightarrow> x' = x "
    by blast
  show ?thesis
    apply (simp add: sin_cos_eq)
    apply (rule ex1I [where a="pi/2 - x"])
     apply (cut_tac [2] x'="pi/2 - xa" in uniq)
    using x
        apply auto
    done
qed

lemma cos_zero_lemma:
  assumes "0 \<le> x" "cos x = 0"
  shows "\<exists>n. odd n \<and> x = of_nat n * (pi/2) \<and> n > 0"
proof -
  have xle: "x < (1 + real_of_int \<lfloor>x/pi\<rfloor>) * pi"
    using floor_correct [of "x/pi"]
    by (simp add: add.commute divide_less_eq)
  obtain n where "real n * pi \<le> x" "x < real (Suc n) * pi"
    apply (rule that [of "nat \<lfloor>x/pi\<rfloor>"])
    using assms
     apply (simp_all add: xle)
    apply (metis floor_less_iff less_irrefl mult_imp_div_pos_less not_le pi_gt_zero)
    done
  then have x: "0 \<le> x - n * pi" "(x - n * pi) \<le> pi" "cos (x - n * pi) = 0"
    by (auto simp: algebra_simps cos_diff assms)
  then have "\<exists>!x. 0 \<le> x \<and> x \<le> pi \<and> cos x = 0"
    by (auto simp: intro!: cos_total)
  then obtain \<theta> where \<theta>: "0 \<le> \<theta>" "\<theta> \<le> pi" "cos \<theta> = 0"
    and uniq: "\<And>\<phi>. 0 \<le> \<phi> \<Longrightarrow> \<phi> \<le> pi \<Longrightarrow> cos \<phi> = 0 \<Longrightarrow> \<phi> = \<theta>"
    by blast
  then have "x - real n * pi = \<theta>"
    using x by blast
  moreover have "pi/2 = \<theta>"
    using pi_half_ge_zero uniq by fastforce
  ultimately show ?thesis
    by (rule_tac x = "Suc (2 * n)" in exI) (simp add: algebra_simps)
qed

lemma sin_zero_lemma: "0 \<le> x \<Longrightarrow> sin x = 0 \<Longrightarrow> \<exists>n::nat. even n \<and> x = real n * (pi/2)"
  using cos_zero_lemma [of "x + pi/2"]
  apply (clarsimp simp add: cos_add)
  apply (rule_tac x = "n - 1" in exI)
  apply (simp add: algebra_simps of_nat_diff)
  done

lemma cos_zero_iff:
  "cos x = 0 \<longleftrightarrow> ((\<exists>n. odd n \<and> x = real n * (pi/2)) \<or> (\<exists>n. odd n \<and> x = - (real n * (pi/2))))"
  (is "?lhs = ?rhs")
proof -
  have *: "cos (real n * pi / 2) = 0" if "odd n" for n :: nat
  proof -
    from that obtain m where "n = 2 * m + 1" ..
    then show ?thesis
      by (simp add: field_simps) (simp add: cos_add add_divide_distrib)
  qed
  show ?thesis
  proof
    show ?rhs if ?lhs
      using that cos_zero_lemma [of x] cos_zero_lemma [of "-x"] by force
    show ?lhs if ?rhs
      using that by (auto dest: * simp del: eq_divide_eq_numeral1)
  qed
qed

lemma sin_zero_iff:
  "sin x = 0 \<longleftrightarrow> ((\<exists>n. even n \<and> x = real n * (pi/2)) \<or> (\<exists>n. even n \<and> x = - (real n * (pi/2))))"
  (is "?lhs = ?rhs")
proof
  show ?rhs if ?lhs
    using that sin_zero_lemma [of x] sin_zero_lemma [of "-x"] by force
  show ?lhs if ?rhs
    using that by (auto elim: evenE)
qed

lemma cos_zero_iff_int: "cos x = 0 \<longleftrightarrow> (\<exists>n. odd n \<and> x = of_int n * (pi/2))"
proof safe
  assume "cos x = 0"
  then show "\<exists>n. odd n \<and> x = of_int n * (pi/2)"
    apply (simp add: cos_zero_iff)
    apply safe
     apply (metis even_int_iff of_int_of_nat_eq)
    apply (rule_tac x="- (int n)" in exI)
    apply simp
    done
next
  fix n :: int
  assume "odd n"
  then show "cos (of_int n * (pi / 2)) = 0"
    apply (simp add: cos_zero_iff)
    apply (cases n rule: int_cases2)
     apply simp_all
    done
qed

lemma sin_zero_iff_int: "sin x = 0 \<longleftrightarrow> (\<exists>n. even n \<and> x = of_int n * (pi/2))"
proof safe
  assume "sin x = 0"
  then show "\<exists>n. even n \<and> x = of_int n * (pi / 2)"
    apply (simp add: sin_zero_iff)
    apply safe
     apply (metis even_int_iff of_int_of_nat_eq)
    apply (rule_tac x="- (int n)" in exI)
    apply simp
    done
next
  fix n :: int
  assume "even n"
  then show "sin (of_int n * (pi / 2)) = 0"
    apply (simp add: sin_zero_iff)
    apply (cases n rule: int_cases2)
     apply simp_all
    done
qed

lemma sin_zero_iff_int2: "sin x = 0 \<longleftrightarrow> (\<exists>n::int. x = of_int n * pi)"
  apply (simp only: sin_zero_iff_int)
  apply (safe elim!: evenE)
   apply (simp_all add: field_simps)
  using dvd_triv_left apply fastforce
  done

lemma cos_monotone_0_pi:
  assumes "0 \<le> y" and "y < x" and "x \<le> pi"
  shows "cos x < cos y"
proof -
  have "- (x - y) < 0" using assms by auto
  from MVT2[OF \<open>y < x\<close> DERIV_cos[THEN impI, THEN allI]]
  obtain z where "y < z" and "z < x" and cos_diff: "cos x - cos y = (x - y) * - sin z"
    by auto
  then have "0 < z" and "z < pi"
    using assms by auto
  then have "0 < sin z"
    using sin_gt_zero by auto
  then have "cos x - cos y < 0"
    unfolding cos_diff minus_mult_commute[symmetric]
    using \<open>- (x - y) < 0\<close> by (rule mult_pos_neg2)
  then show ?thesis by auto
qed

lemma cos_monotone_0_pi_le:
  assumes "0 \<le> y" and "y \<le> x" and "x \<le> pi"
  shows "cos x \<le> cos y"
proof (cases "y < x")
  case True
  show ?thesis
    using cos_monotone_0_pi[OF \<open>0 \<le> y\<close> True \<open>x \<le> pi\<close>] by auto
next
  case False
  then have "y = x" using \<open>y \<le> x\<close> by auto
  then show ?thesis by auto
qed

lemma cos_monotone_minus_pi_0:
  assumes "- pi \<le> y" and "y < x" and "x \<le> 0"
  shows "cos y < cos x"
proof -
  have "0 \<le> - x" and "- x < - y" and "- y \<le> pi"
    using assms by auto
  from cos_monotone_0_pi[OF this] show ?thesis
    unfolding cos_minus .
qed

lemma cos_monotone_minus_pi_0':
  assumes "- pi \<le> y" and "y \<le> x" and "x \<le> 0"
  shows "cos y \<le> cos x"
proof (cases "y < x")
  case True
  show ?thesis using cos_monotone_minus_pi_0[OF \<open>-pi \<le> y\<close> True \<open>x \<le> 0\<close>]
    by auto
next
  case False
  then have "y = x" using \<open>y \<le> x\<close> by auto
  then show ?thesis by auto
qed

lemma sin_monotone_2pi:
  assumes "- (pi/2) \<le> y" and "y < x" and "x \<le> pi/2"
  shows "sin y < sin x"
  apply (simp add: sin_cos_eq)
  apply (rule cos_monotone_0_pi)
  using assms
    apply auto
  done

lemma sin_monotone_2pi_le:
  assumes "- (pi / 2) \<le> y" and "y \<le> x" and "x \<le> pi / 2"
  shows "sin y \<le> sin x"
  by (metis assms le_less sin_monotone_2pi)

lemma sin_x_le_x:
  fixes x :: real
  assumes x: "x \<ge> 0"
  shows "sin x \<le> x"
proof -
  let ?f = "\<lambda>x. x - sin x"
  from x have "?f x \<ge> ?f 0"
    apply (rule DERIV_nonneg_imp_nondecreasing)
    apply (intro allI impI exI[of _ "1 - cos x" for x])
    apply (auto intro!: derivative_eq_intros simp: field_simps)
    done
  then show "sin x \<le> x" by simp
qed

lemma sin_x_ge_neg_x:
  fixes x :: real
  assumes x: "x \<ge> 0"
  shows "sin x \<ge> - x"
proof -
  let ?f = "\<lambda>x. x + sin x"
  from x have "?f x \<ge> ?f 0"
    apply (rule DERIV_nonneg_imp_nondecreasing)
    apply (intro allI impI exI[of _ "1 + cos x" for x])
    apply (auto intro!: derivative_eq_intros simp: field_simps real_0_le_add_iff)
    done
  then show "sin x \<ge> -x" by simp
qed

lemma abs_sin_x_le_abs_x: "\<bar>sin x\<bar> \<le> \<bar>x\<bar>"
  for x :: real
  using sin_x_ge_neg_x [of x] sin_x_le_x [of x] sin_x_ge_neg_x [of "-x"] sin_x_le_x [of "-x"]
  by (auto simp: abs_real_def)


subsection \<open>More Corollaries about Sine and Cosine\<close>

lemma sin_cos_npi [simp]: "sin (real (Suc (2 * n)) * pi / 2) = (-1) ^ n"
proof -
  have "sin ((real n + 1/2) * pi) = cos (real n * pi)"
    by (auto simp: algebra_simps sin_add)
  then show ?thesis
    by (simp add: distrib_right add_divide_distrib add.commute mult.commute [of pi])
qed

lemma cos_2npi [simp]: "cos (2 * real n * pi) = 1"
  for n :: nat
  by (cases "even n") (simp_all add: cos_double mult.assoc)

lemma cos_3over2_pi [simp]: "cos (3/2*pi) = 0"
  apply (subgoal_tac "cos (pi + pi/2) = 0")
   apply simp
  apply (subst cos_add)
  apply simp
  done

lemma sin_2npi [simp]: "sin (2 * real n * pi) = 0"
  for n :: nat
  by (auto simp: mult.assoc sin_double)

lemma sin_3over2_pi [simp]: "sin (3/2*pi) = - 1"
  apply (subgoal_tac "sin (pi + pi/2) = - 1")
   apply simp
  apply (subst sin_add)
  apply simp
  done

lemma cos_pi_eq_zero [simp]: "cos (pi * real (Suc (2 * m)) / 2) = 0"
  by (simp only: cos_add sin_add of_nat_Suc distrib_right distrib_left add_divide_distrib, auto)

lemma DERIV_cos_add [simp]: "DERIV (\<lambda>x. cos (x + k)) xa :> - sin (xa + k)"
  by (auto intro!: derivative_eq_intros)

lemma sin_zero_norm_cos_one:
  fixes x :: "'a::{real_normed_field,banach}"
  assumes "sin x = 0"
  shows "norm (cos x) = 1"
  using sin_cos_squared_add [of x, unfolded assms]
  by (simp add: square_norm_one)

lemma sin_zero_abs_cos_one: "sin x = 0 \<Longrightarrow> \<bar>cos x\<bar> = (1::real)"
  using sin_zero_norm_cos_one by fastforce

lemma cos_one_sin_zero:
  fixes x :: "'a::{real_normed_field,banach}"
  assumes "cos x = 1"
  shows "sin x = 0"
  using sin_cos_squared_add [of x, unfolded assms]
  by simp

lemma sin_times_pi_eq_0: "sin (x * pi) = 0 \<longleftrightarrow> x \<in> \<int>"
  by (simp add: sin_zero_iff_int2) (metis Ints_cases Ints_of_int)

lemma cos_one_2pi: "cos x = 1 \<longleftrightarrow> (\<exists>n::nat. x = n * 2 * pi) | (\<exists>n::nat. x = - (n * 2 * pi))"
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  then have "sin x = 0"
    by (simp add: cos_one_sin_zero)
  then show ?rhs
  proof (simp only: sin_zero_iff, elim exE disjE conjE)
    fix n :: nat
    assume n: "even n" "x = real n * (pi/2)"
    then obtain m where m: "n = 2 * m"
      using dvdE by blast
    then have me: "even m" using \<open>?lhs\<close> n
      by (auto simp: field_simps) (metis one_neq_neg_one  power_minus_odd power_one)
    show ?rhs
      using m me n
      by (auto simp: field_simps elim!: evenE)
  next
    fix n :: nat
    assume n: "even n" "x = - (real n * (pi/2))"
    then obtain m where m: "n = 2 * m"
      using dvdE by blast
    then have me: "even m" using \<open>?lhs\<close> n
      by (auto simp: field_simps) (metis one_neq_neg_one  power_minus_odd power_one)
    show ?rhs
      using m me n
      by (auto simp: field_simps elim!: evenE)
  qed
next
  assume ?rhs
  then show "cos x = 1"
    by (metis cos_2npi cos_minus mult.assoc mult.left_commute)
qed

lemma cos_one_2pi_int: "cos x = 1 \<longleftrightarrow> (\<exists>n::int. x = n * 2 * pi)"
  apply auto  (* FIXME simproc bug? *)
   apply (auto simp: cos_one_2pi)
    apply (metis of_int_of_nat_eq)
   apply (metis mult_minus_right of_int_minus of_int_of_nat_eq)
  apply (metis mult_minus_right of_int_of_nat)
  done

lemma sin_cos_sqrt: "0 \<le> sin x \<Longrightarrow> sin x = sqrt (1 - (cos(x) ^ 2))"
  using sin_squared_eq real_sqrt_unique by fastforce

lemma sin_eq_0_pi: "- pi < x \<Longrightarrow> x < pi \<Longrightarrow> sin x = 0 \<Longrightarrow> x = 0"
  by (metis sin_gt_zero sin_minus minus_less_iff neg_0_less_iff_less not_less_iff_gr_or_eq)

lemma cos_treble_cos: "cos (3 * x) = 4 * cos x ^ 3 - 3 * cos x"
  for x :: "'a::{real_normed_field,banach}"
proof -
  have *: "(sin x * (sin x * 3)) = 3 - (cos x * (cos x * 3))"
    by (simp add: mult.assoc [symmetric] sin_squared_eq [unfolded power2_eq_square])
  have "cos(3 * x) = cos(2*x + x)"
    by simp
  also have "\<dots> = 4 * cos x ^ 3 - 3 * cos x"
    apply (simp only: cos_add cos_double sin_double)
    apply (simp add: * field_simps power2_eq_square power3_eq_cube)
    done
  finally show ?thesis .
qed

lemma cos_45: "cos (pi / 4) = sqrt 2 / 2"
proof -
  let ?c = "cos (pi / 4)"
  let ?s = "sin (pi / 4)"
  have nonneg: "0 \<le> ?c"
    by (simp add: cos_ge_zero)
  have "0 = cos (pi / 4 + pi / 4)"
    by simp
  also have "cos (pi / 4 + pi / 4) = ?c\<^sup>2 - ?s\<^sup>2"
    by (simp only: cos_add power2_eq_square)
  also have "\<dots> = 2 * ?c\<^sup>2 - 1"
    by (simp add: sin_squared_eq)
  finally have "?c\<^sup>2 = (sqrt 2 / 2)\<^sup>2"
    by (simp add: power_divide)
  then show ?thesis
    using nonneg by (rule power2_eq_imp_eq) simp
qed

lemma cos_30: "cos (pi / 6) = sqrt 3/2"
proof -
  let ?c = "cos (pi / 6)"
  let ?s = "sin (pi / 6)"
  have pos_c: "0 < ?c"
    by (rule cos_gt_zero) simp_all
  have "0 = cos (pi / 6 + pi / 6 + pi / 6)"
    by simp
  also have "\<dots> = (?c * ?c - ?s * ?s) * ?c - (?s * ?c + ?c * ?s) * ?s"
    by (simp only: cos_add sin_add)
  also have "\<dots> = ?c * (?c\<^sup>2 - 3 * ?s\<^sup>2)"
    by (simp add: algebra_simps power2_eq_square)
  finally have "?c\<^sup>2 = (sqrt 3/2)\<^sup>2"
    using pos_c by (simp add: sin_squared_eq power_divide)
  then show ?thesis
    using pos_c [THEN order_less_imp_le]
    by (rule power2_eq_imp_eq) simp
qed

lemma sin_45: "sin (pi / 4) = sqrt 2 / 2"
  by (simp add: sin_cos_eq cos_45)

lemma sin_60: "sin (pi / 3) = sqrt 3/2"
  by (simp add: sin_cos_eq cos_30)

lemma cos_60: "cos (pi / 3) = 1 / 2"
  apply (rule power2_eq_imp_eq)
    apply (simp add: cos_squared_eq sin_60 power_divide)
   apply (rule cos_ge_zero)
    apply (rule order_trans [where y=0])
     apply simp_all
  done

lemma sin_30: "sin (pi / 6) = 1 / 2"
  by (simp add: sin_cos_eq cos_60)

lemma cos_integer_2pi: "n \<in> \<int> \<Longrightarrow> cos(2 * pi * n) = 1"
  by (metis Ints_cases cos_one_2pi_int mult.assoc mult.commute)

lemma sin_integer_2pi: "n \<in> \<int> \<Longrightarrow> sin(2 * pi * n) = 0"
  by (metis sin_two_pi Ints_mult mult.assoc mult.commute sin_times_pi_eq_0)

lemma cos_int_2npi [simp]: "cos (2 * of_int n * pi) = 1"
  for n :: int
  by (simp add: cos_one_2pi_int)

lemma sin_int_2npi [simp]: "sin (2 * of_int n * pi) = 0"
  for n :: int
  by (metis Ints_of_int mult.assoc mult.commute sin_integer_2pi)

lemma sincos_principal_value: "\<exists>y. (- pi < y \<and> y \<le> pi) \<and> (sin y = sin x \<and> cos y = cos x)"
  apply (rule exI [where x="pi - (2 * pi) * frac ((pi - x) / (2 * pi))"])
  apply (auto simp: field_simps frac_lt_1)
   apply (simp_all add: frac_def divide_simps)
   apply (simp_all add: add_divide_distrib diff_divide_distrib)
   apply (simp_all add: sin_diff cos_diff mult.assoc [symmetric] cos_integer_2pi sin_integer_2pi)
  done


subsection \<open>Tangent\<close>

definition tan :: "'a \<Rightarrow> 'a::{real_normed_field,banach}"
  where "tan = (\<lambda>x. sin x / cos x)"

lemma tan_of_real: "of_real (tan x) = (tan (of_real x) :: 'a::{real_normed_field,banach})"
  by (simp add: tan_def sin_of_real cos_of_real)

lemma tan_in_Reals [simp]: "z \<in> \<real> \<Longrightarrow> tan z \<in> \<real>"
  for z :: "'a::{real_normed_field,banach}"
  by (simp add: tan_def)

lemma tan_zero [simp]: "tan 0 = 0"
  by (simp add: tan_def)

lemma tan_pi [simp]: "tan pi = 0"
  by (simp add: tan_def)

lemma tan_npi [simp]: "tan (real n * pi) = 0"
  for n :: nat
  by (simp add: tan_def)

lemma tan_minus [simp]: "tan (- x) = - tan x"
  by (simp add: tan_def)

lemma tan_periodic [simp]: "tan (x + 2 * pi) = tan x"
  by (simp add: tan_def)

lemma lemma_tan_add1: "cos x \<noteq> 0 \<Longrightarrow> cos y \<noteq> 0 \<Longrightarrow> 1 - tan x * tan y = cos (x + y)/(cos x * cos y)"
  by (simp add: tan_def cos_add field_simps)

lemma add_tan_eq: "cos x \<noteq> 0 \<Longrightarrow> cos y \<noteq> 0 \<Longrightarrow> tan x + tan y = sin(x + y)/(cos x * cos y)"
  for x :: "'a::{real_normed_field,banach}"
  by (simp add: tan_def sin_add field_simps)

lemma tan_add:
  "cos x \<noteq> 0 \<Longrightarrow> cos y \<noteq> 0 \<Longrightarrow> cos (x + y) \<noteq> 0 \<Longrightarrow> tan (x + y) = (tan x + tan y)/(1 - tan x * tan y)"
  for x :: "'a::{real_normed_field,banach}"
  by (simp add: add_tan_eq lemma_tan_add1 field_simps) (simp add: tan_def)

lemma tan_double: "cos x \<noteq> 0 \<Longrightarrow> cos (2 * x) \<noteq> 0 \<Longrightarrow> tan (2 * x) = (2 * tan x) / (1 - (tan x)\<^sup>2)"
  for x :: "'a::{real_normed_field,banach}"
  using tan_add [of x x] by (simp add: power2_eq_square)

lemma tan_gt_zero: "0 < x \<Longrightarrow> x < pi/2 \<Longrightarrow> 0 < tan x"
  by (simp add: tan_def zero_less_divide_iff sin_gt_zero2 cos_gt_zero_pi)

lemma tan_less_zero:
  assumes "- pi/2 < x" and "x < 0"
  shows "tan x < 0"
proof -
  have "0 < tan (- x)"
    using assms by (simp only: tan_gt_zero)
  then show ?thesis by simp
qed

lemma tan_half: "tan x = sin (2 * x) / (cos (2 * x) + 1)"
  for x :: "'a::{real_normed_field,banach,field}"
  unfolding tan_def sin_double cos_double sin_squared_eq
  by (simp add: power2_eq_square)

lemma tan_30: "tan (pi / 6) = 1 / sqrt 3"
  unfolding tan_def by (simp add: sin_30 cos_30)

lemma tan_45: "tan (pi / 4) = 1"
  unfolding tan_def by (simp add: sin_45 cos_45)

lemma tan_60: "tan (pi / 3) = sqrt 3"
  unfolding tan_def by (simp add: sin_60 cos_60)

lemma DERIV_tan [simp]: "cos x \<noteq> 0 \<Longrightarrow> DERIV tan x :> inverse ((cos x)\<^sup>2)"
  for x :: "'a::{real_normed_field,banach}"
  unfolding tan_def
  by (auto intro!: derivative_eq_intros, simp add: divide_inverse power2_eq_square)

lemma isCont_tan: "cos x \<noteq> 0 \<Longrightarrow> isCont tan x"
  for x :: "'a::{real_normed_field,banach}"
  by (rule DERIV_tan [THEN DERIV_isCont])

lemma isCont_tan' [simp,continuous_intros]:
  fixes a :: "'a::{real_normed_field,banach}" and f :: "'a \<Rightarrow> 'a"
  shows "isCont f a \<Longrightarrow> cos (f a) \<noteq> 0 \<Longrightarrow> isCont (\<lambda>x. tan (f x)) a"
  by (rule isCont_o2 [OF _ isCont_tan])

lemma tendsto_tan [tendsto_intros]:
  fixes f :: "'a \<Rightarrow> 'a::{real_normed_field,banach}"
  shows "(f \<longlongrightarrow> a) F \<Longrightarrow> cos a \<noteq> 0 \<Longrightarrow> ((\<lambda>x. tan (f x)) \<longlongrightarrow> tan a) F"
  by (rule isCont_tendsto_compose [OF isCont_tan])

lemma continuous_tan:
  fixes f :: "'a \<Rightarrow> 'a::{real_normed_field,banach}"
  shows "continuous F f \<Longrightarrow> cos (f (Lim F (\<lambda>x. x))) \<noteq> 0 \<Longrightarrow> continuous F (\<lambda>x. tan (f x))"
  unfolding continuous_def by (rule tendsto_tan)

lemma continuous_on_tan [continuous_intros]:
  fixes f :: "'a \<Rightarrow> 'a::{real_normed_field,banach}"
  shows "continuous_on s f \<Longrightarrow> (\<forall>x\<in>s. cos (f x) \<noteq> 0) \<Longrightarrow> continuous_on s (\<lambda>x. tan (f x))"
  unfolding continuous_on_def by (auto intro: tendsto_tan)

lemma continuous_within_tan [continuous_intros]:
  fixes f :: "'a \<Rightarrow> 'a::{real_normed_field,banach}"
  shows "continuous (at x within s) f \<Longrightarrow>
    cos (f x) \<noteq> 0 \<Longrightarrow> continuous (at x within s) (\<lambda>x. tan (f x))"
  unfolding continuous_within by (rule tendsto_tan)

lemma LIM_cos_div_sin: "(\<lambda>x. cos(x)/sin(x)) \<midarrow>pi/2\<rightarrow> 0"
  by (rule LIM_cong_limit, (rule tendsto_intros)+, simp_all)

lemma lemma_tan_total: "0 < y \<Longrightarrow> \<exists>x. 0 < x \<and> x < pi/2 \<and> y < tan x"
  apply (insert LIM_cos_div_sin)
  apply (simp only: LIM_eq)
  apply (drule_tac x = "inverse y" in spec)
  apply safe
   apply force
  apply (drule_tac ?d1.0 = s in pi_half_gt_zero [THEN [2] real_lbound_gt_zero])
  apply safe
  apply (rule_tac x = "(pi/2) - e" in exI)
  apply (simp (no_asm_simp))
  apply (drule_tac x = "(pi/2) - e" in spec)
  apply (auto simp add: tan_def sin_diff cos_diff)
  apply (rule inverse_less_iff_less [THEN iffD1])
    apply (auto simp add: divide_inverse)
   apply (rule mult_pos_pos)
    apply (subgoal_tac [3] "0 < sin e \<and> 0 < cos e")
     apply (auto intro: cos_gt_zero sin_gt_zero2 simp: mult.commute)
  done

lemma tan_total_pos: "0 \<le> y \<Longrightarrow> \<exists>x. 0 \<le> x \<and> x < pi/2 \<and> tan x = y"
  apply (frule order_le_imp_less_or_eq)
  apply safe
   prefer 2 apply force
  apply (drule lemma_tan_total)
  apply safe
  apply (cut_tac f = tan and a = 0 and b = x and y = y in IVT_objl)
  apply (auto intro!: DERIV_tan [THEN DERIV_isCont])
  apply (drule_tac y = xa in order_le_imp_less_or_eq)
  apply (auto dest: cos_gt_zero)
  done

lemma lemma_tan_total1: "\<exists>x. -(pi/2) < x \<and> x < (pi/2) \<and> tan x = y"
  apply (insert linorder_linear [of 0 y])
  apply safe
   apply (drule tan_total_pos)
   apply (cut_tac [2] y="-y" in tan_total_pos)
    apply safe
    apply (rule_tac [3] x = "-x" in exI)
    apply (auto del: exI intro!: exI)
  done

lemma tan_total: "\<exists>! x. -(pi/2) < x \<and> x < (pi/2) \<and> tan x = y"
  apply (insert lemma_tan_total1 [where y = y])
  apply auto
  apply hypsubst_thin
  apply (cut_tac x = xa and y = y in linorder_less_linear)
  apply auto
   apply (subgoal_tac [2] "\<exists>z. y < z \<and> z < xa \<and> DERIV tan z :> 0")
    apply (subgoal_tac "\<exists>z. xa < z \<and> z < y \<and> DERIV tan z :> 0")
     apply (rule_tac [4] Rolle)
        apply (rule_tac [2] Rolle)
           apply (auto del: exI intro!: DERIV_tan DERIV_isCont exI
            simp add: real_differentiable_def)
       apply (rule_tac [!] DERIV_tan asm_rl)
       apply (auto dest!: DERIV_unique [OF _ DERIV_tan]
        simp add: cos_gt_zero_pi [THEN less_imp_neq, THEN not_sym])
  done

lemma tan_monotone:
  assumes "- (pi / 2) < y" and "y < x" and "x < pi / 2"
  shows "tan y < tan x"
proof -
  have "\<forall>x'. y \<le> x' \<and> x' \<le> x \<longrightarrow> DERIV tan x' :> inverse ((cos x')\<^sup>2)"
  proof (rule allI, rule impI)
    fix x' :: real
    assume "y \<le> x' \<and> x' \<le> x"
    then have "-(pi/2) < x'" and "x' < pi/2"
      using assms by auto
    from cos_gt_zero_pi[OF this]
    have "cos x' \<noteq> 0" by auto
    then show "DERIV tan x' :> inverse ((cos x')\<^sup>2)"
      by (rule DERIV_tan)
  qed
  from MVT2[OF \<open>y < x\<close> this]
  obtain z where "y < z" and "z < x"
    and tan_diff: "tan x - tan y = (x - y) * inverse ((cos z)\<^sup>2)" by auto
  then have "- (pi / 2) < z" and "z < pi / 2"
    using assms by auto
  then have "0 < cos z"
    using cos_gt_zero_pi by auto
  then have inv_pos: "0 < inverse ((cos z)\<^sup>2)"
    by auto
  have "0 < x - y" using \<open>y < x\<close> by auto
  with inv_pos have "0 < tan x - tan y"
    unfolding tan_diff by auto
  then show ?thesis by auto
qed

lemma tan_monotone':
  assumes "- (pi / 2) < y"
    and "y < pi / 2"
    and "- (pi / 2) < x"
    and "x < pi / 2"
  shows "y < x \<longleftrightarrow> tan y < tan x"
proof
  assume "y < x"
  then show "tan y < tan x"
    using tan_monotone and \<open>- (pi / 2) < y\<close> and \<open>x < pi / 2\<close> by auto
next
  assume "tan y < tan x"
  show "y < x"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then have "x \<le> y" by auto
    then have "tan x \<le> tan y"
    proof (cases "x = y")
      case True
      then show ?thesis by auto
    next
      case False
      then have "x < y" using \<open>x \<le> y\<close> by auto
      from tan_monotone[OF \<open>- (pi/2) < x\<close> this \<open>y < pi / 2\<close>] show ?thesis
        by auto
    qed
    then show False
      using \<open>tan y < tan x\<close> by auto
  qed
qed

lemma tan_inverse: "1 / (tan y) = tan (pi / 2 - y)"
  unfolding tan_def sin_cos_eq[of y] cos_sin_eq[of y] by auto

lemma tan_periodic_pi[simp]: "tan (x + pi) = tan x"
  by (simp add: tan_def)

lemma tan_periodic_nat[simp]: "tan (x + real n * pi) = tan x"
  for n :: nat
proof (induct n arbitrary: x)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have split_pi_off: "x + real (Suc n) * pi = (x + real n * pi) + pi"
    unfolding Suc_eq_plus1 of_nat_add  distrib_right by auto
  show ?case
    unfolding split_pi_off using Suc by auto
qed

lemma tan_periodic_int[simp]: "tan (x + of_int i * pi) = tan x"
proof (cases "0 \<le> i")
  case True
  then have i_nat: "of_int i = of_int (nat i)" by auto
  show ?thesis unfolding i_nat
    by (metis of_int_of_nat_eq tan_periodic_nat)
next
  case False
  then have i_nat: "of_int i = - of_int (nat (- i))" by auto
  have "tan x = tan (x + of_int i * pi - of_int i * pi)"
    by auto
  also have "\<dots> = tan (x + of_int i * pi)"
    unfolding i_nat mult_minus_left diff_minus_eq_add
    by (metis of_int_of_nat_eq tan_periodic_nat)
  finally show ?thesis by auto
qed

lemma tan_periodic_n[simp]: "tan (x + numeral n * pi) = tan x"
  using tan_periodic_int[of _ "numeral n" ] by simp

lemma tan_minus_45: "tan (-(pi/4)) = -1"
  unfolding tan_def by (simp add: sin_45 cos_45)

lemma tan_diff:
  "cos x \<noteq> 0 \<Longrightarrow> cos y \<noteq> 0 \<Longrightarrow> cos (x - y) \<noteq> 0 \<Longrightarrow> tan (x - y) = (tan x - tan y)/(1 + tan x * tan y)"
  for x :: "'a::{real_normed_field,banach}"
  using tan_add [of x "-y"] by simp

lemma tan_pos_pi2_le: "0 \<le> x \<Longrightarrow> x < pi/2 \<Longrightarrow> 0 \<le> tan x"
  using less_eq_real_def tan_gt_zero by auto

lemma cos_tan: "\<bar>x\<bar> < pi/2 \<Longrightarrow> cos x = 1 / sqrt (1 + tan x ^ 2)"
  using cos_gt_zero_pi [of x]
  by (simp add: divide_simps tan_def real_sqrt_divide abs_if split: if_split_asm)

lemma sin_tan: "\<bar>x\<bar> < pi/2 \<Longrightarrow> sin x = tan x / sqrt (1 + tan x ^ 2)"
  using cos_gt_zero [of "x"] cos_gt_zero [of "-x"]
  by (force simp add: divide_simps tan_def real_sqrt_divide abs_if split: if_split_asm)

lemma tan_mono_le: "-(pi/2) < x \<Longrightarrow> x \<le> y \<Longrightarrow> y < pi/2 \<Longrightarrow> tan x \<le> tan y"
  using less_eq_real_def tan_monotone by auto

lemma tan_mono_lt_eq:
  "-(pi/2) < x \<Longrightarrow> x < pi/2 \<Longrightarrow> -(pi/2) < y \<Longrightarrow> y < pi/2 \<Longrightarrow> tan x < tan y \<longleftrightarrow> x < y"
  using tan_monotone' by blast

lemma tan_mono_le_eq:
  "-(pi/2) < x \<Longrightarrow> x < pi/2 \<Longrightarrow> -(pi/2) < y \<Longrightarrow> y < pi/2 \<Longrightarrow> tan x \<le> tan y \<longleftrightarrow> x \<le> y"
  by (meson tan_mono_le not_le tan_monotone)

lemma tan_bound_pi2: "\<bar>x\<bar> < pi/4 \<Longrightarrow> \<bar>tan x\<bar> < 1"
  using tan_45 tan_monotone [of x "pi/4"] tan_monotone [of "-x" "pi/4"]
  by (auto simp: abs_if split: if_split_asm)

lemma tan_cot: "tan(pi/2 - x) = inverse(tan x)"
  by (simp add: tan_def sin_diff cos_diff)


subsection \<open>Cotangent\<close>

definition cot :: "'a \<Rightarrow> 'a::{real_normed_field,banach}"
  where "cot = (\<lambda>x. cos x / sin x)"

lemma cot_of_real: "of_real (cot x) = (cot (of_real x) :: 'a::{real_normed_field,banach})"
  by (simp add: cot_def sin_of_real cos_of_real)

lemma cot_in_Reals [simp]: "z \<in> \<real> \<Longrightarrow> cot z \<in> \<real>"
  for z :: "'a::{real_normed_field,banach}"
  by (simp add: cot_def)

lemma cot_zero [simp]: "cot 0 = 0"
  by (simp add: cot_def)

lemma cot_pi [simp]: "cot pi = 0"
  by (simp add: cot_def)

lemma cot_npi [simp]: "cot (real n * pi) = 0"
  for n :: nat
  by (simp add: cot_def)

lemma cot_minus [simp]: "cot (- x) = - cot x"
  by (simp add: cot_def)

lemma cot_periodic [simp]: "cot (x + 2 * pi) = cot x"
  by (simp add: cot_def)

lemma cot_altdef: "cot x = inverse (tan x)"
  by (simp add: cot_def tan_def)

lemma tan_altdef: "tan x = inverse (cot x)"
  by (simp add: cot_def tan_def)

lemma tan_cot': "tan (pi/2 - x) = cot x"
  by (simp add: tan_cot cot_altdef)

lemma cot_gt_zero: "0 < x \<Longrightarrow> x < pi/2 \<Longrightarrow> 0 < cot x"
  by (simp add: cot_def zero_less_divide_iff sin_gt_zero2 cos_gt_zero_pi)

lemma cot_less_zero:
  assumes lb: "- pi/2 < x" and "x < 0"
  shows "cot x < 0"
proof -
  have "0 < cot (- x)"
    using assms by (simp only: cot_gt_zero)
  then show ?thesis by simp
qed

lemma DERIV_cot [simp]: "sin x \<noteq> 0 \<Longrightarrow> DERIV cot x :> -inverse ((sin x)\<^sup>2)"
  for x :: "'a::{real_normed_field,banach}"
  unfolding cot_def using cos_squared_eq[of x]
  by (auto intro!: derivative_eq_intros) (simp add: divide_inverse power2_eq_square)

lemma isCont_cot: "sin x \<noteq> 0 \<Longrightarrow> isCont cot x"
  for x :: "'a::{real_normed_field,banach}"
  by (rule DERIV_cot [THEN DERIV_isCont])

lemma isCont_cot' [simp,continuous_intros]:
  "isCont f a \<Longrightarrow> sin (f a) \<noteq> 0 \<Longrightarrow> isCont (\<lambda>x. cot (f x)) a"
  for a :: "'a::{real_normed_field,banach}" and f :: "'a \<Rightarrow> 'a"
  by (rule isCont_o2 [OF _ isCont_cot])

lemma tendsto_cot [tendsto_intros]: "(f \<longlongrightarrow> a) F \<Longrightarrow> sin a \<noteq> 0 \<Longrightarrow> ((\<lambda>x. cot (f x)) \<longlongrightarrow> cot a) F"
  for f :: "'a \<Rightarrow> 'a::{real_normed_field,banach}"
  by (rule isCont_tendsto_compose [OF isCont_cot])

lemma continuous_cot:
  "continuous F f \<Longrightarrow> sin (f (Lim F (\<lambda>x. x))) \<noteq> 0 \<Longrightarrow> continuous F (\<lambda>x. cot (f x))"
  for f :: "'a \<Rightarrow> 'a::{real_normed_field,banach}"
  unfolding continuous_def by (rule tendsto_cot)

lemma continuous_on_cot [continuous_intros]:
  fixes f :: "'a \<Rightarrow> 'a::{real_normed_field,banach}"
  shows "continuous_on s f \<Longrightarrow> (\<forall>x\<in>s. sin (f x) \<noteq> 0) \<Longrightarrow> continuous_on s (\<lambda>x. cot (f x))"
  unfolding continuous_on_def by (auto intro: tendsto_cot)

lemma continuous_within_cot [continuous_intros]:
  fixes f :: "'a \<Rightarrow> 'a::{real_normed_field,banach}"
  shows "continuous (at x within s) f \<Longrightarrow> sin (f x) \<noteq> 0 \<Longrightarrow> continuous (at x within s) (\<lambda>x. cot (f x))"
  unfolding continuous_within by (rule tendsto_cot)


subsection \<open>Inverse Trigonometric Functions\<close>

definition arcsin :: "real \<Rightarrow> real"
  where "arcsin y = (THE x. -(pi/2) \<le> x \<and> x \<le> pi/2 \<and> sin x = y)"

definition arccos :: "real \<Rightarrow> real"
  where "arccos y = (THE x. 0 \<le> x \<and> x \<le> pi \<and> cos x = y)"

definition arctan :: "real \<Rightarrow> real"
  where "arctan y = (THE x. -(pi/2) < x \<and> x < pi/2 \<and> tan x = y)"

lemma arcsin: "- 1 \<le> y \<Longrightarrow> y \<le> 1 \<Longrightarrow> - (pi/2) \<le> arcsin y \<and> arcsin y \<le> pi/2 \<and> sin (arcsin y) = y"
  unfolding arcsin_def by (rule theI' [OF sin_total])

lemma arcsin_pi: "- 1 \<le> y \<Longrightarrow> y \<le> 1 \<Longrightarrow> - (pi/2) \<le> arcsin y \<and> arcsin y \<le> pi \<and> sin (arcsin y) = y"
  by (drule (1) arcsin) (force intro: order_trans)

lemma sin_arcsin [simp]: "- 1 \<le> y \<Longrightarrow> y \<le> 1 \<Longrightarrow> sin (arcsin y) = y"
  by (blast dest: arcsin)

lemma arcsin_bounded: "- 1 \<le> y \<Longrightarrow> y \<le> 1 \<Longrightarrow> - (pi/2) \<le> arcsin y \<and> arcsin y \<le> pi/2"
  by (blast dest: arcsin)

lemma arcsin_lbound: "- 1 \<le> y \<Longrightarrow> y \<le> 1 \<Longrightarrow> - (pi/2) \<le> arcsin y"
  by (blast dest: arcsin)

lemma arcsin_ubound: "- 1 \<le> y \<Longrightarrow> y \<le> 1 \<Longrightarrow> arcsin y \<le> pi/2"
  by (blast dest: arcsin)

lemma arcsin_lt_bounded: "- 1 < y \<Longrightarrow> y < 1 \<Longrightarrow> - (pi/2) < arcsin y \<and> arcsin y < pi/2"
  apply (frule order_less_imp_le)
  apply (frule_tac y = y in order_less_imp_le)
  apply (frule arcsin_bounded)
   apply safe
    apply simp
   apply (drule_tac y = "arcsin y" in order_le_imp_less_or_eq)
   apply (drule_tac [2] y = "pi/2" in order_le_imp_less_or_eq)
   apply safe
   apply (drule_tac [!] f = sin in arg_cong)
   apply auto
  done

lemma arcsin_sin: "- (pi/2) \<le> x \<Longrightarrow> x \<le> pi/2 \<Longrightarrow> arcsin (sin x) = x"
  apply (unfold arcsin_def)
  apply (rule the1_equality)
   apply (rule sin_total)
    apply auto
  done

lemma arcsin_0 [simp]: "arcsin 0 = 0"
  using arcsin_sin [of 0] by simp

lemma arcsin_1 [simp]: "arcsin 1 = pi/2"
  using arcsin_sin [of "pi/2"] by simp

lemma arcsin_minus_1 [simp]: "arcsin (- 1) = - (pi/2)"
  using arcsin_sin [of "- pi/2"] by simp

lemma arcsin_minus: "- 1 \<le> x \<Longrightarrow> x \<le> 1 \<Longrightarrow> arcsin (- x) = - arcsin x"
  by (metis (no_types, hide_lams) arcsin arcsin_sin minus_minus neg_le_iff_le sin_minus)

lemma arcsin_eq_iff: "\<bar>x\<bar> \<le> 1 \<Longrightarrow> \<bar>y\<bar> \<le> 1 \<Longrightarrow> arcsin x = arcsin y \<longleftrightarrow> x = y"
  by (metis abs_le_iff arcsin minus_le_iff)

lemma cos_arcsin_nonzero: "- 1 < x \<Longrightarrow> x < 1 \<Longrightarrow> cos (arcsin x) \<noteq> 0"
  using arcsin_lt_bounded cos_gt_zero_pi by force

lemma arccos: "- 1 \<le> y \<Longrightarrow> y \<le> 1 \<Longrightarrow> 0 \<le> arccos y \<and> arccos y \<le> pi \<and> cos (arccos y) = y"
  unfolding arccos_def by (rule theI' [OF cos_total])

lemma cos_arccos [simp]: "- 1 \<le> y \<Longrightarrow> y \<le> 1 \<Longrightarrow> cos (arccos y) = y"
  by (blast dest: arccos)

lemma arccos_bounded: "- 1 \<le> y \<Longrightarrow> y \<le> 1 \<Longrightarrow> 0 \<le> arccos y \<and> arccos y \<le> pi"
  by (blast dest: arccos)

lemma arccos_lbound: "- 1 \<le> y \<Longrightarrow> y \<le> 1 \<Longrightarrow> 0 \<le> arccos y"
  by (blast dest: arccos)

lemma arccos_ubound: "- 1 \<le> y \<Longrightarrow> y \<le> 1 \<Longrightarrow> arccos y \<le> pi"
  by (blast dest: arccos)

lemma arccos_lt_bounded: "- 1 < y \<Longrightarrow> y < 1 \<Longrightarrow> 0 < arccos y \<and> arccos y < pi"
  apply (frule order_less_imp_le)
  apply (frule_tac y = y in order_less_imp_le)
  apply (frule arccos_bounded)
   apply auto
   apply (drule_tac y = "arccos y" in order_le_imp_less_or_eq)
   apply (drule_tac [2] y = pi in order_le_imp_less_or_eq)
   apply auto
   apply (drule_tac [!] f = cos in arg_cong)
   apply auto
  done

lemma arccos_cos: "0 \<le> x \<Longrightarrow> x \<le> pi \<Longrightarrow> arccos (cos x) = x"
  by (auto simp: arccos_def intro!: the1_equality cos_total)

lemma arccos_cos2: "x \<le> 0 \<Longrightarrow> - pi \<le> x \<Longrightarrow> arccos (cos x) = -x"
  by (auto simp: arccos_def intro!: the1_equality cos_total)

lemma cos_arcsin: "- 1 \<le> x \<Longrightarrow> x \<le> 1 \<Longrightarrow> cos (arcsin x) = sqrt (1 - x\<^sup>2)"
  apply (subgoal_tac "x\<^sup>2 \<le> 1")
   apply (rule power2_eq_imp_eq)
     apply (simp add: cos_squared_eq)
    apply (rule cos_ge_zero)
     apply (erule (1) arcsin_lbound)
    apply (erule (1) arcsin_ubound)
   apply simp
  apply (subgoal_tac "\<bar>x\<bar>\<^sup>2 \<le> 1\<^sup>2")
   apply simp
  apply (rule power_mono)
   apply simp
  apply simp
  done

lemma sin_arccos: "- 1 \<le> x \<Longrightarrow> x \<le> 1 \<Longrightarrow> sin (arccos x) = sqrt (1 - x\<^sup>2)"
  apply (subgoal_tac "x\<^sup>2 \<le> 1")
   apply (rule power2_eq_imp_eq)
     apply (simp add: sin_squared_eq)
    apply (rule sin_ge_zero)
     apply (erule (1) arccos_lbound)
    apply (erule (1) arccos_ubound)
   apply simp
  apply (subgoal_tac "\<bar>x\<bar>\<^sup>2 \<le> 1\<^sup>2")
   apply simp
  apply (rule power_mono)
   apply simp
  apply simp
  done

lemma arccos_0 [simp]: "arccos 0 = pi/2"
  by (metis arccos_cos cos_gt_zero cos_pi cos_pi_half pi_gt_zero
      pi_half_ge_zero not_le not_zero_less_neg_numeral numeral_One)

lemma arccos_1 [simp]: "arccos 1 = 0"
  using arccos_cos by force

lemma arccos_minus_1 [simp]: "arccos (- 1) = pi"
  by (metis arccos_cos cos_pi order_refl pi_ge_zero)

lemma arccos_minus: "-1 \<le> x \<Longrightarrow> x \<le> 1 \<Longrightarrow> arccos (- x) = pi - arccos x"
  by (metis arccos_cos arccos_cos2 cos_minus_pi cos_total diff_le_0_iff_le le_add_same_cancel1
      minus_diff_eq uminus_add_conv_diff)

lemma sin_arccos_nonzero: "- 1 < x \<Longrightarrow> x < 1 \<Longrightarrow> \<not> sin (arccos x) = 0"
  using arccos_lt_bounded sin_gt_zero by force

lemma arctan: "- (pi/2) < arctan y \<and> arctan y < pi/2 \<and> tan (arctan y) = y"
  unfolding arctan_def by (rule theI' [OF tan_total])

lemma tan_arctan: "tan (arctan y) = y"
  by (simp add: arctan)

lemma arctan_bounded: "- (pi/2) < arctan y \<and> arctan y < pi/2"
  by (auto simp only: arctan)

lemma arctan_lbound: "- (pi/2) < arctan y"
  by (simp add: arctan)

lemma arctan_ubound: "arctan y < pi/2"
  by (auto simp only: arctan)

lemma arctan_unique:
  assumes "-(pi/2) < x"
    and "x < pi/2"
    and "tan x = y"
  shows "arctan y = x"
  using assms arctan [of y] tan_total [of y] by (fast elim: ex1E)

lemma arctan_tan: "-(pi/2) < x \<Longrightarrow> x < pi/2 \<Longrightarrow> arctan (tan x) = x"
  by (rule arctan_unique) simp_all

lemma arctan_zero_zero [simp]: "arctan 0 = 0"
  by (rule arctan_unique) simp_all

lemma arctan_minus: "arctan (- x) = - arctan x"
  apply (rule arctan_unique)
    apply (simp only: neg_less_iff_less arctan_ubound)
   apply (metis minus_less_iff arctan_lbound)
  apply (simp add: arctan)
  done

lemma cos_arctan_not_zero [simp]: "cos (arctan x) \<noteq> 0"
  by (intro less_imp_neq [symmetric] cos_gt_zero_pi arctan_lbound arctan_ubound)

lemma cos_arctan: "cos (arctan x) = 1 / sqrt (1 + x\<^sup>2)"
proof (rule power2_eq_imp_eq)
  have "0 < 1 + x\<^sup>2" by (simp add: add_pos_nonneg)
  show "0 \<le> 1 / sqrt (1 + x\<^sup>2)" by simp
  show "0 \<le> cos (arctan x)"
    by (intro less_imp_le cos_gt_zero_pi arctan_lbound arctan_ubound)
  have "(cos (arctan x))\<^sup>2 * (1 + (tan (arctan x))\<^sup>2) = 1"
    unfolding tan_def by (simp add: distrib_left power_divide)
  then show "(cos (arctan x))\<^sup>2 = (1 / sqrt (1 + x\<^sup>2))\<^sup>2"
    using \<open>0 < 1 + x\<^sup>2\<close> by (simp add: arctan power_divide eq_divide_eq)
qed

lemma sin_arctan: "sin (arctan x) = x / sqrt (1 + x\<^sup>2)"
  using add_pos_nonneg [OF zero_less_one zero_le_power2 [of x]]
  using tan_arctan [of x] unfolding tan_def cos_arctan
  by (simp add: eq_divide_eq)

lemma tan_sec: "cos x \<noteq> 0 \<Longrightarrow> 1 + (tan x)\<^sup>2 = (inverse (cos x))\<^sup>2"
  for x :: "'a::{real_normed_field,banach,field}"
  apply (rule power_inverse [THEN subst])
  apply (rule_tac c1 = "(cos x)\<^sup>2" in mult_right_cancel [THEN iffD1])
   apply (auto simp add: tan_def field_simps)
  done

lemma arctan_less_iff: "arctan x < arctan y \<longleftrightarrow> x < y"
  by (metis tan_monotone' arctan_lbound arctan_ubound tan_arctan)

lemma arctan_le_iff: "arctan x \<le> arctan y \<longleftrightarrow> x \<le> y"
  by (simp only: not_less [symmetric] arctan_less_iff)

lemma arctan_eq_iff: "arctan x = arctan y \<longleftrightarrow> x = y"
  by (simp only: eq_iff [where 'a=real] arctan_le_iff)

lemma zero_less_arctan_iff [simp]: "0 < arctan x \<longleftrightarrow> 0 < x"
  using arctan_less_iff [of 0 x] by simp

lemma arctan_less_zero_iff [simp]: "arctan x < 0 \<longleftrightarrow> x < 0"
  using arctan_less_iff [of x 0] by simp

lemma zero_le_arctan_iff [simp]: "0 \<le> arctan x \<longleftrightarrow> 0 \<le> x"
  using arctan_le_iff [of 0 x] by simp

lemma arctan_le_zero_iff [simp]: "arctan x \<le> 0 \<longleftrightarrow> x \<le> 0"
  using arctan_le_iff [of x 0] by simp

lemma arctan_eq_zero_iff [simp]: "arctan x = 0 \<longleftrightarrow> x = 0"
  using arctan_eq_iff [of x 0] by simp

lemma continuous_on_arcsin': "continuous_on {-1 .. 1} arcsin"
proof -
  have "continuous_on (sin ` {- pi / 2 .. pi / 2}) arcsin"
    by (rule continuous_on_inv) (auto intro: continuous_intros simp: arcsin_sin)
  also have "sin ` {- pi / 2 .. pi / 2} = {-1 .. 1}"
  proof safe
    fix x :: real
    assume "x \<in> {-1..1}"
    then show "x \<in> sin ` {- pi / 2..pi / 2}"
      using arcsin_lbound arcsin_ubound
      by (intro image_eqI[where x="arcsin x"]) auto
  qed simp
  finally show ?thesis .
qed

lemma continuous_on_arcsin [continuous_intros]:
  "continuous_on s f \<Longrightarrow> (\<forall>x\<in>s. -1 \<le> f x \<and> f x \<le> 1) \<Longrightarrow> continuous_on s (\<lambda>x. arcsin (f x))"
  using continuous_on_compose[of s f, OF _ continuous_on_subset[OF  continuous_on_arcsin']]
  by (auto simp: comp_def subset_eq)

lemma isCont_arcsin: "-1 < x \<Longrightarrow> x < 1 \<Longrightarrow> isCont arcsin x"
  using continuous_on_arcsin'[THEN continuous_on_subset, of "{ -1 <..< 1 }"]
  by (auto simp: continuous_on_eq_continuous_at subset_eq)

lemma continuous_on_arccos': "continuous_on {-1 .. 1} arccos"
proof -
  have "continuous_on (cos ` {0 .. pi}) arccos"
    by (rule continuous_on_inv) (auto intro: continuous_intros simp: arccos_cos)
  also have "cos ` {0 .. pi} = {-1 .. 1}"
  proof safe
    fix x :: real
    assume "x \<in> {-1..1}"
    then show "x \<in> cos ` {0..pi}"
      using arccos_lbound arccos_ubound
      by (intro image_eqI[where x="arccos x"]) auto
  qed simp
  finally show ?thesis .
qed

lemma continuous_on_arccos [continuous_intros]:
  "continuous_on s f \<Longrightarrow> (\<forall>x\<in>s. -1 \<le> f x \<and> f x \<le> 1) \<Longrightarrow> continuous_on s (\<lambda>x. arccos (f x))"
  using continuous_on_compose[of s f, OF _ continuous_on_subset[OF  continuous_on_arccos']]
  by (auto simp: comp_def subset_eq)

lemma isCont_arccos: "-1 < x \<Longrightarrow> x < 1 \<Longrightarrow> isCont arccos x"
  using continuous_on_arccos'[THEN continuous_on_subset, of "{ -1 <..< 1 }"]
  by (auto simp: continuous_on_eq_continuous_at subset_eq)

lemma isCont_arctan: "isCont arctan x"
  apply (rule arctan_lbound [of x, THEN dense, THEN exE])
  apply clarify
  apply (rule arctan_ubound [of x, THEN dense, THEN exE])
  apply clarify
  apply (subgoal_tac "isCont arctan (tan (arctan x))")
   apply (simp add: arctan)
  apply (erule (1) isCont_inverse_function2 [where f=tan])
   apply (metis arctan_tan order_le_less_trans order_less_le_trans)
  apply (metis cos_gt_zero_pi isCont_tan order_less_le_trans less_le)
  done

lemma tendsto_arctan [tendsto_intros]: "(f \<longlongrightarrow> x) F \<Longrightarrow> ((\<lambda>x. arctan (f x)) \<longlongrightarrow> arctan x) F"
  by (rule isCont_tendsto_compose [OF isCont_arctan])

lemma continuous_arctan [continuous_intros]: "continuous F f \<Longrightarrow> continuous F (\<lambda>x. arctan (f x))"
  unfolding continuous_def by (rule tendsto_arctan)

lemma continuous_on_arctan [continuous_intros]:
  "continuous_on s f \<Longrightarrow> continuous_on s (\<lambda>x. arctan (f x))"
  unfolding continuous_on_def by (auto intro: tendsto_arctan)

lemma DERIV_arcsin: "- 1 < x \<Longrightarrow> x < 1 \<Longrightarrow> DERIV arcsin x :> inverse (sqrt (1 - x\<^sup>2))"
  apply (rule DERIV_inverse_function [where f=sin and a="-1" and b=1])
       apply (rule DERIV_cong [OF DERIV_sin])
       apply (simp add: cos_arcsin)
      apply (subgoal_tac "\<bar>x\<bar>\<^sup>2 < 1\<^sup>2")
       apply simp
      apply (rule power_strict_mono)
        apply simp
       apply simp
      apply simp
     apply assumption
    apply assumption
   apply simp
  apply (erule (1) isCont_arcsin)
  done

lemma DERIV_arccos: "- 1 < x \<Longrightarrow> x < 1 \<Longrightarrow> DERIV arccos x :> inverse (- sqrt (1 - x\<^sup>2))"
  apply (rule DERIV_inverse_function [where f=cos and a="-1" and b=1])
       apply (rule DERIV_cong [OF DERIV_cos])
       apply (simp add: sin_arccos)
      apply (subgoal_tac "\<bar>x\<bar>\<^sup>2 < 1\<^sup>2")
       apply simp
      apply (rule power_strict_mono)
        apply simp
       apply simp
      apply simp
     apply assumption
    apply assumption
   apply simp
  apply (erule (1) isCont_arccos)
  done

lemma DERIV_arctan: "DERIV arctan x :> inverse (1 + x\<^sup>2)"
  apply (rule DERIV_inverse_function [where f=tan and a="x - 1" and b="x + 1"])
       apply (rule DERIV_cong [OF DERIV_tan])
        apply (rule cos_arctan_not_zero)
       apply (simp_all add: add_pos_nonneg arctan isCont_arctan)
   apply (simp add: arctan power_inverse [symmetric] tan_sec [symmetric])
  apply (subgoal_tac "0 < 1 + x\<^sup>2")
   apply simp
  apply (simp_all add: add_pos_nonneg arctan isCont_arctan)
  done

declare
  DERIV_arcsin[THEN DERIV_chain2, derivative_intros]
  DERIV_arcsin[THEN DERIV_chain2, unfolded has_field_derivative_def, derivative_intros]
  DERIV_arccos[THEN DERIV_chain2, derivative_intros]
  DERIV_arccos[THEN DERIV_chain2, unfolded has_field_derivative_def, derivative_intros]
  DERIV_arctan[THEN DERIV_chain2, derivative_intros]
  DERIV_arctan[THEN DERIV_chain2, unfolded has_field_derivative_def, derivative_intros]

lemma filterlim_tan_at_right: "filterlim tan at_bot (at_right (- (pi/2)))"
  by (rule filterlim_at_bot_at_right[where Q="\<lambda>x. - pi/2 < x \<and> x < pi/2" and P="\<lambda>x. True" and g=arctan])
     (auto simp: arctan le_less eventually_at dist_real_def simp del: less_divide_eq_numeral1
           intro!: tan_monotone exI[of _ "pi/2"])

lemma filterlim_tan_at_left: "filterlim tan at_top (at_left (pi/2))"
  by (rule filterlim_at_top_at_left[where Q="\<lambda>x. - pi/2 < x \<and> x < pi/2" and P="\<lambda>x. True" and g=arctan])
     (auto simp: arctan le_less eventually_at dist_real_def simp del: less_divide_eq_numeral1
           intro!: tan_monotone exI[of _ "pi/2"])

lemma tendsto_arctan_at_top: "(arctan \<longlongrightarrow> (pi/2)) at_top"
proof (rule tendstoI)
  fix e :: real
  assume "0 < e"
  define y where "y = pi/2 - min (pi/2) e"
  then have y: "0 \<le> y" "y < pi/2" "pi/2 \<le> e + y"
    using \<open>0 < e\<close> by auto
  show "eventually (\<lambda>x. dist (arctan x) (pi / 2) < e) at_top"
  proof (intro eventually_at_top_dense[THEN iffD2] exI allI impI)
    fix x
    assume "tan y < x"
    then have "arctan (tan y) < arctan x"
      by (simp add: arctan_less_iff)
    with y have "y < arctan x"
      by (subst (asm) arctan_tan) simp_all
    with arctan_ubound[of x, arith] y \<open>0 < e\<close>
    show "dist (arctan x) (pi / 2) < e"
      by (simp add: dist_real_def)
  qed
qed

lemma tendsto_arctan_at_bot: "(arctan \<longlongrightarrow> - (pi/2)) at_bot"
  unfolding filterlim_at_bot_mirror arctan_minus
  by (intro tendsto_minus tendsto_arctan_at_top)


subsection \<open>Prove Totality of the Trigonometric Functions\<close>

lemma cos_arccos_abs: "\<bar>y\<bar> \<le> 1 \<Longrightarrow> cos (arccos y) = y"
  by (simp add: abs_le_iff)

lemma sin_arccos_abs: "\<bar>y\<bar> \<le> 1 \<Longrightarrow> sin (arccos y) = sqrt (1 - y\<^sup>2)"
  by (simp add: sin_arccos abs_le_iff)

lemma sin_mono_less_eq:
  "- (pi/2) \<le> x \<Longrightarrow> x \<le> pi/2 \<Longrightarrow> - (pi/2) \<le> y \<Longrightarrow> y \<le> pi/2 \<Longrightarrow> sin x < sin y \<longleftrightarrow> x < y"
  by (metis not_less_iff_gr_or_eq sin_monotone_2pi)

lemma sin_mono_le_eq:
  "- (pi/2) \<le> x \<Longrightarrow> x \<le> pi/2 \<Longrightarrow> - (pi/2) \<le> y \<Longrightarrow> y \<le> pi/2 \<Longrightarrow> sin x \<le> sin y \<longleftrightarrow> x \<le> y"
  by (meson leD le_less_linear sin_monotone_2pi sin_monotone_2pi_le)

lemma sin_inj_pi:
  "- (pi/2) \<le> x \<Longrightarrow> x \<le> pi/2 \<Longrightarrow> - (pi/2) \<le> y \<Longrightarrow> y \<le> pi/2 \<Longrightarrow> sin x = sin y \<Longrightarrow> x = y"
  by (metis arcsin_sin)

lemma cos_mono_less_eq: "0 \<le> x \<Longrightarrow> x \<le> pi \<Longrightarrow> 0 \<le> y \<Longrightarrow> y \<le> pi \<Longrightarrow> cos x < cos y \<longleftrightarrow> y < x"
  by (meson cos_monotone_0_pi cos_monotone_0_pi_le leD le_less_linear)

lemma cos_mono_le_eq: "0 \<le> x \<Longrightarrow> x \<le> pi \<Longrightarrow> 0 \<le> y \<Longrightarrow> y \<le> pi \<Longrightarrow> cos x \<le> cos y \<longleftrightarrow> y \<le> x"
  by (metis arccos_cos cos_monotone_0_pi_le eq_iff linear)

lemma cos_inj_pi: "0 \<le> x \<Longrightarrow> x \<le> pi \<Longrightarrow> 0 \<le> y \<Longrightarrow> y \<le> pi \<Longrightarrow> cos x = cos y \<Longrightarrow> x = y"
  by (metis arccos_cos)

lemma arccos_le_pi2: "\<lbrakk>0 \<le> y; y \<le> 1\<rbrakk> \<Longrightarrow> arccos y \<le> pi/2"
  by (metis (mono_tags) arccos_0 arccos cos_le_one cos_monotone_0_pi_le
      cos_pi cos_pi_half pi_half_ge_zero antisym_conv less_eq_neg_nonpos linear minus_minus order.trans order_refl)

lemma sincos_total_pi_half:
  assumes "0 \<le> x" "0 \<le> y" "x\<^sup>2 + y\<^sup>2 = 1"
  shows "\<exists>t. 0 \<le> t \<and> t \<le> pi/2 \<and> x = cos t \<and> y = sin t"
proof -
  have x1: "x \<le> 1"
    using assms by (metis le_add_same_cancel1 power2_le_imp_le power_one zero_le_power2)
  with assms have *: "0 \<le> arccos x" "cos (arccos x) = x"
    by (auto simp: arccos)
  from assms have "y = sqrt (1 - x\<^sup>2)"
    by (metis abs_of_nonneg add.commute add_diff_cancel real_sqrt_abs)
  with x1 * assms arccos_le_pi2 [of x] show ?thesis
    by (rule_tac x="arccos x" in exI) (auto simp: sin_arccos)
qed

lemma sincos_total_pi:
  assumes "0 \<le> y" "x\<^sup>2 + y\<^sup>2 = 1"
  shows "\<exists>t. 0 \<le> t \<and> t \<le> pi \<and> x = cos t \<and> y = sin t"
proof (cases rule: le_cases [of 0 x])
  case le
  from sincos_total_pi_half [OF le] show ?thesis
    by (metis pi_ge_two pi_half_le_two add.commute add_le_cancel_left add_mono assms)
next
  case ge
  then have "0 \<le> -x"
    by simp
  then obtain t where t: "t\<ge>0" "t \<le> pi/2" "-x = cos t" "y = sin t"
    using sincos_total_pi_half assms
    by auto (metis \<open>0 \<le> - x\<close> power2_minus)
  show ?thesis
    by (rule exI [where x = "pi -t"]) (use t in auto)
qed

lemma sincos_total_2pi_le:
  assumes "x\<^sup>2 + y\<^sup>2 = 1"
  shows "\<exists>t. 0 \<le> t \<and> t \<le> 2 * pi \<and> x = cos t \<and> y = sin t"
proof (cases rule: le_cases [of 0 y])
  case le
  from sincos_total_pi [OF le] show ?thesis
    by (metis assms le_add_same_cancel1 mult.commute mult_2_right order.trans)
next
  case ge
  then have "0 \<le> -y"
    by simp
  then obtain t where t: "t\<ge>0" "t \<le> pi" "x = cos t" "-y = sin t"
    using sincos_total_pi assms
    by auto (metis \<open>0 \<le> - y\<close> power2_minus)
  show ?thesis
    by (rule exI [where x = "2 * pi - t"]) (use t in auto)
qed

lemma sincos_total_2pi:
  assumes "x\<^sup>2 + y\<^sup>2 = 1"
  obtains t where "0 \<le> t" "t < 2*pi" "x = cos t" "y = sin t"
proof -
  from sincos_total_2pi_le [OF assms]
  obtain t where t: "0 \<le> t" "t \<le> 2*pi" "x = cos t" "y = sin t"
    by blast
  show ?thesis
    by (cases "t = 2 * pi") (use t that in \<open>force+\<close>)
qed

lemma arcsin_less_mono: "\<bar>x\<bar> \<le> 1 \<Longrightarrow> \<bar>y\<bar> \<le> 1 \<Longrightarrow> arcsin x < arcsin y \<longleftrightarrow> x < y"
  by (rule trans [OF sin_mono_less_eq [symmetric]]) (use arcsin_ubound arcsin_lbound in auto)

lemma arcsin_le_mono: "\<bar>x\<bar> \<le> 1 \<Longrightarrow> \<bar>y\<bar> \<le> 1 \<Longrightarrow> arcsin x \<le> arcsin y \<longleftrightarrow> x \<le> y"
  using arcsin_less_mono not_le by blast

lemma arcsin_less_arcsin: "- 1 \<le> x \<Longrightarrow> x < y \<Longrightarrow> y \<le> 1 \<Longrightarrow> arcsin x < arcsin y"
  using arcsin_less_mono by auto

lemma arcsin_le_arcsin: "- 1 \<le> x \<Longrightarrow> x \<le> y \<Longrightarrow> y \<le> 1 \<Longrightarrow> arcsin x \<le> arcsin y"
  using arcsin_le_mono by auto

lemma arccos_less_mono: "\<bar>x\<bar> \<le> 1 \<Longrightarrow> \<bar>y\<bar> \<le> 1 \<Longrightarrow> arccos x < arccos y \<longleftrightarrow> y < x"
  by (rule trans [OF cos_mono_less_eq [symmetric]]) (use arccos_ubound arccos_lbound in auto)

lemma arccos_le_mono: "\<bar>x\<bar> \<le> 1 \<Longrightarrow> \<bar>y\<bar> \<le> 1 \<Longrightarrow> arccos x \<le> arccos y \<longleftrightarrow> y \<le> x"
  using arccos_less_mono [of y x] by (simp add: not_le [symmetric])

lemma arccos_less_arccos: "- 1 \<le> x \<Longrightarrow> x < y \<Longrightarrow> y \<le> 1 \<Longrightarrow> arccos y < arccos x"
  using arccos_less_mono by auto

lemma arccos_le_arccos: "- 1 \<le> x \<Longrightarrow> x \<le> y \<Longrightarrow> y \<le> 1 \<Longrightarrow> arccos y \<le> arccos x"
  using arccos_le_mono by auto

lemma arccos_eq_iff: "\<bar>x\<bar> \<le> 1 \<and> \<bar>y\<bar> \<le> 1 \<Longrightarrow> arccos x = arccos y \<longleftrightarrow> x = y"
  using cos_arccos_abs by fastforce


subsection \<open>Machin's formula\<close>

lemma arctan_one: "arctan 1 = pi / 4"
  by (rule arctan_unique) (simp_all add: tan_45 m2pi_less_pi)

lemma tan_total_pi4:
  assumes "\<bar>x\<bar> < 1"
  shows "\<exists>z. - (pi / 4) < z \<and> z < pi / 4 \<and> tan z = x"
proof
  show "- (pi / 4) < arctan x \<and> arctan x < pi / 4 \<and> tan (arctan x) = x"
    unfolding arctan_one [symmetric] arctan_minus [symmetric]
    unfolding arctan_less_iff
    using assms by (auto simp add: arctan)
qed

lemma arctan_add:
  assumes "\<bar>x\<bar> \<le> 1" "\<bar>y\<bar> < 1"
  shows "arctan x + arctan y = arctan ((x + y) / (1 - x * y))"
proof (rule arctan_unique [symmetric])
  have "- (pi / 4) \<le> arctan x" "- (pi / 4) < arctan y"
    unfolding arctan_one [symmetric] arctan_minus [symmetric]
    unfolding arctan_le_iff arctan_less_iff
    using assms by auto
  from add_le_less_mono [OF this] show 1: "- (pi / 2) < arctan x + arctan y"
    by simp
  have "arctan x \<le> pi / 4" "arctan y < pi / 4"
    unfolding arctan_one [symmetric]
    unfolding arctan_le_iff arctan_less_iff
    using assms by auto
  from add_le_less_mono [OF this] show 2: "arctan x + arctan y < pi / 2"
    by simp
  show "tan (arctan x + arctan y) = (x + y) / (1 - x * y)"
    using cos_gt_zero_pi [OF 1 2] by (simp add: arctan tan_add)
qed

lemma arctan_double: "\<bar>x\<bar> < 1 \<Longrightarrow> 2 * arctan x = arctan ((2 * x) / (1 - x\<^sup>2))"
  by (metis arctan_add linear mult_2 not_less power2_eq_square)

theorem machin: "pi / 4 = 4 * arctan (1 / 5) - arctan (1 / 239)"
proof -
  have "\<bar>1 / 5\<bar> < (1 :: real)"
    by auto
  from arctan_add[OF less_imp_le[OF this] this] have "2 * arctan (1 / 5) = arctan (5 / 12)"
    by auto
  moreover
  have "\<bar>5 / 12\<bar> < (1 :: real)"
    by auto
  from arctan_add[OF less_imp_le[OF this] this] have "2 * arctan (5 / 12) = arctan (120 / 119)"
    by auto
  moreover
  have "\<bar>1\<bar> \<le> (1::real)" and "\<bar>1 / 239\<bar> < (1::real)"
    by auto
  from arctan_add[OF this] have "arctan 1 + arctan (1 / 239) = arctan (120 / 119)"
    by auto
  ultimately have "arctan 1 + arctan (1 / 239) = 4 * arctan (1 / 5)"
    by auto
  then show ?thesis
    unfolding arctan_one by algebra
qed

lemma machin_Euler: "5 * arctan (1 / 7) + 2 * arctan (3 / 79) = pi / 4"
proof -
  have 17: "\<bar>1 / 7\<bar> < (1 :: real)" by auto
  with arctan_double have "2 * arctan (1 / 7) = arctan (7 / 24)"
    by simp (simp add: field_simps)
  moreover
  have "\<bar>7 / 24\<bar> < (1 :: real)" by auto
  with arctan_double have "2 * arctan (7 / 24) = arctan (336 / 527)"
    by simp (simp add: field_simps)
  moreover
  have "\<bar>336 / 527\<bar> < (1 :: real)" by auto
  from arctan_add[OF less_imp_le[OF 17] this]
  have "arctan(1/7) + arctan (336 / 527) = arctan (2879 / 3353)"
    by auto
  ultimately have I: "5 * arctan (1 / 7) = arctan (2879 / 3353)" by auto
  have 379: "\<bar>3 / 79\<bar> < (1 :: real)" by auto
  with arctan_double have II: "2 * arctan (3 / 79) = arctan (237 / 3116)"
    by simp (simp add: field_simps)
  have *: "\<bar>2879 / 3353\<bar> < (1 :: real)" by auto
  have "\<bar>237 / 3116\<bar> < (1 :: real)" by auto
  from arctan_add[OF less_imp_le[OF *] this] have "arctan (2879/3353) + arctan (237/3116) = pi/4"
    by (simp add: arctan_one)
  with I II show ?thesis by auto
qed

(*But could also prove MACHIN_GAUSS:
  12 * arctan(1/18) + 8 * arctan(1/57) - 5 * arctan(1/239) = pi/4*)


subsection \<open>Introducing the inverse tangent power series\<close>

lemma monoseq_arctan_series:
  fixes x :: real
  assumes "\<bar>x\<bar> \<le> 1"
  shows "monoseq (\<lambda>n. 1 / real (n * 2 + 1) * x^(n * 2 + 1))"
    (is "monoseq ?a")
proof (cases "x = 0")
  case True
  then show ?thesis by (auto simp: monoseq_def)
next
  case False
  have "norm x \<le> 1" and "x \<le> 1" and "-1 \<le> x"
    using assms by auto
  show "monoseq ?a"
  proof -
    have mono: "1 / real (Suc (Suc n * 2)) * x ^ Suc (Suc n * 2) \<le>
        1 / real (Suc (n * 2)) * x ^ Suc (n * 2)"
      if "0 \<le> x" and "x \<le> 1" for n and x :: real
    proof (rule mult_mono)
      show "1 / real (Suc (Suc n * 2)) \<le> 1 / real (Suc (n * 2))"
        by (rule frac_le) simp_all
      show "0 \<le> 1 / real (Suc (n * 2))"
        by auto
      show "x ^ Suc (Suc n * 2) \<le> x ^ Suc (n * 2)"
        by (rule power_decreasing) (simp_all add: \<open>0 \<le> x\<close> \<open>x \<le> 1\<close>)
      show "0 \<le> x ^ Suc (Suc n * 2)"
        by (rule zero_le_power) (simp add: \<open>0 \<le> x\<close>)
    qed
    show ?thesis
    proof (cases "0 \<le> x")
      case True
      from mono[OF this \<open>x \<le> 1\<close>, THEN allI]
      show ?thesis
        unfolding Suc_eq_plus1[symmetric] by (rule mono_SucI2)
    next
      case False
      then have "0 \<le> - x" and "- x \<le> 1"
        using \<open>-1 \<le> x\<close> by auto
      from mono[OF this]
      have "1 / real (Suc (Suc n * 2)) * x ^ Suc (Suc n * 2) \<ge>
          1 / real (Suc (n * 2)) * x ^ Suc (n * 2)" for n
        using \<open>0 \<le> -x\<close> by auto
      then show ?thesis
        unfolding Suc_eq_plus1[symmetric] by (rule mono_SucI1[OF allI])
    qed
  qed
qed

lemma zeroseq_arctan_series:
  fixes x :: real
  assumes "\<bar>x\<bar> \<le> 1"
  shows "(\<lambda>n. 1 / real (n * 2 + 1) * x^(n * 2 + 1)) \<longlonglongrightarrow> 0"
    (is "?a \<longlonglongrightarrow> 0")
proof (cases "x = 0")
  case True
  then show ?thesis by simp
next
  case False
  have "norm x \<le> 1" and "x \<le> 1" and "-1 \<le> x"
    using assms by auto
  show "?a \<longlonglongrightarrow> 0"
  proof (cases "\<bar>x\<bar> < 1")
    case True
    then have "norm x < 1" by auto
    from tendsto_mult[OF LIMSEQ_inverse_real_of_nat LIMSEQ_power_zero[OF \<open>norm x < 1\<close>, THEN LIMSEQ_Suc]]
    have "(\<lambda>n. 1 / real (n + 1) * x ^ (n + 1)) \<longlonglongrightarrow> 0"
      unfolding inverse_eq_divide Suc_eq_plus1 by simp
    then show ?thesis
      using pos2 by (rule LIMSEQ_linear)
  next
    case False
    then have "x = -1 \<or> x = 1"
      using \<open>\<bar>x\<bar> \<le> 1\<close> by auto
    then have n_eq: "\<And> n. x ^ (n * 2 + 1) = x"
      unfolding One_nat_def by auto
    from tendsto_mult[OF LIMSEQ_inverse_real_of_nat[THEN LIMSEQ_linear, OF pos2, unfolded inverse_eq_divide] tendsto_const[of x]]
    show ?thesis
      unfolding n_eq Suc_eq_plus1 by auto
  qed
qed

lemma summable_arctan_series:
  fixes n :: nat
  assumes "\<bar>x\<bar> \<le> 1"
  shows "summable (\<lambda> k. (-1)^k * (1 / real (k*2+1) * x ^ (k*2+1)))"
    (is "summable (?c x)")
  by (rule summable_Leibniz(1),
      rule zeroseq_arctan_series[OF assms],
      rule monoseq_arctan_series[OF assms])

lemma DERIV_arctan_series:
  assumes "\<bar>x\<bar> < 1"
  shows "DERIV (\<lambda>x'. \<Sum>k. (-1)^k * (1 / real (k * 2 + 1) * x' ^ (k * 2 + 1))) x :>
      (\<Sum>k. (-1)^k * x^(k * 2))"
    (is "DERIV ?arctan _ :> ?Int")
proof -
  let ?f = "\<lambda>n. if even n then (-1)^(n div 2) * 1 / real (Suc n) else 0"

  have n_even: "even n \<Longrightarrow> 2 * (n div 2) = n" for n :: nat
    by presburger
  then have if_eq: "?f n * real (Suc n) * x'^n =
      (if even n then (-1)^(n div 2) * x'^(2 * (n div 2)) else 0)"
    for n x'
    by auto

  have summable_Integral: "summable (\<lambda> n. (- 1) ^ n * x^(2 * n))" if "\<bar>x\<bar> < 1" for x :: real
  proof -
    from that have "x\<^sup>2 < 1"
      by (simp add: abs_square_less_1)
    have "summable (\<lambda> n. (- 1) ^ n * (x\<^sup>2) ^n)"
      by (rule summable_Leibniz(1))
        (auto intro!: LIMSEQ_realpow_zero monoseq_realpow \<open>x\<^sup>2 < 1\<close> order_less_imp_le[OF \<open>x\<^sup>2 < 1\<close>])
    then show ?thesis
      by (simp only: power_mult)
  qed

  have sums_even: "op sums f = op sums (\<lambda> n. if even n then f (n div 2) else 0)"
    for f :: "nat \<Rightarrow> real"
  proof -
    have "f sums x = (\<lambda> n. if even n then f (n div 2) else 0) sums x" for x :: real
    proof
      assume "f sums x"
      from sums_if[OF sums_zero this] show "(\<lambda>n. if even n then f (n div 2) else 0) sums x"
        by auto
    next
      assume "(\<lambda> n. if even n then f (n div 2) else 0) sums x"
      from LIMSEQ_linear[OF this[simplified sums_def] pos2, simplified sum_split_even_odd[simplified mult.commute]]
      show "f sums x"
        unfolding sums_def by auto
    qed
    then show ?thesis ..
  qed

  have Int_eq: "(\<Sum>n. ?f n * real (Suc n) * x^n) = ?Int"
    unfolding if_eq mult.commute[of _ 2]
      suminf_def sums_even[of "\<lambda> n. (- 1) ^ n * x ^ (2 * n)", symmetric]
    by auto

  have arctan_eq: "(\<Sum>n. ?f n * x^(Suc n)) = ?arctan x" for x
  proof -
    have if_eq': "\<And>n. (if even n then (- 1) ^ (n div 2) * 1 / real (Suc n) else 0) * x ^ Suc n =
      (if even n then (- 1) ^ (n div 2) * (1 / real (Suc (2 * (n div 2))) * x ^ Suc (2 * (n div 2))) else 0)"
      using n_even by auto
    have idx_eq: "\<And>n. n * 2 + 1 = Suc (2 * n)"
      by auto
    then show ?thesis
      unfolding if_eq' idx_eq suminf_def
        sums_even[of "\<lambda> n. (- 1) ^ n * (1 / real (Suc (2 * n)) * x ^ Suc (2 * n))", symmetric]
      by auto
  qed

  have "DERIV (\<lambda> x. \<Sum> n. ?f n * x^(Suc n)) x :> (\<Sum>n. ?f n * real (Suc n) * x^n)"
  proof (rule DERIV_power_series')
    show "x \<in> {- 1 <..< 1}"
      using \<open>\<bar> x \<bar> < 1\<close> by auto
    show "summable (\<lambda> n. ?f n * real (Suc n) * x'^n)"
      if x'_bounds: "x' \<in> {- 1 <..< 1}" for x' :: real
    proof -
      from that have "\<bar>x'\<bar> < 1" by auto
      then have *: "summable (\<lambda>n. (- 1) ^ n * x' ^ (2 * n))"
        by (rule summable_Integral)
      show ?thesis
        unfolding if_eq
        apply (rule sums_summable [where l="0 + (\<Sum>n. (-1)^n * x'^(2 * n))"])
        apply (rule sums_if)
         apply (rule sums_zero)
        apply (rule summable_sums)
        apply (rule *)
        done
    qed
  qed auto
  then show ?thesis
    by (simp only: Int_eq arctan_eq)
qed

lemma arctan_series:
  assumes "\<bar>x\<bar> \<le> 1"
  shows "arctan x = (\<Sum>k. (-1)^k * (1 / real (k * 2 + 1) * x ^ (k * 2 + 1)))"
    (is "_ = suminf (\<lambda> n. ?c x n)")
proof -
  let ?c' = "\<lambda>x n. (-1)^n * x^(n*2)"

  have DERIV_arctan_suminf: "DERIV (\<lambda> x. suminf (?c x)) x :> (suminf (?c' x))"
    if "0 < r" and "r < 1" and "\<bar>x\<bar> < r" for r x :: real
  proof (rule DERIV_arctan_series)
    from that show "\<bar>x\<bar> < 1"
      using \<open>r < 1\<close> and \<open>\<bar>x\<bar> < r\<close> by auto
  qed

  {
    fix x :: real
    assume "\<bar>x\<bar> \<le> 1"
    note summable_Leibniz[OF zeroseq_arctan_series[OF this] monoseq_arctan_series[OF this]]
  } note arctan_series_borders = this

  have when_less_one: "arctan x = (\<Sum>k. ?c x k)" if "\<bar>x\<bar> < 1" for x :: real
  proof -
    obtain r where "\<bar>x\<bar> < r" and "r < 1"
      using dense[OF \<open>\<bar>x\<bar> < 1\<close>] by blast
    then have "0 < r" and "- r < x" and "x < r" by auto

    have suminf_eq_arctan_bounded: "suminf (?c x) - arctan x = suminf (?c a) - arctan a"
      if "-r < a" and "b < r" and "a < b" and "a \<le> x" and "x \<le> b" for x a b
    proof -
      from that have "\<bar>x\<bar> < r" by auto
      show "suminf (?c x) - arctan x = suminf (?c a) - arctan a"
      proof (rule DERIV_isconst2[of "a" "b"])
        show "a < b" and "a \<le> x" and "x \<le> b"
          using \<open>a < b\<close> \<open>a \<le> x\<close> \<open>x \<le> b\<close> by auto
        have "\<forall>x. - r < x \<and> x < r \<longrightarrow> DERIV (\<lambda> x. suminf (?c x) - arctan x) x :> 0"
        proof (rule allI, rule impI)
          fix x
          assume "-r < x \<and> x < r"
          then have "\<bar>x\<bar> < r" by auto
          with \<open>r < 1\<close> have "\<bar>x\<bar> < 1" by auto
          have "\<bar>- (x\<^sup>2)\<bar> < 1" using abs_square_less_1 \<open>\<bar>x\<bar> < 1\<close> by auto
          then have "(\<lambda>n. (- (x\<^sup>2)) ^ n) sums (1 / (1 - (- (x\<^sup>2))))"
            unfolding real_norm_def[symmetric] by (rule geometric_sums)
          then have "(?c' x) sums (1 / (1 - (- (x\<^sup>2))))"
            unfolding power_mult_distrib[symmetric] power_mult mult.commute[of _ 2] by auto
          then have suminf_c'_eq_geom: "inverse (1 + x\<^sup>2) = suminf (?c' x)"
            using sums_unique unfolding inverse_eq_divide by auto
          have "DERIV (\<lambda> x. suminf (?c x)) x :> (inverse (1 + x\<^sup>2))"
            unfolding suminf_c'_eq_geom
            by (rule DERIV_arctan_suminf[OF \<open>0 < r\<close> \<open>r < 1\<close> \<open>\<bar>x\<bar> < r\<close>])
          from DERIV_diff [OF this DERIV_arctan] show "DERIV (\<lambda>x. suminf (?c x) - arctan x) x :> 0"
            by auto
        qed
        then have DERIV_in_rball: "\<forall>y. a \<le> y \<and> y \<le> b \<longrightarrow> DERIV (\<lambda>x. suminf (?c x) - arctan x) y :> 0"
          using \<open>-r < a\<close> \<open>b < r\<close> by auto
        then show "\<forall>y. a < y \<and> y < b \<longrightarrow> DERIV (\<lambda>x. suminf (?c x) - arctan x) y :> 0"
          using \<open>\<bar>x\<bar> < r\<close> by auto
        show "\<forall>y. a \<le> y \<and> y \<le> b \<longrightarrow> isCont (\<lambda>x. suminf (?c x) - arctan x) y"
          using DERIV_in_rball DERIV_isCont by auto
      qed
    qed

    have suminf_arctan_zero: "suminf (?c 0) - arctan 0 = 0"
      unfolding Suc_eq_plus1[symmetric] power_Suc2 mult_zero_right arctan_zero_zero suminf_zero
      by auto

    have "suminf (?c x) - arctan x = 0"
    proof (cases "x = 0")
      case True
      then show ?thesis
        using suminf_arctan_zero by auto
    next
      case False
      then have "0 < \<bar>x\<bar>" and "- \<bar>x\<bar> < \<bar>x\<bar>"
        by auto
      have "suminf (?c (- \<bar>x\<bar>)) - arctan (- \<bar>x\<bar>) = suminf (?c 0) - arctan 0"
        by (rule suminf_eq_arctan_bounded[where x1="0" and a1="-\<bar>x\<bar>" and b1="\<bar>x\<bar>", symmetric])
          (simp_all only: \<open>\<bar>x\<bar> < r\<close> \<open>-\<bar>x\<bar> < \<bar>x\<bar>\<close> neg_less_iff_less)
      moreover
      have "suminf (?c x) - arctan x = suminf (?c (- \<bar>x\<bar>)) - arctan (- \<bar>x\<bar>)"
        by (rule suminf_eq_arctan_bounded[where x1="x" and a1="- \<bar>x\<bar>" and b1="\<bar>x\<bar>"])
           (simp_all only: \<open>\<bar>x\<bar> < r\<close> \<open>- \<bar>x\<bar> < \<bar>x\<bar>\<close> neg_less_iff_less)
      ultimately show ?thesis
        using suminf_arctan_zero by auto
    qed
    then show ?thesis by auto
  qed

  show "arctan x = suminf (\<lambda>n. ?c x n)"
  proof (cases "\<bar>x\<bar> < 1")
    case True
    then show ?thesis by (rule when_less_one)
  next
    case False
    then have "\<bar>x\<bar> = 1" using \<open>\<bar>x\<bar> \<le> 1\<close> by auto
    let ?a = "\<lambda>x n. \<bar>1 / real (n * 2 + 1) * x^(n * 2 + 1)\<bar>"
    let ?diff = "\<lambda>x n. \<bar>arctan x - (\<Sum>i<n. ?c x i)\<bar>"
    have "?diff 1 n \<le> ?a 1 n" for n :: nat
    proof -
      have "0 < (1 :: real)" by auto
      moreover
      have "?diff x n \<le> ?a x n" if "0 < x" and "x < 1" for x :: real
      proof -
        from that have "\<bar>x\<bar> \<le> 1" and "\<bar>x\<bar> < 1"
          by auto
        from \<open>0 < x\<close> have "0 < 1 / real (0 * 2 + (1::nat)) * x ^ (0 * 2 + 1)"
          by auto
        note bounds = mp[OF arctan_series_borders(2)[OF \<open>\<bar>x\<bar> \<le> 1\<close>] this, unfolded when_less_one[OF \<open>\<bar>x\<bar> < 1\<close>, symmetric], THEN spec]
        have "0 < 1 / real (n*2+1) * x^(n*2+1)"
          by (rule mult_pos_pos) (simp_all only: zero_less_power[OF \<open>0 < x\<close>], auto)
        then have a_pos: "?a x n = 1 / real (n*2+1) * x^(n*2+1)"
          by (rule abs_of_pos)
        show ?thesis
        proof (cases "even n")
          case True
          then have sgn_pos: "(-1)^n = (1::real)" by auto
          from \<open>even n\<close> obtain m where "n = 2 * m" ..
          then have "2 * m = n" ..
          from bounds[of m, unfolded this atLeastAtMost_iff]
          have "\<bar>arctan x - (\<Sum>i<n. (?c x i))\<bar> \<le> (\<Sum>i<n + 1. (?c x i)) - (\<Sum>i<n. (?c x i))"
            by auto
          also have "\<dots> = ?c x n" by auto
          also have "\<dots> = ?a x n" unfolding sgn_pos a_pos by auto
          finally show ?thesis .
        next
          case False
          then have sgn_neg: "(-1)^n = (-1::real)" by auto
          from \<open>odd n\<close> obtain m where "n = 2 * m + 1" ..
          then have m_def: "2 * m + 1 = n" ..
          then have m_plus: "2 * (m + 1) = n + 1" by auto
          from bounds[of "m + 1", unfolded this atLeastAtMost_iff, THEN conjunct1] bounds[of m, unfolded m_def atLeastAtMost_iff, THEN conjunct2]
          have "\<bar>arctan x - (\<Sum>i<n. (?c x i))\<bar> \<le> (\<Sum>i<n. (?c x i)) - (\<Sum>i<n+1. (?c x i))" by auto
          also have "\<dots> = - ?c x n" by auto
          also have "\<dots> = ?a x n" unfolding sgn_neg a_pos by auto
          finally show ?thesis .
        qed
      qed
      hence "\<forall>x \<in> { 0 <..< 1 }. 0 \<le> ?a x n - ?diff x n" by auto
      moreover have "isCont (\<lambda> x. ?a x n - ?diff x n) x" for x
        unfolding diff_conv_add_uminus divide_inverse
        by (auto intro!: isCont_add isCont_rabs continuous_ident isCont_minus isCont_arctan
          isCont_inverse isCont_mult isCont_power continuous_const isCont_sum
          simp del: add_uminus_conv_diff)
      ultimately have "0 \<le> ?a 1 n - ?diff 1 n"
        by (rule LIM_less_bound)
      then show ?thesis by auto
    qed
    have "?a 1 \<longlonglongrightarrow> 0"
      unfolding tendsto_rabs_zero_iff power_one divide_inverse One_nat_def
      by (auto intro!: tendsto_mult LIMSEQ_linear LIMSEQ_inverse_real_of_nat simp del: of_nat_Suc)
    have "?diff 1 \<longlonglongrightarrow> 0"
    proof (rule LIMSEQ_I)
      fix r :: real
      assume "0 < r"
      obtain N :: nat where N_I: "N \<le> n \<Longrightarrow> ?a 1 n < r" for n
        using LIMSEQ_D[OF \<open>?a 1 \<longlonglongrightarrow> 0\<close> \<open>0 < r\<close>] by auto
      have "norm (?diff 1 n - 0) < r" if "N \<le> n" for n
        using \<open>?diff 1 n \<le> ?a 1 n\<close> N_I[OF that] by auto
      then show "\<exists>N. \<forall> n \<ge> N. norm (?diff 1 n - 0) < r" by blast
    qed
    from this [unfolded tendsto_rabs_zero_iff, THEN tendsto_add [OF _ tendsto_const], of "- arctan 1", THEN tendsto_minus]
    have "(?c 1) sums (arctan 1)" unfolding sums_def by auto
    then have "arctan 1 = (\<Sum>i. ?c 1 i)" by (rule sums_unique)

    show ?thesis
    proof (cases "x = 1")
      case True
      then show ?thesis by (simp add: \<open>arctan 1 = (\<Sum> i. ?c 1 i)\<close>)
    next
      case False
      then have "x = -1" using \<open>\<bar>x\<bar> = 1\<close> by auto

      have "- (pi / 2) < 0" using pi_gt_zero by auto
      have "- (2 * pi) < 0" using pi_gt_zero by auto

      have c_minus_minus: "?c (- 1) i = - ?c 1 i" for i by auto

      have "arctan (- 1) = arctan (tan (-(pi / 4)))"
        unfolding tan_45 tan_minus ..
      also have "\<dots> = - (pi / 4)"
        by (rule arctan_tan) (auto simp: order_less_trans[OF \<open>- (pi / 2) < 0\<close> pi_gt_zero])
      also have "\<dots> = - (arctan (tan (pi / 4)))"
        unfolding neg_equal_iff_equal
        by (rule arctan_tan[symmetric]) (auto simp: order_less_trans[OF \<open>- (2 * pi) < 0\<close> pi_gt_zero])
      also have "\<dots> = - (arctan 1)"
        unfolding tan_45 ..
      also have "\<dots> = - (\<Sum> i. ?c 1 i)"
        using \<open>arctan 1 = (\<Sum> i. ?c 1 i)\<close> by auto
      also have "\<dots> = (\<Sum> i. ?c (- 1) i)"
        using suminf_minus[OF sums_summable[OF \<open>(?c 1) sums (arctan 1)\<close>]]
        unfolding c_minus_minus by auto
      finally show ?thesis using \<open>x = -1\<close> by auto
    qed
  qed
qed

lemma arctan_half: "arctan x = 2 * arctan (x / (1 + sqrt(1 + x\<^sup>2)))"
  for x :: real
proof -
  obtain y where low: "- (pi / 2) < y" and high: "y < pi / 2" and y_eq: "tan y = x"
    using tan_total by blast
  then have low2: "- (pi / 2) < y / 2" and high2: "y / 2 < pi / 2"
    by auto

  have "0 < cos y" by (rule cos_gt_zero_pi[OF low high])
  then have "cos y \<noteq> 0" and cos_sqrt: "sqrt ((cos y)\<^sup>2) = cos y"
    by auto

  have "1 + (tan y)\<^sup>2 = 1 + (sin y)\<^sup>2 / (cos y)\<^sup>2"
    unfolding tan_def power_divide ..
  also have "\<dots> = (cos y)\<^sup>2 / (cos y)\<^sup>2 + (sin y)\<^sup>2 / (cos y)\<^sup>2"
    using \<open>cos y \<noteq> 0\<close> by auto
  also have "\<dots> = 1 / (cos y)\<^sup>2"
    unfolding add_divide_distrib[symmetric] sin_cos_squared_add2 ..
  finally have "1 + (tan y)\<^sup>2 = 1 / (cos y)\<^sup>2" .

  have "sin y / (cos y + 1) = tan y / ((cos y + 1) / cos y)"
    unfolding tan_def using \<open>cos y \<noteq> 0\<close> by (simp add: field_simps)
  also have "\<dots> = tan y / (1 + 1 / cos y)"
    using \<open>cos y \<noteq> 0\<close> unfolding add_divide_distrib by auto
  also have "\<dots> = tan y / (1 + 1 / sqrt ((cos y)\<^sup>2))"
    unfolding cos_sqrt ..
  also have "\<dots> = tan y / (1 + sqrt (1 / (cos y)\<^sup>2))"
    unfolding real_sqrt_divide by auto
  finally have eq: "sin y / (cos y + 1) = tan y / (1 + sqrt(1 + (tan y)\<^sup>2))"
    unfolding \<open>1 + (tan y)\<^sup>2 = 1 / (cos y)\<^sup>2\<close> .

  have "arctan x = y"
    using arctan_tan low high y_eq by auto
  also have "\<dots> = 2 * (arctan (tan (y/2)))"
    using arctan_tan[OF low2 high2] by auto
  also have "\<dots> = 2 * (arctan (sin y / (cos y + 1)))"
    unfolding tan_half by auto
  finally show ?thesis
    unfolding eq \<open>tan y = x\<close> .
qed

lemma arctan_monotone: "x < y \<Longrightarrow> arctan x < arctan y"
  by (simp only: arctan_less_iff)

lemma arctan_monotone': "x \<le> y \<Longrightarrow> arctan x \<le> arctan y"
  by (simp only: arctan_le_iff)

lemma arctan_inverse:
  assumes "x \<noteq> 0"
  shows "arctan (1 / x) = sgn x * pi / 2 - arctan x"
proof (rule arctan_unique)
  show "- (pi / 2) < sgn x * pi / 2 - arctan x"
    using arctan_bounded [of x] assms
    unfolding sgn_real_def
    apply (auto simp add: arctan algebra_simps)
    apply (drule zero_less_arctan_iff [THEN iffD2])
    apply arith
    done
  show "sgn x * pi / 2 - arctan x < pi / 2"
    using arctan_bounded [of "- x"] assms
    unfolding sgn_real_def arctan_minus
    by (auto simp add: algebra_simps)
  show "tan (sgn x * pi / 2 - arctan x) = 1 / x"
    unfolding tan_inverse [of "arctan x", unfolded tan_arctan]
    unfolding sgn_real_def
    by (simp add: tan_def cos_arctan sin_arctan sin_diff cos_diff)
qed

theorem pi_series: "pi / 4 = (\<Sum>k. (-1)^k * 1 / real (k * 2 + 1))"
  (is "_ = ?SUM")
proof -
  have "pi / 4 = arctan 1"
    using arctan_one by auto
  also have "\<dots> = ?SUM"
    using arctan_series[of 1] by auto
  finally show ?thesis by auto
qed


subsection \<open>Existence of Polar Coordinates\<close>

lemma cos_x_y_le_one: "\<bar>x / sqrt (x\<^sup>2 + y\<^sup>2)\<bar> \<le> 1"
  by (rule power2_le_imp_le [OF _ zero_le_one])
    (simp add: power_divide divide_le_eq not_sum_power2_lt_zero)

lemmas cos_arccos_lemma1 = cos_arccos_abs [OF cos_x_y_le_one]

lemmas sin_arccos_lemma1 = sin_arccos_abs [OF cos_x_y_le_one]

lemma polar_Ex: "\<exists>r::real. \<exists>a. x = r * cos a \<and> y = r * sin a"
proof -
  have polar_ex1: "0 < y \<Longrightarrow> \<exists>r a. x = r * cos a \<and> y = r * sin a" for y
    apply (rule exI [where x = "sqrt (x\<^sup>2 + y\<^sup>2)"])
    apply (rule exI [where x = "arccos (x / sqrt (x\<^sup>2 + y\<^sup>2))"])
    apply (simp add: cos_arccos_lemma1 sin_arccos_lemma1 power_divide
        real_sqrt_mult [symmetric] right_diff_distrib)
    done
  show ?thesis
  proof (cases "0::real" y rule: linorder_cases)
    case less
    then show ?thesis
      by (rule polar_ex1)
  next
    case equal
    then show ?thesis
      by (force simp add: intro!: cos_zero sin_zero)
  next
    case greater
    with polar_ex1 [where y="-y"] show ?thesis
      by auto (metis cos_minus minus_minus minus_mult_right sin_minus)
  qed
qed


subsection \<open>Basics about polynomial functions: products, extremal behaviour and root counts\<close>

lemma pairs_le_eq_Sigma: "{(i, j). i + j \<le> m} = Sigma (atMost m) (\<lambda>r. atMost (m - r))"
  for m :: nat
  by auto

lemma sum_up_index_split: "(\<Sum>k\<le>m + n. f k) = (\<Sum>k\<le>m. f k) + (\<Sum>k = Suc m..m + n. f k)"
  by (metis atLeast0AtMost Suc_eq_plus1 le0 sum_ub_add_nat)

lemma Sigma_interval_disjoint: "(SIGMA i:A. {..v i}) \<inter> (SIGMA i:A.{v i<..w}) = {}"
  for w :: "'a::order"
  by auto

lemma product_atMost_eq_Un: "A \<times> {..m} = (SIGMA i:A.{..m - i}) \<union> (SIGMA i:A.{m - i<..m})"
  for m :: nat
  by auto

lemma polynomial_product: (*with thanks to Chaitanya Mangla*)
  fixes x :: "'a::idom"
  assumes m: "\<And>i. i > m \<Longrightarrow> a i = 0"
    and n: "\<And>j. j > n \<Longrightarrow> b j = 0"
  shows "(\<Sum>i\<le>m. (a i) * x ^ i) * (\<Sum>j\<le>n. (b j) * x ^ j) =
    (\<Sum>r\<le>m + n. (\<Sum>k\<le>r. (a k) * (b (r - k))) * x ^ r)"
proof -
  have "(\<Sum>i\<le>m. (a i) * x ^ i) * (\<Sum>j\<le>n. (b j) * x ^ j) = (\<Sum>i\<le>m. \<Sum>j\<le>n. (a i * x ^ i) * (b j * x ^ j))"
    by (rule sum_product)
  also have "\<dots> = (\<Sum>i\<le>m + n. \<Sum>j\<le>n + m. a i * x ^ i * (b j * x ^ j))"
    using assms by (auto simp: sum_up_index_split)
  also have "\<dots> = (\<Sum>r\<le>m + n. \<Sum>j\<le>m + n - r. a r * x ^ r * (b j * x ^ j))"
    apply (simp add: add_ac sum.Sigma product_atMost_eq_Un)
    apply (clarsimp simp add: sum_Un Sigma_interval_disjoint intro!: sum.neutral)
    apply (metis add_diff_assoc2 add.commute add_lessD1 leD m n nat_le_linear neqE)
    done
  also have "\<dots> = (\<Sum>(i,j)\<in>{(i,j). i+j \<le> m+n}. (a i * x ^ i) * (b j * x ^ j))"
    by (auto simp: pairs_le_eq_Sigma sum.Sigma)
  also have "\<dots> = (\<Sum>r\<le>m + n. (\<Sum>k\<le>r. (a k) * (b (r - k))) * x ^ r)"
    apply (subst sum_triangle_reindex_eq)
    apply (auto simp: algebra_simps sum_distrib_left intro!: sum.cong)
    apply (metis le_add_diff_inverse power_add)
    done
  finally show ?thesis .
qed

lemma polynomial_product_nat:
  fixes x :: nat
  assumes m: "\<And>i. i > m \<Longrightarrow> a i = 0"
    and n: "\<And>j. j > n \<Longrightarrow> b j = 0"
  shows "(\<Sum>i\<le>m. (a i) * x ^ i) * (\<Sum>j\<le>n. (b j) * x ^ j) =
    (\<Sum>r\<le>m + n. (\<Sum>k\<le>r. (a k) * (b (r - k))) * x ^ r)"
  using polynomial_product [of m a n b x] assms
  by (simp only: of_nat_mult [symmetric] of_nat_power [symmetric]
      of_nat_eq_iff Int.int_sum [symmetric])

lemma polyfun_diff: (*COMPLEX_SUB_POLYFUN in HOL Light*)
  fixes x :: "'a::idom"
  assumes "1 \<le> n"
  shows "(\<Sum>i\<le>n. a i * x^i) - (\<Sum>i\<le>n. a i * y^i) =
    (x - y) * (\<Sum>j<n. (\<Sum>i=Suc j..n. a i * y^(i - j - 1)) * x^j)"
proof -
  have h: "bij_betw (\<lambda>(i,j). (j,i)) ((SIGMA i : atMost n. lessThan i)) (SIGMA j : lessThan n. {Suc j..n})"
    by (auto simp: bij_betw_def inj_on_def)
  have "(\<Sum>i\<le>n. a i * x^i) - (\<Sum>i\<le>n. a i * y^i) = (\<Sum>i\<le>n. a i * (x^i - y^i))"
    by (simp add: right_diff_distrib sum_subtractf)
  also have "\<dots> = (\<Sum>i\<le>n. a i * (x - y) * (\<Sum>j<i. y^(i - Suc j) * x^j))"
    by (simp add: power_diff_sumr2 mult.assoc)
  also have "\<dots> = (\<Sum>i\<le>n. \<Sum>j<i. a i * (x - y) * (y^(i - Suc j) * x^j))"
    by (simp add: sum_distrib_left)
  also have "\<dots> = (\<Sum>(i,j) \<in> (SIGMA i : atMost n. lessThan i). a i * (x - y) * (y^(i - Suc j) * x^j))"
    by (simp add: sum.Sigma)
  also have "\<dots> = (\<Sum>(j,i) \<in> (SIGMA j : lessThan n. {Suc j..n}). a i * (x - y) * (y^(i - Suc j) * x^j))"
    by (auto simp add: sum.reindex_bij_betw [OF h, symmetric] intro: sum.strong_cong)
  also have "\<dots> = (\<Sum>j<n. \<Sum>i=Suc j..n. a i * (x - y) * (y^(i - Suc j) * x^j))"
    by (simp add: sum.Sigma)
  also have "\<dots> = (x - y) * (\<Sum>j<n. (\<Sum>i=Suc j..n. a i * y^(i - j - 1)) * x^j)"
    by (simp add: sum_distrib_left mult_ac)
  finally show ?thesis .
qed

lemma polyfun_diff_alt: (*COMPLEX_SUB_POLYFUN_ALT in HOL Light*)
  fixes x :: "'a::idom"
  assumes "1 \<le> n"
  shows "(\<Sum>i\<le>n. a i * x^i) - (\<Sum>i\<le>n. a i * y^i) =
    (x - y) * ((\<Sum>j<n. \<Sum>k<n-j. a(j + k + 1) * y^k * x^j))"
proof -
  have "(\<Sum>i=Suc j..n. a i * y^(i - j - 1)) = (\<Sum>k<n-j. a(j+k+1) * y^k)"
    if "j < n" for j :: nat
  proof -
    have h: "bij_betw (\<lambda>i. i - (j + 1)) {Suc j..n} (lessThan (n-j))"
      apply (auto simp: bij_betw_def inj_on_def)
      apply (rule_tac x="x + Suc j" in image_eqI)
       apply (auto simp: )
      done
    then show ?thesis
      by (auto simp add: sum.reindex_bij_betw [OF h, symmetric] intro: sum.strong_cong)
  qed
  then show ?thesis
    by (simp add: polyfun_diff [OF assms] sum_distrib_right)
qed

lemma polyfun_linear_factor:  (*COMPLEX_POLYFUN_LINEAR_FACTOR in HOL Light*)
  fixes a :: "'a::idom"
  shows "\<exists>b. \<forall>z. (\<Sum>i\<le>n. c(i) * z^i) = (z - a) * (\<Sum>i<n. b(i) * z^i) + (\<Sum>i\<le>n. c(i) * a^i)"
proof (cases "n = 0")
  case True then show ?thesis
    by simp
next
  case False
  have "(\<exists>b. \<forall>z. (\<Sum>i\<le>n. c i * z^i) = (z - a) * (\<Sum>i<n. b i * z^i) + (\<Sum>i\<le>n. c i * a^i)) \<longleftrightarrow>
        (\<exists>b. \<forall>z. (\<Sum>i\<le>n. c i * z^i) - (\<Sum>i\<le>n. c i * a^i) = (z - a) * (\<Sum>i<n. b i * z^i))"
    by (simp add: algebra_simps)
  also have "\<dots> \<longleftrightarrow>
    (\<exists>b. \<forall>z. (z - a) * (\<Sum>j<n. (\<Sum>i = Suc j..n. c i * a^(i - Suc j)) * z^j) =
      (z - a) * (\<Sum>i<n. b i * z^i))"
    using False by (simp add: polyfun_diff)
  also have "\<dots> = True" by auto
  finally show ?thesis
    by simp
qed

lemma polyfun_linear_factor_root:  (*COMPLEX_POLYFUN_LINEAR_FACTOR_ROOT in HOL Light*)
  fixes a :: "'a::idom"
  assumes "(\<Sum>i\<le>n. c(i) * a^i) = 0"
  obtains b where "\<And>z. (\<Sum>i\<le>n. c i * z^i) = (z - a) * (\<Sum>i<n. b i * z^i)"
  using polyfun_linear_factor [of c n a] assms by auto

(*The material of this section, up until this point, could go into a new theory of polynomials
  based on Main alone. The remaining material involves limits, continuity, series, etc.*)

lemma isCont_polynom: "isCont (\<lambda>w. \<Sum>i\<le>n. c i * w^i) a"
  for c :: "nat \<Rightarrow> 'a::real_normed_div_algebra"
  by simp

lemma zero_polynom_imp_zero_coeffs:
  fixes c :: "nat \<Rightarrow> 'a::{ab_semigroup_mult,real_normed_div_algebra}"
  assumes "\<And>w. (\<Sum>i\<le>n. c i * w^i) = 0"  "k \<le> n"
  shows "c k = 0"
  using assms
proof (induction n arbitrary: c k)
  case 0
  then show ?case
    by simp
next
  case (Suc n c k)
  have [simp]: "c 0 = 0" using Suc.prems(1) [of 0]
    by simp
  have "(\<Sum>i\<le>Suc n. c i * w^i) = w * (\<Sum>i\<le>n. c (Suc i) * w^i)" for w
  proof -
    have "(\<Sum>i\<le>Suc n. c i * w^i) = (\<Sum>i\<le>n. c (Suc i) * w ^ Suc i)"
      unfolding Set_Interval.sum_atMost_Suc_shift
      by simp
    also have "\<dots> = w * (\<Sum>i\<le>n. c (Suc i) * w^i)"
      by (simp add: sum_distrib_left ac_simps)
    finally show ?thesis .
  qed
  then have w: "\<And>w. w \<noteq> 0 \<Longrightarrow> (\<Sum>i\<le>n. c (Suc i) * w^i) = 0"
    using Suc  by auto
  then have "(\<lambda>h. \<Sum>i\<le>n. c (Suc i) * h^i) \<midarrow>0\<rightarrow> 0"
    by (simp cong: LIM_cong)  \<comment> \<open>the case \<open>w = 0\<close> by continuity\<close>
  then have "(\<Sum>i\<le>n. c (Suc i) * 0^i) = 0"
    using isCont_polynom [of 0 "\<lambda>i. c (Suc i)" n] LIM_unique
    by (force simp add: Limits.isCont_iff)
  then have "\<And>w. (\<Sum>i\<le>n. c (Suc i) * w^i) = 0"
    using w by metis
  then have "\<And>i. i \<le> n \<Longrightarrow> c (Suc i) = 0"
    using Suc.IH [of "\<lambda>i. c (Suc i)"] by blast
  then show ?case using \<open>k \<le> Suc n\<close>
    by (cases k) auto
qed

lemma polyfun_rootbound: (*COMPLEX_POLYFUN_ROOTBOUND in HOL Light*)
  fixes c :: "nat \<Rightarrow> 'a::{idom,real_normed_div_algebra}"
  assumes "c k \<noteq> 0" "k\<le>n"
  shows "finite {z. (\<Sum>i\<le>n. c(i) * z^i) = 0} \<and> card {z. (\<Sum>i\<le>n. c(i) * z^i) = 0} \<le> n"
  using assms
proof (induction n arbitrary: c k)
  case 0
  then show ?case
    by simp
next
  case (Suc m c k)
  let ?succase = ?case
  show ?case
  proof (cases "{z. (\<Sum>i\<le>Suc m. c(i) * z^i) = 0} = {}")
    case True
    then show ?succase
      by simp
  next
    case False
    then obtain z0 where z0: "(\<Sum>i\<le>Suc m. c(i) * z0^i) = 0"
      by blast
    then obtain b where b: "\<And>w. (\<Sum>i\<le>Suc m. c i * w^i) = (w - z0) * (\<Sum>i\<le>m. b i * w^i)"
      using polyfun_linear_factor_root [OF z0, unfolded lessThan_Suc_atMost]
      by blast
    then have eq: "{z. (\<Sum>i\<le>Suc m. c i * z^i) = 0} = insert z0 {z. (\<Sum>i\<le>m. b i * z^i) = 0}"
      by auto
    have "\<not> (\<forall>k\<le>m. b k = 0)"
    proof
      assume [simp]: "\<forall>k\<le>m. b k = 0"
      then have "\<And>w. (\<Sum>i\<le>m. b i * w^i) = 0"
        by simp
      then have "\<And>w. (\<Sum>i\<le>Suc m. c i * w^i) = 0"
        using b by simp
      then have "\<And>k. k \<le> Suc m \<Longrightarrow> c k = 0"
        using zero_polynom_imp_zero_coeffs by blast
      then show False using Suc.prems by blast
    qed
    then obtain k' where bk': "b k' \<noteq> 0" "k' \<le> m"
      by blast
    show ?succase
      using Suc.IH [of b k'] bk'
      by (simp add: eq card_insert_if del: sum_atMost_Suc)
    qed
qed

lemma
  fixes c :: "nat \<Rightarrow> 'a::{idom,real_normed_div_algebra}"
  assumes "c k \<noteq> 0" "k\<le>n"
  shows polyfun_roots_finite: "finite {z. (\<Sum>i\<le>n. c(i) * z^i) = 0}"
    and polyfun_roots_card: "card {z. (\<Sum>i\<le>n. c(i) * z^i) = 0} \<le> n"
  using polyfun_rootbound assms by auto

lemma polyfun_finite_roots: (*COMPLEX_POLYFUN_FINITE_ROOTS in HOL Light*)
  fixes c :: "nat \<Rightarrow> 'a::{idom,real_normed_div_algebra}"
  shows "finite {x. (\<Sum>i\<le>n. c i * x^i) = 0} \<longleftrightarrow> (\<exists>i\<le>n. c i \<noteq> 0)"
    (is "?lhs = ?rhs")
proof
  assume ?lhs
  moreover have "\<not> finite {x. (\<Sum>i\<le>n. c i * x^i) = 0}" if "\<forall>i\<le>n. c i = 0"
  proof -
    from that have "\<And>x. (\<Sum>i\<le>n. c i * x^i) = 0"
      by simp
    then show ?thesis
      using ex_new_if_finite [OF infinite_UNIV_char_0 [where 'a='a]]
      by auto
  qed
  ultimately show ?rhs by metis
next
  assume ?rhs
  with polyfun_rootbound show ?lhs by blast
qed

lemma polyfun_eq_0: "(\<forall>x. (\<Sum>i\<le>n. c i * x^i) = 0) \<longleftrightarrow> (\<forall>i\<le>n. c i = 0)"
  for c :: "nat \<Rightarrow> 'a::{idom,real_normed_div_algebra}"
  (*COMPLEX_POLYFUN_EQ_0 in HOL Light*)
  using zero_polynom_imp_zero_coeffs by auto

lemma polyfun_eq_coeffs: "(\<forall>x. (\<Sum>i\<le>n. c i * x^i) = (\<Sum>i\<le>n. d i * x^i)) \<longleftrightarrow> (\<forall>i\<le>n. c i = d i)"
  for c :: "nat \<Rightarrow> 'a::{idom,real_normed_div_algebra}"
proof -
  have "(\<forall>x. (\<Sum>i\<le>n. c i * x^i) = (\<Sum>i\<le>n. d i * x^i)) \<longleftrightarrow> (\<forall>x. (\<Sum>i\<le>n. (c i - d i) * x^i) = 0)"
    by (simp add: left_diff_distrib Groups_Big.sum_subtractf)
  also have "\<dots> \<longleftrightarrow> (\<forall>i\<le>n. c i - d i = 0)"
    by (rule polyfun_eq_0)
  finally show ?thesis
    by simp
qed

lemma polyfun_eq_const: (*COMPLEX_POLYFUN_EQ_CONST in HOL Light*)
  fixes c :: "nat \<Rightarrow> 'a::{idom,real_normed_div_algebra}"
  shows "(\<forall>x. (\<Sum>i\<le>n. c i * x^i) = k) \<longleftrightarrow> c 0 = k \<and> (\<forall>i \<in> {1..n}. c i = 0)"
    (is "?lhs = ?rhs")
proof -
  have *: "\<forall>x. (\<Sum>i\<le>n. (if i=0 then k else 0) * x^i) = k"
    by (induct n) auto
  show ?thesis
  proof
    assume ?lhs
    with * have "(\<forall>i\<le>n. c i = (if i=0 then k else 0))"
      by (simp add: polyfun_eq_coeffs [symmetric])
    then show ?rhs by simp
  next
    assume ?rhs
    then show ?lhs by (induct n) auto
  qed
qed

lemma root_polyfun:
  fixes z :: "'a::idom"
  assumes "1 \<le> n"
  shows "z^n = a \<longleftrightarrow> (\<Sum>i\<le>n. (if i = 0 then -a else if i=n then 1 else 0) * z^i) = 0"
  using assms by (cases n) (simp_all add: sum_head_Suc atLeast0AtMost [symmetric])

lemma
  assumes "SORT_CONSTRAINT('a::{idom,real_normed_div_algebra})"
    and "1 \<le> n"
  shows finite_roots_unity: "finite {z::'a. z^n = 1}"
    and card_roots_unity: "card {z::'a. z^n = 1} \<le> n"
  using polyfun_rootbound [of "\<lambda>i. if i = 0 then -1 else if i=n then 1 else 0" n n] assms(2)
  by (auto simp add: root_polyfun [OF assms(2)])

end
