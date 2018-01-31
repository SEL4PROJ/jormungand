 (* Author:     Johannes Hoelzl, TU Muenchen
   Coercions removed by Dmitriy Traytel *)

section \<open>Prove Real Valued Inequalities by Computation\<close>

theory Approximation
imports
  Complex_Main
  "~~/src/HOL/Library/Float"
  Dense_Linear_Order
  "~~/src/HOL/Library/Code_Target_Numeral"
keywords "approximate" :: diag
begin

declare powr_numeral [simp]
declare powr_neg_one [simp]
declare powr_neg_numeral [simp]

section "Horner Scheme"

subsection \<open>Define auxiliary helper \<open>horner\<close> function\<close>

primrec horner :: "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real" where
"horner F G 0 i k x       = 0" |
"horner F G (Suc n) i k x = 1 / k - x * horner F G n (F i) (G i k) x"

lemma horner_schema':
  fixes x :: real and a :: "nat \<Rightarrow> real"
  shows "a 0 - x * (\<Sum> i=0..<n. (-1)^i * a (Suc i) * x^i) = (\<Sum> i=0..<Suc n. (-1)^i * a i * x^i)"
proof -
  have shift_pow: "\<And>i. - (x * ((-1)^i * a (Suc i) * x ^ i)) = (-1)^(Suc i) * a (Suc i) * x ^ (Suc i)"
    by auto
  show ?thesis
    unfolding sum_distrib_left shift_pow uminus_add_conv_diff [symmetric] sum_negf[symmetric]
    sum_head_upt_Suc[OF zero_less_Suc]
    sum.reindex[OF inj_Suc, unfolded comp_def, symmetric, of "\<lambda> n. (-1)^n  *a n * x^n"] by auto
qed

lemma horner_schema:
  fixes f :: "nat \<Rightarrow> nat" and G :: "nat \<Rightarrow> nat \<Rightarrow> nat" and F :: "nat \<Rightarrow> nat"
  assumes f_Suc: "\<And>n. f (Suc n) = G ((F ^^ n) s) (f n)"
  shows "horner F G n ((F ^^ j') s) (f j') x = (\<Sum> j = 0..< n. (- 1) ^ j * (1 / (f (j' + j))) * x ^ j)"
proof (induct n arbitrary: j')
  case 0
  then show ?case by auto
next
  case (Suc n)
  show ?case unfolding horner.simps Suc[where j'="Suc j'", unfolded funpow.simps comp_def f_Suc]
    using horner_schema'[of "\<lambda> j. 1 / (f (j' + j))"] by auto
qed

lemma horner_bounds':
  fixes lb :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> float \<Rightarrow> float" and ub :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> float \<Rightarrow> float"
  assumes "0 \<le> real_of_float x" and f_Suc: "\<And>n. f (Suc n) = G ((F ^^ n) s) (f n)"
    and lb_0: "\<And> i k x. lb 0 i k x = 0"
    and lb_Suc: "\<And> n i k x. lb (Suc n) i k x = float_plus_down prec
        (lapprox_rat prec 1 k)
        (- float_round_up prec (x * (ub n (F i) (G i k) x)))"
    and ub_0: "\<And> i k x. ub 0 i k x = 0"
    and ub_Suc: "\<And> n i k x. ub (Suc n) i k x = float_plus_up prec
        (rapprox_rat prec 1 k)
        (- float_round_down prec (x * (lb n (F i) (G i k) x)))"
  shows "(lb n ((F ^^ j') s) (f j') x) \<le> horner F G n ((F ^^ j') s) (f j') x \<and>
         horner F G n ((F ^^ j') s) (f j') x \<le> (ub n ((F ^^ j') s) (f j') x)"
  (is "?lb n j' \<le> ?horner n j' \<and> ?horner n j' \<le> ?ub n j'")
proof (induct n arbitrary: j')
  case 0
  thus ?case unfolding lb_0 ub_0 horner.simps by auto
next
  case (Suc n)
  thus ?case using lapprox_rat[of prec 1 "f j'"] using rapprox_rat[of 1 "f j'" prec]
    Suc[where j'="Suc j'"] \<open>0 \<le> real_of_float x\<close>
    by (auto intro!: add_mono mult_left_mono float_round_down_le float_round_up_le
      order_trans[OF add_mono[OF _ float_plus_down_le]]
      order_trans[OF _ add_mono[OF _ float_plus_up_le]]
      simp add: lb_Suc ub_Suc field_simps f_Suc)
qed

subsection "Theorems for floating point functions implementing the horner scheme"

text \<open>

Here @{term_type "f :: nat \<Rightarrow> nat"} is the sequence defining the Taylor series, the coefficients are
all alternating and reciprocs. We use @{term G} and @{term F} to describe the computation of @{term f}.

\<close>

lemma horner_bounds:
  fixes F :: "nat \<Rightarrow> nat" and G :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  assumes "0 \<le> real_of_float x" and f_Suc: "\<And>n. f (Suc n) = G ((F ^^ n) s) (f n)"
    and lb_0: "\<And> i k x. lb 0 i k x = 0"
    and lb_Suc: "\<And> n i k x. lb (Suc n) i k x = float_plus_down prec
        (lapprox_rat prec 1 k)
        (- float_round_up prec (x * (ub n (F i) (G i k) x)))"
    and ub_0: "\<And> i k x. ub 0 i k x = 0"
    and ub_Suc: "\<And> n i k x. ub (Suc n) i k x = float_plus_up prec
        (rapprox_rat prec 1 k)
        (- float_round_down prec (x * (lb n (F i) (G i k) x)))"
  shows "(lb n ((F ^^ j') s) (f j') x) \<le> (\<Sum>j=0..<n. (- 1) ^ j * (1 / (f (j' + j))) * (x ^ j))"
      (is "?lb")
    and "(\<Sum>j=0..<n. (- 1) ^ j * (1 / (f (j' + j))) * (x ^ j)) \<le> (ub n ((F ^^ j') s) (f j') x)"
      (is "?ub")
proof -
  have "?lb  \<and> ?ub"
    using horner_bounds'[where lb=lb, OF \<open>0 \<le> real_of_float x\<close> f_Suc lb_0 lb_Suc ub_0 ub_Suc]
    unfolding horner_schema[where f=f, OF f_Suc] by simp
  thus "?lb" and "?ub" by auto
qed

lemma horner_bounds_nonpos:
  fixes F :: "nat \<Rightarrow> nat" and G :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  assumes "real_of_float x \<le> 0" and f_Suc: "\<And>n. f (Suc n) = G ((F ^^ n) s) (f n)"
    and lb_0: "\<And> i k x. lb 0 i k x = 0"
    and lb_Suc: "\<And> n i k x. lb (Suc n) i k x = float_plus_down prec
        (lapprox_rat prec 1 k)
        (float_round_down prec (x * (ub n (F i) (G i k) x)))"
    and ub_0: "\<And> i k x. ub 0 i k x = 0"
    and ub_Suc: "\<And> n i k x. ub (Suc n) i k x = float_plus_up prec
        (rapprox_rat prec 1 k)
        (float_round_up prec (x * (lb n (F i) (G i k) x)))"
  shows "(lb n ((F ^^ j') s) (f j') x) \<le> (\<Sum>j=0..<n. (1 / (f (j' + j))) * real_of_float x ^ j)" (is "?lb")
    and "(\<Sum>j=0..<n. (1 / (f (j' + j))) * real_of_float x ^ j) \<le> (ub n ((F ^^ j') s) (f j') x)" (is "?ub")
proof -
  have diff_mult_minus: "x - y * z = x + - y * z" for x y z :: float by simp
  have sum_eq: "(\<Sum>j=0..<n. (1 / (f (j' + j))) * real_of_float x ^ j) =
    (\<Sum>j = 0..<n. (- 1) ^ j * (1 / (f (j' + j))) * real_of_float (- x) ^ j)"
    by (auto simp add: field_simps power_mult_distrib[symmetric])
  have "0 \<le> real_of_float (-x)" using assms by auto
  from horner_bounds[where G=G and F=F and f=f and s=s and prec=prec
    and lb="\<lambda> n i k x. lb n i k (-x)" and ub="\<lambda> n i k x. ub n i k (-x)",
    unfolded lb_Suc ub_Suc diff_mult_minus,
    OF this f_Suc lb_0 _ ub_0 _]
  show "?lb" and "?ub" unfolding minus_minus sum_eq
    by (auto simp: minus_float_round_up_eq minus_float_round_down_eq)
qed


subsection \<open>Selectors for next even or odd number\<close>

text \<open>
The horner scheme computes alternating series. To get the upper and lower bounds we need to
guarantee to access a even or odd member. To do this we use @{term get_odd} and @{term get_even}.
\<close>

definition get_odd :: "nat \<Rightarrow> nat" where
  "get_odd n = (if odd n then n else (Suc n))"

definition get_even :: "nat \<Rightarrow> nat" where
  "get_even n = (if even n then n else (Suc n))"

lemma get_odd[simp]: "odd (get_odd n)"
  unfolding get_odd_def by (cases "odd n") auto

lemma get_even[simp]: "even (get_even n)"
  unfolding get_even_def by (cases "even n") auto

lemma get_odd_ex: "\<exists> k. Suc k = get_odd n \<and> odd (Suc k)"
  by (auto simp: get_odd_def odd_pos intro!: exI[of _ "n - 1"])

lemma get_even_double: "\<exists>i. get_even n = 2 * i"
  using get_even by (blast elim: evenE)

lemma get_odd_double: "\<exists>i. get_odd n = 2 * i + 1"
  using get_odd by (blast elim: oddE)


section "Power function"

definition float_power_bnds :: "nat \<Rightarrow> nat \<Rightarrow> float \<Rightarrow> float \<Rightarrow> float * float" where
"float_power_bnds prec n l u =
  (if 0 < l then (power_down_fl prec l n, power_up_fl prec u n)
  else if odd n then
    (- power_up_fl prec \<bar>l\<bar> n,
      if u < 0 then - power_down_fl prec \<bar>u\<bar> n else power_up_fl prec u n)
  else if u < 0 then (power_down_fl prec \<bar>u\<bar> n, power_up_fl prec \<bar>l\<bar> n)
  else (0, power_up_fl prec (max \<bar>l\<bar> \<bar>u\<bar>) n))"

lemma le_minus_power_downI: "0 \<le> x \<Longrightarrow> x ^ n \<le> - a \<Longrightarrow> a \<le> - power_down prec x n"
  by (subst le_minus_iff) (auto intro: power_down_le power_mono_odd)

lemma float_power_bnds:
  "(l1, u1) = float_power_bnds prec n l u \<Longrightarrow> x \<in> {l .. u} \<Longrightarrow> (x::real) ^ n \<in> {l1..u1}"
  by (auto
    simp: float_power_bnds_def max_def real_power_up_fl real_power_down_fl minus_le_iff
    split: if_split_asm
    intro!: power_up_le power_down_le le_minus_power_downI
    intro: power_mono_odd power_mono power_mono_even zero_le_even_power)

lemma bnds_power:
  "\<forall>(x::real) l u. (l1, u1) = float_power_bnds prec n l u \<and> x \<in> {l .. u} \<longrightarrow>
    l1 \<le> x ^ n \<and> x ^ n \<le> u1"
  using float_power_bnds by auto

section \<open>Approximation utility functions\<close>

definition bnds_mult :: "nat \<Rightarrow> float \<Rightarrow> float \<Rightarrow> float \<Rightarrow> float \<Rightarrow> float \<times> float" where
  "bnds_mult prec a1 a2 b1 b2 =
      (float_plus_down prec (nprt a1 * pprt b2)
          (float_plus_down prec (nprt a2 * nprt b2)
            (float_plus_down prec (pprt a1 * pprt b1) (pprt a2 * nprt b1))),
        float_plus_up prec (pprt a2 * pprt b2)
            (float_plus_up prec (pprt a1 * nprt b2)
              (float_plus_up prec (nprt a2 * pprt b1) (nprt a1 * nprt b1))))"

lemma bnds_mult:
  fixes prec :: nat and a1 aa2 b1 b2 :: float
  assumes "(l, u) = bnds_mult prec a1 a2 b1 b2"
  assumes "a \<in> {real_of_float a1..real_of_float a2}"
  assumes "b \<in> {real_of_float b1..real_of_float b2}"
  shows   "a * b \<in> {real_of_float l..real_of_float u}"
proof -
  from assms have "real_of_float l \<le> a * b" 
    by (intro order.trans[OF _ mult_ge_prts[of a1 a a2 b1 b b2]])
       (auto simp: bnds_mult_def intro!: float_plus_down_le)
  moreover from assms have "real_of_float u \<ge> a * b" 
    by (intro order.trans[OF mult_le_prts[of a1 a a2 b1 b b2]])
       (auto simp: bnds_mult_def intro!: float_plus_up_le)
  ultimately show ?thesis by simp
qed

definition map_bnds :: "(nat \<Rightarrow> float \<Rightarrow> float) \<Rightarrow> (nat \<Rightarrow> float \<Rightarrow> float) \<Rightarrow>
                           nat \<Rightarrow> (float \<times> float) \<Rightarrow> (float \<times> float)" where
  "map_bnds lb ub prec = (\<lambda>(l,u). (lb prec l, ub prec u))"

lemma map_bnds:
  assumes "(lf, uf) = map_bnds lb ub prec (l, u)"
  assumes "mono f"
  assumes "x \<in> {real_of_float l..real_of_float u}"
  assumes "real_of_float (lb prec l) \<le> f (real_of_float l)"
  assumes "real_of_float (ub prec u) \<ge> f (real_of_float u)"
  shows   "f x \<in> {real_of_float lf..real_of_float uf}"
proof -
  from assms have "real_of_float lf = real_of_float (lb prec l)"
    by (simp add: map_bnds_def)
  also have "real_of_float (lb prec l) \<le> f (real_of_float l)"  by fact
  also from assms have "\<dots> \<le> f x"
    by (intro monoD[OF \<open>mono f\<close>]) auto
  finally have lf: "real_of_float lf \<le> f x" .

  from assms have "f x \<le> f (real_of_float u)"
    by (intro monoD[OF \<open>mono f\<close>]) auto
  also have "\<dots> \<le> real_of_float (ub prec u)" by fact
  also from assms have "\<dots> = real_of_float uf"
    by (simp add: map_bnds_def)
  finally have uf: "f x \<le> real_of_float uf" .

  from lf uf show ?thesis by simp
qed


section "Square root"

text \<open>
The square root computation is implemented as newton iteration. As first first step we use the
nearest power of two greater than the square root.
\<close>

fun sqrt_iteration :: "nat \<Rightarrow> nat \<Rightarrow> float \<Rightarrow> float" where
"sqrt_iteration prec 0 x = Float 1 ((bitlen \<bar>mantissa x\<bar> + exponent x) div 2 + 1)" |
"sqrt_iteration prec (Suc m) x = (let y = sqrt_iteration prec m x
                                  in Float 1 (- 1) * float_plus_up prec y (float_divr prec x y))"

lemma compute_sqrt_iteration_base[code]:
  shows "sqrt_iteration prec n (Float m e) =
    (if n = 0 then Float 1 ((if m = 0 then 0 else bitlen \<bar>m\<bar> + e) div 2 + 1)
    else (let y = sqrt_iteration prec (n - 1) (Float m e) in
      Float 1 (- 1) * float_plus_up prec y (float_divr prec (Float m e) y)))"
  using bitlen_Float by (cases n) simp_all

function ub_sqrt lb_sqrt :: "nat \<Rightarrow> float \<Rightarrow> float" where
"ub_sqrt prec x = (if 0 < x then (sqrt_iteration prec prec x)
              else if x < 0 then - lb_sqrt prec (- x)
                            else 0)" |
"lb_sqrt prec x = (if 0 < x then (float_divl prec x (sqrt_iteration prec prec x))
              else if x < 0 then - ub_sqrt prec (- x)
                            else 0)"
by pat_completeness auto
termination by (relation "measure (\<lambda> v. let (prec, x) = case_sum id id v in (if x < 0 then 1 else 0))", auto)

declare lb_sqrt.simps[simp del]
declare ub_sqrt.simps[simp del]

lemma sqrt_ub_pos_pos_1:
  assumes "sqrt x < b" and "0 < b" and "0 < x"
  shows "sqrt x < (b + x / b)/2"
proof -
  from assms have "0 < (b - sqrt x)\<^sup>2 " by simp
  also have "\<dots> = b\<^sup>2 - 2 * b * sqrt x + (sqrt x)\<^sup>2" by algebra
  also have "\<dots> = b\<^sup>2 - 2 * b * sqrt x + x" using assms by simp
  finally have "0 < b\<^sup>2 - 2 * b * sqrt x + x" .
  hence "0 < b / 2 - sqrt x + x / (2 * b)" using assms
    by (simp add: field_simps power2_eq_square)
  thus ?thesis by (simp add: field_simps)
qed

lemma sqrt_iteration_bound:
  assumes "0 < real_of_float x"
  shows "sqrt x < sqrt_iteration prec n x"
proof (induct n)
  case 0
  show ?case
  proof (cases x)
    case (Float m e)
    hence "0 < m"
      using assms
      apply (auto simp: sign_simps)
      by (meson not_less powr_ge_pzero)
    hence "0 < sqrt m" by auto

    have int_nat_bl: "(nat (bitlen m)) = bitlen m"
      using bitlen_nonneg by auto

    have "x = (m / 2^nat (bitlen m)) * 2 powr (e + (nat (bitlen m)))"
      unfolding Float by (auto simp: powr_realpow[symmetric] field_simps powr_add)
    also have "\<dots> < 1 * 2 powr (e + nat (bitlen m))"
    proof (rule mult_strict_right_mono, auto)
      show "m < 2^nat (bitlen m)"
        using bitlen_bounds[OF \<open>0 < m\<close>, THEN conjunct2]
        unfolding of_int_less_iff[of m, symmetric] by auto
    qed
    finally have "sqrt x < sqrt (2 powr (e + bitlen m))"
      unfolding int_nat_bl by auto
    also have "\<dots> \<le> 2 powr ((e + bitlen m) div 2 + 1)"
    proof -
      let ?E = "e + bitlen m"
      have E_mod_pow: "2 powr (?E mod 2) < 4"
      proof (cases "?E mod 2 = 1")
        case True
        thus ?thesis by auto
      next
        case False
        have "0 \<le> ?E mod 2" by auto
        have "?E mod 2 < 2" by auto
        from this[THEN zless_imp_add1_zle]
        have "?E mod 2 \<le> 0" using False by auto
        from xt1(5)[OF \<open>0 \<le> ?E mod 2\<close> this]
        show ?thesis by auto
      qed
      hence "sqrt (2 powr (?E mod 2)) < sqrt (2 * 2)"
        by (auto simp del: real_sqrt_four)
      hence E_mod_pow: "sqrt (2 powr (?E mod 2)) < 2" by auto

      have E_eq: "2 powr ?E = 2 powr (?E div 2 + ?E div 2 + ?E mod 2)"
        by auto
      have "sqrt (2 powr ?E) = sqrt (2 powr (?E div 2) * 2 powr (?E div 2) * 2 powr (?E mod 2))"
        unfolding E_eq unfolding powr_add[symmetric] by (metis of_int_add)
      also have "\<dots> = 2 powr (?E div 2) * sqrt (2 powr (?E mod 2))"
        unfolding real_sqrt_mult[of _ "2 powr (?E mod 2)"] real_sqrt_abs2 by auto
      also have "\<dots> < 2 powr (?E div 2) * 2 powr 1"
        by (rule mult_strict_left_mono) (auto intro: E_mod_pow)
      also have "\<dots> = 2 powr (?E div 2 + 1)"
        unfolding add.commute[of _ 1] powr_add[symmetric] by simp
      finally show ?thesis by auto
    qed
    finally show ?thesis using \<open>0 < m\<close>
      unfolding Float
      by (subst compute_sqrt_iteration_base) (simp add: ac_simps)
  qed
next
  case (Suc n)
  let ?b = "sqrt_iteration prec n x"
  have "0 < sqrt x"
    using \<open>0 < real_of_float x\<close> by auto
  also have "\<dots> < real_of_float ?b"
    using Suc .
  finally have "sqrt x < (?b + x / ?b)/2"
    using sqrt_ub_pos_pos_1[OF Suc _ \<open>0 < real_of_float x\<close>] by auto
  also have "\<dots> \<le> (?b + (float_divr prec x ?b))/2"
    by (rule divide_right_mono, auto simp add: float_divr)
  also have "\<dots> = (Float 1 (- 1)) * (?b + (float_divr prec x ?b))"
    by simp
  also have "\<dots> \<le> (Float 1 (- 1)) * (float_plus_up prec ?b (float_divr prec x ?b))"
    by (auto simp add: algebra_simps float_plus_up_le)
  finally show ?case
    unfolding sqrt_iteration.simps Let_def distrib_left .
qed

lemma sqrt_iteration_lower_bound:
  assumes "0 < real_of_float x"
  shows "0 < real_of_float (sqrt_iteration prec n x)" (is "0 < ?sqrt")
proof -
  have "0 < sqrt x" using assms by auto
  also have "\<dots> < ?sqrt" using sqrt_iteration_bound[OF assms] .
  finally show ?thesis .
qed

lemma lb_sqrt_lower_bound:
  assumes "0 \<le> real_of_float x"
  shows "0 \<le> real_of_float (lb_sqrt prec x)"
proof (cases "0 < x")
  case True
  hence "0 < real_of_float x" and "0 \<le> x"
    using \<open>0 \<le> real_of_float x\<close> by auto
  hence "0 < sqrt_iteration prec prec x"
    using sqrt_iteration_lower_bound by auto
  hence "0 \<le> real_of_float (float_divl prec x (sqrt_iteration prec prec x))"
    using float_divl_lower_bound[OF \<open>0 \<le> x\<close>] unfolding less_eq_float_def by auto
  thus ?thesis
    unfolding lb_sqrt.simps using True by auto
next
  case False
  with \<open>0 \<le> real_of_float x\<close> have "real_of_float x = 0" by auto
  thus ?thesis
    unfolding lb_sqrt.simps by auto
qed

lemma bnds_sqrt': "sqrt x \<in> {(lb_sqrt prec x) .. (ub_sqrt prec x)}"
proof -
  have lb: "lb_sqrt prec x \<le> sqrt x" if "0 < x" for x :: float
  proof -
    from that have "0 < real_of_float x" and "0 \<le> real_of_float x" by auto
    hence sqrt_gt0: "0 < sqrt x" by auto
    hence sqrt_ub: "sqrt x < sqrt_iteration prec prec x"
      using sqrt_iteration_bound by auto
    have "(float_divl prec x (sqrt_iteration prec prec x)) \<le>
          x / (sqrt_iteration prec prec x)" by (rule float_divl)
    also have "\<dots> < x / sqrt x"
      by (rule divide_strict_left_mono[OF sqrt_ub \<open>0 < real_of_float x\<close>
               mult_pos_pos[OF order_less_trans[OF sqrt_gt0 sqrt_ub] sqrt_gt0]])
    also have "\<dots> = sqrt x"
      unfolding inverse_eq_iff_eq[of _ "sqrt x", symmetric]
                sqrt_divide_self_eq[OF \<open>0 \<le> real_of_float x\<close>, symmetric] by auto
    finally show ?thesis
      unfolding lb_sqrt.simps if_P[OF \<open>0 < x\<close>] by auto
  qed
  have ub: "sqrt x \<le> ub_sqrt prec x" if "0 < x" for x :: float
  proof -
    from that have "0 < real_of_float x" by auto
    hence "0 < sqrt x" by auto
    hence "sqrt x < sqrt_iteration prec prec x"
      using sqrt_iteration_bound by auto
    then show ?thesis
      unfolding ub_sqrt.simps if_P[OF \<open>0 < x\<close>] by auto
  qed
  show ?thesis
    using lb[of "-x"] ub[of "-x"] lb[of x] ub[of x]
    by (auto simp add: lb_sqrt.simps ub_sqrt.simps real_sqrt_minus)
qed

lemma bnds_sqrt: "\<forall>(x::real) lx ux.
  (l, u) = (lb_sqrt prec lx, ub_sqrt prec ux) \<and> x \<in> {lx .. ux} \<longrightarrow> l \<le> sqrt x \<and> sqrt x \<le> u"
proof ((rule allI) +, rule impI, erule conjE, rule conjI)
  fix x :: real
  fix lx ux
  assume "(l, u) = (lb_sqrt prec lx, ub_sqrt prec ux)"
    and x: "x \<in> {lx .. ux}"
  hence l: "l = lb_sqrt prec lx " and u: "u = ub_sqrt prec ux" by auto

  have "sqrt lx \<le> sqrt x" using x by auto
  from order_trans[OF _ this]
  show "l \<le> sqrt x" unfolding l using bnds_sqrt'[of lx prec] by auto

  have "sqrt x \<le> sqrt ux" using x by auto
  from order_trans[OF this]
  show "sqrt x \<le> u" unfolding u using bnds_sqrt'[of ux prec] by auto
qed


section "Arcus tangens and \<pi>"

subsection "Compute arcus tangens series"

text \<open>
As first step we implement the computation of the arcus tangens series. This is only valid in the range
@{term "{-1 :: real .. 1}"}. This is used to compute \<pi> and then the entire arcus tangens.
\<close>

fun ub_arctan_horner :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> float \<Rightarrow> float"
and lb_arctan_horner :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> float \<Rightarrow> float" where
  "ub_arctan_horner prec 0 k x = 0"
| "ub_arctan_horner prec (Suc n) k x = float_plus_up prec
      (rapprox_rat prec 1 k) (- float_round_down prec (x * (lb_arctan_horner prec n (k + 2) x)))"
| "lb_arctan_horner prec 0 k x = 0"
| "lb_arctan_horner prec (Suc n) k x = float_plus_down prec
      (lapprox_rat prec 1 k) (- float_round_up prec (x * (ub_arctan_horner prec n (k + 2) x)))"

lemma arctan_0_1_bounds':
  assumes "0 \<le> real_of_float y" "real_of_float y \<le> 1"
    and "even n"
  shows "arctan (sqrt y) \<in>
      {(sqrt y * lb_arctan_horner prec n 1 y) .. (sqrt y * ub_arctan_horner prec (Suc n) 1 y)}"
proof -
  let ?c = "\<lambda>i. (- 1) ^ i * (1 / (i * 2 + (1::nat)) * sqrt y ^ (i * 2 + 1))"
  let ?S = "\<lambda>n. \<Sum> i=0..<n. ?c i"

  have "0 \<le> sqrt y" using assms by auto
  have "sqrt y \<le> 1" using assms by auto
  from \<open>even n\<close> obtain m where "2 * m = n" by (blast elim: evenE)

  have "arctan (sqrt y) \<in> { ?S n .. ?S (Suc n) }"
  proof (cases "sqrt y = 0")
    case True
    then show ?thesis by simp
  next
    case False
    hence "0 < sqrt y" using \<open>0 \<le> sqrt y\<close> by auto
    hence prem: "0 < 1 / (0 * 2 + (1::nat)) * sqrt y ^ (0 * 2 + 1)" by auto

    have "\<bar> sqrt y \<bar> \<le> 1"  using \<open>0 \<le> sqrt y\<close> \<open>sqrt y \<le> 1\<close> by auto
    from mp[OF summable_Leibniz(2)[OF zeroseq_arctan_series[OF this]
      monoseq_arctan_series[OF this]] prem, THEN spec, of m, unfolded \<open>2 * m = n\<close>]
    show ?thesis unfolding arctan_series[OF \<open>\<bar> sqrt y \<bar> \<le> 1\<close>] Suc_eq_plus1 atLeast0LessThan .
  qed
  note arctan_bounds = this[unfolded atLeastAtMost_iff]

  have F: "\<And>n. 2 * Suc n + 1 = 2 * n + 1 + 2" by auto

  note bounds = horner_bounds[where s=1 and f="\<lambda>i. 2 * i + 1" and j'=0
    and lb="\<lambda>n i k x. lb_arctan_horner prec n k x"
    and ub="\<lambda>n i k x. ub_arctan_horner prec n k x",
    OF \<open>0 \<le> real_of_float y\<close> F lb_arctan_horner.simps ub_arctan_horner.simps]

  have "(sqrt y * lb_arctan_horner prec n 1 y) \<le> arctan (sqrt y)"
  proof -
    have "(sqrt y * lb_arctan_horner prec n 1 y) \<le> ?S n"
      using bounds(1) \<open>0 \<le> sqrt y\<close>
      apply (simp only: power_add power_one_right mult.assoc[symmetric] sum_distrib_right[symmetric])
      apply (simp only: mult.commute[where 'a=real] mult.commute[of _ "2::nat"] power_mult)
      apply (auto intro!: mult_left_mono)
      done
    also have "\<dots> \<le> arctan (sqrt y)" using arctan_bounds ..
    finally show ?thesis .
  qed
  moreover
  have "arctan (sqrt y) \<le> (sqrt y * ub_arctan_horner prec (Suc n) 1 y)"
  proof -
    have "arctan (sqrt y) \<le> ?S (Suc n)" using arctan_bounds ..
    also have "\<dots> \<le> (sqrt y * ub_arctan_horner prec (Suc n) 1 y)"
      using bounds(2)[of "Suc n"] \<open>0 \<le> sqrt y\<close>
      apply (simp only: power_add power_one_right mult.assoc[symmetric] sum_distrib_right[symmetric])
      apply (simp only: mult.commute[where 'a=real] mult.commute[of _ "2::nat"] power_mult)
      apply (auto intro!: mult_left_mono)
      done
    finally show ?thesis .
  qed
  ultimately show ?thesis by auto
qed

lemma arctan_0_1_bounds:
  assumes "0 \<le> real_of_float y" "real_of_float y \<le> 1"
  shows "arctan (sqrt y) \<in>
    {(sqrt y * lb_arctan_horner prec (get_even n) 1 y) ..
      (sqrt y * ub_arctan_horner prec (get_odd n) 1 y)}"
  using
    arctan_0_1_bounds'[OF assms, of n prec]
    arctan_0_1_bounds'[OF assms, of "n + 1" prec]
    arctan_0_1_bounds'[OF assms, of "n - 1" prec]
  by (auto simp: get_even_def get_odd_def odd_pos
    simp del: ub_arctan_horner.simps lb_arctan_horner.simps)

lemma arctan_lower_bound:
  assumes "0 \<le> x"
  shows "x / (1 + x\<^sup>2) \<le> arctan x" (is "?l x \<le> _")
proof -
  have "?l x - arctan x \<le> ?l 0 - arctan 0"
    using assms
    by (intro DERIV_nonpos_imp_nonincreasing[where f="\<lambda>x. ?l x - arctan x"])
      (auto intro!: derivative_eq_intros simp: add_nonneg_eq_0_iff field_simps)
  thus ?thesis by simp
qed

lemma arctan_divide_mono: "0 < x \<Longrightarrow> x \<le> y \<Longrightarrow> arctan y / y \<le> arctan x / x"
  by (rule DERIV_nonpos_imp_nonincreasing[where f="\<lambda>x. arctan x / x"])
    (auto intro!: derivative_eq_intros divide_nonpos_nonneg
      simp: inverse_eq_divide arctan_lower_bound)

lemma arctan_mult_mono: "0 \<le> x \<Longrightarrow> x \<le> y \<Longrightarrow> x * arctan y \<le> y * arctan x"
  using arctan_divide_mono[of x y] by (cases "x = 0") (simp_all add: field_simps)

lemma arctan_mult_le:
  assumes "0 \<le> x" "x \<le> y" "y * z \<le> arctan y"
  shows "x * z \<le> arctan x"
proof (cases "x = 0")
  case True
  then show ?thesis by simp
next
  case False
  with assms have "z \<le> arctan y / y" by (simp add: field_simps)
  also have "\<dots> \<le> arctan x / x" using assms \<open>x \<noteq> 0\<close> by (auto intro!: arctan_divide_mono)
  finally show ?thesis using assms \<open>x \<noteq> 0\<close> by (simp add: field_simps)
qed

lemma arctan_le_mult:
  assumes "0 < x" "x \<le> y" "arctan x \<le> x * z"
  shows "arctan y \<le> y * z"
proof -
  from assms have "arctan y / y \<le> arctan x / x" by (auto intro!: arctan_divide_mono)
  also have "\<dots> \<le> z" using assms by (auto simp: field_simps)
  finally show ?thesis using assms by (simp add: field_simps)
qed

lemma arctan_0_1_bounds_le:
  assumes "0 \<le> x" "x \<le> 1" "0 < real_of_float xl" "real_of_float xl \<le> x * x" "x * x \<le> real_of_float xu" "real_of_float xu \<le> 1"
  shows "arctan x \<in>
      {x * lb_arctan_horner p1 (get_even n) 1 xu .. x * ub_arctan_horner p2 (get_odd n) 1 xl}"
proof -
  from assms have "real_of_float xl \<le> 1" "sqrt (real_of_float xl) \<le> x" "x \<le> sqrt (real_of_float xu)" "0 \<le> real_of_float xu"
    "0 \<le> real_of_float xl" "0 < sqrt (real_of_float xl)"
    by (auto intro!: real_le_rsqrt real_le_lsqrt simp: power2_eq_square)
  from arctan_0_1_bounds[OF \<open>0 \<le> real_of_float xu\<close>  \<open>real_of_float xu \<le> 1\<close>]
  have "sqrt (real_of_float xu) * real_of_float (lb_arctan_horner p1 (get_even n) 1 xu) \<le> arctan (sqrt (real_of_float xu))"
    by simp
  from arctan_mult_le[OF \<open>0 \<le> x\<close> \<open>x \<le> sqrt _\<close>  this]
  have "x * real_of_float (lb_arctan_horner p1 (get_even n) 1 xu) \<le> arctan x" .
  moreover
  from arctan_0_1_bounds[OF \<open>0 \<le> real_of_float xl\<close>  \<open>real_of_float xl \<le> 1\<close>]
  have "arctan (sqrt (real_of_float xl)) \<le> sqrt (real_of_float xl) * real_of_float (ub_arctan_horner p2 (get_odd n) 1 xl)"
    by simp
  from arctan_le_mult[OF \<open>0 < sqrt xl\<close> \<open>sqrt xl \<le> x\<close> this]
  have "arctan x \<le> x * real_of_float (ub_arctan_horner p2 (get_odd n) 1 xl)" .
  ultimately show ?thesis by simp
qed

lemma arctan_0_1_bounds_round:
  assumes "0 \<le> real_of_float x" "real_of_float x \<le> 1"
  shows "arctan x \<in>
      {real_of_float x * lb_arctan_horner p1 (get_even n) 1 (float_round_up (Suc p2) (x * x)) ..
        real_of_float x * ub_arctan_horner p3 (get_odd n) 1 (float_round_down (Suc p4) (x * x))}"
  using assms
  apply (cases "x > 0")
   apply (intro arctan_0_1_bounds_le)
   apply (auto simp: float_round_down.rep_eq float_round_up.rep_eq
    intro!: truncate_up_le1 mult_le_one truncate_down_le truncate_up_le truncate_down_pos
      mult_pos_pos)
  done


subsection "Compute \<pi>"

definition ub_pi :: "nat \<Rightarrow> float" where
  "ub_pi prec =
    (let
      A = rapprox_rat prec 1 5 ;
      B = lapprox_rat prec 1 239
    in ((Float 1 2) * float_plus_up prec
      ((Float 1 2) * float_round_up prec (A * (ub_arctan_horner prec (get_odd (prec div 4 + 1)) 1
        (float_round_down (Suc prec) (A * A)))))
      (- float_round_down prec (B * (lb_arctan_horner prec (get_even (prec div 14 + 1)) 1
        (float_round_up (Suc prec) (B * B)))))))"

definition lb_pi :: "nat \<Rightarrow> float" where
  "lb_pi prec =
    (let
      A = lapprox_rat prec 1 5 ;
      B = rapprox_rat prec 1 239
    in ((Float 1 2) * float_plus_down prec
      ((Float 1 2) * float_round_down prec (A * (lb_arctan_horner prec (get_even (prec div 4 + 1)) 1
        (float_round_up (Suc prec) (A * A)))))
      (- float_round_up prec (B * (ub_arctan_horner prec (get_odd (prec div 14 + 1)) 1
        (float_round_down (Suc prec) (B * B)))))))"

lemma pi_boundaries: "pi \<in> {(lb_pi n) .. (ub_pi n)}"
proof -
  have machin_pi: "pi = 4 * (4 * arctan (1 / 5) - arctan (1 / 239))"
    unfolding machin[symmetric] by auto

  {
    fix prec n :: nat
    fix k :: int
    assume "1 < k" hence "0 \<le> k" and "0 < k" and "1 \<le> k" by auto
    let ?k = "rapprox_rat prec 1 k"
    let ?kl = "float_round_down (Suc prec) (?k * ?k)"
    have "1 div k = 0" using div_pos_pos_trivial[OF _ \<open>1 < k\<close>] by auto

    have "0 \<le> real_of_float ?k" by (rule order_trans[OF _ rapprox_rat]) (auto simp add: \<open>0 \<le> k\<close>)
    have "real_of_float ?k \<le> 1"
      by (auto simp add: \<open>0 < k\<close> \<open>1 \<le> k\<close> less_imp_le
        intro!: mult_le_one order_trans[OF _ rapprox_rat] rapprox_rat_le1)
    have "1 / k \<le> ?k" using rapprox_rat[where x=1 and y=k] by auto
    hence "arctan (1 / k) \<le> arctan ?k" by (rule arctan_monotone')
    also have "\<dots> \<le> (?k * ub_arctan_horner prec (get_odd n) 1 ?kl)"
      using arctan_0_1_bounds_round[OF \<open>0 \<le> real_of_float ?k\<close> \<open>real_of_float ?k \<le> 1\<close>]
      by auto
    finally have "arctan (1 / k) \<le> ?k * ub_arctan_horner prec (get_odd n) 1 ?kl" .
  } note ub_arctan = this

  {
    fix prec n :: nat
    fix k :: int
    assume "1 < k" hence "0 \<le> k" and "0 < k" by auto
    let ?k = "lapprox_rat prec 1 k"
    let ?ku = "float_round_up (Suc prec) (?k * ?k)"
    have "1 div k = 0" using div_pos_pos_trivial[OF _ \<open>1 < k\<close>] by auto
    have "1 / k \<le> 1" using \<open>1 < k\<close> by auto
    have "0 \<le> real_of_float ?k" using lapprox_rat_nonneg[where x=1 and y=k, OF zero_le_one \<open>0 \<le> k\<close>]
      by (auto simp add: \<open>1 div k = 0\<close>)
    have "0 \<le> real_of_float (?k * ?k)" by simp
    have "real_of_float ?k \<le> 1" using lapprox_rat by (rule order_trans, auto simp add: \<open>1 / k \<le> 1\<close>)
    hence "real_of_float (?k * ?k) \<le> 1" using \<open>0 \<le> real_of_float ?k\<close> by (auto intro!: mult_le_one)

    have "?k \<le> 1 / k" using lapprox_rat[where x=1 and y=k] by auto

    have "?k * lb_arctan_horner prec (get_even n) 1 ?ku \<le> arctan ?k"
      using arctan_0_1_bounds_round[OF \<open>0 \<le> real_of_float ?k\<close> \<open>real_of_float ?k \<le> 1\<close>]
      by auto
    also have "\<dots> \<le> arctan (1 / k)" using \<open>?k \<le> 1 / k\<close> by (rule arctan_monotone')
    finally have "?k * lb_arctan_horner prec (get_even n) 1 ?ku \<le> arctan (1 / k)" .
  } note lb_arctan = this

  have "pi \<le> ub_pi n "
    unfolding ub_pi_def machin_pi Let_def times_float.rep_eq Float_num
    using lb_arctan[of 239] ub_arctan[of 5] powr_realpow[of 2 2]
    by (intro mult_left_mono float_plus_up_le float_plus_down_le)
      (auto intro!: mult_left_mono float_round_down_le float_round_up_le diff_mono)
  moreover have "lb_pi n \<le> pi"
    unfolding lb_pi_def machin_pi Let_def times_float.rep_eq Float_num
    using lb_arctan[of 5] ub_arctan[of 239]
    by (intro mult_left_mono float_plus_up_le float_plus_down_le)
      (auto intro!: mult_left_mono float_round_down_le float_round_up_le diff_mono)
  ultimately show ?thesis by auto
qed


subsection "Compute arcus tangens in the entire domain"

function lb_arctan :: "nat \<Rightarrow> float \<Rightarrow> float" and ub_arctan :: "nat \<Rightarrow> float \<Rightarrow> float" where
  "lb_arctan prec x =
    (let
      ub_horner = \<lambda> x. float_round_up prec
        (x *
          ub_arctan_horner prec (get_odd (prec div 4 + 1)) 1 (float_round_down (Suc prec) (x * x)));
      lb_horner = \<lambda> x. float_round_down prec
        (x *
          lb_arctan_horner prec (get_even (prec div 4 + 1)) 1 (float_round_up (Suc prec) (x * x)))
    in
      if x < 0 then - ub_arctan prec (-x)
      else if x \<le> Float 1 (- 1) then lb_horner x
      else if x \<le> Float 1 1 then
        Float 1 1 *
        lb_horner
          (float_divl prec x
            (float_plus_up prec 1
              (ub_sqrt prec (float_plus_up prec 1 (float_round_up prec (x * x))))))
      else let inv = float_divr prec 1 x in
        if inv > 1 then 0
        else float_plus_down prec (lb_pi prec * Float 1 (- 1)) ( - ub_horner inv))"

| "ub_arctan prec x =
    (let
      lb_horner = \<lambda> x. float_round_down prec
        (x *
          lb_arctan_horner prec (get_even (prec div 4 + 1)) 1 (float_round_up (Suc prec) (x * x))) ;
      ub_horner = \<lambda> x. float_round_up prec
        (x *
          ub_arctan_horner prec (get_odd (prec div 4 + 1)) 1 (float_round_down (Suc prec) (x * x)))
    in if x < 0 then - lb_arctan prec (-x)
    else if x \<le> Float 1 (- 1) then ub_horner x
    else if x \<le> Float 1 1 then
      let y = float_divr prec x
        (float_plus_down
          (Suc prec) 1 (lb_sqrt prec (float_plus_down prec 1 (float_round_down prec (x * x)))))
      in if y > 1 then ub_pi prec * Float 1 (- 1) else Float 1 1 * ub_horner y
    else float_plus_up prec (ub_pi prec * Float 1 (- 1)) ( - lb_horner (float_divl prec 1 x)))"
by pat_completeness auto
termination
by (relation "measure (\<lambda> v. let (prec, x) = case_sum id id v in (if x < 0 then 1 else 0))", auto)

declare ub_arctan_horner.simps[simp del]
declare lb_arctan_horner.simps[simp del]

lemma lb_arctan_bound':
  assumes "0 \<le> real_of_float x"
  shows "lb_arctan prec x \<le> arctan x"
proof -
  have "\<not> x < 0" and "0 \<le> x"
    using \<open>0 \<le> real_of_float x\<close> by (auto intro!: truncate_up_le )

  let "?ub_horner x" =
      "x * ub_arctan_horner prec (get_odd (prec div 4 + 1)) 1 (float_round_down (Suc prec) (x * x))"
    and "?lb_horner x" =
      "x * lb_arctan_horner prec (get_even (prec div 4 + 1)) 1 (float_round_up (Suc prec) (x * x))"

  show ?thesis
  proof (cases "x \<le> Float 1 (- 1)")
    case True
    hence "real_of_float x \<le> 1" by simp
    from arctan_0_1_bounds_round[OF \<open>0 \<le> real_of_float x\<close> \<open>real_of_float x \<le> 1\<close>]
    show ?thesis
      unfolding lb_arctan.simps Let_def if_not_P[OF \<open>\<not> x < 0\<close>] if_P[OF True] using \<open>0 \<le> x\<close>
      by (auto intro!: float_round_down_le)
  next
    case False
    hence "0 < real_of_float x" by auto
    let ?R = "1 + sqrt (1 + real_of_float x * real_of_float x)"
    let ?sxx = "float_plus_up prec 1 (float_round_up prec (x * x))"
    let ?fR = "float_plus_up prec 1 (ub_sqrt prec ?sxx)"
    let ?DIV = "float_divl prec x ?fR"

    have divisor_gt0: "0 < ?R" by (auto intro: add_pos_nonneg)

    have "sqrt (1 + x*x) \<le> sqrt ?sxx"
      by (auto simp: float_plus_up.rep_eq plus_up_def float_round_up.rep_eq intro!: truncate_up_le)
    also have "\<dots> \<le> ub_sqrt prec ?sxx"
      using bnds_sqrt'[of ?sxx prec] by auto
    finally
    have "sqrt (1 + x*x) \<le> ub_sqrt prec ?sxx" .
    hence "?R \<le> ?fR" by (auto simp: float_plus_up.rep_eq plus_up_def intro!: truncate_up_le)
    hence "0 < ?fR" and "0 < real_of_float ?fR" using \<open>0 < ?R\<close> by auto

    have monotone: "?DIV \<le> x / ?R"
    proof -
      have "?DIV \<le> real_of_float x / ?fR" by (rule float_divl)
      also have "\<dots> \<le> x / ?R" by (rule divide_left_mono[OF \<open>?R \<le> ?fR\<close> \<open>0 \<le> real_of_float x\<close> mult_pos_pos[OF order_less_le_trans[OF divisor_gt0 \<open>?R \<le> real_of_float ?fR\<close>] divisor_gt0]])
      finally show ?thesis .
    qed

    show ?thesis
    proof (cases "x \<le> Float 1 1")
      case True
      have "x \<le> sqrt (1 + x * x)"
        using real_sqrt_sum_squares_ge2[where x=1, unfolded numeral_2_eq_2] by auto
      also note \<open>\<dots> \<le> (ub_sqrt prec ?sxx)\<close>
      finally have "real_of_float x \<le> ?fR"
        by (auto simp: float_plus_up.rep_eq plus_up_def intro!: truncate_up_le)
      moreover have "?DIV \<le> real_of_float x / ?fR"
        by (rule float_divl)
      ultimately have "real_of_float ?DIV \<le> 1"
        unfolding divide_le_eq_1_pos[OF \<open>0 < real_of_float ?fR\<close>, symmetric] by auto

      have "0 \<le> real_of_float ?DIV"
        using float_divl_lower_bound[OF \<open>0 \<le> x\<close>] \<open>0 < ?fR\<close>
        unfolding less_eq_float_def by auto

      from arctan_0_1_bounds_round[OF \<open>0 \<le> real_of_float (?DIV)\<close> \<open>real_of_float (?DIV) \<le> 1\<close>]
      have "Float 1 1 * ?lb_horner ?DIV \<le> 2 * arctan ?DIV"
        by simp
      also have "\<dots> \<le> 2 * arctan (x / ?R)"
        using arctan_monotone'[OF monotone] by (auto intro!: mult_left_mono arctan_monotone')
      also have "2 * arctan (x / ?R) = arctan x"
        using arctan_half[symmetric] unfolding numeral_2_eq_2 power_Suc2 power_0 mult_1_left .
      finally show ?thesis
        unfolding lb_arctan.simps Let_def if_not_P[OF \<open>\<not> x < 0\<close>]
          if_not_P[OF \<open>\<not> x \<le> Float 1 (- 1)\<close>] if_P[OF True]
        by (auto simp: float_round_down.rep_eq
          intro!: order_trans[OF mult_left_mono[OF truncate_down]])
    next
      case False
      hence "2 < real_of_float x" by auto
      hence "1 \<le> real_of_float x" by auto

      let "?invx" = "float_divr prec 1 x"
      have "0 \<le> arctan x" using arctan_monotone'[OF \<open>0 \<le> real_of_float x\<close>]
        using arctan_tan[of 0, unfolded tan_zero] by auto

      show ?thesis
      proof (cases "1 < ?invx")
        case True
        show ?thesis
          unfolding lb_arctan.simps Let_def if_not_P[OF \<open>\<not> x < 0\<close>]
            if_not_P[OF \<open>\<not> x \<le> Float 1 (- 1)\<close>] if_not_P[OF False] if_P[OF True]
          using \<open>0 \<le> arctan x\<close> by auto
      next
        case False
        hence "real_of_float ?invx \<le> 1" by auto
        have "0 \<le> real_of_float ?invx"
          by (rule order_trans[OF _ float_divr]) (auto simp add: \<open>0 \<le> real_of_float x\<close>)

        have "1 / x \<noteq> 0" and "0 < 1 / x"
          using \<open>0 < real_of_float x\<close> by auto

        have "arctan (1 / x) \<le> arctan ?invx"
          unfolding one_float.rep_eq[symmetric] by (rule arctan_monotone', rule float_divr)
        also have "\<dots> \<le> ?ub_horner ?invx"
          using arctan_0_1_bounds_round[OF \<open>0 \<le> real_of_float ?invx\<close> \<open>real_of_float ?invx \<le> 1\<close>]
          by (auto intro!: float_round_up_le)
        also note float_round_up
        finally have "pi / 2 - float_round_up prec (?ub_horner ?invx) \<le> arctan x"
          using \<open>0 \<le> arctan x\<close> arctan_inverse[OF \<open>1 / x \<noteq> 0\<close>]
          unfolding sgn_pos[OF \<open>0 < 1 / real_of_float x\<close>] le_diff_eq by auto
        moreover
        have "lb_pi prec * Float 1 (- 1) \<le> pi / 2"
          unfolding Float_num times_divide_eq_right mult_1_left using pi_boundaries by simp
        ultimately
        show ?thesis
          unfolding lb_arctan.simps Let_def if_not_P[OF \<open>\<not> x < 0\<close>]
            if_not_P[OF \<open>\<not> x \<le> Float 1 (- 1)\<close>] if_not_P[OF \<open>\<not> x \<le> Float 1 1\<close>] if_not_P[OF False]
          by (auto intro!: float_plus_down_le)
      qed
    qed
  qed
qed

lemma ub_arctan_bound':
  assumes "0 \<le> real_of_float x"
  shows "arctan x \<le> ub_arctan prec x"
proof -
  have "\<not> x < 0" and "0 \<le> x"
    using \<open>0 \<le> real_of_float x\<close> by auto

  let "?ub_horner x" =
    "float_round_up prec (x * ub_arctan_horner prec (get_odd (prec div 4 + 1)) 1 (float_round_down (Suc prec) (x * x)))"
  let "?lb_horner x" =
    "float_round_down prec (x * lb_arctan_horner prec (get_even (prec div 4 + 1)) 1 (float_round_up (Suc prec) (x * x)))"

  show ?thesis
  proof (cases "x \<le> Float 1 (- 1)")
    case True
    hence "real_of_float x \<le> 1" by auto
    show ?thesis
      unfolding ub_arctan.simps Let_def if_not_P[OF \<open>\<not> x < 0\<close>] if_P[OF True]
      using arctan_0_1_bounds_round[OF \<open>0 \<le> real_of_float x\<close> \<open>real_of_float x \<le> 1\<close>]
      by (auto intro!: float_round_up_le)
  next
    case False
    hence "0 < real_of_float x" by auto
    let ?R = "1 + sqrt (1 + real_of_float x * real_of_float x)"
    let ?sxx = "float_plus_down prec 1 (float_round_down prec (x * x))"
    let ?fR = "float_plus_down (Suc prec) 1 (lb_sqrt prec ?sxx)"
    let ?DIV = "float_divr prec x ?fR"

    have sqr_ge0: "0 \<le> 1 + real_of_float x * real_of_float x"
      using sum_power2_ge_zero[of 1 "real_of_float x", unfolded numeral_2_eq_2] by auto
    hence "0 \<le> real_of_float (1 + x*x)" by auto

    hence divisor_gt0: "0 < ?R" by (auto intro: add_pos_nonneg)

    have "lb_sqrt prec ?sxx \<le> sqrt ?sxx"
      using bnds_sqrt'[of ?sxx] by auto
    also have "\<dots> \<le> sqrt (1 + x*x)"
      by (auto simp: float_plus_down.rep_eq plus_down_def float_round_down.rep_eq truncate_down_le)
    finally have "lb_sqrt prec ?sxx \<le> sqrt (1 + x*x)" .
    hence "?fR \<le> ?R"
      by (auto simp: float_plus_down.rep_eq plus_down_def truncate_down_le)
    have "0 < real_of_float ?fR"
      by (auto simp: float_plus_down.rep_eq plus_down_def float_round_down.rep_eq
        intro!: truncate_down_ge1 lb_sqrt_lower_bound order_less_le_trans[OF zero_less_one]
        truncate_down_nonneg add_nonneg_nonneg)
    have monotone: "x / ?R \<le> (float_divr prec x ?fR)"
    proof -
      from divide_left_mono[OF \<open>?fR \<le> ?R\<close> \<open>0 \<le> real_of_float x\<close> mult_pos_pos[OF divisor_gt0 \<open>0 < real_of_float ?fR\<close>]]
      have "x / ?R \<le> x / ?fR" .
      also have "\<dots> \<le> ?DIV" by (rule float_divr)
      finally show ?thesis .
    qed

    show ?thesis
    proof (cases "x \<le> Float 1 1")
      case True
      show ?thesis
      proof (cases "?DIV > 1")
        case True
        have "pi / 2 \<le> ub_pi prec * Float 1 (- 1)"
          unfolding Float_num times_divide_eq_right mult_1_left using pi_boundaries by auto
        from order_less_le_trans[OF arctan_ubound this, THEN less_imp_le]
        show ?thesis
          unfolding ub_arctan.simps Let_def if_not_P[OF \<open>\<not> x < 0\<close>]
            if_not_P[OF \<open>\<not> x \<le> Float 1 (- 1)\<close>] if_P[OF \<open>x \<le> Float 1 1\<close>] if_P[OF True] .
      next
        case False
        hence "real_of_float ?DIV \<le> 1" by auto

        have "0 \<le> x / ?R"
          using \<open>0 \<le> real_of_float x\<close> \<open>0 < ?R\<close> unfolding zero_le_divide_iff by auto
        hence "0 \<le> real_of_float ?DIV"
          using monotone by (rule order_trans)

        have "arctan x = 2 * arctan (x / ?R)"
          using arctan_half unfolding numeral_2_eq_2 power_Suc2 power_0 mult_1_left .
        also have "\<dots> \<le> 2 * arctan (?DIV)"
          using arctan_monotone'[OF monotone] by (auto intro!: mult_left_mono)
        also have "\<dots> \<le> (Float 1 1 * ?ub_horner ?DIV)" unfolding Float_num
          using arctan_0_1_bounds_round[OF \<open>0 \<le> real_of_float ?DIV\<close> \<open>real_of_float ?DIV \<le> 1\<close>]
          by (auto intro!: float_round_up_le)
        finally show ?thesis
          unfolding ub_arctan.simps Let_def if_not_P[OF \<open>\<not> x < 0\<close>]
            if_not_P[OF \<open>\<not> x \<le> Float 1 (- 1)\<close>] if_P[OF \<open>x \<le> Float 1 1\<close>] if_not_P[OF False] .
      qed
    next
      case False
      hence "2 < real_of_float x" by auto
      hence "1 \<le> real_of_float x" by auto
      hence "0 < real_of_float x" by auto
      hence "0 < x" by auto

      let "?invx" = "float_divl prec 1 x"
      have "0 \<le> arctan x"
        using arctan_monotone'[OF \<open>0 \<le> real_of_float x\<close>] and arctan_tan[of 0, unfolded tan_zero] by auto

      have "real_of_float ?invx \<le> 1"
        unfolding less_float_def
        by (rule order_trans[OF float_divl])
          (auto simp add: \<open>1 \<le> real_of_float x\<close> divide_le_eq_1_pos[OF \<open>0 < real_of_float x\<close>])
      have "0 \<le> real_of_float ?invx"
        using \<open>0 < x\<close> by (intro float_divl_lower_bound) auto

      have "1 / x \<noteq> 0" and "0 < 1 / x"
        using \<open>0 < real_of_float x\<close> by auto

      have "(?lb_horner ?invx) \<le> arctan (?invx)"
        using arctan_0_1_bounds_round[OF \<open>0 \<le> real_of_float ?invx\<close> \<open>real_of_float ?invx \<le> 1\<close>]
        by (auto intro!: float_round_down_le)
      also have "\<dots> \<le> arctan (1 / x)"
        unfolding one_float.rep_eq[symmetric] by (rule arctan_monotone') (rule float_divl)
      finally have "arctan x \<le> pi / 2 - (?lb_horner ?invx)"
        using \<open>0 \<le> arctan x\<close> arctan_inverse[OF \<open>1 / x \<noteq> 0\<close>]
        unfolding sgn_pos[OF \<open>0 < 1 / x\<close>] le_diff_eq by auto
      moreover
      have "pi / 2 \<le> ub_pi prec * Float 1 (- 1)"
        unfolding Float_num times_divide_eq_right mult_1_right
        using pi_boundaries by auto
      ultimately
      show ?thesis
        unfolding ub_arctan.simps Let_def if_not_P[OF \<open>\<not> x < 0\<close>]
          if_not_P[OF \<open>\<not> x \<le> Float 1 (- 1)\<close>] if_not_P[OF False]
        by (auto intro!: float_round_up_le float_plus_up_le)
    qed
  qed
qed

lemma arctan_boundaries: "arctan x \<in> {(lb_arctan prec x) .. (ub_arctan prec x)}"
proof (cases "0 \<le> x")
  case True
  hence "0 \<le> real_of_float x" by auto
  show ?thesis
    using ub_arctan_bound'[OF \<open>0 \<le> real_of_float x\<close>] lb_arctan_bound'[OF \<open>0 \<le> real_of_float x\<close>]
    unfolding atLeastAtMost_iff by auto
next
  case False
  let ?mx = "-x"
  from False have "x < 0" and "0 \<le> real_of_float ?mx"
    by auto
  hence bounds: "lb_arctan prec ?mx \<le> arctan ?mx \<and> arctan ?mx \<le> ub_arctan prec ?mx"
    using ub_arctan_bound'[OF \<open>0 \<le> real_of_float ?mx\<close>] lb_arctan_bound'[OF \<open>0 \<le> real_of_float ?mx\<close>] by auto
  show ?thesis
    unfolding minus_float.rep_eq arctan_minus lb_arctan.simps[where x=x]
      ub_arctan.simps[where x=x] Let_def if_P[OF \<open>x < 0\<close>]
    unfolding atLeastAtMost_iff using bounds[unfolded minus_float.rep_eq arctan_minus]
    by (simp add: arctan_minus)
qed

lemma bnds_arctan: "\<forall> (x::real) lx ux. (l, u) = (lb_arctan prec lx, ub_arctan prec ux) \<and> x \<in> {lx .. ux} \<longrightarrow> l \<le> arctan x \<and> arctan x \<le> u"
proof (rule allI, rule allI, rule allI, rule impI)
  fix x :: real
  fix lx ux
  assume "(l, u) = (lb_arctan prec lx, ub_arctan prec ux) \<and> x \<in> {lx .. ux}"
  hence l: "lb_arctan prec lx = l "
    and u: "ub_arctan prec ux = u"
    and x: "x \<in> {lx .. ux}"
    by auto
  show "l \<le> arctan x \<and> arctan x \<le> u"
  proof
    show "l \<le> arctan x"
    proof -
      from arctan_boundaries[of lx prec, unfolded l]
      have "l \<le> arctan lx" by (auto simp del: lb_arctan.simps)
      also have "\<dots> \<le> arctan x" using x by (auto intro: arctan_monotone')
      finally show ?thesis .
    qed
    show "arctan x \<le> u"
    proof -
      have "arctan x \<le> arctan ux" using x by (auto intro: arctan_monotone')
      also have "\<dots> \<le> u" using arctan_boundaries[of ux prec, unfolded u] by (auto simp del: ub_arctan.simps)
      finally show ?thesis .
    qed
  qed
qed


section "Sinus and Cosinus"

subsection "Compute the cosinus and sinus series"

fun ub_sin_cos_aux :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> float \<Rightarrow> float"
and lb_sin_cos_aux :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> float \<Rightarrow> float" where
  "ub_sin_cos_aux prec 0 i k x = 0"
| "ub_sin_cos_aux prec (Suc n) i k x = float_plus_up prec
    (rapprox_rat prec 1 k) (-
      float_round_down prec (x * (lb_sin_cos_aux prec n (i + 2) (k * i * (i + 1)) x)))"
| "lb_sin_cos_aux prec 0 i k x = 0"
| "lb_sin_cos_aux prec (Suc n) i k x = float_plus_down prec
    (lapprox_rat prec 1 k) (-
      float_round_up prec (x * (ub_sin_cos_aux prec n (i + 2) (k * i * (i + 1)) x)))"

lemma cos_aux:
  shows "(lb_sin_cos_aux prec n 1 1 (x * x)) \<le> (\<Sum> i=0..<n. (- 1) ^ i * (1/(fact (2 * i))) * x ^(2 * i))" (is "?lb")
  and "(\<Sum> i=0..<n. (- 1) ^ i * (1/(fact (2 * i))) * x^(2 * i)) \<le> (ub_sin_cos_aux prec n 1 1 (x * x))" (is "?ub")
proof -
  have "0 \<le> real_of_float (x * x)" by auto
  let "?f n" = "fact (2 * n) :: nat"
  have f_eq: "?f (Suc n) = ?f n * ((\<lambda>i. i + 2) ^^ n) 1 * (((\<lambda>i. i + 2) ^^ n) 1 + 1)" for n
  proof -
    have "\<And>m. ((\<lambda>i. i + 2) ^^ n) m = m + 2 * n" by (induct n) auto
    then show ?thesis by auto
  qed
  from horner_bounds[where lb="lb_sin_cos_aux prec" and ub="ub_sin_cos_aux prec" and j'=0,
    OF \<open>0 \<le> real_of_float (x * x)\<close> f_eq lb_sin_cos_aux.simps ub_sin_cos_aux.simps]
  show ?lb and ?ub
    by (auto simp add: power_mult power2_eq_square[of "real_of_float x"])
qed

lemma lb_sin_cos_aux_zero_le_one: "lb_sin_cos_aux prec n i j 0 \<le> 1"
  by (cases j n rule: nat.exhaust[case_product nat.exhaust])
    (auto intro!: float_plus_down_le order_trans[OF lapprox_rat])

lemma one_le_ub_sin_cos_aux: "odd n \<Longrightarrow> 1 \<le> ub_sin_cos_aux prec n i (Suc 0) 0"
  by (cases n) (auto intro!: float_plus_up_le order_trans[OF _ rapprox_rat])

lemma cos_boundaries:
  assumes "0 \<le> real_of_float x" and "x \<le> pi / 2"
  shows "cos x \<in> {(lb_sin_cos_aux prec (get_even n) 1 1 (x * x)) .. (ub_sin_cos_aux prec (get_odd n) 1 1 (x * x))}"
proof (cases "real_of_float x = 0")
  case False
  hence "real_of_float x \<noteq> 0" by auto
  hence "0 < x" and "0 < real_of_float x"
    using \<open>0 \<le> real_of_float x\<close> by auto
  have "0 < x * x"
    using \<open>0 < x\<close> by simp

  have morph_to_if_power: "(\<Sum> i=0..<n. (-1::real) ^ i * (1/(fact (2 * i))) * x ^ (2 * i)) =
    (\<Sum> i = 0 ..< 2 * n. (if even(i) then ((- 1) ^ (i div 2))/((fact i)) else 0) * x ^ i)"
    (is "?sum = ?ifsum") for x n
  proof -
    have "?sum = ?sum + (\<Sum> j = 0 ..< n. 0)" by auto
    also have "\<dots> =
      (\<Sum> j = 0 ..< n. (- 1) ^ ((2 * j) div 2) / ((fact (2 * j))) * x ^(2 * j)) + (\<Sum> j = 0 ..< n. 0)" by auto
    also have "\<dots> = (\<Sum> i = 0 ..< 2 * n. if even i then (- 1) ^ (i div 2) / ((fact i)) * x ^ i else 0)"
      unfolding sum_split_even_odd atLeast0LessThan ..
    also have "\<dots> = (\<Sum> i = 0 ..< 2 * n. (if even i then (- 1) ^ (i div 2) / ((fact i)) else 0) * x ^ i)"
      by (rule sum.cong) auto
    finally show ?thesis .
  qed

  { fix n :: nat assume "0 < n"
    hence "0 < 2 * n" by auto
    obtain t where "0 < t" and "t < real_of_float x" and
      cos_eq: "cos x = (\<Sum> i = 0 ..< 2 * n. (if even(i) then ((- 1) ^ (i div 2))/((fact i)) else 0) * (real_of_float x) ^ i)
      + (cos (t + 1/2 * (2 * n) * pi) / (fact (2*n))) * (real_of_float x)^(2*n)"
      (is "_ = ?SUM + ?rest / ?fact * ?pow")
      using Maclaurin_cos_expansion2[OF \<open>0 < real_of_float x\<close> \<open>0 < 2 * n\<close>]
      unfolding cos_coeff_def atLeast0LessThan by auto

    have "cos t * (- 1) ^ n = cos t * cos (n * pi) + sin t * sin (n * pi)" by auto
    also have "\<dots> = cos (t + n * pi)" by (simp add: cos_add)
    also have "\<dots> = ?rest" by auto
    finally have "cos t * (- 1) ^ n = ?rest" .
    moreover
    have "t \<le> pi / 2" using \<open>t < real_of_float x\<close> and \<open>x \<le> pi / 2\<close> by auto
    hence "0 \<le> cos t" using \<open>0 < t\<close> and cos_ge_zero by auto
    ultimately have even: "even n \<Longrightarrow> 0 \<le> ?rest" and odd: "odd n \<Longrightarrow> 0 \<le> - ?rest " by auto

    have "0 < ?fact" by auto
    have "0 < ?pow" using \<open>0 < real_of_float x\<close> by auto

    {
      assume "even n"
      have "(lb_sin_cos_aux prec n 1 1 (x * x)) \<le> ?SUM"
        unfolding morph_to_if_power[symmetric] using cos_aux by auto
      also have "\<dots> \<le> cos x"
      proof -
        from even[OF \<open>even n\<close>] \<open>0 < ?fact\<close> \<open>0 < ?pow\<close>
        have "0 \<le> (?rest / ?fact) * ?pow" by simp
        thus ?thesis unfolding cos_eq by auto
      qed
      finally have "(lb_sin_cos_aux prec n 1 1 (x * x)) \<le> cos x" .
    } note lb = this

    {
      assume "odd n"
      have "cos x \<le> ?SUM"
      proof -
        from \<open>0 < ?fact\<close> and \<open>0 < ?pow\<close> and odd[OF \<open>odd n\<close>]
        have "0 \<le> (- ?rest) / ?fact * ?pow"
          by (metis mult_nonneg_nonneg divide_nonneg_pos less_imp_le)
        thus ?thesis unfolding cos_eq by auto
      qed
      also have "\<dots> \<le> (ub_sin_cos_aux prec n 1 1 (x * x))"
        unfolding morph_to_if_power[symmetric] using cos_aux by auto
      finally have "cos x \<le> (ub_sin_cos_aux prec n 1 1 (x * x))" .
    } note ub = this and lb
  } note ub = this(1) and lb = this(2)

  have "cos x \<le> (ub_sin_cos_aux prec (get_odd n) 1 1 (x * x))"
    using ub[OF odd_pos[OF get_odd] get_odd] .
  moreover have "(lb_sin_cos_aux prec (get_even n) 1 1 (x * x)) \<le> cos x"
  proof (cases "0 < get_even n")
    case True
    show ?thesis using lb[OF True get_even] .
  next
    case False
    hence "get_even n = 0" by auto
    have "- (pi / 2) \<le> x"
      by (rule order_trans[OF _ \<open>0 < real_of_float x\<close>[THEN less_imp_le]]) auto
    with \<open>x \<le> pi / 2\<close> show ?thesis
      unfolding \<open>get_even n = 0\<close> lb_sin_cos_aux.simps minus_float.rep_eq zero_float.rep_eq
      using cos_ge_zero by auto
  qed
  ultimately show ?thesis by auto
next
  case True
  hence "x = 0"
    by transfer
  thus ?thesis
    using lb_sin_cos_aux_zero_le_one one_le_ub_sin_cos_aux
    by simp
qed

lemma sin_aux:
  assumes "0 \<le> real_of_float x"
  shows "(x * lb_sin_cos_aux prec n 2 1 (x * x)) \<le>
      (\<Sum> i=0..<n. (- 1) ^ i * (1/(fact (2 * i + 1))) * x^(2 * i + 1))" (is "?lb")
    and "(\<Sum> i=0..<n. (- 1) ^ i * (1/(fact (2 * i + 1))) * x^(2 * i + 1)) \<le>
      (x * ub_sin_cos_aux prec n 2 1 (x * x))" (is "?ub")
proof -
  have "0 \<le> real_of_float (x * x)" by auto
  let "?f n" = "fact (2 * n + 1) :: nat"
  have f_eq: "?f (Suc n) = ?f n * ((\<lambda>i. i + 2) ^^ n) 2 * (((\<lambda>i. i + 2) ^^ n) 2 + 1)" for n
  proof -
    have F: "\<And>m. ((\<lambda>i. i + 2) ^^ n) m = m + 2 * n" by (induct n) auto
    show ?thesis
      unfolding F by auto
  qed
  from horner_bounds[where lb="lb_sin_cos_aux prec" and ub="ub_sin_cos_aux prec" and j'=0,
    OF \<open>0 \<le> real_of_float (x * x)\<close> f_eq lb_sin_cos_aux.simps ub_sin_cos_aux.simps]
  show "?lb" and "?ub" using \<open>0 \<le> real_of_float x\<close>
    apply (simp_all only: power_add power_one_right mult.assoc[symmetric] sum_distrib_right[symmetric])
    apply (simp_all only: mult.commute[where 'a=real] of_nat_fact)
    apply (auto intro!: mult_left_mono simp add: power_mult power2_eq_square[of "real_of_float x"])
    done
qed

lemma sin_boundaries:
  assumes "0 \<le> real_of_float x"
    and "x \<le> pi / 2"
  shows "sin x \<in> {(x * lb_sin_cos_aux prec (get_even n) 2 1 (x * x)) .. (x * ub_sin_cos_aux prec (get_odd n) 2 1 (x * x))}"
proof (cases "real_of_float x = 0")
  case False
  hence "real_of_float x \<noteq> 0" by auto
  hence "0 < x" and "0 < real_of_float x"
    using \<open>0 \<le> real_of_float x\<close> by auto
  have "0 < x * x"
    using \<open>0 < x\<close> by simp

  have sum_morph: "(\<Sum>j = 0 ..< n. (- 1) ^ (((2 * j + 1) - Suc 0) div 2) / ((fact (2 * j + 1))) * x ^(2 * j + 1)) =
    (\<Sum> i = 0 ..< 2 * n. (if even(i) then 0 else ((- 1) ^ ((i - Suc 0) div 2))/((fact i))) * x ^ i)"
    (is "?SUM = _") for x :: real and n
  proof -
    have pow: "!!i. x ^ (2 * i + 1) = x * x ^ (2 * i)"
      by auto
    have "?SUM = (\<Sum> j = 0 ..< n. 0) + ?SUM"
      by auto
    also have "\<dots> = (\<Sum> i = 0 ..< 2 * n. if even i then 0 else (- 1) ^ ((i - Suc 0) div 2) / ((fact i)) * x ^ i)"
      unfolding sum_split_even_odd atLeast0LessThan ..
    also have "\<dots> = (\<Sum> i = 0 ..< 2 * n. (if even i then 0 else (- 1) ^ ((i - Suc 0) div 2) / ((fact i))) * x ^ i)"
      by (rule sum.cong) auto
    finally show ?thesis .
  qed

  { fix n :: nat assume "0 < n"
    hence "0 < 2 * n + 1" by auto
    obtain t where "0 < t" and "t < real_of_float x" and
      sin_eq: "sin x = (\<Sum> i = 0 ..< 2 * n + 1. (if even(i) then 0 else ((- 1) ^ ((i - Suc 0) div 2))/((fact i))) * (real_of_float x) ^ i)
      + (sin (t + 1/2 * (2 * n + 1) * pi) / (fact (2*n + 1))) * (real_of_float x)^(2*n + 1)"
      (is "_ = ?SUM + ?rest / ?fact * ?pow")
      using Maclaurin_sin_expansion3[OF \<open>0 < 2 * n + 1\<close> \<open>0 < real_of_float x\<close>]
      unfolding sin_coeff_def atLeast0LessThan by auto

    have "?rest = cos t * (- 1) ^ n"
      unfolding sin_add cos_add of_nat_add distrib_right distrib_left by auto
    moreover
    have "t \<le> pi / 2"
      using \<open>t < real_of_float x\<close> and \<open>x \<le> pi / 2\<close> by auto
    hence "0 \<le> cos t"
      using \<open>0 < t\<close> and cos_ge_zero by auto
    ultimately have even: "even n \<Longrightarrow> 0 \<le> ?rest" and odd: "odd n \<Longrightarrow> 0 \<le> - ?rest"
      by auto

    have "0 < ?fact"
      by (simp del: fact_Suc)
    have "0 < ?pow"
      using \<open>0 < real_of_float x\<close> by (rule zero_less_power)

    {
      assume "even n"
      have "(x * lb_sin_cos_aux prec n 2 1 (x * x)) \<le>
            (\<Sum> i = 0 ..< 2 * n. (if even(i) then 0 else ((- 1) ^ ((i - Suc 0) div 2))/((fact i))) * (real_of_float x) ^ i)"
        using sin_aux[OF \<open>0 \<le> real_of_float x\<close>] unfolding sum_morph[symmetric] by auto
      also have "\<dots> \<le> ?SUM" by auto
      also have "\<dots> \<le> sin x"
      proof -
        from even[OF \<open>even n\<close>] \<open>0 < ?fact\<close> \<open>0 < ?pow\<close>
        have "0 \<le> (?rest / ?fact) * ?pow" by simp
        thus ?thesis unfolding sin_eq by auto
      qed
      finally have "(x * lb_sin_cos_aux prec n 2 1 (x * x)) \<le> sin x" .
    } note lb = this

    {
      assume "odd n"
      have "sin x \<le> ?SUM"
      proof -
        from \<open>0 < ?fact\<close> and \<open>0 < ?pow\<close> and odd[OF \<open>odd n\<close>]
        have "0 \<le> (- ?rest) / ?fact * ?pow"
          by (metis mult_nonneg_nonneg divide_nonneg_pos less_imp_le)
        thus ?thesis unfolding sin_eq by auto
      qed
      also have "\<dots> \<le> (\<Sum> i = 0 ..< 2 * n. (if even(i) then 0 else ((- 1) ^ ((i - Suc 0) div 2))/((fact i))) * (real_of_float x) ^ i)"
         by auto
      also have "\<dots> \<le> (x * ub_sin_cos_aux prec n 2 1 (x * x))"
        using sin_aux[OF \<open>0 \<le> real_of_float x\<close>] unfolding sum_morph[symmetric] by auto
      finally have "sin x \<le> (x * ub_sin_cos_aux prec n 2 1 (x * x))" .
    } note ub = this and lb
  } note ub = this(1) and lb = this(2)

  have "sin x \<le> (x * ub_sin_cos_aux prec (get_odd n) 2 1 (x * x))"
    using ub[OF odd_pos[OF get_odd] get_odd] .
  moreover have "(x * lb_sin_cos_aux prec (get_even n) 2 1 (x * x)) \<le> sin x"
  proof (cases "0 < get_even n")
    case True
    show ?thesis
      using lb[OF True get_even] .
  next
    case False
    hence "get_even n = 0" by auto
    with \<open>x \<le> pi / 2\<close> \<open>0 \<le> real_of_float x\<close>
    show ?thesis
      unfolding \<open>get_even n = 0\<close> ub_sin_cos_aux.simps minus_float.rep_eq
      using sin_ge_zero by auto
  qed
  ultimately show ?thesis by auto
next
  case True
  show ?thesis
  proof (cases "n = 0")
    case True
    thus ?thesis
      unfolding \<open>n = 0\<close> get_even_def get_odd_def
      using \<open>real_of_float x = 0\<close> lapprox_rat[where x="-1" and y=1] by auto
  next
    case False
    with not0_implies_Suc obtain m where "n = Suc m" by blast
    thus ?thesis
      unfolding \<open>n = Suc m\<close> get_even_def get_odd_def
      using \<open>real_of_float x = 0\<close> rapprox_rat[where x=1 and y=1] lapprox_rat[where x=1 and y=1]
      by (cases "even (Suc m)") auto
  qed
qed


subsection "Compute the cosinus in the entire domain"

definition lb_cos :: "nat \<Rightarrow> float \<Rightarrow> float" where
"lb_cos prec x = (let
    horner = \<lambda> x. lb_sin_cos_aux prec (get_even (prec div 4 + 1)) 1 1 (x * x) ;
    half = \<lambda> x. if x < 0 then - 1 else float_plus_down prec (Float 1 1 * x * x) (- 1)
  in if x < Float 1 (- 1) then horner x
else if x < 1          then half (horner (x * Float 1 (- 1)))
                       else half (half (horner (x * Float 1 (- 2)))))"

definition ub_cos :: "nat \<Rightarrow> float \<Rightarrow> float" where
"ub_cos prec x = (let
    horner = \<lambda> x. ub_sin_cos_aux prec (get_odd (prec div 4 + 1)) 1 1 (x * x) ;
    half = \<lambda> x. float_plus_up prec (Float 1 1 * x * x) (- 1)
  in if x < Float 1 (- 1) then horner x
else if x < 1          then half (horner (x * Float 1 (- 1)))
                       else half (half (horner (x * Float 1 (- 2)))))"

lemma lb_cos:
  assumes "0 \<le> real_of_float x" and "x \<le> pi"
  shows "cos x \<in> {(lb_cos prec x) .. (ub_cos prec x)}" (is "?cos x \<in> {(?lb x) .. (?ub x) }")
proof -
  have x_half[symmetric]: "cos x = 2 * cos (x / 2) * cos (x / 2) - 1" for x :: real
  proof -
    have "cos x = cos (x / 2 + x / 2)"
      by auto
    also have "\<dots> = cos (x / 2) * cos (x / 2) + sin (x / 2) * sin (x / 2) - sin (x / 2) * sin (x / 2) + cos (x / 2) * cos (x / 2) - 1"
      unfolding cos_add by auto
    also have "\<dots> = 2 * cos (x / 2) * cos (x / 2) - 1"
      by algebra
    finally show ?thesis .
  qed

  have "\<not> x < 0" using \<open>0 \<le> real_of_float x\<close> by auto
  let "?ub_horner x" = "ub_sin_cos_aux prec (get_odd (prec div 4 + 1)) 1 1 (x * x)"
  let "?lb_horner x" = "lb_sin_cos_aux prec (get_even (prec div 4 + 1)) 1 1 (x * x)"
  let "?ub_half x" = "float_plus_up prec (Float 1 1 * x * x) (- 1)"
  let "?lb_half x" = "if x < 0 then - 1 else float_plus_down prec (Float 1 1 * x * x) (- 1)"

  show ?thesis
  proof (cases "x < Float 1 (- 1)")
    case True
    hence "x \<le> pi / 2"
      using pi_ge_two by auto
    show ?thesis
      unfolding lb_cos_def[where x=x] ub_cos_def[where x=x]
        if_not_P[OF \<open>\<not> x < 0\<close>] if_P[OF \<open>x < Float 1 (- 1)\<close>] Let_def
      using cos_boundaries[OF \<open>0 \<le> real_of_float x\<close> \<open>x \<le> pi / 2\<close>] .
  next
    case False
    { fix y x :: float let ?x2 = "(x * Float 1 (- 1))"
      assume "y \<le> cos ?x2" and "-pi \<le> x" and "x \<le> pi"
      hence "- (pi / 2) \<le> ?x2" and "?x2 \<le> pi / 2"
        using pi_ge_two unfolding Float_num by auto
      hence "0 \<le> cos ?x2"
        by (rule cos_ge_zero)

      have "(?lb_half y) \<le> cos x"
      proof (cases "y < 0")
        case True
        show ?thesis
          using cos_ge_minus_one unfolding if_P[OF True] by auto
      next
        case False
        hence "0 \<le> real_of_float y" by auto
        from mult_mono[OF \<open>y \<le> cos ?x2\<close> \<open>y \<le> cos ?x2\<close> \<open>0 \<le> cos ?x2\<close> this]
        have "real_of_float y * real_of_float y \<le> cos ?x2 * cos ?x2" .
        hence "2 * real_of_float y * real_of_float y \<le> 2 * cos ?x2 * cos ?x2"
          by auto
        hence "2 * real_of_float y * real_of_float y - 1 \<le> 2 * cos (x / 2) * cos (x / 2) - 1"
          unfolding Float_num by auto
        thus ?thesis
          unfolding if_not_P[OF False] x_half Float_num
          by (auto intro!: float_plus_down_le)
      qed
    } note lb_half = this

    { fix y x :: float let ?x2 = "(x * Float 1 (- 1))"
      assume ub: "cos ?x2 \<le> y" and "- pi \<le> x" and "x \<le> pi"
      hence "- (pi / 2) \<le> ?x2" and "?x2 \<le> pi / 2"
        using pi_ge_two unfolding Float_num by auto
      hence "0 \<le> cos ?x2" by (rule cos_ge_zero)

      have "cos x \<le> (?ub_half y)"
      proof -
        have "0 \<le> real_of_float y"
          using \<open>0 \<le> cos ?x2\<close> ub by (rule order_trans)
        from mult_mono[OF ub ub this \<open>0 \<le> cos ?x2\<close>]
        have "cos ?x2 * cos ?x2 \<le> real_of_float y * real_of_float y" .
        hence "2 * cos ?x2 * cos ?x2 \<le> 2 * real_of_float y * real_of_float y"
          by auto
        hence "2 * cos (x / 2) * cos (x / 2) - 1 \<le> 2 * real_of_float y * real_of_float y - 1"
          unfolding Float_num by auto
        thus ?thesis
          unfolding x_half Float_num
          by (auto intro!: float_plus_up_le)
      qed
    } note ub_half = this

    let ?x2 = "x * Float 1 (- 1)"
    let ?x4 = "x * Float 1 (- 1) * Float 1 (- 1)"

    have "-pi \<le> x"
      using pi_ge_zero[THEN le_imp_neg_le, unfolded minus_zero] \<open>0 \<le> real_of_float x\<close>
      by (rule order_trans)

    show ?thesis
    proof (cases "x < 1")
      case True
      hence "real_of_float x \<le> 1" by auto
      have "0 \<le> real_of_float ?x2" and "?x2 \<le> pi / 2"
        using pi_ge_two \<open>0 \<le> real_of_float x\<close> using assms by auto
      from cos_boundaries[OF this]
      have lb: "(?lb_horner ?x2) \<le> ?cos ?x2" and ub: "?cos ?x2 \<le> (?ub_horner ?x2)"
        by auto

      have "(?lb x) \<le> ?cos x"
      proof -
        from lb_half[OF lb \<open>-pi \<le> x\<close> \<open>x \<le> pi\<close>]
        show ?thesis
          unfolding lb_cos_def[where x=x] Let_def
          using \<open>\<not> x < 0\<close> \<open>\<not> x < Float 1 (- 1)\<close> \<open>x < 1\<close> by auto
      qed
      moreover have "?cos x \<le> (?ub x)"
      proof -
        from ub_half[OF ub \<open>-pi \<le> x\<close> \<open>x \<le> pi\<close>]
        show ?thesis
          unfolding ub_cos_def[where x=x] Let_def
          using \<open>\<not> x < 0\<close> \<open>\<not> x < Float 1 (- 1)\<close> \<open>x < 1\<close> by auto
      qed
      ultimately show ?thesis by auto
    next
      case False
      have "0 \<le> real_of_float ?x4" and "?x4 \<le> pi / 2"
        using pi_ge_two \<open>0 \<le> real_of_float x\<close> \<open>x \<le> pi\<close> unfolding Float_num by auto
      from cos_boundaries[OF this]
      have lb: "(?lb_horner ?x4) \<le> ?cos ?x4" and ub: "?cos ?x4 \<le> (?ub_horner ?x4)"
        by auto

      have eq_4: "?x2 * Float 1 (- 1) = x * Float 1 (- 2)"
        by transfer simp

      have "(?lb x) \<le> ?cos x"
      proof -
        have "-pi \<le> ?x2" and "?x2 \<le> pi"
          using pi_ge_two \<open>0 \<le> real_of_float x\<close> \<open>x \<le> pi\<close> by auto
        from lb_half[OF lb_half[OF lb this] \<open>-pi \<le> x\<close> \<open>x \<le> pi\<close>, unfolded eq_4]
        show ?thesis
          unfolding lb_cos_def[where x=x] if_not_P[OF \<open>\<not> x < 0\<close>]
            if_not_P[OF \<open>\<not> x < Float 1 (- 1)\<close>] if_not_P[OF \<open>\<not> x < 1\<close>] Let_def .
      qed
      moreover have "?cos x \<le> (?ub x)"
      proof -
        have "-pi \<le> ?x2" and "?x2 \<le> pi"
          using pi_ge_two \<open>0 \<le> real_of_float x\<close> \<open> x \<le> pi\<close> by auto
        from ub_half[OF ub_half[OF ub this] \<open>-pi \<le> x\<close> \<open>x \<le> pi\<close>, unfolded eq_4]
        show ?thesis
          unfolding ub_cos_def[where x=x] if_not_P[OF \<open>\<not> x < 0\<close>]
            if_not_P[OF \<open>\<not> x < Float 1 (- 1)\<close>] if_not_P[OF \<open>\<not> x < 1\<close>] Let_def .
      qed
      ultimately show ?thesis by auto
    qed
  qed
qed

lemma lb_cos_minus:
  assumes "-pi \<le> x"
    and "real_of_float x \<le> 0"
  shows "cos (real_of_float(-x)) \<in> {(lb_cos prec (-x)) .. (ub_cos prec (-x))}"
proof -
  have "0 \<le> real_of_float (-x)" and "(-x) \<le> pi"
    using \<open>-pi \<le> x\<close> \<open>real_of_float x \<le> 0\<close> by auto
  from lb_cos[OF this] show ?thesis .
qed

definition bnds_cos :: "nat \<Rightarrow> float \<Rightarrow> float \<Rightarrow> float * float" where
"bnds_cos prec lx ux = (let
    lpi = float_round_down prec (lb_pi prec) ;
    upi = float_round_up prec (ub_pi prec) ;
    k = floor_fl (float_divr prec (lx + lpi) (2 * lpi)) ;
    lx = float_plus_down prec lx (- k * 2 * (if k < 0 then lpi else upi)) ;
    ux = float_plus_up prec ux (- k * 2 * (if k < 0 then upi else lpi))
  in   if - lpi \<le> lx \<and> ux \<le> 0    then (lb_cos prec (-lx), ub_cos prec (-ux))
  else if 0 \<le> lx \<and> ux \<le> lpi      then (lb_cos prec ux, ub_cos prec lx)
  else if - lpi \<le> lx \<and> ux \<le> lpi  then (min (lb_cos prec (-lx)) (lb_cos prec ux), Float 1 0)
  else if 0 \<le> lx \<and> ux \<le> 2 * lpi  then (Float (- 1) 0, max (ub_cos prec lx) (ub_cos prec (- (ux - 2 * lpi))))
  else if -2 * lpi \<le> lx \<and> ux \<le> 0 then (Float (- 1) 0, max (ub_cos prec (lx + 2 * lpi)) (ub_cos prec (-ux)))
                                 else (Float (- 1) 0, Float 1 0))"

lemma floor_int: obtains k :: int where "real_of_int k = (floor_fl f)"
  by (simp add: floor_fl_def)

lemma cos_periodic_nat[simp]:
  fixes n :: nat
  shows "cos (x + n * (2 * pi)) = cos x"
proof (induct n arbitrary: x)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have split_pi_off: "x + (Suc n) * (2 * pi) = (x + n * (2 * pi)) + 2 * pi"
    unfolding Suc_eq_plus1 of_nat_add of_int_1 distrib_right by auto
  show ?case
    unfolding split_pi_off using Suc by auto
qed

lemma cos_periodic_int[simp]:
  fixes i :: int
  shows "cos (x + i * (2 * pi)) = cos x"
proof (cases "0 \<le> i")
  case True
  hence i_nat: "real_of_int i = nat i" by auto
  show ?thesis
    unfolding i_nat by auto
next
  case False
    hence i_nat: "i = - real (nat (-i))" by auto
  have "cos x = cos (x + i * (2 * pi) - i * (2 * pi))"
    by auto
  also have "\<dots> = cos (x + i * (2 * pi))"
    unfolding i_nat mult_minus_left diff_minus_eq_add by (rule cos_periodic_nat)
  finally show ?thesis by auto
qed

lemma bnds_cos: "\<forall>(x::real) lx ux. (l, u) =
  bnds_cos prec lx ux \<and> x \<in> {lx .. ux} \<longrightarrow> l \<le> cos x \<and> cos x \<le> u"
proof (rule allI | rule impI | erule conjE)+
  fix x :: real
  fix lx ux
  assume bnds: "(l, u) = bnds_cos prec lx ux" and x: "x \<in> {lx .. ux}"

  let ?lpi = "float_round_down prec (lb_pi prec)"
  let ?upi = "float_round_up prec (ub_pi prec)"
  let ?k = "floor_fl (float_divr prec (lx + ?lpi) (2 * ?lpi))"
  let ?lx2 = "(- ?k * 2 * (if ?k < 0 then ?lpi else ?upi))"
  let ?ux2 = "(- ?k * 2 * (if ?k < 0 then ?upi else ?lpi))"
  let ?lx = "float_plus_down prec lx ?lx2"
  let ?ux = "float_plus_up prec ux ?ux2"

  obtain k :: int where k: "k = real_of_float ?k"
    by (rule floor_int)

  have upi: "pi \<le> ?upi" and lpi: "?lpi \<le> pi"
    using float_round_up[of "ub_pi prec" prec] pi_boundaries[of prec]
      float_round_down[of prec "lb_pi prec"]
    by auto
  hence "lx + ?lx2 \<le> x - k * (2 * pi) \<and> x - k * (2 * pi) \<le> ux + ?ux2"
    using x
    by (cases "k = 0")
      (auto intro!: add_mono
        simp add: k [symmetric] uminus_add_conv_diff [symmetric]
        simp del: float_of_numeral uminus_add_conv_diff)
  hence "?lx \<le> x - k * (2 * pi) \<and> x - k * (2 * pi) \<le> ?ux"
    by (auto intro!: float_plus_down_le float_plus_up_le)
  note lx = this[THEN conjunct1] and ux = this[THEN conjunct2]
  hence lx_less_ux: "?lx \<le> real_of_float ?ux" by (rule order_trans)

  { assume "- ?lpi \<le> ?lx" and x_le_0: "x - k * (2 * pi) \<le> 0"
    with lpi[THEN le_imp_neg_le] lx
    have pi_lx: "- pi \<le> ?lx" and lx_0: "real_of_float ?lx \<le> 0"
      by simp_all

    have "(lb_cos prec (- ?lx)) \<le> cos (real_of_float (- ?lx))"
      using lb_cos_minus[OF pi_lx lx_0] by simp
    also have "\<dots> \<le> cos (x + (-k) * (2 * pi))"
      using cos_monotone_minus_pi_0'[OF pi_lx lx x_le_0]
      by (simp only: uminus_float.rep_eq of_int_minus
        cos_minus mult_minus_left) simp
    finally have "(lb_cos prec (- ?lx)) \<le> cos x"
      unfolding cos_periodic_int . }
  note negative_lx = this

  { assume "0 \<le> ?lx" and pi_x: "x - k * (2 * pi) \<le> pi"
    with lx
    have pi_lx: "?lx \<le> pi" and lx_0: "0 \<le> real_of_float ?lx"
      by auto

    have "cos (x + (-k) * (2 * pi)) \<le> cos ?lx"
      using cos_monotone_0_pi_le[OF lx_0 lx pi_x]
      by (simp only: of_int_minus
        cos_minus mult_minus_left) simp
    also have "\<dots> \<le> (ub_cos prec ?lx)"
      using lb_cos[OF lx_0 pi_lx] by simp
    finally have "cos x \<le> (ub_cos prec ?lx)"
      unfolding cos_periodic_int . }
  note positive_lx = this

  { assume pi_x: "- pi \<le> x - k * (2 * pi)" and "?ux \<le> 0"
    with ux
    have pi_ux: "- pi \<le> ?ux" and ux_0: "real_of_float ?ux \<le> 0"
      by simp_all

    have "cos (x + (-k) * (2 * pi)) \<le> cos (real_of_float (- ?ux))"
      using cos_monotone_minus_pi_0'[OF pi_x ux ux_0]
      by (simp only: uminus_float.rep_eq of_int_minus
          cos_minus mult_minus_left) simp
    also have "\<dots> \<le> (ub_cos prec (- ?ux))"
      using lb_cos_minus[OF pi_ux ux_0, of prec] by simp
    finally have "cos x \<le> (ub_cos prec (- ?ux))"
      unfolding cos_periodic_int . }
  note negative_ux = this

  { assume "?ux \<le> ?lpi" and x_ge_0: "0 \<le> x - k * (2 * pi)"
    with lpi ux
    have pi_ux: "?ux \<le> pi" and ux_0: "0 \<le> real_of_float ?ux"
      by simp_all

    have "(lb_cos prec ?ux) \<le> cos ?ux"
      using lb_cos[OF ux_0 pi_ux] by simp
    also have "\<dots> \<le> cos (x + (-k) * (2 * pi))"
      using cos_monotone_0_pi_le[OF x_ge_0 ux pi_ux]
      by (simp only: of_int_minus
        cos_minus mult_minus_left) simp
    finally have "(lb_cos prec ?ux) \<le> cos x"
      unfolding cos_periodic_int . }
  note positive_ux = this

  show "l \<le> cos x \<and> cos x \<le> u"
  proof (cases "- ?lpi \<le> ?lx \<and> ?ux \<le> 0")
    case True
    with bnds have l: "l = lb_cos prec (-?lx)" and u: "u = ub_cos prec (-?ux)"
      by (auto simp add: bnds_cos_def Let_def)
    from True lpi[THEN le_imp_neg_le] lx ux
    have "- pi \<le> x - k * (2 * pi)" and "x - k * (2 * pi) \<le> 0"
      by auto
    with True negative_ux negative_lx show ?thesis
      unfolding l u by simp
  next
    case 1: False
    show ?thesis
    proof (cases "0 \<le> ?lx \<and> ?ux \<le> ?lpi")
      case True with bnds 1
      have l: "l = lb_cos prec ?ux"
        and u: "u = ub_cos prec ?lx"
        by (auto simp add: bnds_cos_def Let_def)
      from True lpi lx ux
      have "0 \<le> x - k * (2 * pi)" and "x - k * (2 * pi) \<le> pi"
        by auto
      with True positive_ux positive_lx show ?thesis
        unfolding l u by simp
    next
      case 2: False
      show ?thesis
      proof (cases "- ?lpi \<le> ?lx \<and> ?ux \<le> ?lpi")
        case Cond: True
        with bnds 1 2 have l: "l = min (lb_cos prec (-?lx)) (lb_cos prec ?ux)"
          and u: "u = Float 1 0"
          by (auto simp add: bnds_cos_def Let_def)
        show ?thesis
          unfolding u l using negative_lx positive_ux Cond
          by (cases "x - k * (2 * pi) < 0") (auto simp add: real_of_float_min)
      next
        case 3: False
        show ?thesis
        proof (cases "0 \<le> ?lx \<and> ?ux \<le> 2 * ?lpi")
          case Cond: True
          with bnds 1 2 3
          have l: "l = Float (- 1) 0"
            and u: "u = max (ub_cos prec ?lx) (ub_cos prec (- (?ux - 2 * ?lpi)))"
            by (auto simp add: bnds_cos_def Let_def)

          have "cos x \<le> real_of_float u"
          proof (cases "x - k * (2 * pi) < pi")
            case True
            hence "x - k * (2 * pi) \<le> pi" by simp
            from positive_lx[OF Cond[THEN conjunct1] this] show ?thesis
              unfolding u by (simp add: real_of_float_max)
          next
            case False
            hence "pi \<le> x - k * (2 * pi)" by simp
            hence pi_x: "- pi \<le> x - k * (2 * pi) - 2 * pi" by simp

            have "?ux \<le> 2 * pi"
              using Cond lpi by auto
            hence "x - k * (2 * pi) - 2 * pi \<le> 0"
              using ux by simp

            have ux_0: "real_of_float (?ux - 2 * ?lpi) \<le> 0"
              using Cond by auto

            from 2 and Cond have "\<not> ?ux \<le> ?lpi" by auto
            hence "- ?lpi \<le> ?ux - 2 * ?lpi" by auto
            hence pi_ux: "- pi \<le> (?ux - 2 * ?lpi)"
              using lpi[THEN le_imp_neg_le] by auto

            have x_le_ux: "x - k * (2 * pi) - 2 * pi \<le> (?ux - 2 * ?lpi)"
              using ux lpi by auto
            have "cos x = cos (x + (-k) * (2 * pi) + (-1::int) * (2 * pi))"
              unfolding cos_periodic_int ..
            also have "\<dots> \<le> cos ((?ux - 2 * ?lpi))"
              using cos_monotone_minus_pi_0'[OF pi_x x_le_ux ux_0]
              by (simp only: minus_float.rep_eq of_int_minus of_int_1
                mult_minus_left mult_1_left) simp
            also have "\<dots> = cos ((- (?ux - 2 * ?lpi)))"
              unfolding uminus_float.rep_eq cos_minus ..
            also have "\<dots> \<le> (ub_cos prec (- (?ux - 2 * ?lpi)))"
              using lb_cos_minus[OF pi_ux ux_0] by simp
            finally show ?thesis unfolding u by (simp add: real_of_float_max)
          qed
          thus ?thesis unfolding l by auto
        next
          case 4: False
          show ?thesis
          proof (cases "-2 * ?lpi \<le> ?lx \<and> ?ux \<le> 0")
            case Cond: True
            with bnds 1 2 3 4 have l: "l = Float (- 1) 0"
              and u: "u = max (ub_cos prec (?lx + 2 * ?lpi)) (ub_cos prec (-?ux))"
              by (auto simp add: bnds_cos_def Let_def)

            have "cos x \<le> u"
            proof (cases "-pi < x - k * (2 * pi)")
              case True
              hence "-pi \<le> x - k * (2 * pi)" by simp
              from negative_ux[OF this Cond[THEN conjunct2]] show ?thesis
                unfolding u by (simp add: real_of_float_max)
            next
              case False
              hence "x - k * (2 * pi) \<le> -pi" by simp
              hence pi_x: "x - k * (2 * pi) + 2 * pi \<le> pi" by simp

              have "-2 * pi \<le> ?lx" using Cond lpi by auto

              hence "0 \<le> x - k * (2 * pi) + 2 * pi" using lx by simp

              have lx_0: "0 \<le> real_of_float (?lx + 2 * ?lpi)"
                using Cond lpi by auto

              from 1 and Cond have "\<not> -?lpi \<le> ?lx" by auto
              hence "?lx + 2 * ?lpi \<le> ?lpi" by auto
              hence pi_lx: "(?lx + 2 * ?lpi) \<le> pi"
                using lpi[THEN le_imp_neg_le] by auto

              have lx_le_x: "(?lx + 2 * ?lpi) \<le> x - k * (2 * pi) + 2 * pi"
                using lx lpi by auto

              have "cos x = cos (x + (-k) * (2 * pi) + (1 :: int) * (2 * pi))"
                unfolding cos_periodic_int ..
              also have "\<dots> \<le> cos ((?lx + 2 * ?lpi))"
                using cos_monotone_0_pi_le[OF lx_0 lx_le_x pi_x]
                by (simp only: minus_float.rep_eq of_int_minus of_int_1
                  mult_minus_left mult_1_left) simp
              also have "\<dots> \<le> (ub_cos prec (?lx + 2 * ?lpi))"
                using lb_cos[OF lx_0 pi_lx] by simp
              finally show ?thesis unfolding u by (simp add: real_of_float_max)
            qed
            thus ?thesis unfolding l by auto
          next
            case False
            with bnds 1 2 3 4 show ?thesis
              by (auto simp add: bnds_cos_def Let_def)
          qed
        qed
      qed
    qed
  qed
qed


section "Exponential function"

subsection "Compute the series of the exponential function"

fun ub_exp_horner :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> float \<Rightarrow> float"
  and lb_exp_horner :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> float \<Rightarrow> float"
where
"ub_exp_horner prec 0 i k x       = 0" |
"ub_exp_horner prec (Suc n) i k x = float_plus_up prec
    (rapprox_rat prec 1 (int k)) (float_round_up prec (x * lb_exp_horner prec n (i + 1) (k * i) x))" |
"lb_exp_horner prec 0 i k x       = 0" |
"lb_exp_horner prec (Suc n) i k x = float_plus_down prec
    (lapprox_rat prec 1 (int k)) (float_round_down prec (x * ub_exp_horner prec n (i + 1) (k * i) x))"

lemma bnds_exp_horner:
  assumes "real_of_float x \<le> 0"
  shows "exp x \<in> {lb_exp_horner prec (get_even n) 1 1 x .. ub_exp_horner prec (get_odd n) 1 1 x}"
proof -
  have f_eq: "fact (Suc n) = fact n * ((\<lambda>i::nat. i + 1) ^^ n) 1" for n
  proof -
    have F: "\<And> m. ((\<lambda>i. i + 1) ^^ n) m = n + m"
      by (induct n) auto
    show ?thesis
      unfolding F by auto
  qed

  note bounds = horner_bounds_nonpos[where f="fact" and lb="lb_exp_horner prec" and ub="ub_exp_horner prec" and j'=0 and s=1,
    OF assms f_eq lb_exp_horner.simps ub_exp_horner.simps]

  have "lb_exp_horner prec (get_even n) 1 1 x \<le> exp x"
  proof -
    have "lb_exp_horner prec (get_even n) 1 1 x \<le> (\<Sum>j = 0..<get_even n. 1 / (fact j) * real_of_float x ^ j)"
      using bounds(1) by auto
    also have "\<dots> \<le> exp x"
    proof -
      obtain t where "\<bar>t\<bar> \<le> \<bar>real_of_float x\<bar>" and "exp x = (\<Sum>m = 0..<get_even n. real_of_float x ^ m / (fact m)) + exp t / (fact (get_even n)) * (real_of_float x) ^ (get_even n)"
        using Maclaurin_exp_le unfolding atLeast0LessThan by blast
      moreover have "0 \<le> exp t / (fact (get_even n)) * (real_of_float x) ^ (get_even n)"
        by (auto simp: zero_le_even_power)
      ultimately show ?thesis using get_odd exp_gt_zero by auto
    qed
    finally show ?thesis .
  qed
  moreover
  have "exp x \<le> ub_exp_horner prec (get_odd n) 1 1 x"
  proof -
    have x_less_zero: "real_of_float x ^ get_odd n \<le> 0"
    proof (cases "real_of_float x = 0")
      case True
      have "(get_odd n) \<noteq> 0" using get_odd[THEN odd_pos] by auto
      thus ?thesis unfolding True power_0_left by auto
    next
      case False hence "real_of_float x < 0" using \<open>real_of_float x \<le> 0\<close> by auto
      show ?thesis by (rule less_imp_le, auto simp add: \<open>real_of_float x < 0\<close>)
    qed
    obtain t where "\<bar>t\<bar> \<le> \<bar>real_of_float x\<bar>"
      and "exp x = (\<Sum>m = 0..<get_odd n. (real_of_float x) ^ m / (fact m)) + exp t / (fact (get_odd n)) * (real_of_float x) ^ (get_odd n)"
      using Maclaurin_exp_le unfolding atLeast0LessThan by blast
    moreover have "exp t / (fact (get_odd n)) * (real_of_float x) ^ (get_odd n) \<le> 0"
      by (auto intro!: mult_nonneg_nonpos divide_nonpos_pos simp add: x_less_zero)
    ultimately have "exp x \<le> (\<Sum>j = 0..<get_odd n. 1 / (fact j) * real_of_float x ^ j)"
      using get_odd exp_gt_zero by auto
    also have "\<dots> \<le> ub_exp_horner prec (get_odd n) 1 1 x"
      using bounds(2) by auto
    finally show ?thesis .
  qed
  ultimately show ?thesis by auto
qed

lemma ub_exp_horner_nonneg: "real_of_float x \<le> 0 \<Longrightarrow>
  0 \<le> real_of_float (ub_exp_horner prec (get_odd n) (Suc 0) (Suc 0) x)"
  using bnds_exp_horner[of x prec n]
  by (intro order_trans[OF exp_ge_zero]) auto


subsection "Compute the exponential function on the entire domain"

function ub_exp :: "nat \<Rightarrow> float \<Rightarrow> float" and lb_exp :: "nat \<Rightarrow> float \<Rightarrow> float" where
"lb_exp prec x =
  (if 0 < x then float_divl prec 1 (ub_exp prec (-x))
  else
    let
      horner = (\<lambda> x. let  y = lb_exp_horner prec (get_even (prec + 2)) 1 1 x in
        if y \<le> 0 then Float 1 (- 2) else y)
    in
      if x < - 1 then
        power_down_fl prec (horner (float_divl prec x (- floor_fl x))) (nat (- int_floor_fl x))
      else horner x)" |
"ub_exp prec x =
  (if 0 < x then float_divr prec 1 (lb_exp prec (-x))
  else if x < - 1 then
    power_up_fl prec
      (ub_exp_horner prec (get_odd (prec + 2)) 1 1
        (float_divr prec x (- floor_fl x))) (nat (- int_floor_fl x))
  else ub_exp_horner prec (get_odd (prec + 2)) 1 1 x)"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda> v. let (prec, x) = case_sum id id v in (if 0 < x then 1 else 0))") auto

lemma exp_m1_ge_quarter: "(1 / 4 :: real) \<le> exp (- 1)"
proof -
  have eq4: "4 = Suc (Suc (Suc (Suc 0)))" by auto
  have "1 / 4 = (Float 1 (- 2))"
    unfolding Float_num by auto
  also have "\<dots> \<le> lb_exp_horner 3 (get_even 3) 1 1 (- 1)"
    by (subst less_eq_float.rep_eq [symmetric]) code_simp
  also have "\<dots> \<le> exp (- 1 :: float)"
    using bnds_exp_horner[where x="- 1"] by auto
  finally show ?thesis
    by simp
qed

lemma lb_exp_pos:
  assumes "\<not> 0 < x"
  shows "0 < lb_exp prec x"
proof -
  let "?lb_horner x" = "lb_exp_horner prec (get_even (prec + 2)) 1 1 x"
  let "?horner x" = "let y = ?lb_horner x in if y \<le> 0 then Float 1 (- 2) else y"
  have pos_horner: "0 < ?horner x" for x
    unfolding Let_def by (cases "?lb_horner x \<le> 0") auto
  moreover have "0 < real_of_float ((?horner x) ^ num)" for x :: float and num :: nat
  proof -
    have "0 < real_of_float (?horner x) ^ num" using \<open>0 < ?horner x\<close> by simp
    also have "\<dots> = (?horner x) ^ num" by auto
    finally show ?thesis .
  qed
  ultimately show ?thesis
    unfolding lb_exp.simps if_not_P[OF \<open>\<not> 0 < x\<close>] Let_def
    by (cases "floor_fl x", cases "x < - 1")
      (auto simp: real_power_up_fl real_power_down_fl intro!: power_up_less power_down_pos)
qed

lemma exp_boundaries':
  assumes "x \<le> 0"
  shows "exp x \<in> { (lb_exp prec x) .. (ub_exp prec x)}"
proof -
  let "?lb_exp_horner x" = "lb_exp_horner prec (get_even (prec + 2)) 1 1 x"
  let "?ub_exp_horner x" = "ub_exp_horner prec (get_odd (prec + 2)) 1 1 x"

  have "real_of_float x \<le> 0" and "\<not> x > 0"
    using \<open>x \<le> 0\<close> by auto
  show ?thesis
  proof (cases "x < - 1")
    case False
    hence "- 1 \<le> real_of_float x" by auto
    show ?thesis
    proof (cases "?lb_exp_horner x \<le> 0")
      case True
      from \<open>\<not> x < - 1\<close>
      have "- 1 \<le> real_of_float x" by auto
      hence "exp (- 1) \<le> exp x"
        unfolding exp_le_cancel_iff .
      from order_trans[OF exp_m1_ge_quarter this] have "Float 1 (- 2) \<le> exp x"
        unfolding Float_num .
      with True show ?thesis
        using bnds_exp_horner \<open>real_of_float x \<le> 0\<close> \<open>\<not> x > 0\<close> \<open>\<not> x < - 1\<close> by auto
    next
      case False
      thus ?thesis
        using bnds_exp_horner \<open>real_of_float x \<le> 0\<close> \<open>\<not> x > 0\<close> \<open>\<not> x < - 1\<close> by (auto simp add: Let_def)
    qed
  next
    case True
    let ?num = "nat (- int_floor_fl x)"

    have "real_of_int (int_floor_fl x) < - 1"
      using int_floor_fl[of x] \<open>x < - 1\<close> by simp
    hence "real_of_int (int_floor_fl x) < 0" by simp
    hence "int_floor_fl x < 0" by auto
    hence "1 \<le> - int_floor_fl x" by auto
    hence "0 < nat (- int_floor_fl x)" by auto
    hence "0 < ?num"  by auto
    hence "real ?num \<noteq> 0" by auto
    have num_eq: "real ?num = - int_floor_fl x"
      using \<open>0 < nat (- int_floor_fl x)\<close> by auto
    have "0 < - int_floor_fl x"
      using \<open>0 < ?num\<close>[unfolded of_nat_less_iff[symmetric]] by simp
    hence "real_of_int (int_floor_fl x) < 0"
      unfolding less_float_def by auto
    have fl_eq: "real_of_int (- int_floor_fl x) = real_of_float (- floor_fl x)"
      by (simp add: floor_fl_def int_floor_fl_def)
    from \<open>0 < - int_floor_fl x\<close> have "0 \<le> real_of_float (- floor_fl x)"
      by (simp add: floor_fl_def int_floor_fl_def)
    from \<open>real_of_int (int_floor_fl x) < 0\<close> have "real_of_float (floor_fl x) < 0"
      by (simp add: floor_fl_def int_floor_fl_def)
    have "exp x \<le> ub_exp prec x"
    proof -
      have div_less_zero: "real_of_float (float_divr prec x (- floor_fl x)) \<le> 0"
        using float_divr_nonpos_pos_upper_bound[OF \<open>real_of_float x \<le> 0\<close> \<open>0 \<le> real_of_float (- floor_fl x)\<close>]
        unfolding less_eq_float_def zero_float.rep_eq .

      have "exp x = exp (?num * (x / ?num))"
        using \<open>real ?num \<noteq> 0\<close> by auto
      also have "\<dots> = exp (x / ?num) ^ ?num"
        unfolding exp_real_of_nat_mult ..
      also have "\<dots> \<le> exp (float_divr prec x (- floor_fl x)) ^ ?num"
        unfolding num_eq fl_eq
        by (rule power_mono, rule exp_le_cancel_iff[THEN iffD2], rule float_divr) auto
      also have "\<dots> \<le> (?ub_exp_horner (float_divr prec x (- floor_fl x))) ^ ?num"
        unfolding real_of_float_power
        by (rule power_mono, rule bnds_exp_horner[OF div_less_zero, unfolded atLeastAtMost_iff, THEN conjunct2], auto)
      also have "\<dots> \<le> real_of_float (power_up_fl prec (?ub_exp_horner (float_divr prec x (- floor_fl x))) ?num)"
        by (auto simp add: real_power_up_fl intro!: power_up ub_exp_horner_nonneg div_less_zero)
      finally show ?thesis
        unfolding ub_exp.simps if_not_P[OF \<open>\<not> 0 < x\<close>] if_P[OF \<open>x < - 1\<close>] floor_fl_def Let_def .
    qed
    moreover
    have "lb_exp prec x \<le> exp x"
    proof -
      let ?divl = "float_divl prec x (- floor_fl x)"
      let ?horner = "?lb_exp_horner ?divl"

      show ?thesis
      proof (cases "?horner \<le> 0")
        case False
        hence "0 \<le> real_of_float ?horner" by auto

        have div_less_zero: "real_of_float (float_divl prec x (- floor_fl x)) \<le> 0"
          using \<open>real_of_float (floor_fl x) < 0\<close> \<open>real_of_float x \<le> 0\<close>
          by (auto intro!: order_trans[OF float_divl] divide_nonpos_neg)

        have "(?lb_exp_horner (float_divl prec x (- floor_fl x))) ^ ?num \<le>
          exp (float_divl prec x (- floor_fl x)) ^ ?num"
          using \<open>0 \<le> real_of_float ?horner\<close>[unfolded floor_fl_def[symmetric]]
            bnds_exp_horner[OF div_less_zero, unfolded atLeastAtMost_iff, THEN conjunct1]
          by (auto intro!: power_mono)
        also have "\<dots> \<le> exp (x / ?num) ^ ?num"
          unfolding num_eq fl_eq
          using float_divl by (auto intro!: power_mono simp del: uminus_float.rep_eq)
        also have "\<dots> = exp (?num * (x / ?num))"
          unfolding exp_real_of_nat_mult ..
        also have "\<dots> = exp x"
          using \<open>real ?num \<noteq> 0\<close> by auto
        finally show ?thesis
          using False
          unfolding lb_exp.simps if_not_P[OF \<open>\<not> 0 < x\<close>] if_P[OF \<open>x < - 1\<close>]
            int_floor_fl_def Let_def if_not_P[OF False]
          by (auto simp: real_power_down_fl intro!: power_down_le)
      next
        case True
        have "power_down_fl prec (Float 1 (- 2))  ?num \<le> (Float 1 (- 2)) ^ ?num"
          by (metis Float_le_zero_iff less_imp_le linorder_not_less
            not_numeral_le_zero numeral_One power_down_fl)
        then have "power_down_fl prec (Float 1 (- 2))  ?num \<le> real_of_float (Float 1 (- 2)) ^ ?num"
          by simp
        also
        have "real_of_float (floor_fl x) \<noteq> 0" and "real_of_float (floor_fl x) \<le> 0"
          using \<open>real_of_float (floor_fl x) < 0\<close> by auto
        from divide_right_mono_neg[OF floor_fl[of x] \<open>real_of_float (floor_fl x) \<le> 0\<close>, unfolded divide_self[OF \<open>real_of_float (floor_fl x) \<noteq> 0\<close>]]
        have "- 1 \<le> x / (- floor_fl x)"
          unfolding minus_float.rep_eq by auto
        from order_trans[OF exp_m1_ge_quarter this[unfolded exp_le_cancel_iff[where x="- 1", symmetric]]]
        have "Float 1 (- 2) \<le> exp (x / (- floor_fl x))"
          unfolding Float_num .
        hence "real_of_float (Float 1 (- 2)) ^ ?num \<le> exp (x / (- floor_fl x)) ^ ?num"
          by (metis Float_num(5) power_mono zero_le_divide_1_iff zero_le_numeral)
        also have "\<dots> = exp x"
          unfolding num_eq fl_eq exp_real_of_nat_mult[symmetric]
          using \<open>real_of_float (floor_fl x) \<noteq> 0\<close> by auto
        finally show ?thesis
          unfolding lb_exp.simps if_not_P[OF \<open>\<not> 0 < x\<close>] if_P[OF \<open>x < - 1\<close>]
            int_floor_fl_def Let_def if_P[OF True] real_of_float_power .
      qed
    qed
    ultimately show ?thesis by auto
  qed
qed

lemma exp_boundaries: "exp x \<in> { lb_exp prec x .. ub_exp prec x }"
proof -
  show ?thesis
  proof (cases "0 < x")
    case False
    hence "x \<le> 0" by auto
    from exp_boundaries'[OF this] show ?thesis .
  next
    case True
    hence "-x \<le> 0" by auto

    have "lb_exp prec x \<le> exp x"
    proof -
      from exp_boundaries'[OF \<open>-x \<le> 0\<close>]
      have ub_exp: "exp (- real_of_float x) \<le> ub_exp prec (-x)"
        unfolding atLeastAtMost_iff minus_float.rep_eq by auto

      have "float_divl prec 1 (ub_exp prec (-x)) \<le> 1 / ub_exp prec (-x)"
        using float_divl[where x=1] by auto
      also have "\<dots> \<le> exp x"
        using ub_exp[unfolded inverse_le_iff_le[OF order_less_le_trans[OF exp_gt_zero ub_exp]
          exp_gt_zero, symmetric]]
        unfolding exp_minus nonzero_inverse_inverse_eq[OF exp_not_eq_zero] inverse_eq_divide
        by auto
      finally show ?thesis
        unfolding lb_exp.simps if_P[OF True] .
    qed
    moreover
    have "exp x \<le> ub_exp prec x"
    proof -
      have "\<not> 0 < -x" using \<open>0 < x\<close> by auto

      from exp_boundaries'[OF \<open>-x \<le> 0\<close>]
      have lb_exp: "lb_exp prec (-x) \<le> exp (- real_of_float x)"
        unfolding atLeastAtMost_iff minus_float.rep_eq by auto

      have "exp x \<le> (1 :: float) / lb_exp prec (-x)"
        using lb_exp lb_exp_pos[OF \<open>\<not> 0 < -x\<close>, of prec]
        by (simp del: lb_exp.simps add: exp_minus field_simps)
      also have "\<dots> \<le> float_divr prec 1 (lb_exp prec (-x))"
        using float_divr .
      finally show ?thesis
        unfolding ub_exp.simps if_P[OF True] .
    qed
    ultimately show ?thesis
      by auto
  qed
qed

lemma bnds_exp: "\<forall>(x::real) lx ux. (l, u) =
  (lb_exp prec lx, ub_exp prec ux) \<and> x \<in> {lx .. ux} \<longrightarrow> l \<le> exp x \<and> exp x \<le> u"
proof (rule allI, rule allI, rule allI, rule impI)
  fix x :: real and lx ux
  assume "(l, u) = (lb_exp prec lx, ub_exp prec ux) \<and> x \<in> {lx .. ux}"
  hence l: "lb_exp prec lx = l " and u: "ub_exp prec ux = u" and x: "x \<in> {lx .. ux}"
    by auto
  show "l \<le> exp x \<and> exp x \<le> u"
  proof
    show "l \<le> exp x"
    proof -
      from exp_boundaries[of lx prec, unfolded l]
      have "l \<le> exp lx" by (auto simp del: lb_exp.simps)
      also have "\<dots> \<le> exp x" using x by auto
      finally show ?thesis .
    qed
    show "exp x \<le> u"
    proof -
      have "exp x \<le> exp ux" using x by auto
      also have "\<dots> \<le> u" using exp_boundaries[of ux prec, unfolded u] by (auto simp del: ub_exp.simps)
      finally show ?thesis .
    qed
  qed
qed


section "Logarithm"

subsection "Compute the logarithm series"

fun ub_ln_horner :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> float \<Rightarrow> float"
and lb_ln_horner :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> float \<Rightarrow> float" where
"ub_ln_horner prec 0 i x       = 0" |
"ub_ln_horner prec (Suc n) i x = float_plus_up prec
    (rapprox_rat prec 1 (int i)) (- float_round_down prec (x * lb_ln_horner prec n (Suc i) x))" |
"lb_ln_horner prec 0 i x       = 0" |
"lb_ln_horner prec (Suc n) i x = float_plus_down prec
    (lapprox_rat prec 1 (int i)) (- float_round_up prec (x * ub_ln_horner prec n (Suc i) x))"

lemma ln_bounds:
  assumes "0 \<le> x"
    and "x < 1"
  shows "(\<Sum>i=0..<2*n. (- 1) ^ i * (1 / real (i + 1)) * x ^ (Suc i)) \<le> ln (x + 1)" (is "?lb")
  and "ln (x + 1) \<le> (\<Sum>i=0..<2*n + 1. (- 1) ^ i * (1 / real (i + 1)) * x ^ (Suc i))" (is "?ub")
proof -
  let "?a n" = "(1/real (n +1)) * x ^ (Suc n)"

  have ln_eq: "(\<Sum> i. (- 1) ^ i * ?a i) = ln (x + 1)"
    using ln_series[of "x + 1"] \<open>0 \<le> x\<close> \<open>x < 1\<close> by auto

  have "norm x < 1" using assms by auto
  have "?a \<longlonglongrightarrow> 0" unfolding Suc_eq_plus1[symmetric] inverse_eq_divide[symmetric]
    using tendsto_mult[OF LIMSEQ_inverse_real_of_nat LIMSEQ_Suc[OF LIMSEQ_power_zero[OF \<open>norm x < 1\<close>]]] by auto
  have "0 \<le> ?a n" for n
    by (rule mult_nonneg_nonneg) (auto simp: \<open>0 \<le> x\<close>)
  have "?a (Suc n) \<le> ?a n" for n
    unfolding inverse_eq_divide[symmetric]
  proof (rule mult_mono)
    show "0 \<le> x ^ Suc (Suc n)"
      by (auto simp add: \<open>0 \<le> x\<close>)
    have "x ^ Suc (Suc n) \<le> x ^ Suc n * 1"
      unfolding power_Suc2 mult.assoc[symmetric]
      by (rule mult_left_mono, fact less_imp_le[OF \<open>x < 1\<close>]) (auto simp: \<open>0 \<le> x\<close>)
    thus "x ^ Suc (Suc n) \<le> x ^ Suc n" by auto
  qed auto
  from summable_Leibniz'(2,4)[OF \<open>?a \<longlonglongrightarrow> 0\<close> \<open>\<And>n. 0 \<le> ?a n\<close>, OF \<open>\<And>n. ?a (Suc n) \<le> ?a n\<close>, unfolded ln_eq]
  show ?lb and ?ub
    unfolding atLeast0LessThan by auto
qed

lemma ln_float_bounds:
  assumes "0 \<le> real_of_float x"
    and "real_of_float x < 1"
  shows "x * lb_ln_horner prec (get_even n) 1 x \<le> ln (x + 1)" (is "?lb \<le> ?ln")
    and "ln (x + 1) \<le> x * ub_ln_horner prec (get_odd n) 1 x" (is "?ln \<le> ?ub")
proof -
  obtain ev where ev: "get_even n = 2 * ev" using get_even_double ..
  obtain od where od: "get_odd n = 2 * od + 1" using get_odd_double ..

  let "?s n" = "(- 1) ^ n * (1 / real (1 + n)) * (real_of_float x)^(Suc n)"

  have "?lb \<le> sum ?s {0 ..< 2 * ev}"
    unfolding power_Suc2 mult.assoc[symmetric] times_float.rep_eq sum_distrib_right[symmetric]
    unfolding mult.commute[of "real_of_float x"] ev 
    using horner_bounds(1)[where G="\<lambda> i k. Suc k" and F="\<lambda>x. x" and f="\<lambda>x. x" 
                    and lb="\<lambda>n i k x. lb_ln_horner prec n k x" 
                    and ub="\<lambda>n i k x. ub_ln_horner prec n k x" and j'=1 and n="2*ev",
      OF \<open>0 \<le> real_of_float x\<close> refl lb_ln_horner.simps ub_ln_horner.simps] \<open>0 \<le> real_of_float x\<close>
    unfolding real_of_float_power
    by (rule mult_right_mono)
  also have "\<dots> \<le> ?ln"
    using ln_bounds(1)[OF \<open>0 \<le> real_of_float x\<close> \<open>real_of_float x < 1\<close>] by auto
  finally show "?lb \<le> ?ln" .

  have "?ln \<le> sum ?s {0 ..< 2 * od + 1}"
    using ln_bounds(2)[OF \<open>0 \<le> real_of_float x\<close> \<open>real_of_float x < 1\<close>] by auto
  also have "\<dots> \<le> ?ub"
    unfolding power_Suc2 mult.assoc[symmetric] times_float.rep_eq sum_distrib_right[symmetric]
    unfolding mult.commute[of "real_of_float x"] od
    using horner_bounds(2)[where G="\<lambda> i k. Suc k" and F="\<lambda>x. x" and f="\<lambda>x. x" and lb="\<lambda>n i k x. lb_ln_horner prec n k x" and ub="\<lambda>n i k x. ub_ln_horner prec n k x" and j'=1 and n="2*od+1",
      OF \<open>0 \<le> real_of_float x\<close> refl lb_ln_horner.simps ub_ln_horner.simps] \<open>0 \<le> real_of_float x\<close>
    unfolding real_of_float_power
    by (rule mult_right_mono)
  finally show "?ln \<le> ?ub" .
qed

lemma ln_add:
  fixes x :: real
  assumes "0 < x" and "0 < y"
  shows "ln (x + y) = ln x + ln (1 + y / x)"
proof -
  have "x \<noteq> 0" using assms by auto
  have "x + y = x * (1 + y / x)"
    unfolding distrib_left times_divide_eq_right nonzero_mult_div_cancel_left[OF \<open>x \<noteq> 0\<close>]
    by auto
  moreover
  have "0 < y / x" using assms by auto
  hence "0 < 1 + y / x" by auto
  ultimately show ?thesis
    using ln_mult assms by auto
qed


subsection "Compute the logarithm of 2"

definition ub_ln2 where "ub_ln2 prec = (let third = rapprox_rat (max prec 1) 1 3
                                        in float_plus_up prec
                                          ((Float 1 (- 1) * ub_ln_horner prec (get_odd prec) 1 (Float 1 (- 1))))
                                           (float_round_up prec (third * ub_ln_horner prec (get_odd prec) 1 third)))"
definition lb_ln2 where "lb_ln2 prec = (let third = lapprox_rat prec 1 3
                                        in float_plus_down prec
                                          ((Float 1 (- 1) * lb_ln_horner prec (get_even prec) 1 (Float 1 (- 1))))
                                           (float_round_down prec (third * lb_ln_horner prec (get_even prec) 1 third)))"

lemma ub_ln2: "ln 2 \<le> ub_ln2 prec" (is "?ub_ln2")
  and lb_ln2: "lb_ln2 prec \<le> ln 2" (is "?lb_ln2")
proof -
  let ?uthird = "rapprox_rat (max prec 1) 1 3"
  let ?lthird = "lapprox_rat prec 1 3"

  have ln2_sum: "ln 2 = ln (1/2 + 1) + ln (1 / 3 + 1::real)"
    using ln_add[of "3 / 2" "1 / 2"] by auto
  have lb3: "?lthird \<le> 1 / 3" using lapprox_rat[of prec 1 3] by auto
  hence lb3_ub: "real_of_float ?lthird < 1" by auto
  have lb3_lb: "0 \<le> real_of_float ?lthird" using lapprox_rat_nonneg[of 1 3] by auto
  have ub3: "1 / 3 \<le> ?uthird" using rapprox_rat[of 1 3] by auto
  hence ub3_lb: "0 \<le> real_of_float ?uthird" by auto

  have lb2: "0 \<le> real_of_float (Float 1 (- 1))" and ub2: "real_of_float (Float 1 (- 1)) < 1"
    unfolding Float_num by auto

  have "0 \<le> (1::int)" and "0 < (3::int)" by auto
  have ub3_ub: "real_of_float ?uthird < 1"
    by (simp add: Float.compute_rapprox_rat Float.compute_lapprox_rat rapprox_posrat_less1)

  have third_gt0: "(0 :: real) < 1 / 3 + 1" by auto
  have uthird_gt0: "0 < real_of_float ?uthird + 1" using ub3_lb by auto
  have lthird_gt0: "0 < real_of_float ?lthird + 1" using lb3_lb by auto

  show ?ub_ln2
    unfolding ub_ln2_def Let_def ln2_sum Float_num(4)[symmetric]
  proof (rule float_plus_up_le, rule add_mono, fact ln_float_bounds(2)[OF lb2 ub2])
    have "ln (1 / 3 + 1) \<le> ln (real_of_float ?uthird + 1)"
      unfolding ln_le_cancel_iff[OF third_gt0 uthird_gt0] using ub3 by auto
    also have "\<dots> \<le> ?uthird * ub_ln_horner prec (get_odd prec) 1 ?uthird"
      using ln_float_bounds(2)[OF ub3_lb ub3_ub] .
    also note float_round_up
    finally show "ln (1 / 3 + 1) \<le> float_round_up prec (?uthird * ub_ln_horner prec (get_odd prec) 1 ?uthird)" .
  qed
  show ?lb_ln2
    unfolding lb_ln2_def Let_def ln2_sum Float_num(4)[symmetric]
  proof (rule float_plus_down_le, rule add_mono, fact ln_float_bounds(1)[OF lb2 ub2])
    have "?lthird * lb_ln_horner prec (get_even prec) 1 ?lthird \<le> ln (real_of_float ?lthird + 1)"
      using ln_float_bounds(1)[OF lb3_lb lb3_ub] .
    note float_round_down_le[OF this]
    also have "\<dots> \<le> ln (1 / 3 + 1)"
      unfolding ln_le_cancel_iff[OF lthird_gt0 third_gt0]
      using lb3 by auto
    finally show "float_round_down prec (?lthird * lb_ln_horner prec (get_even prec) 1 ?lthird) \<le>
      ln (1 / 3 + 1)" .
  qed
qed


subsection "Compute the logarithm in the entire domain"

function ub_ln :: "nat \<Rightarrow> float \<Rightarrow> float option" and lb_ln :: "nat \<Rightarrow> float \<Rightarrow> float option" where
"ub_ln prec x = (if x \<le> 0          then None
            else if x < 1          then Some (- the (lb_ln prec (float_divl (max prec 1) 1 x)))
            else let horner = \<lambda>x. float_round_up prec (x * ub_ln_horner prec (get_odd prec) 1 x) in
                 if x \<le> Float 3 (- 1) then Some (horner (x - 1))
            else if x < Float 1 1  then Some (float_round_up prec (horner (Float 1 (- 1)) + horner (x * rapprox_rat prec 2 3 - 1)))
                                   else let l = bitlen (mantissa x) - 1 in
                                        Some (float_plus_up prec (float_round_up prec (ub_ln2 prec * (Float (exponent x + l) 0))) (horner (Float (mantissa x) (- l) - 1))))" |
"lb_ln prec x = (if x \<le> 0          then None
            else if x < 1          then Some (- the (ub_ln prec (float_divr prec 1 x)))
            else let horner = \<lambda>x. float_round_down prec (x * lb_ln_horner prec (get_even prec) 1 x) in
                 if x \<le> Float 3 (- 1) then Some (horner (x - 1))
            else if x < Float 1 1  then Some (float_round_down prec (horner (Float 1 (- 1)) +
                                              horner (max (x * lapprox_rat prec 2 3 - 1) 0)))
                                   else let l = bitlen (mantissa x) - 1 in
                                        Some (float_plus_down prec (float_round_down prec (lb_ln2 prec * (Float (exponent x + l) 0))) (horner (Float (mantissa x) (- l) - 1))))"
  by pat_completeness auto

termination
proof (relation "measure (\<lambda> v. let (prec, x) = case_sum id id v in (if x < 1 then 1 else 0))", auto)
  fix prec and x :: float
  assume "\<not> real_of_float x \<le> 0" and "real_of_float x < 1" and "real_of_float (float_divl (max prec (Suc 0)) 1 x) < 1"
  hence "0 < real_of_float x" "1 \<le> max prec (Suc 0)" "real_of_float x < 1"
    by auto
  from float_divl_pos_less1_bound[OF \<open>0 < real_of_float x\<close> \<open>real_of_float x < 1\<close>[THEN less_imp_le] \<open>1 \<le> max prec (Suc 0)\<close>]
  show False
    using \<open>real_of_float (float_divl (max prec (Suc 0)) 1 x) < 1\<close> by auto
next
  fix prec x
  assume "\<not> real_of_float x \<le> 0" and "real_of_float x < 1" and "real_of_float (float_divr prec 1 x) < 1"
  hence "0 < x" by auto
  from float_divr_pos_less1_lower_bound[OF \<open>0 < x\<close>, of prec] \<open>real_of_float x < 1\<close> show False
    using \<open>real_of_float (float_divr prec 1 x) < 1\<close> by auto
qed

lemma float_pos_eq_mantissa_pos: "x > 0 \<longleftrightarrow> mantissa x > 0"
  apply (subst Float_mantissa_exponent[of x, symmetric])
  apply (auto simp add: zero_less_mult_iff zero_float_def  dest: less_zeroE)
  apply (metis not_le powr_ge_pzero)
  done

lemma Float_pos_eq_mantissa_pos: "Float m e > 0 \<longleftrightarrow> m > 0"
  using powr_gt_zero[of 2 "e"]
  by (auto simp add: zero_less_mult_iff zero_float_def simp del: powr_gt_zero dest: less_zeroE)

lemma Float_representation_aux:
  fixes m e
  defines "x \<equiv> Float m e"
  assumes "x > 0"
  shows "Float (exponent x + (bitlen (mantissa x) - 1)) 0 = Float (e + (bitlen m - 1)) 0" (is ?th1)
    and "Float (mantissa x) (- (bitlen (mantissa x) - 1)) = Float m ( - (bitlen m - 1))"  (is ?th2)
proof -
  from assms have mantissa_pos: "m > 0" "mantissa x > 0"
    using Float_pos_eq_mantissa_pos[of m e] float_pos_eq_mantissa_pos[of x] by simp_all
  thus ?th1
    using bitlen_Float[of m e] assms
    by (auto simp add: zero_less_mult_iff intro!: arg_cong2[where f=Float])
  have "x \<noteq> float_of 0"
    unfolding zero_float_def[symmetric] using \<open>0 < x\<close> by auto
  from denormalize_shift[OF assms(1) this] guess i . note i = this

  have "2 powr (1 - (real_of_int (bitlen (mantissa x)) + real_of_int i)) =
    2 powr (1 - (real_of_int (bitlen (mantissa x)))) * inverse (2 powr (real i))"
    by (simp add: powr_minus[symmetric] powr_add[symmetric] field_simps)
  hence "real_of_int (mantissa x) * 2 powr (1 - real_of_int (bitlen (mantissa x))) =
    (real_of_int (mantissa x) * 2 ^ i) * 2 powr (1 - real_of_int (bitlen (mantissa x * 2 ^ i)))"
    using \<open>mantissa x > 0\<close> by (simp add: powr_realpow)
  then show ?th2
    unfolding i by transfer auto
qed

lemma compute_ln[code]:
  fixes m e
  defines "x \<equiv> Float m e"
  shows "ub_ln prec x = (if x \<le> 0          then None
              else if x < 1          then Some (- the (lb_ln prec (float_divl (max prec 1) 1 x)))
            else let horner = \<lambda>x. float_round_up prec (x * ub_ln_horner prec (get_odd prec) 1 x) in
                 if x \<le> Float 3 (- 1) then Some (horner (x - 1))
            else if x < Float 1 1  then Some (float_round_up prec (horner (Float 1 (- 1)) + horner (x * rapprox_rat prec 2 3 - 1)))
                                   else let l = bitlen m - 1 in
                                        Some (float_plus_up prec (float_round_up prec (ub_ln2 prec * (Float (e + l) 0))) (horner (Float m (- l) - 1))))"
    (is ?th1)
  and "lb_ln prec x = (if x \<le> 0          then None
            else if x < 1          then Some (- the (ub_ln prec (float_divr prec 1 x)))
            else let horner = \<lambda>x. float_round_down prec (x * lb_ln_horner prec (get_even prec) 1 x) in
                 if x \<le> Float 3 (- 1) then Some (horner (x - 1))
            else if x < Float 1 1  then Some (float_round_down prec (horner (Float 1 (- 1)) +
                                              horner (max (x * lapprox_rat prec 2 3 - 1) 0)))
                                   else let l = bitlen m - 1 in
                                        Some (float_plus_down prec (float_round_down prec (lb_ln2 prec * (Float (e + l) 0))) (horner (Float m (- l) - 1))))"
    (is ?th2)
proof -
  from assms Float_pos_eq_mantissa_pos have "x > 0 \<Longrightarrow> m > 0"
    by simp
  thus ?th1 ?th2
    using Float_representation_aux[of m e]
    unfolding x_def[symmetric]
    by (auto dest: not_le_imp_less)
qed

lemma ln_shifted_float:
  assumes "0 < m"
  shows "ln (Float m e) = ln 2 * (e + (bitlen m - 1)) + ln (Float m (- (bitlen m - 1)))"
proof -
  let ?B = "2^nat (bitlen m - 1)"
  define bl where "bl = bitlen m - 1"
  have "0 < real_of_int m" and "\<And>X. (0 :: real) < 2^X" and "0 < (2 :: real)" and "m \<noteq> 0"
    using assms by auto
  hence "0 \<le> bl" by (simp add: bitlen_alt_def bl_def)
  show ?thesis
  proof (cases "0 \<le> e")
    case True
    thus ?thesis
      unfolding bl_def[symmetric] using \<open>0 < real_of_int m\<close> \<open>0 \<le> bl\<close>
      apply (simp add: ln_mult)
      apply (cases "e=0")
        apply (cases "bl = 0", simp_all add: powr_minus ln_inverse ln_powr)
        apply (cases "bl = 0", simp_all add: powr_minus ln_inverse ln_powr field_simps)
      done
  next
    case False
    hence "0 < -e" by auto
    have lne: "ln (2 powr real_of_int e) = ln (inverse (2 powr - e))"
      by (simp add: powr_minus)
    hence pow_gt0: "(0::real) < 2^nat (-e)"
      by auto
    hence inv_gt0: "(0::real) < inverse (2^nat (-e))"
      by auto
    show ?thesis
      using False unfolding bl_def[symmetric]
      using \<open>0 < real_of_int m\<close> \<open>0 \<le> bl\<close>
      by (auto simp add: lne ln_mult ln_powr ln_div field_simps)
  qed
qed

lemma ub_ln_lb_ln_bounds':
  assumes "1 \<le> x"
  shows "the (lb_ln prec x) \<le> ln x \<and> ln x \<le> the (ub_ln prec x)"
    (is "?lb \<le> ?ln \<and> ?ln \<le> ?ub")
proof (cases "x < Float 1 1")
  case True
  hence "real_of_float (x - 1) < 1" and "real_of_float x < 2" by auto
  have "\<not> x \<le> 0" and "\<not> x < 1" using \<open>1 \<le> x\<close> by auto
  hence "0 \<le> real_of_float (x - 1)" using \<open>1 \<le> x\<close> by auto

  have [simp]: "(Float 3 (- 1)) = 3 / 2" by simp

  show ?thesis
  proof (cases "x \<le> Float 3 (- 1)")
    case True
    show ?thesis
      unfolding lb_ln.simps
      unfolding ub_ln.simps Let_def
      using ln_float_bounds[OF \<open>0 \<le> real_of_float (x - 1)\<close> \<open>real_of_float (x - 1) < 1\<close>, of prec]
        \<open>\<not> x \<le> 0\<close> \<open>\<not> x < 1\<close> True
      by (auto intro!: float_round_down_le float_round_up_le)
  next
    case False
    hence *: "3 / 2 < x" by auto

    with ln_add[of "3 / 2" "x - 3 / 2"]
    have add: "ln x = ln (3 / 2) + ln (real_of_float x * 2 / 3)"
      by (auto simp add: algebra_simps diff_divide_distrib)

    let "?ub_horner x" = "float_round_up prec (x * ub_ln_horner prec (get_odd prec) 1 x)"
    let "?lb_horner x" = "float_round_down prec (x * lb_ln_horner prec (get_even prec) 1 x)"

    { have up: "real_of_float (rapprox_rat prec 2 3) \<le> 1"
        by (rule rapprox_rat_le1) simp_all
      have low: "2 / 3 \<le> rapprox_rat prec 2 3"
        by (rule order_trans[OF _ rapprox_rat]) simp
      from mult_less_le_imp_less[OF * low] *
      have pos: "0 < real_of_float (x * rapprox_rat prec 2 3 - 1)" by auto

      have "ln (real_of_float x * 2/3)
        \<le> ln (real_of_float (x * rapprox_rat prec 2 3 - 1) + 1)"
      proof (rule ln_le_cancel_iff[symmetric, THEN iffD1])
        show "real_of_float x * 2 / 3 \<le> real_of_float (x * rapprox_rat prec 2 3 - 1) + 1"
          using * low by auto
        show "0 < real_of_float x * 2 / 3" using * by simp
        show "0 < real_of_float (x * rapprox_rat prec 2 3 - 1) + 1" using pos by auto
      qed
      also have "\<dots> \<le> ?ub_horner (x * rapprox_rat prec 2 3 - 1)"
      proof (rule float_round_up_le, rule ln_float_bounds(2))
        from mult_less_le_imp_less[OF \<open>real_of_float x < 2\<close> up] low *
        show "real_of_float (x * rapprox_rat prec 2 3 - 1) < 1" by auto
        show "0 \<le> real_of_float (x * rapprox_rat prec 2 3 - 1)" using pos by auto
      qed
     finally have "ln x \<le> ?ub_horner (Float 1 (-1))
          + ?ub_horner ((x * rapprox_rat prec 2 3 - 1))"
        using ln_float_bounds(2)[of "Float 1 (- 1)" prec prec] add
        by (auto intro!: add_mono float_round_up_le)
      note float_round_up_le[OF this, of prec]
    }
    moreover
    { let ?max = "max (x * lapprox_rat prec 2 3 - 1) 0"

      have up: "lapprox_rat prec 2 3 \<le> 2/3"
        by (rule order_trans[OF lapprox_rat], simp)

      have low: "0 \<le> real_of_float (lapprox_rat prec 2 3)"
        using lapprox_rat_nonneg[of 2 3 prec] by simp

      have "?lb_horner ?max
        \<le> ln (real_of_float ?max + 1)"
      proof (rule float_round_down_le, rule ln_float_bounds(1))
        from mult_less_le_imp_less[OF \<open>real_of_float x < 2\<close> up] * low
        show "real_of_float ?max < 1" by (cases "real_of_float (lapprox_rat prec 2 3) = 0",
          auto simp add: real_of_float_max)
        show "0 \<le> real_of_float ?max" by (auto simp add: real_of_float_max)
      qed
      also have "\<dots> \<le> ln (real_of_float x * 2/3)"
      proof (rule ln_le_cancel_iff[symmetric, THEN iffD1])
        show "0 < real_of_float ?max + 1" by (auto simp add: real_of_float_max)
        show "0 < real_of_float x * 2/3" using * by auto
        show "real_of_float ?max + 1 \<le> real_of_float x * 2/3" using * up
          by (cases "0 < real_of_float x * real_of_float (lapprox_posrat prec 2 3) - 1",
              auto simp add: max_def)
      qed
      finally have "?lb_horner (Float 1 (- 1)) + ?lb_horner ?max \<le> ln x"
        using ln_float_bounds(1)[of "Float 1 (- 1)" prec prec] add
        by (auto intro!: add_mono float_round_down_le)
      note float_round_down_le[OF this, of prec]
    }
    ultimately
    show ?thesis unfolding lb_ln.simps unfolding ub_ln.simps Let_def
      using \<open>\<not> x \<le> 0\<close> \<open>\<not> x < 1\<close> True False by auto
  qed
next
  case False
  hence "\<not> x \<le> 0" and "\<not> x < 1" "0 < x" "\<not> x \<le> Float 3 (- 1)"
    using \<open>1 \<le> x\<close> by auto
  show ?thesis
  proof -
    define m where "m = mantissa x"
    define e where "e = exponent x"
    from Float_mantissa_exponent[of x] have Float: "x = Float m e"
      by (simp add: m_def e_def)
    let ?s = "Float (e + (bitlen m - 1)) 0"
    let ?x = "Float m (- (bitlen m - 1))"

    have "0 < m" and "m \<noteq> 0" using \<open>0 < x\<close> Float powr_gt_zero[of 2 e]
      apply (auto simp add: zero_less_mult_iff)
      using not_le powr_ge_pzero apply blast
      done
    define bl where "bl = bitlen m - 1"
    hence "bl \<ge> 0"
      using \<open>m > 0\<close> by (simp add: bitlen_alt_def)
    have "1 \<le> Float m e"
      using \<open>1 \<le> x\<close> Float unfolding less_eq_float_def by auto
    from bitlen_div[OF \<open>0 < m\<close>] float_gt1_scale[OF \<open>1 \<le> Float m e\<close>] \<open>bl \<ge> 0\<close>
    have x_bnds: "0 \<le> real_of_float (?x - 1)" "real_of_float (?x - 1) < 1"
      unfolding bl_def[symmetric]
      by (auto simp: powr_realpow[symmetric] field_simps)
         (auto simp : powr_minus field_simps)

    {
      have "float_round_down prec (lb_ln2 prec * ?s) \<le> ln 2 * (e + (bitlen m - 1))"
          (is "real_of_float ?lb2 \<le> _")
        apply (rule float_round_down_le)
        unfolding nat_0 power_0 mult_1_right times_float.rep_eq
        using lb_ln2[of prec]
      proof (rule mult_mono)
        from float_gt1_scale[OF \<open>1 \<le> Float m e\<close>]
        show "0 \<le> real_of_float (Float (e + (bitlen m - 1)) 0)" by simp
      qed auto
      moreover
      from ln_float_bounds(1)[OF x_bnds]
      have "float_round_down prec ((?x - 1) * lb_ln_horner prec (get_even prec) 1 (?x - 1)) \<le> ln ?x" (is "real_of_float ?lb_horner \<le> _")
        by (auto intro!: float_round_down_le)
      ultimately have "float_plus_down prec ?lb2 ?lb_horner \<le> ln x"
        unfolding Float ln_shifted_float[OF \<open>0 < m\<close>, of e] by (auto intro!: float_plus_down_le)
    }
    moreover
    {
      from ln_float_bounds(2)[OF x_bnds]
      have "ln ?x \<le> float_round_up prec ((?x - 1) * ub_ln_horner prec (get_odd prec) 1 (?x - 1))"
          (is "_ \<le> real_of_float ?ub_horner")
        by (auto intro!: float_round_up_le)
      moreover
      have "ln 2 * (e + (bitlen m - 1)) \<le> float_round_up prec (ub_ln2 prec * ?s)"
          (is "_ \<le> real_of_float ?ub2")
        apply (rule float_round_up_le)
        unfolding nat_0 power_0 mult_1_right times_float.rep_eq
        using ub_ln2[of prec]
      proof (rule mult_mono)
        from float_gt1_scale[OF \<open>1 \<le> Float m e\<close>]
        show "0 \<le> real_of_int (e + (bitlen m - 1))" by auto
        have "0 \<le> ln (2 :: real)" by simp
        thus "0 \<le> real_of_float (ub_ln2 prec)" using ub_ln2[of prec] by arith
      qed auto
      ultimately have "ln x \<le> float_plus_up prec ?ub2 ?ub_horner"
        unfolding Float ln_shifted_float[OF \<open>0 < m\<close>, of e]
        by (auto intro!: float_plus_up_le)
    }
    ultimately show ?thesis
      unfolding lb_ln.simps
      unfolding ub_ln.simps
      unfolding if_not_P[OF \<open>\<not> x \<le> 0\<close>] if_not_P[OF \<open>\<not> x < 1\<close>]
        if_not_P[OF False] if_not_P[OF \<open>\<not> x \<le> Float 3 (- 1)\<close>] Let_def
      unfolding plus_float.rep_eq e_def[symmetric] m_def[symmetric]
      by simp
  qed
qed

lemma ub_ln_lb_ln_bounds:
  assumes "0 < x"
  shows "the (lb_ln prec x) \<le> ln x \<and> ln x \<le> the (ub_ln prec x)"
    (is "?lb \<le> ?ln \<and> ?ln \<le> ?ub")
proof (cases "x < 1")
  case False
  hence "1 \<le> x"
    unfolding less_float_def less_eq_float_def by auto
  show ?thesis
    using ub_ln_lb_ln_bounds'[OF \<open>1 \<le> x\<close>] .
next
  case True
  have "\<not> x \<le> 0" using \<open>0 < x\<close> by auto
  from True have "real_of_float x \<le> 1" "x \<le> 1"
    by simp_all
  have "0 < real_of_float x" and "real_of_float x \<noteq> 0"
    using \<open>0 < x\<close> by auto
  hence A: "0 < 1 / real_of_float x" by auto

  {
    let ?divl = "float_divl (max prec 1) 1 x"
    have A': "1 \<le> ?divl" using float_divl_pos_less1_bound[OF \<open>0 < real_of_float x\<close> \<open>real_of_float x \<le> 1\<close>] by auto
    hence B: "0 < real_of_float ?divl" by auto

    have "ln ?divl \<le> ln (1 / x)" unfolding ln_le_cancel_iff[OF B A] using float_divl[of _ 1 x] by auto
    hence "ln x \<le> - ln ?divl" unfolding nonzero_inverse_eq_divide[OF \<open>real_of_float x \<noteq> 0\<close>, symmetric] ln_inverse[OF \<open>0 < real_of_float x\<close>] by auto
    from this ub_ln_lb_ln_bounds'[OF A', THEN conjunct1, THEN le_imp_neg_le]
    have "?ln \<le> - the (lb_ln prec ?divl)" unfolding uminus_float.rep_eq by (rule order_trans)
  } moreover
  {
    let ?divr = "float_divr prec 1 x"
    have A': "1 \<le> ?divr" using float_divr_pos_less1_lower_bound[OF \<open>0 < x\<close> \<open>x \<le> 1\<close>] unfolding less_eq_float_def less_float_def by auto
    hence B: "0 < real_of_float ?divr" by auto

    have "ln (1 / x) \<le> ln ?divr" unfolding ln_le_cancel_iff[OF A B] using float_divr[of 1 x] by auto
    hence "- ln ?divr \<le> ln x" unfolding nonzero_inverse_eq_divide[OF \<open>real_of_float x \<noteq> 0\<close>, symmetric] ln_inverse[OF \<open>0 < real_of_float x\<close>] by auto
    from ub_ln_lb_ln_bounds'[OF A', THEN conjunct2, THEN le_imp_neg_le] this
    have "- the (ub_ln prec ?divr) \<le> ?ln" unfolding uminus_float.rep_eq by (rule order_trans)
  }
  ultimately show ?thesis unfolding lb_ln.simps[where x=x]  ub_ln.simps[where x=x]
    unfolding if_not_P[OF \<open>\<not> x \<le> 0\<close>] if_P[OF True] by auto
qed

lemma lb_ln:
  assumes "Some y = lb_ln prec x"
  shows "y \<le> ln x" and "0 < real_of_float x"
proof -
  have "0 < x"
  proof (rule ccontr)
    assume "\<not> 0 < x"
    hence "x \<le> 0"
      unfolding less_eq_float_def less_float_def by auto
    thus False
      using assms by auto
  qed
  thus "0 < real_of_float x" by auto
  have "the (lb_ln prec x) \<le> ln x"
    using ub_ln_lb_ln_bounds[OF \<open>0 < x\<close>] ..
  thus "y \<le> ln x"
    unfolding assms[symmetric] by auto
qed

lemma ub_ln:
  assumes "Some y = ub_ln prec x"
  shows "ln x \<le> y" and "0 < real_of_float x"
proof -
  have "0 < x"
  proof (rule ccontr)
    assume "\<not> 0 < x"
    hence "x \<le> 0" by auto
    thus False
      using assms by auto
  qed
  thus "0 < real_of_float x" by auto
  have "ln x \<le> the (ub_ln prec x)"
    using ub_ln_lb_ln_bounds[OF \<open>0 < x\<close>] ..
  thus "ln x \<le> y"
    unfolding assms[symmetric] by auto
qed

lemma bnds_ln: "\<forall>(x::real) lx ux. (Some l, Some u) =
  (lb_ln prec lx, ub_ln prec ux) \<and> x \<in> {lx .. ux} \<longrightarrow> l \<le> ln x \<and> ln x \<le> u"
proof (rule allI, rule allI, rule allI, rule impI)
  fix x :: real
  fix lx ux
  assume "(Some l, Some u) = (lb_ln prec lx, ub_ln prec ux) \<and> x \<in> {lx .. ux}"
  hence l: "Some l = lb_ln prec lx " and u: "Some u = ub_ln prec ux" and x: "x \<in> {lx .. ux}"
    by auto

  have "ln ux \<le> u" and "0 < real_of_float ux"
    using ub_ln u by auto
  have "l \<le> ln lx" and "0 < real_of_float lx" and "0 < x"
    using lb_ln[OF l] x by auto

  from ln_le_cancel_iff[OF \<open>0 < real_of_float lx\<close> \<open>0 < x\<close>] \<open>l \<le> ln lx\<close>
  have "l \<le> ln x"
    using x unfolding atLeastAtMost_iff by auto
  moreover
  from ln_le_cancel_iff[OF \<open>0 < x\<close> \<open>0 < real_of_float ux\<close>] \<open>ln ux \<le> real_of_float u\<close>
  have "ln x \<le> u"
    using x unfolding atLeastAtMost_iff by auto
  ultimately show "l \<le> ln x \<and> ln x \<le> u" ..
qed


section \<open>Real power function\<close>

definition bnds_powr :: "nat \<Rightarrow> float \<Rightarrow> float \<Rightarrow> float \<Rightarrow> float \<Rightarrow> (float \<times> float) option" where
  "bnds_powr prec l1 u1 l2 u2 = (
     if l1 = 0 \<and> u1 = 0 then
       Some (0, 0)
     else if l1 = 0 \<and> l2 \<ge> 1 then
       let uln = the (ub_ln prec u1)
       in  Some (0, ub_exp prec (float_round_up prec (uln * (if uln \<ge> 0 then u2 else l2))))
     else if l1 \<le> 0 then
       None
     else
       Some (map_bnds lb_exp ub_exp prec 
               (bnds_mult prec (the (lb_ln prec l1)) (the (ub_ln prec u1)) l2 u2)))"

lemmas [simp del] = lb_exp.simps ub_exp.simps

lemma mono_exp_real: "mono (exp :: real \<Rightarrow> real)"
  by (auto simp: mono_def)

lemma ub_exp_nonneg: "real_of_float (ub_exp prec x) \<ge> 0"
proof -
  have "0 \<le> exp (real_of_float x)" by simp
  also from exp_boundaries[of x prec] 
    have "\<dots> \<le> real_of_float (ub_exp prec x)" by simp
  finally show ?thesis .
qed

lemma bnds_powr:
  assumes lu: "Some (l, u) = bnds_powr prec l1 u1 l2 u2"
  assumes x: "x \<in> {real_of_float l1..real_of_float u1}"
  assumes y: "y \<in> {real_of_float l2..real_of_float u2}"
  shows   "x powr y \<in> {real_of_float l..real_of_float u}"
proof -
  consider "l1 = 0" "u1 = 0" | "l1 = 0" "u1 \<noteq> 0" "l2 \<ge> 1" | 
           "l1 \<le> 0" "\<not>(l1 = 0 \<and> (u1 = 0 \<or> l2 \<ge> 1))" | "l1 > 0" by force
  thus ?thesis
  proof cases
    assume "l1 = 0" "u1 = 0"
    with x lu show ?thesis by (auto simp: bnds_powr_def)
  next
    assume A: "l1 = 0" "u1 \<noteq> 0" "l2 \<ge> 1"
    define uln where "uln = the (ub_ln prec u1)"
    show ?thesis
    proof (cases "x = 0")
      case False
      with A x y have "x powr y = exp (ln x * y)" by (simp add: powr_def)
      also {
        from A x False have "ln x \<le> ln (real_of_float u1)" by simp
        also from ub_ln_lb_ln_bounds[of u1 prec] A y x False
          have "ln (real_of_float u1) \<le> real_of_float uln" by (simp add: uln_def del: lb_ln.simps)
        also from A x y have "\<dots> * y \<le> real_of_float uln * (if uln \<ge> 0 then u2 else l2)"
          by (auto intro: mult_left_mono mult_left_mono_neg)
        also have "\<dots> \<le> real_of_float (float_round_up prec (uln * (if uln \<ge> 0 then u2 else l2)))"
          by (simp add: float_round_up_le)
        finally have "ln x * y \<le> \<dots>" using A y by - simp
      }
      also have "exp (real_of_float (float_round_up prec (uln * (if uln \<ge> 0 then u2 else l2)))) \<le>
                   real_of_float (ub_exp prec (float_round_up prec
                       (uln * (if uln \<ge> 0 then u2 else l2))))"
        using exp_boundaries by simp
      finally show ?thesis using A x y lu 
        by (simp add: bnds_powr_def uln_def Let_def del: lb_ln.simps ub_ln.simps)
    qed (insert x y lu A, simp_all add: bnds_powr_def Let_def ub_exp_nonneg
                                   del: lb_ln.simps ub_ln.simps)
  next
    assume "l1 \<le> 0" "\<not>(l1 = 0 \<and> (u1 = 0 \<or> l2 \<ge> 1))"
    with lu show ?thesis by (simp add: bnds_powr_def split: if_split_asm)
  next
    assume l1: "l1 > 0"
    obtain lm um where lmum:
      "(lm, um) = bnds_mult prec (the (lb_ln prec l1)) (the (ub_ln prec u1)) l2 u2"
      by (cases "bnds_mult prec (the (lb_ln prec l1)) (the (ub_ln prec u1)) l2 u2") simp
    with l1 have "(l, u) = map_bnds lb_exp ub_exp prec (lm, um)"
      using lu by (simp add: bnds_powr_def del: lb_ln.simps ub_ln.simps split: if_split_asm)
    hence "exp (ln x * y) \<in> {real_of_float l..real_of_float u}"
    proof (rule map_bnds[OF _ mono_exp_real], goal_cases)
      case 1
      let ?lln = "the (lb_ln prec l1)" and ?uln = "the (ub_ln prec u1)"
      from ub_ln_lb_ln_bounds[of l1 prec] ub_ln_lb_ln_bounds[of u1 prec] x l1
        have "real_of_float ?lln \<le> ln (real_of_float l1) \<and> 
              ln (real_of_float u1) \<le> real_of_float ?uln"
        by (auto simp del: lb_ln.simps ub_ln.simps)
      moreover from l1 x have "ln (real_of_float l1) \<le> ln x \<and> ln x \<le> ln (real_of_float u1)"
        by auto
      ultimately have ln: "real_of_float ?lln \<le> ln x \<and> ln x \<le> real_of_float ?uln" by simp
      from lmum show ?case
        by (rule bnds_mult) (insert y ln, simp_all)
    qed (insert exp_boundaries[of lm prec] exp_boundaries[of um prec], simp_all)
    with x l1 show ?thesis
      by (simp add: powr_def mult_ac)
  qed
qed


section "Implement floatarith"

subsection "Define syntax and semantics"

datatype floatarith
  = Add floatarith floatarith
  | Minus floatarith
  | Mult floatarith floatarith
  | Inverse floatarith
  | Cos floatarith
  | Arctan floatarith
  | Abs floatarith
  | Max floatarith floatarith
  | Min floatarith floatarith
  | Pi
  | Sqrt floatarith
  | Exp floatarith
  | Powr floatarith floatarith
  | Ln floatarith
  | Power floatarith nat
  | Floor floatarith
  | Var nat
  | Num float

fun interpret_floatarith :: "floatarith \<Rightarrow> real list \<Rightarrow> real" where
"interpret_floatarith (Add a b) vs   = (interpret_floatarith a vs) + (interpret_floatarith b vs)" |
"interpret_floatarith (Minus a) vs    = - (interpret_floatarith a vs)" |
"interpret_floatarith (Mult a b) vs   = (interpret_floatarith a vs) * (interpret_floatarith b vs)" |
"interpret_floatarith (Inverse a) vs  = inverse (interpret_floatarith a vs)" |
"interpret_floatarith (Cos a) vs      = cos (interpret_floatarith a vs)" |
"interpret_floatarith (Arctan a) vs   = arctan (interpret_floatarith a vs)" |
"interpret_floatarith (Min a b) vs    = min (interpret_floatarith a vs) (interpret_floatarith b vs)" |
"interpret_floatarith (Max a b) vs    = max (interpret_floatarith a vs) (interpret_floatarith b vs)" |
"interpret_floatarith (Abs a) vs      = \<bar>interpret_floatarith a vs\<bar>" |
"interpret_floatarith Pi vs           = pi" |
"interpret_floatarith (Sqrt a) vs     = sqrt (interpret_floatarith a vs)" |
"interpret_floatarith (Exp a) vs      = exp (interpret_floatarith a vs)" |
"interpret_floatarith (Powr a b) vs   = interpret_floatarith a vs powr interpret_floatarith b vs" |
"interpret_floatarith (Ln a) vs       = ln (interpret_floatarith a vs)" |
"interpret_floatarith (Power a n) vs  = (interpret_floatarith a vs)^n" |
"interpret_floatarith (Floor a) vs      = floor (interpret_floatarith a vs)" |
"interpret_floatarith (Num f) vs      = f" |
"interpret_floatarith (Var n) vs     = vs ! n"

lemma interpret_floatarith_divide:
  "interpret_floatarith (Mult a (Inverse b)) vs =
    (interpret_floatarith a vs) / (interpret_floatarith b vs)"
  unfolding divide_inverse interpret_floatarith.simps ..

lemma interpret_floatarith_diff:
  "interpret_floatarith (Add a (Minus b)) vs =
    (interpret_floatarith a vs) - (interpret_floatarith b vs)"
  unfolding interpret_floatarith.simps by simp

lemma interpret_floatarith_sin:
  "interpret_floatarith (Cos (Add (Mult Pi (Num (Float 1 (- 1)))) (Minus a))) vs =
    sin (interpret_floatarith a vs)"
  unfolding sin_cos_eq interpret_floatarith.simps
    interpret_floatarith_divide interpret_floatarith_diff
  by auto


subsection "Implement approximation function"

fun lift_bin :: "(float * float) option \<Rightarrow> (float * float) option \<Rightarrow> (float \<Rightarrow> float \<Rightarrow> float \<Rightarrow> float \<Rightarrow> (float * float) option) \<Rightarrow> (float * float) option" where
"lift_bin (Some (l1, u1)) (Some (l2, u2)) f = f l1 u1 l2 u2" |
"lift_bin a b f = None"

fun lift_bin' :: "(float * float) option \<Rightarrow> (float * float) option \<Rightarrow> (float \<Rightarrow> float \<Rightarrow> float \<Rightarrow> float \<Rightarrow> (float * float)) \<Rightarrow> (float * float) option" where
"lift_bin' (Some (l1, u1)) (Some (l2, u2)) f = Some (f l1 u1 l2 u2)" |
"lift_bin' a b f = None"

fun lift_un :: "(float * float) option \<Rightarrow> (float \<Rightarrow> float \<Rightarrow> ((float option) * (float option))) \<Rightarrow> (float * float) option" where
"lift_un (Some (l1, u1)) f = (case (f l1 u1) of (Some l, Some u) \<Rightarrow> Some (l, u)
                                             | t \<Rightarrow> None)" |
"lift_un b f = None"

fun lift_un' :: "(float * float) option \<Rightarrow> (float \<Rightarrow> float \<Rightarrow> (float * float)) \<Rightarrow> (float * float) option" where
"lift_un' (Some (l1, u1)) f = Some (f l1 u1)" |
"lift_un' b f = None"

definition bounded_by :: "real list \<Rightarrow> (float \<times> float) option list \<Rightarrow> bool" where 
  "bounded_by xs vs \<longleftrightarrow>
  (\<forall> i < length vs. case vs ! i of None \<Rightarrow> True
         | Some (l, u) \<Rightarrow> xs ! i \<in> { real_of_float l .. real_of_float u })"
                                                                     
lemma bounded_byE:
  assumes "bounded_by xs vs"
  shows "\<And> i. i < length vs \<Longrightarrow> case vs ! i of None \<Rightarrow> True
         | Some (l, u) \<Rightarrow> xs ! i \<in> { real_of_float l .. real_of_float u }"
  using assms bounded_by_def by blast

lemma bounded_by_update:
  assumes "bounded_by xs vs"
    and bnd: "xs ! i \<in> { real_of_float l .. real_of_float u }"
  shows "bounded_by xs (vs[i := Some (l,u)])"
proof -
  {
    fix j
    let ?vs = "vs[i := Some (l,u)]"
    assume "j < length ?vs"
    hence [simp]: "j < length vs" by simp
    have "case ?vs ! j of None \<Rightarrow> True | Some (l, u) \<Rightarrow> xs ! j \<in> { real_of_float l .. real_of_float u }"
    proof (cases "?vs ! j")
      case (Some b)
      thus ?thesis
      proof (cases "i = j")
        case True
        thus ?thesis using \<open>?vs ! j = Some b\<close> and bnd by auto
      next
        case False
        thus ?thesis using \<open>bounded_by xs vs\<close> unfolding bounded_by_def by auto
      qed
    qed auto
  }
  thus ?thesis unfolding bounded_by_def by auto
qed

lemma bounded_by_None: "bounded_by xs (replicate (length xs) None)"
  unfolding bounded_by_def by auto

fun approx approx' :: "nat \<Rightarrow> floatarith \<Rightarrow> (float * float) option list \<Rightarrow> (float * float) option" where
"approx' prec a bs          = (case (approx prec a bs) of Some (l, u) \<Rightarrow> Some (float_round_down prec l, float_round_up prec u) | None \<Rightarrow> None)" |
"approx prec (Add a b) bs   =
  lift_bin' (approx' prec a bs) (approx' prec b bs)
    (\<lambda> l1 u1 l2 u2. (float_plus_down prec l1 l2, float_plus_up prec u1 u2))" |
"approx prec (Minus a) bs   = lift_un' (approx' prec a bs) (\<lambda> l u. (-u, -l))" |
"approx prec (Mult a b) bs  =
  lift_bin' (approx' prec a bs) (approx' prec b bs) (bnds_mult prec)" |
"approx prec (Inverse a) bs = lift_un (approx' prec a bs) (\<lambda> l u. if (0 < l \<or> u < 0) then (Some (float_divl prec 1 u), Some (float_divr prec 1 l)) else (None, None))" |
"approx prec (Cos a) bs     = lift_un' (approx' prec a bs) (bnds_cos prec)" |
"approx prec Pi bs          = Some (lb_pi prec, ub_pi prec)" |
"approx prec (Min a b) bs   = lift_bin' (approx' prec a bs) (approx' prec b bs) (\<lambda> l1 u1 l2 u2. (min l1 l2, min u1 u2))" |
"approx prec (Max a b) bs   = lift_bin' (approx' prec a bs) (approx' prec b bs) (\<lambda> l1 u1 l2 u2. (max l1 l2, max u1 u2))" |
"approx prec (Abs a) bs     = lift_un' (approx' prec a bs) (\<lambda>l u. (if l < 0 \<and> 0 < u then 0 else min \<bar>l\<bar> \<bar>u\<bar>, max \<bar>l\<bar> \<bar>u\<bar>))" |
"approx prec (Arctan a) bs  = lift_un' (approx' prec a bs) (\<lambda> l u. (lb_arctan prec l, ub_arctan prec u))" |
"approx prec (Sqrt a) bs    = lift_un' (approx' prec a bs) (\<lambda> l u. (lb_sqrt prec l, ub_sqrt prec u))" |
"approx prec (Exp a) bs     = lift_un' (approx' prec a bs) (\<lambda> l u. (lb_exp prec l, ub_exp prec u))" |
"approx prec (Powr a b) bs  = lift_bin (approx' prec a bs) (approx' prec b bs) (bnds_powr prec)" |
"approx prec (Ln a) bs      = lift_un (approx' prec a bs) (\<lambda> l u. (lb_ln prec l, ub_ln prec u))" |
"approx prec (Power a n) bs = lift_un' (approx' prec a bs) (float_power_bnds prec n)" |
"approx prec (Floor a) bs = lift_un' (approx' prec a bs) (\<lambda> l u. (floor_fl l, floor_fl u))" |
"approx prec (Num f) bs     = Some (f, f)" |
"approx prec (Var i) bs    = (if i < length bs then bs ! i else None)"

lemma approx_approx':
  assumes Pa: "\<And>l u. Some (l, u) = approx prec a vs \<Longrightarrow>
      l \<le> interpret_floatarith a xs \<and> interpret_floatarith a xs \<le> u"
    and approx': "Some (l, u) = approx' prec a vs"
  shows "l \<le> interpret_floatarith a xs \<and> interpret_floatarith a xs \<le> u"
proof -
  obtain l' u' where S: "Some (l', u') = approx prec a vs"
    using approx' unfolding approx'.simps by (cases "approx prec a vs") auto
  have l': "l = float_round_down prec l'" and u': "u = float_round_up prec u'"
    using approx' unfolding approx'.simps S[symmetric] by auto
  show ?thesis unfolding l' u'
    using order_trans[OF Pa[OF S, THEN conjunct2] float_round_up[of u']]
    using order_trans[OF float_round_down[of _ l'] Pa[OF S, THEN conjunct1]] by auto
qed

lemma lift_bin_ex:
  assumes lift_bin_Some: "Some (l, u) = lift_bin a b f"
  shows "\<exists> l1 u1 l2 u2. Some (l1, u1) = a \<and> Some (l2, u2) = b"
proof (cases a)
  case None
  hence "None = lift_bin a b f"
    unfolding None lift_bin.simps ..
  thus ?thesis
    using lift_bin_Some by auto
next
  case (Some a')
  show ?thesis
  proof (cases b)
    case None
    hence "None = lift_bin a b f"
      unfolding None lift_bin.simps ..
    thus ?thesis using lift_bin_Some by auto
  next
    case (Some b')
    obtain la ua where a': "a' = (la, ua)"
      by (cases a') auto
    obtain lb ub where b': "b' = (lb, ub)"
      by (cases b') auto
    thus ?thesis
      unfolding \<open>a = Some a'\<close> \<open>b = Some b'\<close> a' b' by auto
  qed
qed

lemma lift_bin_f:
  assumes lift_bin_Some: "Some (l, u) = lift_bin (g a) (g b) f"
    and Pa: "\<And>l u. Some (l, u) = g a \<Longrightarrow> P l u a"
    and Pb: "\<And>l u. Some (l, u) = g b \<Longrightarrow> P l u b"
  shows "\<exists> l1 u1 l2 u2. P l1 u1 a \<and> P l2 u2 b \<and> Some (l, u) = f l1 u1 l2 u2"
proof -
  obtain l1 u1 l2 u2
    where Sa: "Some (l1, u1) = g a"
      and Sb: "Some (l2, u2) = g b"
    using lift_bin_ex[OF assms(1)] by auto
  have lu: "Some (l, u) = f l1 u1 l2 u2"
    using lift_bin_Some[unfolded Sa[symmetric] Sb[symmetric] lift_bin.simps] by auto
  thus ?thesis
    using Pa[OF Sa] Pb[OF Sb] by auto
qed

lemma lift_bin:
  assumes lift_bin_Some: "Some (l, u) = lift_bin (approx' prec a bs) (approx' prec b bs) f"
    and Pa: "\<And>l u. Some (l, u) = approx prec a bs \<Longrightarrow>
      real_of_float l \<le> interpret_floatarith a xs \<and> interpret_floatarith a xs \<le> real_of_float u" (is "\<And>l u. _ = ?g a \<Longrightarrow> ?P l u a")
    and Pb: "\<And>l u. Some (l, u) = approx prec b bs \<Longrightarrow>
      real_of_float l \<le> interpret_floatarith b xs \<and> interpret_floatarith b xs \<le> real_of_float u"
  shows "\<exists>l1 u1 l2 u2. (real_of_float l1 \<le> interpret_floatarith a xs \<and> interpret_floatarith a xs \<le> real_of_float u1) \<and>
                       (real_of_float l2 \<le> interpret_floatarith b xs \<and> interpret_floatarith b xs \<le> real_of_float u2) \<and>
                       Some (l, u) = (f l1 u1 l2 u2)"
proof -
  { fix l u assume "Some (l, u) = approx' prec a bs"
    with approx_approx'[of prec a bs, OF _ this] Pa
    have "l \<le> interpret_floatarith a xs \<and> interpret_floatarith a xs \<le> u" by auto } note Pa = this
  { fix l u assume "Some (l, u) = approx' prec b bs"
    with approx_approx'[of prec b bs, OF _ this] Pb
    have "l \<le> interpret_floatarith b xs \<and> interpret_floatarith b xs \<le> u" by auto } note Pb = this

  from lift_bin_f[where g="\<lambda>a. approx' prec a bs" and P = ?P, OF lift_bin_Some, OF Pa Pb]
  show ?thesis by auto
qed

lemma lift_bin'_ex:
  assumes lift_bin'_Some: "Some (l, u) = lift_bin' a b f"
  shows "\<exists> l1 u1 l2 u2. Some (l1, u1) = a \<and> Some (l2, u2) = b"
proof (cases a)
  case None
  hence "None = lift_bin' a b f"
    unfolding None lift_bin'.simps ..
  thus ?thesis
    using lift_bin'_Some by auto
next
  case (Some a')
  show ?thesis
  proof (cases b)
    case None
    hence "None = lift_bin' a b f"
      unfolding None lift_bin'.simps ..
    thus ?thesis using lift_bin'_Some by auto
  next
    case (Some b')
    obtain la ua where a': "a' = (la, ua)"
      by (cases a') auto
    obtain lb ub where b': "b' = (lb, ub)"
      by (cases b') auto
    thus ?thesis
      unfolding \<open>a = Some a'\<close> \<open>b = Some b'\<close> a' b' by auto
  qed
qed

lemma lift_bin'_f:
  assumes lift_bin'_Some: "Some (l, u) = lift_bin' (g a) (g b) f"
    and Pa: "\<And>l u. Some (l, u) = g a \<Longrightarrow> P l u a"
    and Pb: "\<And>l u. Some (l, u) = g b \<Longrightarrow> P l u b"
  shows "\<exists> l1 u1 l2 u2. P l1 u1 a \<and> P l2 u2 b \<and> l = fst (f l1 u1 l2 u2) \<and> u = snd (f l1 u1 l2 u2)"
proof -
  obtain l1 u1 l2 u2
    where Sa: "Some (l1, u1) = g a"
      and Sb: "Some (l2, u2) = g b"
    using lift_bin'_ex[OF assms(1)] by auto
  have lu: "(l, u) = f l1 u1 l2 u2"
    using lift_bin'_Some[unfolded Sa[symmetric] Sb[symmetric] lift_bin'.simps] by auto
  have "l = fst (f l1 u1 l2 u2)" and "u = snd (f l1 u1 l2 u2)"
    unfolding lu[symmetric] by auto
  thus ?thesis
    using Pa[OF Sa] Pb[OF Sb] by auto
qed

lemma lift_bin':
  assumes lift_bin'_Some: "Some (l, u) = lift_bin' (approx' prec a bs) (approx' prec b bs) f"
    and Pa: "\<And>l u. Some (l, u) = approx prec a bs \<Longrightarrow>
      l \<le> interpret_floatarith a xs \<and> interpret_floatarith a xs \<le> u" (is "\<And>l u. _ = ?g a \<Longrightarrow> ?P l u a")
    and Pb: "\<And>l u. Some (l, u) = approx prec b bs \<Longrightarrow>
      l \<le> interpret_floatarith b xs \<and> interpret_floatarith b xs \<le> u"
  shows "\<exists>l1 u1 l2 u2. (l1 \<le> interpret_floatarith a xs \<and> interpret_floatarith a xs \<le> u1) \<and>
                       (l2 \<le> interpret_floatarith b xs \<and> interpret_floatarith b xs \<le> u2) \<and>
                       l = fst (f l1 u1 l2 u2) \<and> u = snd (f l1 u1 l2 u2)"
proof -
  { fix l u assume "Some (l, u) = approx' prec a bs"
    with approx_approx'[of prec a bs, OF _ this] Pa
    have "l \<le> interpret_floatarith a xs \<and> interpret_floatarith a xs \<le> u" by auto } note Pa = this
  { fix l u assume "Some (l, u) = approx' prec b bs"
    with approx_approx'[of prec b bs, OF _ this] Pb
    have "l \<le> interpret_floatarith b xs \<and> interpret_floatarith b xs \<le> u" by auto } note Pb = this

  from lift_bin'_f[where g="\<lambda>a. approx' prec a bs" and P = ?P, OF lift_bin'_Some, OF Pa Pb]
  show ?thesis by auto
qed

lemma lift_un'_ex:
  assumes lift_un'_Some: "Some (l, u) = lift_un' a f"
  shows "\<exists> l u. Some (l, u) = a"
proof (cases a)
  case None
  hence "None = lift_un' a f"
    unfolding None lift_un'.simps ..
  thus ?thesis
    using lift_un'_Some by auto
next
  case (Some a')
  obtain la ua where a': "a' = (la, ua)"
    by (cases a') auto
  thus ?thesis
    unfolding \<open>a = Some a'\<close> a' by auto
qed

lemma lift_un'_f:
  assumes lift_un'_Some: "Some (l, u) = lift_un' (g a) f"
    and Pa: "\<And>l u. Some (l, u) = g a \<Longrightarrow> P l u a"
  shows "\<exists> l1 u1. P l1 u1 a \<and> l = fst (f l1 u1) \<and> u = snd (f l1 u1)"
proof -
  obtain l1 u1 where Sa: "Some (l1, u1) = g a"
    using lift_un'_ex[OF assms(1)] by auto
  have lu: "(l, u) = f l1 u1"
    using lift_un'_Some[unfolded Sa[symmetric] lift_un'.simps] by auto
  have "l = fst (f l1 u1)" and "u = snd (f l1 u1)"
    unfolding lu[symmetric] by auto
  thus ?thesis
    using Pa[OF Sa] by auto
qed

lemma lift_un':
  assumes lift_un'_Some: "Some (l, u) = lift_un' (approx' prec a bs) f"
    and Pa: "\<And>l u. Some (l, u) = approx prec a bs \<Longrightarrow>
      l \<le> interpret_floatarith a xs \<and> interpret_floatarith a xs \<le> u"
      (is "\<And>l u. _ = ?g a \<Longrightarrow> ?P l u a")
  shows "\<exists>l1 u1. (l1 \<le> interpret_floatarith a xs \<and> interpret_floatarith a xs \<le> u1) \<and>
    l = fst (f l1 u1) \<and> u = snd (f l1 u1)"
proof -
  have Pa: "l \<le> interpret_floatarith a xs \<and> interpret_floatarith a xs \<le> u"
    if "Some (l, u) = approx' prec a bs" for l u
    using approx_approx'[of prec a bs, OF _ that] Pa
     by auto
  from lift_un'_f[where g="\<lambda>a. approx' prec a bs" and P = ?P, OF lift_un'_Some, OF Pa]
  show ?thesis by auto
qed

lemma lift_un'_bnds:
  assumes bnds: "\<forall> (x::real) lx ux. (l, u) = f lx ux \<and> x \<in> { lx .. ux } \<longrightarrow> l \<le> f' x \<and> f' x \<le> u"
    and lift_un'_Some: "Some (l, u) = lift_un' (approx' prec a bs) f"
    and Pa: "\<And>l u. Some (l, u) = approx prec a bs \<Longrightarrow>
      l \<le> interpret_floatarith a xs \<and> interpret_floatarith a xs \<le> u"
  shows "real_of_float l \<le> f' (interpret_floatarith a xs) \<and> f' (interpret_floatarith a xs) \<le> real_of_float u"
proof -
  from lift_un'[OF lift_un'_Some Pa]
  obtain l1 u1 where "l1 \<le> interpret_floatarith a xs"
    and "interpret_floatarith a xs \<le> u1"
    and "l = fst (f l1 u1)"
    and "u = snd (f l1 u1)"
    by blast
  hence "(l, u) = f l1 u1" and "interpret_floatarith a xs \<in> {l1 .. u1}"
    by auto
  thus ?thesis
    using bnds by auto
qed

lemma lift_un_ex:
  assumes lift_un_Some: "Some (l, u) = lift_un a f"
  shows "\<exists>l u. Some (l, u) = a"
proof (cases a)
  case None
  hence "None = lift_un a f"
    unfolding None lift_un.simps ..
  thus ?thesis
    using lift_un_Some by auto
next
  case (Some a')
  obtain la ua where a': "a' = (la, ua)"
    by (cases a') auto
  thus ?thesis
    unfolding \<open>a = Some a'\<close> a' by auto
qed

lemma lift_un_f:
  assumes lift_un_Some: "Some (l, u) = lift_un (g a) f"
    and Pa: "\<And>l u. Some (l, u) = g a \<Longrightarrow> P l u a"
  shows "\<exists> l1 u1. P l1 u1 a \<and> Some l = fst (f l1 u1) \<and> Some u = snd (f l1 u1)"
proof -
  obtain l1 u1 where Sa: "Some (l1, u1) = g a"
    using lift_un_ex[OF assms(1)] by auto
  have "fst (f l1 u1) \<noteq> None \<and> snd (f l1 u1) \<noteq> None"
  proof (rule ccontr)
    assume "\<not> (fst (f l1 u1) \<noteq> None \<and> snd (f l1 u1) \<noteq> None)"
    hence or: "fst (f l1 u1) = None \<or> snd (f l1 u1) = None" by auto
    hence "lift_un (g a) f = None"
    proof (cases "fst (f l1 u1) = None")
      case True
      then obtain b where b: "f l1 u1 = (None, b)"
        by (cases "f l1 u1") auto
      thus ?thesis
        unfolding Sa[symmetric] lift_un.simps b by auto
    next
      case False
      hence "snd (f l1 u1) = None"
        using or by auto
      with False obtain b where b: "f l1 u1 = (Some b, None)"
        by (cases "f l1 u1") auto
      thus ?thesis
        unfolding Sa[symmetric] lift_un.simps b by auto
    qed
    thus False
      using lift_un_Some by auto
  qed
  then obtain a' b' where f: "f l1 u1 = (Some a', Some b')"
    by (cases "f l1 u1") auto
  from lift_un_Some[unfolded Sa[symmetric] lift_un.simps f]
  have "Some l = fst (f l1 u1)" and "Some u = snd (f l1 u1)"
    unfolding f by auto
  thus ?thesis
    unfolding Sa[symmetric] lift_un.simps using Pa[OF Sa] by auto
qed

lemma lift_un:
  assumes lift_un_Some: "Some (l, u) = lift_un (approx' prec a bs) f"
    and Pa: "\<And>l u. Some (l, u) = approx prec a bs \<Longrightarrow>
        l \<le> interpret_floatarith a xs \<and> interpret_floatarith a xs \<le> u"
      (is "\<And>l u. _ = ?g a \<Longrightarrow> ?P l u a")
  shows "\<exists>l1 u1. (l1 \<le> interpret_floatarith a xs \<and> interpret_floatarith a xs \<le> u1) \<and>
                  Some l = fst (f l1 u1) \<and> Some u = snd (f l1 u1)"
proof -
  have Pa: "l \<le> interpret_floatarith a xs \<and> interpret_floatarith a xs \<le> u"
    if "Some (l, u) = approx' prec a bs" for l u
    using approx_approx'[of prec a bs, OF _ that] Pa by auto
  from lift_un_f[where g="\<lambda>a. approx' prec a bs" and P = ?P, OF lift_un_Some, OF Pa]
  show ?thesis by auto
qed

lemma lift_un_bnds:
  assumes bnds: "\<forall>(x::real) lx ux. (Some l, Some u) = f lx ux \<and> x \<in> { lx .. ux } \<longrightarrow> l \<le> f' x \<and> f' x \<le> u"
    and lift_un_Some: "Some (l, u) = lift_un (approx' prec a bs) f"
    and Pa: "\<And>l u. Some (l, u) = approx prec a bs \<Longrightarrow>
      l \<le> interpret_floatarith a xs \<and> interpret_floatarith a xs \<le> u"
  shows "real_of_float l \<le> f' (interpret_floatarith a xs) \<and> f' (interpret_floatarith a xs) \<le> real_of_float u"
proof -
  from lift_un[OF lift_un_Some Pa]
  obtain l1 u1 where "l1 \<le> interpret_floatarith a xs"
    and "interpret_floatarith a xs \<le> u1"
    and "Some l = fst (f l1 u1)"
    and "Some u = snd (f l1 u1)"
    by blast
  hence "(Some l, Some u) = f l1 u1" and "interpret_floatarith a xs \<in> {l1 .. u1}"
    by auto
  thus ?thesis
    using bnds by auto
qed

lemma approx:
  assumes "bounded_by xs vs"
    and "Some (l, u) = approx prec arith vs" (is "_ = ?g arith")
  shows "l \<le> interpret_floatarith arith xs \<and> interpret_floatarith arith xs \<le> u" (is "?P l u arith")
  using \<open>Some (l, u) = approx prec arith vs\<close>
proof (induct arith arbitrary: l u)
  case (Add a b)
  from lift_bin'[OF Add.prems[unfolded approx.simps]] Add.hyps
  obtain l1 u1 l2 u2 where "l = float_plus_down prec l1 l2"
    and "u = float_plus_up prec u1 u2" "l1 \<le> interpret_floatarith a xs"
    and "interpret_floatarith a xs \<le> u1" "l2 \<le> interpret_floatarith b xs"
    and "interpret_floatarith b xs \<le> u2"
    unfolding fst_conv snd_conv by blast
  thus ?case
    unfolding interpret_floatarith.simps by (auto intro!: float_plus_up_le float_plus_down_le)
next
  case (Minus a)
  from lift_un'[OF Minus.prems[unfolded approx.simps]] Minus.hyps
  obtain l1 u1 where "l = -u1" "u = -l1"
    and "l1 \<le> interpret_floatarith a xs" "interpret_floatarith a xs \<le> u1"
    unfolding fst_conv snd_conv by blast
  thus ?case
    unfolding interpret_floatarith.simps using minus_float.rep_eq by auto
next
  case (Mult a b)
  from lift_bin'[OF Mult.prems[unfolded approx.simps]] Mult.hyps
  obtain l1 u1 l2 u2
    where l: "l = fst (bnds_mult prec l1 u1 l2 u2)"
    and u: "u = snd (bnds_mult prec l1 u1 l2 u2)"
    and a: "l1 \<le> interpret_floatarith a xs" "interpret_floatarith a xs \<le> u1"
    and b: "l2 \<le> interpret_floatarith b xs" "interpret_floatarith b xs \<le> u2" unfolding fst_conv snd_conv by blast
  from l u have lu: "(l, u) = bnds_mult prec l1 u1 l2 u2" by simp
  from bnds_mult[OF lu] a b show ?case by simp
next
  case (Inverse a)
  from lift_un[OF Inverse.prems[unfolded approx.simps], unfolded if_distrib[of fst] if_distrib[of snd] fst_conv snd_conv] Inverse.hyps
  obtain l1 u1 where l': "Some l = (if 0 < l1 \<or> u1 < 0 then Some (float_divl prec 1 u1) else None)"
    and u': "Some u = (if 0 < l1 \<or> u1 < 0 then Some (float_divr prec 1 l1) else None)"
    and l1: "l1 \<le> interpret_floatarith a xs"
    and u1: "interpret_floatarith a xs \<le> u1"
    by blast
  have either: "0 < l1 \<or> u1 < 0"
  proof (rule ccontr)
    assume P: "\<not> (0 < l1 \<or> u1 < 0)"
    show False
      using l' unfolding if_not_P[OF P] by auto
  qed
  moreover have l1_le_u1: "real_of_float l1 \<le> real_of_float u1"
    using l1 u1 by auto
  ultimately have "real_of_float l1 \<noteq> 0" and "real_of_float u1 \<noteq> 0"
    by auto

  have inv: "inverse u1 \<le> inverse (interpret_floatarith a xs)
           \<and> inverse (interpret_floatarith a xs) \<le> inverse l1"
  proof (cases "0 < l1")
    case True
    hence "0 < real_of_float u1" and "0 < real_of_float l1" "0 < interpret_floatarith a xs"
      using l1_le_u1 l1 by auto
    show ?thesis
      unfolding inverse_le_iff_le[OF \<open>0 < real_of_float u1\<close> \<open>0 < interpret_floatarith a xs\<close>]
        inverse_le_iff_le[OF \<open>0 < interpret_floatarith a xs\<close> \<open>0 < real_of_float l1\<close>]
      using l1 u1 by auto
  next
    case False
    hence "u1 < 0"
      using either by blast
    hence "real_of_float u1 < 0" and "real_of_float l1 < 0" "interpret_floatarith a xs < 0"
      using l1_le_u1 u1 by auto
    show ?thesis
      unfolding inverse_le_iff_le_neg[OF \<open>real_of_float u1 < 0\<close> \<open>interpret_floatarith a xs < 0\<close>]
        inverse_le_iff_le_neg[OF \<open>interpret_floatarith a xs < 0\<close> \<open>real_of_float l1 < 0\<close>]
      using l1 u1 by auto
  qed

  from l' have "l = float_divl prec 1 u1"
    by (cases "0 < l1 \<or> u1 < 0") auto
  hence "l \<le> inverse u1"
    unfolding nonzero_inverse_eq_divide[OF \<open>real_of_float u1 \<noteq> 0\<close>]
    using float_divl[of prec 1 u1] by auto
  also have "\<dots> \<le> inverse (interpret_floatarith a xs)"
    using inv by auto
  finally have "l \<le> inverse (interpret_floatarith a xs)" .
  moreover
  from u' have "u = float_divr prec 1 l1"
    by (cases "0 < l1 \<or> u1 < 0") auto
  hence "inverse l1 \<le> u"
    unfolding nonzero_inverse_eq_divide[OF \<open>real_of_float l1 \<noteq> 0\<close>]
    using float_divr[of 1 l1 prec] by auto
  hence "inverse (interpret_floatarith a xs) \<le> u"
    by (rule order_trans[OF inv[THEN conjunct2]])
  ultimately show ?case
    unfolding interpret_floatarith.simps using l1 u1 by auto
next
  case (Abs x)
  from lift_un'[OF Abs.prems[unfolded approx.simps], unfolded fst_conv snd_conv] Abs.hyps
  obtain l1 u1 where l': "l = (if l1 < 0 \<and> 0 < u1 then 0 else min \<bar>l1\<bar> \<bar>u1\<bar>)"
    and u': "u = max \<bar>l1\<bar> \<bar>u1\<bar>"
    and l1: "l1 \<le> interpret_floatarith x xs"
    and u1: "interpret_floatarith x xs \<le> u1"
    by blast
  thus ?case
    unfolding l' u'
    by (cases "l1 < 0 \<and> 0 < u1") (auto simp add: real_of_float_min real_of_float_max)
next
  case (Min a b)
  from lift_bin'[OF Min.prems[unfolded approx.simps], unfolded fst_conv snd_conv] Min.hyps
  obtain l1 u1 l2 u2 where l': "l = min l1 l2" and u': "u = min u1 u2"
    and l1: "l1 \<le> interpret_floatarith a xs" and u1: "interpret_floatarith a xs \<le> u1"
    and l1: "l2 \<le> interpret_floatarith b xs" and u1: "interpret_floatarith b xs \<le> u2"
    by blast
  thus ?case
    unfolding l' u' by (auto simp add: real_of_float_min)
next
  case (Max a b)
  from lift_bin'[OF Max.prems[unfolded approx.simps], unfolded fst_conv snd_conv] Max.hyps
  obtain l1 u1 l2 u2 where l': "l = max l1 l2" and u': "u = max u1 u2"
    and l1: "l1 \<le> interpret_floatarith a xs" and u1: "interpret_floatarith a xs \<le> u1"
    and l1: "l2 \<le> interpret_floatarith b xs" and u1: "interpret_floatarith b xs \<le> u2"
    by blast
  thus ?case
    unfolding l' u' by (auto simp add: real_of_float_max)
next
  case (Cos a)
  with lift_un'_bnds[OF bnds_cos] show ?case by auto
next
  case (Arctan a)
  with lift_un'_bnds[OF bnds_arctan] show ?case by auto
next
  case Pi
  with pi_boundaries show ?case by auto
next
  case (Sqrt a)
  with lift_un'_bnds[OF bnds_sqrt] show ?case by auto
next
  case (Exp a)
  with lift_un'_bnds[OF bnds_exp] show ?case by auto
next
  case (Powr a b)
  from lift_bin[OF Powr.prems[unfolded approx.simps]] Powr.hyps
    obtain l1 u1 l2 u2 where lu: "Some (l, u) = bnds_powr prec l1 u1 l2 u2"
      and l1: "l1 \<le> interpret_floatarith a xs" and u1: "interpret_floatarith a xs \<le> u1"
      and l2: "l2 \<le> interpret_floatarith b xs" and u2: "interpret_floatarith b xs \<le> u2"
      by blast
  from bnds_powr[OF lu] l1 u1 l2 u2
    show ?case by simp
next
  case (Ln a)
  with lift_un_bnds[OF bnds_ln] show ?case by auto
next
  case (Power a n)
  with lift_un'_bnds[OF bnds_power] show ?case by auto
next
  case (Floor a)
  from lift_un'[OF Floor.prems[unfolded approx.simps] Floor.hyps]
  show ?case by (auto simp: floor_fl.rep_eq floor_mono)
next
  case (Num f)
  thus ?case by auto
next
  case (Var n)
  from this[symmetric] \<open>bounded_by xs vs\<close>[THEN bounded_byE, of n]
  show ?case by (cases "n < length vs") auto
qed

datatype form = Bound floatarith floatarith floatarith form
              | Assign floatarith floatarith form
              | Less floatarith floatarith
              | LessEqual floatarith floatarith
              | AtLeastAtMost floatarith floatarith floatarith
              | Conj form form
              | Disj form form

fun interpret_form :: "form \<Rightarrow> real list \<Rightarrow> bool" where
"interpret_form (Bound x a b f) vs = (interpret_floatarith x vs \<in> { interpret_floatarith a vs .. interpret_floatarith b vs } \<longrightarrow> interpret_form f vs)" |
"interpret_form (Assign x a f) vs  = (interpret_floatarith x vs = interpret_floatarith a vs \<longrightarrow> interpret_form f vs)" |
"interpret_form (Less a b) vs      = (interpret_floatarith a vs < interpret_floatarith b vs)" |
"interpret_form (LessEqual a b) vs = (interpret_floatarith a vs \<le> interpret_floatarith b vs)" |
"interpret_form (AtLeastAtMost x a b) vs = (interpret_floatarith x vs \<in> { interpret_floatarith a vs .. interpret_floatarith b vs })" |
"interpret_form (Conj f g) vs \<longleftrightarrow> interpret_form f vs \<and> interpret_form g vs" |
"interpret_form (Disj f g) vs \<longleftrightarrow> interpret_form f vs \<or> interpret_form g vs"

fun approx_form' and approx_form :: "nat \<Rightarrow> form \<Rightarrow> (float * float) option list \<Rightarrow> nat list \<Rightarrow> bool" where
"approx_form' prec f 0 n l u bs ss = approx_form prec f (bs[n := Some (l, u)]) ss" |
"approx_form' prec f (Suc s) n l u bs ss =
  (let m = (l + u) * Float 1 (- 1)
   in (if approx_form' prec f s n l m bs ss then approx_form' prec f s n m u bs ss else False))" |
"approx_form prec (Bound (Var n) a b f) bs ss =
   (case (approx prec a bs, approx prec b bs)
   of (Some (l, _), Some (_, u)) \<Rightarrow> approx_form' prec f (ss ! n) n l u bs ss
    | _ \<Rightarrow> False)" |
"approx_form prec (Assign (Var n) a f) bs ss =
   (case (approx prec a bs)
   of (Some (l, u)) \<Rightarrow> approx_form' prec f (ss ! n) n l u bs ss
    | _ \<Rightarrow> False)" |
"approx_form prec (Less a b) bs ss =
   (case (approx prec a bs, approx prec b bs)
   of (Some (l, u), Some (l', u')) \<Rightarrow> float_plus_up prec u (-l') < 0
    | _ \<Rightarrow> False)" |
"approx_form prec (LessEqual a b) bs ss =
   (case (approx prec a bs, approx prec b bs)
   of (Some (l, u), Some (l', u')) \<Rightarrow> float_plus_up prec u (-l') \<le> 0
    | _ \<Rightarrow> False)" |
"approx_form prec (AtLeastAtMost x a b) bs ss =
   (case (approx prec x bs, approx prec a bs, approx prec b bs)
   of (Some (lx, ux), Some (l, u), Some (l', u')) \<Rightarrow> float_plus_up prec u (-lx) \<le> 0 \<and> float_plus_up prec ux (-l') \<le> 0
    | _ \<Rightarrow> False)" |
"approx_form prec (Conj a b) bs ss \<longleftrightarrow> approx_form prec a bs ss \<and> approx_form prec b bs ss" |
"approx_form prec (Disj a b) bs ss \<longleftrightarrow> approx_form prec a bs ss \<or> approx_form prec b bs ss" |
"approx_form _ _ _ _ = False"

lemma lazy_conj: "(if A then B else False) = (A \<and> B)" by simp

lemma approx_form_approx_form':
  assumes "approx_form' prec f s n l u bs ss"
    and "(x::real) \<in> { l .. u }"
  obtains l' u' where "x \<in> { l' .. u' }"
    and "approx_form prec f (bs[n := Some (l', u')]) ss"
using assms proof (induct s arbitrary: l u)
  case 0
  from this(1)[of l u] this(2,3)
  show thesis by auto
next
  case (Suc s)

  let ?m = "(l + u) * Float 1 (- 1)"
  have "real_of_float l \<le> ?m" and "?m \<le> real_of_float u"
    unfolding less_eq_float_def using Suc.prems by auto

  with \<open>x \<in> { l .. u }\<close>
  have "x \<in> { l .. ?m} \<or> x \<in> { ?m .. u }" by auto
  thus thesis
  proof (rule disjE)
    assume *: "x \<in> { l .. ?m }"
    with Suc.hyps[OF _ _ *] Suc.prems
    show thesis by (simp add: Let_def lazy_conj)
  next
    assume *: "x \<in> { ?m .. u }"
    with Suc.hyps[OF _ _ *] Suc.prems
    show thesis by (simp add: Let_def lazy_conj)
  qed
qed

lemma approx_form_aux:
  assumes "approx_form prec f vs ss"
    and "bounded_by xs vs"
  shows "interpret_form f xs"
using assms proof (induct f arbitrary: vs)
  case (Bound x a b f)
  then obtain n
    where x_eq: "x = Var n" by (cases x) auto

  with Bound.prems obtain l u' l' u
    where l_eq: "Some (l, u') = approx prec a vs"
    and u_eq: "Some (l', u) = approx prec b vs"
    and approx_form': "approx_form' prec f (ss ! n) n l u vs ss"
    by (cases "approx prec a vs", simp) (cases "approx prec b vs", auto)

  have "interpret_form f xs"
    if "xs ! n \<in> { interpret_floatarith a xs .. interpret_floatarith b xs }"
  proof -
    from approx[OF Bound.prems(2) l_eq] and approx[OF Bound.prems(2) u_eq] that
    have "xs ! n \<in> { l .. u}" by auto

    from approx_form_approx_form'[OF approx_form' this]
    obtain lx ux where bnds: "xs ! n \<in> { lx .. ux }"
      and approx_form: "approx_form prec f (vs[n := Some (lx, ux)]) ss" .

    from \<open>bounded_by xs vs\<close> bnds have "bounded_by xs (vs[n := Some (lx, ux)])"
      by (rule bounded_by_update)
    with Bound.hyps[OF approx_form] show ?thesis
      by blast
  qed
  thus ?case
    using interpret_form.simps x_eq and interpret_floatarith.simps by simp
next
  case (Assign x a f)
  then obtain n where x_eq: "x = Var n"
    by (cases x) auto

  with Assign.prems obtain l u
    where bnd_eq: "Some (l, u) = approx prec a vs"
    and x_eq: "x = Var n"
    and approx_form': "approx_form' prec f (ss ! n) n l u vs ss"
    by (cases "approx prec a vs") auto

  have "interpret_form f xs"
    if bnds: "xs ! n = interpret_floatarith a xs"
  proof -
    from approx[OF Assign.prems(2) bnd_eq] bnds
    have "xs ! n \<in> { l .. u}" by auto
    from approx_form_approx_form'[OF approx_form' this]
    obtain lx ux where bnds: "xs ! n \<in> { lx .. ux }"
      and approx_form: "approx_form prec f (vs[n := Some (lx, ux)]) ss" .

    from \<open>bounded_by xs vs\<close> bnds have "bounded_by xs (vs[n := Some (lx, ux)])"
      by (rule bounded_by_update)
    with Assign.hyps[OF approx_form] show ?thesis
      by blast
  qed
  thus ?case
    using interpret_form.simps x_eq and interpret_floatarith.simps by simp
next
  case (Less a b)
  then obtain l u l' u'
    where l_eq: "Some (l, u) = approx prec a vs"
      and u_eq: "Some (l', u') = approx prec b vs"
      and inequality: "real_of_float (float_plus_up prec u (-l')) < 0"
    by (cases "approx prec a vs", auto, cases "approx prec b vs", auto)
  from le_less_trans[OF float_plus_up inequality]
    approx[OF Less.prems(2) l_eq] approx[OF Less.prems(2) u_eq]
  show ?case by auto
next
  case (LessEqual a b)
  then obtain l u l' u'
    where l_eq: "Some (l, u) = approx prec a vs"
      and u_eq: "Some (l', u') = approx prec b vs"
      and inequality: "real_of_float (float_plus_up prec u (-l')) \<le> 0"
    by (cases "approx prec a vs", auto, cases "approx prec b vs", auto)
  from order_trans[OF float_plus_up inequality]
    approx[OF LessEqual.prems(2) l_eq] approx[OF LessEqual.prems(2) u_eq]
  show ?case by auto
next
  case (AtLeastAtMost x a b)
  then obtain lx ux l u l' u'
    where x_eq: "Some (lx, ux) = approx prec x vs"
    and l_eq: "Some (l, u) = approx prec a vs"
    and u_eq: "Some (l', u') = approx prec b vs"
    and inequality: "real_of_float (float_plus_up prec u (-lx)) \<le> 0" "real_of_float (float_plus_up prec ux (-l')) \<le> 0"
    by (cases "approx prec x vs", auto,
      cases "approx prec a vs", auto,
      cases "approx prec b vs", auto)
  from order_trans[OF float_plus_up inequality(1)] order_trans[OF float_plus_up inequality(2)]
    approx[OF AtLeastAtMost.prems(2) l_eq] approx[OF AtLeastAtMost.prems(2) u_eq] approx[OF AtLeastAtMost.prems(2) x_eq]
  show ?case by auto
qed auto

lemma approx_form:
  assumes "n = length xs"
    and "approx_form prec f (replicate n None) ss"
  shows "interpret_form f xs"
  using approx_form_aux[OF _ bounded_by_None] assms by auto


subsection \<open>Implementing Taylor series expansion\<close>

fun isDERIV :: "nat \<Rightarrow> floatarith \<Rightarrow> real list \<Rightarrow> bool" where
"isDERIV x (Add a b) vs         = (isDERIV x a vs \<and> isDERIV x b vs)" |
"isDERIV x (Mult a b) vs        = (isDERIV x a vs \<and> isDERIV x b vs)" |
"isDERIV x (Minus a) vs         = isDERIV x a vs" |
"isDERIV x (Inverse a) vs       = (isDERIV x a vs \<and> interpret_floatarith a vs \<noteq> 0)" |
"isDERIV x (Cos a) vs           = isDERIV x a vs" |
"isDERIV x (Arctan a) vs        = isDERIV x a vs" |
"isDERIV x (Min a b) vs         = False" |
"isDERIV x (Max a b) vs         = False" |
"isDERIV x (Abs a) vs           = False" |
"isDERIV x Pi vs                = True" |
"isDERIV x (Sqrt a) vs          = (isDERIV x a vs \<and> interpret_floatarith a vs > 0)" |
"isDERIV x (Exp a) vs           = isDERIV x a vs" |
"isDERIV x (Powr a b) vs        =
    (isDERIV x a vs \<and> isDERIV x b vs \<and> interpret_floatarith a vs > 0)" |
"isDERIV x (Ln a) vs            = (isDERIV x a vs \<and> interpret_floatarith a vs > 0)" |
"isDERIV x (Floor a) vs         = (isDERIV x a vs \<and> interpret_floatarith a vs \<notin> \<int>)" |
"isDERIV x (Power a 0) vs       = True" |
"isDERIV x (Power a (Suc n)) vs = isDERIV x a vs" |
"isDERIV x (Num f) vs           = True" |
"isDERIV x (Var n) vs          = True"

fun DERIV_floatarith :: "nat \<Rightarrow> floatarith \<Rightarrow> floatarith" where
"DERIV_floatarith x (Add a b)         = Add (DERIV_floatarith x a) (DERIV_floatarith x b)" |
"DERIV_floatarith x (Mult a b)        = Add (Mult a (DERIV_floatarith x b)) (Mult (DERIV_floatarith x a) b)" |
"DERIV_floatarith x (Minus a)         = Minus (DERIV_floatarith x a)" |
"DERIV_floatarith x (Inverse a)       = Minus (Mult (DERIV_floatarith x a) (Inverse (Power a 2)))" |
"DERIV_floatarith x (Cos a)           = Minus (Mult (Cos (Add (Mult Pi (Num (Float 1 (- 1)))) (Minus a))) (DERIV_floatarith x a))" |
"DERIV_floatarith x (Arctan a)        = Mult (Inverse (Add (Num 1) (Power a 2))) (DERIV_floatarith x a)" |
"DERIV_floatarith x (Min a b)         = Num 0" |
"DERIV_floatarith x (Max a b)         = Num 0" |
"DERIV_floatarith x (Abs a)           = Num 0" |
"DERIV_floatarith x Pi                = Num 0" |
"DERIV_floatarith x (Sqrt a)          = (Mult (Inverse (Mult (Sqrt a) (Num 2))) (DERIV_floatarith x a))" |
"DERIV_floatarith x (Exp a)           = Mult (Exp a) (DERIV_floatarith x a)" |
"DERIV_floatarith x (Powr a b)        =
   Mult (Powr a b) (Add (Mult (DERIV_floatarith x b) (Ln a)) (Mult (Mult (DERIV_floatarith x a) b) (Inverse a)))" |
"DERIV_floatarith x (Ln a)            = Mult (Inverse a) (DERIV_floatarith x a)" |
"DERIV_floatarith x (Power a 0)       = Num 0" |
"DERIV_floatarith x (Power a (Suc n)) = Mult (Num (Float (int (Suc n)) 0)) (Mult (Power a n) (DERIV_floatarith x a))" |
"DERIV_floatarith x (Floor a)         = Num 0" |
"DERIV_floatarith x (Num f)           = Num 0" |
"DERIV_floatarith x (Var n)          = (if x = n then Num 1 else Num 0)"

lemma has_real_derivative_powr':
  fixes f g :: "real \<Rightarrow> real"
  assumes "(f has_real_derivative f') (at x)"
  assumes "(g has_real_derivative g') (at x)"
  assumes "f x > 0"
  defines "h \<equiv> \<lambda>x. f x powr g x * (g' * ln (f x) + f' * g x / f x)"
  shows   "((\<lambda>x. f x powr g x) has_real_derivative h x) (at x)"
proof (subst DERIV_cong_ev[OF refl _ refl])
  from assms have "isCont f x"
    by (simp add: DERIV_continuous)
  hence "f \<midarrow>x\<rightarrow> f x" by (simp add: continuous_at)
  with \<open>f x > 0\<close> have "eventually (\<lambda>x. f x > 0) (nhds x)"
    by (auto simp: tendsto_at_iff_tendsto_nhds dest: order_tendstoD)
  thus "eventually (\<lambda>x. f x powr g x = exp (g x * ln (f x))) (nhds x)"
    by eventually_elim (simp add: powr_def)
next
  from assms show "((\<lambda>x. exp (g x * ln (f x))) has_real_derivative h x) (at x)"
    by (auto intro!: derivative_eq_intros simp: h_def powr_def)
qed

lemma DERIV_floatarith:
  assumes "n < length vs"
  assumes isDERIV: "isDERIV n f (vs[n := x])"
  shows "DERIV (\<lambda> x'. interpret_floatarith f (vs[n := x'])) x :>
               interpret_floatarith (DERIV_floatarith n f) (vs[n := x])"
   (is "DERIV (?i f) x :> _")
using isDERIV
proof (induct f arbitrary: x)
  case (Inverse a)
  thus ?case
    by (auto intro!: derivative_eq_intros simp add: algebra_simps power2_eq_square)
next
  case (Cos a)
  thus ?case
    by (auto intro!: derivative_eq_intros
           simp del: interpret_floatarith.simps(5)
           simp add: interpret_floatarith_sin interpret_floatarith.simps(5)[of a])
next
  case (Power a n)
  thus ?case
    by (cases n) (auto intro!: derivative_eq_intros simp del: power_Suc)
next
  case (Floor a)
  thus ?case
    by (auto intro!: derivative_eq_intros DERIV_isCont floor_has_real_derivative)
next
  case (Ln a)
  thus ?case by (auto intro!: derivative_eq_intros simp add: divide_inverse)
next
  case (Var i)
  thus ?case using \<open>n < length vs\<close> by auto
next
  case (Powr a b)
  note [derivative_intros] = has_real_derivative_powr'
  from Powr show ?case
    by (auto intro!: derivative_eq_intros simp: field_simps)
qed (auto intro!: derivative_eq_intros)

declare approx.simps[simp del]

fun isDERIV_approx :: "nat \<Rightarrow> nat \<Rightarrow> floatarith \<Rightarrow> (float * float) option list \<Rightarrow> bool" where
"isDERIV_approx prec x (Add a b) vs         = (isDERIV_approx prec x a vs \<and> isDERIV_approx prec x b vs)" |
"isDERIV_approx prec x (Mult a b) vs        = (isDERIV_approx prec x a vs \<and> isDERIV_approx prec x b vs)" |
"isDERIV_approx prec x (Minus a) vs         = isDERIV_approx prec x a vs" |
"isDERIV_approx prec x (Inverse a) vs       =
  (isDERIV_approx prec x a vs \<and> (case approx prec a vs of Some (l, u) \<Rightarrow> 0 < l \<or> u < 0 | None \<Rightarrow> False))" |
"isDERIV_approx prec x (Cos a) vs           = isDERIV_approx prec x a vs" |
"isDERIV_approx prec x (Arctan a) vs        = isDERIV_approx prec x a vs" |
"isDERIV_approx prec x (Min a b) vs         = False" |
"isDERIV_approx prec x (Max a b) vs         = False" |
"isDERIV_approx prec x (Abs a) vs           = False" |
"isDERIV_approx prec x Pi vs                = True" |
"isDERIV_approx prec x (Sqrt a) vs          =
  (isDERIV_approx prec x a vs \<and> (case approx prec a vs of Some (l, u) \<Rightarrow> 0 < l | None \<Rightarrow> False))" |
"isDERIV_approx prec x (Exp a) vs           = isDERIV_approx prec x a vs" |
"isDERIV_approx prec x (Powr a b) vs        =
  (isDERIV_approx prec x a vs \<and> isDERIV_approx prec x b vs \<and> (case approx prec a vs of Some (l, u) \<Rightarrow> 0 < l | None \<Rightarrow> False))" |
"isDERIV_approx prec x (Ln a) vs            =
  (isDERIV_approx prec x a vs \<and> (case approx prec a vs of Some (l, u) \<Rightarrow> 0 < l | None \<Rightarrow> False))" |
"isDERIV_approx prec x (Power a 0) vs       = True" |
"isDERIV_approx prec x (Floor a) vs         =
  (isDERIV_approx prec x a vs \<and> (case approx prec a vs of Some (l, u) \<Rightarrow> l > floor u \<and> u < ceiling l | None \<Rightarrow> False))" |
"isDERIV_approx prec x (Power a (Suc n)) vs = isDERIV_approx prec x a vs" |
"isDERIV_approx prec x (Num f) vs           = True" |
"isDERIV_approx prec x (Var n) vs           = True"

lemma isDERIV_approx:
  assumes "bounded_by xs vs"
    and isDERIV_approx: "isDERIV_approx prec x f vs"
  shows "isDERIV x f xs"
  using isDERIV_approx
proof (induct f)
  case (Inverse a)
  then obtain l u where approx_Some: "Some (l, u) = approx prec a vs"
    and *: "0 < l \<or> u < 0"
    by (cases "approx prec a vs") auto
  with approx[OF \<open>bounded_by xs vs\<close> approx_Some]
  have "interpret_floatarith a xs \<noteq> 0" by auto
  thus ?case using Inverse by auto
next
  case (Ln a)
  then obtain l u where approx_Some: "Some (l, u) = approx prec a vs"
    and *: "0 < l"
    by (cases "approx prec a vs") auto
  with approx[OF \<open>bounded_by xs vs\<close> approx_Some]
  have "0 < interpret_floatarith a xs" by auto
  thus ?case using Ln by auto
next
  case (Sqrt a)
  then obtain l u where approx_Some: "Some (l, u) = approx prec a vs"
    and *: "0 < l"
    by (cases "approx prec a vs") auto
  with approx[OF \<open>bounded_by xs vs\<close> approx_Some]
  have "0 < interpret_floatarith a xs" by auto
  thus ?case using Sqrt by auto
next
  case (Power a n)
  thus ?case by (cases n) auto
next
  case (Powr a b)
  from Powr obtain l1 u1 where a: "Some (l1, u1) = approx prec a vs" and pos: "0 < l1"
    by (cases "approx prec a vs") auto
  with approx[OF \<open>bounded_by xs vs\<close> a]
    have "0 < interpret_floatarith a xs" by auto
  with Powr show ?case by auto
next
  case (Floor a)
  then obtain l u where approx_Some: "Some (l, u) = approx prec a vs"
    and "real_of_int \<lfloor>real_of_float u\<rfloor> < real_of_float l" "real_of_float u < real_of_int \<lceil>real_of_float l\<rceil>"
    and "isDERIV x a xs"
    by (cases "approx prec a vs") auto
  with approx[OF \<open>bounded_by xs vs\<close> approx_Some] le_floor_iff
  show ?case
    by (force elim!: Ints_cases)
qed auto

lemma bounded_by_update_var:
  assumes "bounded_by xs vs"
    and "vs ! i = Some (l, u)"
    and bnd: "x \<in> { real_of_float l .. real_of_float u }"
  shows "bounded_by (xs[i := x]) vs"
proof (cases "i < length xs")
  case False
  thus ?thesis
    using \<open>bounded_by xs vs\<close> by auto
next
  case True
  let ?xs = "xs[i := x]"
  from True have "i < length ?xs" by auto
  have "case vs ! j of None \<Rightarrow> True | Some (l, u) \<Rightarrow> ?xs ! j \<in> {real_of_float l .. real_of_float u}"
    if "j < length vs" for j
  proof (cases "vs ! j")
    case None
    then show ?thesis by simp
  next
    case (Some b)
    thus ?thesis
    proof (cases "i = j")
      case True
      thus ?thesis using \<open>vs ! i = Some (l, u)\<close> Some and bnd \<open>i < length ?xs\<close>
        by auto
    next
      case False
      thus ?thesis
        using \<open>bounded_by xs vs\<close>[THEN bounded_byE, OF \<open>j < length vs\<close>] Some by auto
    qed
  qed
  thus ?thesis
    unfolding bounded_by_def by auto
qed

lemma isDERIV_approx':
  assumes "bounded_by xs vs"
    and vs_x: "vs ! x = Some (l, u)"
    and X_in: "X \<in> {real_of_float l .. real_of_float u}"
    and approx: "isDERIV_approx prec x f vs"
  shows "isDERIV x f (xs[x := X])"
proof -
  from bounded_by_update_var[OF \<open>bounded_by xs vs\<close> vs_x X_in] approx
  show ?thesis by (rule isDERIV_approx)
qed

lemma DERIV_approx:
  assumes "n < length xs"
    and bnd: "bounded_by xs vs"
    and isD: "isDERIV_approx prec n f vs"
    and app: "Some (l, u) = approx prec (DERIV_floatarith n f) vs" (is "_ = approx _ ?D _")
  shows "\<exists>(x::real). l \<le> x \<and> x \<le> u \<and>
             DERIV (\<lambda> x. interpret_floatarith f (xs[n := x])) (xs!n) :> x"
         (is "\<exists> x. _ \<and> _ \<and> DERIV (?i f) _ :> _")
proof (rule exI[of _ "?i ?D (xs!n)"], rule conjI[OF _ conjI])
  let "?i f" = "\<lambda>x. interpret_floatarith f (xs[n := x])"
  from approx[OF bnd app]
  show "l \<le> ?i ?D (xs!n)" and "?i ?D (xs!n) \<le> u"
    using \<open>n < length xs\<close> by auto
  from DERIV_floatarith[OF \<open>n < length xs\<close>, of f "xs!n"] isDERIV_approx[OF bnd isD]
  show "DERIV (?i f) (xs!n) :> (?i ?D (xs!n))"
    by simp
qed

lemma lift_bin_aux:
  assumes lift_bin_Some: "Some (l, u) = lift_bin a b f"
  obtains l1 u1 l2 u2
  where "a = Some (l1, u1)"
    and "b = Some (l2, u2)"
    and "f l1 u1 l2 u2 = Some (l, u)"
  using assms by (cases a, simp, cases b, simp, auto)


fun approx_tse where
"approx_tse prec n 0 c k f bs = approx prec f bs" |
"approx_tse prec n (Suc s) c k f bs =
  (if isDERIV_approx prec n f bs then
    lift_bin (approx prec f (bs[n := Some (c,c)]))
             (approx_tse prec n s c (Suc k) (DERIV_floatarith n f) bs)
             (\<lambda> l1 u1 l2 u2. approx prec
                 (Add (Var 0)
                      (Mult (Inverse (Num (Float (int k) 0)))
                                 (Mult (Add (Var (Suc (Suc 0))) (Minus (Num c)))
                                       (Var (Suc 0))))) [Some (l1, u1), Some (l2, u2), bs!n])
  else approx prec f bs)"

lemma bounded_by_Cons:
  assumes bnd: "bounded_by xs vs"
    and x: "x \<in> { real_of_float l .. real_of_float u }"
  shows "bounded_by (x#xs) ((Some (l, u))#vs)"
proof -
  have "case ((Some (l,u))#vs) ! i of Some (l, u) \<Rightarrow> (x#xs)!i \<in> { real_of_float l .. real_of_float u } | None \<Rightarrow> True"
    if *: "i < length ((Some (l, u))#vs)" for i
  proof (cases i)
    case 0
    with x show ?thesis by auto
  next
    case (Suc i)
    with * have "i < length vs" by auto
    from bnd[THEN bounded_byE, OF this]
    show ?thesis unfolding Suc nth_Cons_Suc .
  qed
  thus ?thesis
    by (auto simp add: bounded_by_def)
qed

lemma approx_tse_generic:
  assumes "bounded_by xs vs"
    and bnd_c: "bounded_by (xs[x := c]) vs"
    and "x < length vs" and "x < length xs"
    and bnd_x: "vs ! x = Some (lx, ux)"
    and ate: "Some (l, u) = approx_tse prec x s c k f vs"
  shows "\<exists> n. (\<forall> m < n. \<forall> (z::real) \<in> {lx .. ux}.
      DERIV (\<lambda> y. interpret_floatarith ((DERIV_floatarith x ^^ m) f) (xs[x := y])) z :>
            (interpret_floatarith ((DERIV_floatarith x ^^ (Suc m)) f) (xs[x := z])))
   \<and> (\<forall> (t::real) \<in> {lx .. ux}.  (\<Sum> i = 0..<n. inverse (real (\<Prod> j \<in> {k..<k+i}. j)) *
                  interpret_floatarith ((DERIV_floatarith x ^^ i) f) (xs[x := c]) *
                  (xs!x - c)^i) +
      inverse (real (\<Prod> j \<in> {k..<k+n}. j)) *
      interpret_floatarith ((DERIV_floatarith x ^^ n) f) (xs[x := t]) *
      (xs!x - c)^n \<in> {l .. u})" (is "\<exists> n. ?taylor f k l u n")
  using ate
proof (induct s arbitrary: k f l u)
  case 0
  {
    fix t::real assume "t \<in> {lx .. ux}"
    note bounded_by_update_var[OF \<open>bounded_by xs vs\<close> bnd_x this]
    from approx[OF this 0[unfolded approx_tse.simps]]
    have "(interpret_floatarith f (xs[x := t])) \<in> {l .. u}"
      by (auto simp add: algebra_simps)
  }
  thus ?case by (auto intro!: exI[of _ 0])
next
  case (Suc s)
  show ?case
  proof (cases "isDERIV_approx prec x f vs")
    case False
    note ap = Suc.prems[unfolded approx_tse.simps if_not_P[OF False]]
    {
      fix t::real assume "t \<in> {lx .. ux}"
      note bounded_by_update_var[OF \<open>bounded_by xs vs\<close> bnd_x this]
      from approx[OF this ap]
      have "(interpret_floatarith f (xs[x := t])) \<in> {l .. u}"
        by (auto simp add: algebra_simps)
    }
    thus ?thesis by (auto intro!: exI[of _ 0])
  next
    case True
    with Suc.prems
    obtain l1 u1 l2 u2
      where a: "Some (l1, u1) = approx prec f (vs[x := Some (c,c)])"
        and ate: "Some (l2, u2) = approx_tse prec x s c (Suc k) (DERIV_floatarith x f) vs"
        and final: "Some (l, u) = approx prec
          (Add (Var 0)
               (Mult (Inverse (Num (Float (int k) 0)))
                     (Mult (Add (Var (Suc (Suc 0))) (Minus (Num c)))
                           (Var (Suc 0))))) [Some (l1, u1), Some (l2, u2), vs!x]"
      by (auto elim!: lift_bin_aux)

    from bnd_c \<open>x < length xs\<close>
    have bnd: "bounded_by (xs[x:=c]) (vs[x:= Some (c,c)])"
      by (auto intro!: bounded_by_update)

    from approx[OF this a]
    have f_c: "interpret_floatarith ((DERIV_floatarith x ^^ 0) f) (xs[x := c]) \<in> { l1 .. u1 }"
              (is "?f 0 (real_of_float c) \<in> _")
      by auto

    have funpow_Suc[symmetric]: "(f ^^ Suc n) x = (f ^^ n) (f x)"
      for f :: "'a \<Rightarrow> 'a" and n :: nat and x :: 'a
      by (induct n) auto
    from Suc.hyps[OF ate, unfolded this] obtain n
      where DERIV_hyp: "\<And>m z. \<lbrakk> m < n ; (z::real) \<in> { lx .. ux } \<rbrakk> \<Longrightarrow>
        DERIV (?f (Suc m)) z :> ?f (Suc (Suc m)) z"
      and hyp: "\<forall>t \<in> {real_of_float lx .. real_of_float ux}.
        (\<Sum> i = 0..<n. inverse (real (\<Prod> j \<in> {Suc k..<Suc k + i}. j)) * ?f (Suc i) c * (xs!x - c)^i) +
          inverse (real (\<Prod> j \<in> {Suc k..<Suc k + n}. j)) * ?f (Suc n) t * (xs!x - c)^n \<in> {l2 .. u2}"
          (is "\<forall> t \<in> _. ?X (Suc k) f n t \<in> _")
      by blast

    have DERIV: "DERIV (?f m) z :> ?f (Suc m) z"
      if "m < Suc n" and bnd_z: "z \<in> { lx .. ux }" for m and z::real
    proof (cases m)
      case 0
      with DERIV_floatarith[OF \<open>x < length xs\<close>
        isDERIV_approx'[OF \<open>bounded_by xs vs\<close> bnd_x bnd_z True]]
      show ?thesis by simp
    next
      case (Suc m')
      hence "m' < n"
        using \<open>m < Suc n\<close> by auto
      from DERIV_hyp[OF this bnd_z] show ?thesis
        using Suc by simp
    qed

    have "\<And>k i. k < i \<Longrightarrow> {k ..< i} = insert k {Suc k ..< i}" by auto
    hence prod_head_Suc: "\<And>k i. \<Prod>{k ..< k + Suc i} = k * \<Prod>{Suc k ..< Suc k + i}"
      by auto
    have sum_move0: "\<And>k F. sum F {0..<Suc k} = F 0 + sum (\<lambda> k. F (Suc k)) {0..<k}"
      unfolding sum_shift_bounds_Suc_ivl[symmetric]
      unfolding sum_head_upt_Suc[OF zero_less_Suc] ..
    define C where "C = xs!x - c"

    {
      fix t::real assume t: "t \<in> {lx .. ux}"
      hence "bounded_by [xs!x] [vs!x]"
        using \<open>bounded_by xs vs\<close>[THEN bounded_byE, OF \<open>x < length vs\<close>]
        by (cases "vs!x", auto simp add: bounded_by_def)

      with hyp[THEN bspec, OF t] f_c
      have "bounded_by [?f 0 c, ?X (Suc k) f n t, xs!x] [Some (l1, u1), Some (l2, u2), vs!x]"
        by (auto intro!: bounded_by_Cons)
      from approx[OF this final, unfolded atLeastAtMost_iff[symmetric]]
      have "?X (Suc k) f n t * (xs!x - real_of_float c) * inverse k + ?f 0 c \<in> {l .. u}"
        by (auto simp add: algebra_simps)
      also have "?X (Suc k) f n t * (xs!x - real_of_float c) * inverse (real k) + ?f 0 c =
               (\<Sum> i = 0..<Suc n. inverse (real (\<Prod> j \<in> {k..<k+i}. j)) * ?f i c * (xs!x - c)^i) +
               inverse (real (\<Prod> j \<in> {k..<k+Suc n}. j)) * ?f (Suc n) t * (xs!x - c)^Suc n" (is "_ = ?T")
        unfolding funpow_Suc C_def[symmetric] sum_move0 prod_head_Suc
        by (auto simp add: algebra_simps)
          (simp only: mult.left_commute [of _ "inverse (real k)"] sum_distrib_left [symmetric])
      finally have "?T \<in> {l .. u}" .
    }
    thus ?thesis using DERIV by blast
  qed
qed

lemma prod_fact: "real (\<Prod> {1..<1 + k}) = fact (k :: nat)"
  by (simp add: fact_prod atLeastLessThanSuc_atLeastAtMost)

lemma approx_tse:
  assumes "bounded_by xs vs"
    and bnd_x: "vs ! x = Some (lx, ux)"
    and bnd_c: "real_of_float c \<in> {lx .. ux}"
    and "x < length vs" and "x < length xs"
    and ate: "Some (l, u) = approx_tse prec x s c 1 f vs"
  shows "interpret_floatarith f xs \<in> {l .. u}"
proof -
  define F where [abs_def]: "F n z =
    interpret_floatarith ((DERIV_floatarith x ^^ n) f) (xs[x := z])" for n z
  hence F0: "F 0 = (\<lambda> z. interpret_floatarith f (xs[x := z]))" by auto

  hence "bounded_by (xs[x := c]) vs" and "x < length vs" "x < length xs"
    using \<open>bounded_by xs vs\<close> bnd_x bnd_c \<open>x < length vs\<close> \<open>x < length xs\<close>
    by (auto intro!: bounded_by_update_var)

  from approx_tse_generic[OF \<open>bounded_by xs vs\<close> this bnd_x ate]
  obtain n
    where DERIV: "\<forall> m z. m < n \<and> real_of_float lx \<le> z \<and> z \<le> real_of_float ux \<longrightarrow> DERIV (F m) z :> F (Suc m) z"
    and hyp: "\<And> (t::real). t \<in> {lx .. ux} \<Longrightarrow>
           (\<Sum> j = 0..<n. inverse(fact j) * F j c * (xs!x - c)^j) +
             inverse ((fact n)) * F n t * (xs!x - c)^n
             \<in> {l .. u}" (is "\<And> t. _ \<Longrightarrow> ?taylor t \<in> _")
    unfolding F_def atLeastAtMost_iff[symmetric] prod_fact
    by blast

  have bnd_xs: "xs ! x \<in> { lx .. ux }"
    using \<open>bounded_by xs vs\<close>[THEN bounded_byE, OF \<open>x < length vs\<close>] bnd_x by auto

  show ?thesis
  proof (cases n)
    case 0
    thus ?thesis
      using hyp[OF bnd_xs] unfolding F_def by auto
  next
    case (Suc n')
    show ?thesis
    proof (cases "xs ! x = c")
      case True
      from True[symmetric] hyp[OF bnd_xs] Suc show ?thesis
        unfolding F_def Suc sum_head_upt_Suc[OF zero_less_Suc] sum_shift_bounds_Suc_ivl
        by auto
    next
      case False
      have "lx \<le> real_of_float c" "real_of_float c \<le> ux" "lx \<le> xs!x" "xs!x \<le> ux"
        using Suc bnd_c \<open>bounded_by xs vs\<close>[THEN bounded_byE, OF \<open>x < length vs\<close>] bnd_x by auto
      from taylor[OF zero_less_Suc, of F, OF F0 DERIV[unfolded Suc] this False]
      obtain t::real where t_bnd: "if xs ! x < c then xs ! x < t \<and> t < c else c < t \<and> t < xs ! x"
        and fl_eq: "interpret_floatarith f (xs[x := xs ! x]) =
           (\<Sum>m = 0..<Suc n'. F m c / (fact m) * (xs ! x - c) ^ m) +
           F (Suc n') t / (fact (Suc n')) * (xs ! x - c) ^ Suc n'"
        unfolding atLeast0LessThan by blast

      from t_bnd bnd_xs bnd_c have *: "t \<in> {lx .. ux}"
        by (cases "xs ! x < c") auto

      have "interpret_floatarith f (xs[x := xs ! x]) = ?taylor t"
        unfolding fl_eq Suc by (auto simp add: algebra_simps divide_inverse)
      also have "\<dots> \<in> {l .. u}"
        using * by (rule hyp)
      finally show ?thesis
        by simp
    qed
  qed
qed

fun approx_tse_form' where
"approx_tse_form' prec t f 0 l u cmp =
  (case approx_tse prec 0 t ((l + u) * Float 1 (- 1)) 1 f [Some (l, u)]
     of Some (l, u) \<Rightarrow> cmp l u | None \<Rightarrow> False)" |
"approx_tse_form' prec t f (Suc s) l u cmp =
  (let m = (l + u) * Float 1 (- 1)
   in (if approx_tse_form' prec t f s l m cmp then
      approx_tse_form' prec t f s m u cmp else False))"

lemma approx_tse_form':
  fixes x :: real
  assumes "approx_tse_form' prec t f s l u cmp"
    and "x \<in> {l .. u}"
  shows "\<exists>l' u' ly uy. x \<in> {l' .. u'} \<and> real_of_float l \<le> l' \<and> u' \<le> real_of_float u \<and> cmp ly uy \<and>
    approx_tse prec 0 t ((l' + u') * Float 1 (- 1)) 1 f [Some (l', u')] = Some (ly, uy)"
  using assms
proof (induct s arbitrary: l u)
  case 0
  then obtain ly uy
    where *: "approx_tse prec 0 t ((l + u) * Float 1 (- 1)) 1 f [Some (l, u)] = Some (ly, uy)"
    and **: "cmp ly uy" by (auto elim!: case_optionE)
  with 0 show ?case by auto
next
  case (Suc s)
  let ?m = "(l + u) * Float 1 (- 1)"
  from Suc.prems
  have l: "approx_tse_form' prec t f s l ?m cmp"
    and u: "approx_tse_form' prec t f s ?m u cmp"
    by (auto simp add: Let_def lazy_conj)

  have m_l: "real_of_float l \<le> ?m" and m_u: "?m \<le> real_of_float u"
    unfolding less_eq_float_def using Suc.prems by auto
  with \<open>x \<in> { l .. u }\<close> consider "x \<in> { l .. ?m}" | "x \<in> {?m .. u}"
    by atomize_elim auto
  thus ?case
  proof cases
    case 1
    from Suc.hyps[OF l this]
    obtain l' u' ly uy where
      "x \<in> {l' .. u'} \<and> real_of_float l \<le> l' \<and> real_of_float u' \<le> ?m \<and> cmp ly uy \<and>
        approx_tse prec 0 t ((l' + u') * Float 1 (- 1)) 1 f [Some (l', u')] = Some (ly, uy)"
      by blast
    with m_u show ?thesis
      by (auto intro!: exI)
  next
    case 2
    from Suc.hyps[OF u this]
    obtain l' u' ly uy where
      "x \<in> { l' .. u' } \<and> ?m \<le> real_of_float l' \<and> u' \<le> real_of_float u \<and> cmp ly uy \<and>
        approx_tse prec 0 t ((l' + u') * Float 1 (- 1)) 1 f [Some (l', u')] = Some (ly, uy)"
      by blast
    with m_u show ?thesis
      by (auto intro!: exI)
  qed
qed

lemma approx_tse_form'_less:
  fixes x :: real
  assumes tse: "approx_tse_form' prec t (Add a (Minus b)) s l u (\<lambda> l u. 0 < l)"
    and x: "x \<in> {l .. u}"
  shows "interpret_floatarith b [x] < interpret_floatarith a [x]"
proof -
  from approx_tse_form'[OF tse x]
  obtain l' u' ly uy
    where x': "x \<in> {l' .. u'}"
    and "real_of_float l \<le> real_of_float l'"
    and "real_of_float u' \<le> real_of_float u" and "0 < ly"
    and tse: "approx_tse prec 0 t ((l' + u') * Float 1 (- 1)) 1 (Add a (Minus b)) [Some (l', u')] = Some (ly, uy)"
    by blast

  hence "bounded_by [x] [Some (l', u')]"
    by (auto simp add: bounded_by_def)
  from approx_tse[OF this _ _ _ _ tse[symmetric], of l' u'] x'
  have "ly \<le> interpret_floatarith a [x] - interpret_floatarith b [x]"
    by auto
  from order_less_le_trans[OF _ this, of 0] \<open>0 < ly\<close> show ?thesis
    by auto
qed

lemma approx_tse_form'_le:
  fixes x :: real
  assumes tse: "approx_tse_form' prec t (Add a (Minus b)) s l u (\<lambda> l u. 0 \<le> l)"
    and x: "x \<in> {l .. u}"
  shows "interpret_floatarith b [x] \<le> interpret_floatarith a [x]"
proof -
  from approx_tse_form'[OF tse x]
  obtain l' u' ly uy
    where x': "x \<in> {l' .. u'}"
    and "l \<le> real_of_float l'"
    and "real_of_float u' \<le> u" and "0 \<le> ly"
    and tse: "approx_tse prec 0 t ((l' + u') * Float 1 (- 1)) 1 (Add a (Minus b)) [Some (l', u')] = Some (ly, uy)"
    by blast

  hence "bounded_by [x] [Some (l', u')]" by (auto simp add: bounded_by_def)
  from approx_tse[OF this _ _ _ _ tse[symmetric], of l' u'] x'
  have "ly \<le> interpret_floatarith a [x] - interpret_floatarith b [x]"
    by auto
  from order_trans[OF _ this, of 0] \<open>0 \<le> ly\<close> show ?thesis
    by auto
qed

fun approx_tse_concl where
"approx_tse_concl prec t (Less lf rt) s l u l' u' \<longleftrightarrow>
    approx_tse_form' prec t (Add rt (Minus lf)) s l u' (\<lambda> l u. 0 < l)" |
"approx_tse_concl prec t (LessEqual lf rt) s l u l' u' \<longleftrightarrow>
    approx_tse_form' prec t (Add rt (Minus lf)) s l u' (\<lambda> l u. 0 \<le> l)" |
"approx_tse_concl prec t (AtLeastAtMost x lf rt) s l u l' u' \<longleftrightarrow>
    (if approx_tse_form' prec t (Add x (Minus lf)) s l u' (\<lambda> l u. 0 \<le> l) then
      approx_tse_form' prec t (Add rt (Minus x)) s l u' (\<lambda> l u. 0 \<le> l) else False)" |
"approx_tse_concl prec t (Conj f g) s l u l' u' \<longleftrightarrow>
    approx_tse_concl prec t f s l u l' u' \<and> approx_tse_concl prec t g s l u l' u'" |
"approx_tse_concl prec t (Disj f g) s l u l' u' \<longleftrightarrow>
    approx_tse_concl prec t f s l u l' u' \<or> approx_tse_concl prec t g s l u l' u'" |
"approx_tse_concl _ _ _ _ _ _ _ _ \<longleftrightarrow> False"

definition
  "approx_tse_form prec t s f =
    (case f of
      Bound x a b f \<Rightarrow>
        x = Var 0 \<and>
        (case (approx prec a [None], approx prec b [None]) of
          (Some (l, u), Some (l', u')) \<Rightarrow> approx_tse_concl prec t f s l u l' u'
        | _ \<Rightarrow> False)
    | _ \<Rightarrow> False)"

lemma approx_tse_form:
  assumes "approx_tse_form prec t s f"
  shows "interpret_form f [x]"
proof (cases f)
  case f_def: (Bound i a b f')
  with assms obtain l u l' u'
    where a: "approx prec a [None] = Some (l, u)"
    and b: "approx prec b [None] = Some (l', u')"
    unfolding approx_tse_form_def by (auto elim!: case_optionE)

  from f_def assms have "i = Var 0"
    unfolding approx_tse_form_def by auto
  hence i: "interpret_floatarith i [x] = x" by auto

  {
    let ?f = "\<lambda>z. interpret_floatarith z [x]"
    assume "?f i \<in> { ?f a .. ?f b }"
    with approx[OF _ a[symmetric], of "[x]"] approx[OF _ b[symmetric], of "[x]"]
    have bnd: "x \<in> { l .. u'}" unfolding bounded_by_def i by auto

    have "interpret_form f' [x]"
      using assms[unfolded f_def]
    proof (induct f')
      case (Less lf rt)
      with a b
      have "approx_tse_form' prec t (Add rt (Minus lf)) s l u' (\<lambda> l u. 0 < l)"
        unfolding approx_tse_form_def by auto
      from approx_tse_form'_less[OF this bnd]
      show ?case using Less by auto
    next
      case (LessEqual lf rt)
      with f_def a b assms
      have "approx_tse_form' prec t (Add rt (Minus lf)) s l u' (\<lambda> l u. 0 \<le> l)"
        unfolding approx_tse_form_def by auto
      from approx_tse_form'_le[OF this bnd]
      show ?case using LessEqual by auto
    next
      case (AtLeastAtMost x lf rt)
      with f_def a b assms
      have "approx_tse_form' prec t (Add rt (Minus x)) s l u' (\<lambda> l u. 0 \<le> l)"
        and "approx_tse_form' prec t (Add x (Minus lf)) s l u' (\<lambda> l u. 0 \<le> l)"
        unfolding approx_tse_form_def lazy_conj by (auto split: if_split_asm)
      from approx_tse_form'_le[OF this(1) bnd] approx_tse_form'_le[OF this(2) bnd]
      show ?case using AtLeastAtMost by auto
    qed (auto simp: f_def approx_tse_form_def elim!: case_optionE)
  }
  thus ?thesis unfolding f_def by auto
qed (insert assms, auto simp add: approx_tse_form_def)

text \<open>@{term approx_form_eval} is only used for the {\tt value}-command.\<close>

fun approx_form_eval :: "nat \<Rightarrow> form \<Rightarrow> (float * float) option list \<Rightarrow> (float * float) option list" where
"approx_form_eval prec (Bound (Var n) a b f) bs =
   (case (approx prec a bs, approx prec b bs)
   of (Some (l, _), Some (_, u)) \<Rightarrow> approx_form_eval prec f (bs[n := Some (l, u)])
    | _ \<Rightarrow> bs)" |
"approx_form_eval prec (Assign (Var n) a f) bs =
   (case (approx prec a bs)
   of (Some (l, u)) \<Rightarrow> approx_form_eval prec f (bs[n := Some (l, u)])
    | _ \<Rightarrow> bs)" |
"approx_form_eval prec (Less a b) bs = bs @ [approx prec a bs, approx prec b bs]" |
"approx_form_eval prec (LessEqual a b) bs = bs @ [approx prec a bs, approx prec b bs]" |
"approx_form_eval prec (AtLeastAtMost x a b) bs =
   bs @ [approx prec x bs, approx prec a bs, approx prec b bs]" |
"approx_form_eval _ _ bs = bs"


subsection \<open>Implement proof method \texttt{approximation}\<close>

oracle approximation_oracle = \<open>fn (thy, t) =>
let
  fun bad t = error ("Bad term: " ^ Syntax.string_of_term_global thy t);

  fun term_of_bool true = @{term True}
    | term_of_bool false = @{term False};

  val mk_int = HOLogic.mk_number @{typ int} o @{code integer_of_int};
  fun dest_int (@{term int_of_integer} $ j) = @{code int_of_integer} (snd (HOLogic.dest_number j))
    | dest_int i = @{code int_of_integer} (snd (HOLogic.dest_number i));

  fun term_of_float (@{code Float} (k, l)) =
    @{term Float} $ mk_int k $ mk_int l;

  fun term_of_float_float_option NONE = @{term "None :: (float \<times> float) option"}
    | term_of_float_float_option (SOME ff) = @{term "Some :: float \<times> float \<Rightarrow> _"}
        $ HOLogic.mk_prod (apply2 term_of_float ff);

  val term_of_float_float_option_list =
    HOLogic.mk_list @{typ "(float \<times> float) option"} o map term_of_float_float_option;

  fun nat_of_term t = @{code nat_of_integer}
    (HOLogic.dest_nat t handle TERM _ => snd (HOLogic.dest_number t));

  fun float_of_term (@{term Float} $ k $ l) =
        @{code Float} (dest_int k, dest_int l)
    | float_of_term t = bad t;

  fun floatarith_of_term (@{term Add} $ a $ b) = @{code Add} (floatarith_of_term a, floatarith_of_term b)
    | floatarith_of_term (@{term Minus} $ a) = @{code Minus} (floatarith_of_term a)
    | floatarith_of_term (@{term Mult} $ a $ b) = @{code Mult} (floatarith_of_term a, floatarith_of_term b)
    | floatarith_of_term (@{term Inverse} $ a) = @{code Inverse} (floatarith_of_term a)
    | floatarith_of_term (@{term Cos} $ a) = @{code Cos} (floatarith_of_term a)
    | floatarith_of_term (@{term Arctan} $ a) = @{code Arctan} (floatarith_of_term a)
    | floatarith_of_term (@{term Abs} $ a) = @{code Abs} (floatarith_of_term a)
    | floatarith_of_term (@{term Max} $ a $ b) = @{code Max} (floatarith_of_term a, floatarith_of_term b)
    | floatarith_of_term (@{term Min} $ a $ b) = @{code Min} (floatarith_of_term a, floatarith_of_term b)
    | floatarith_of_term @{term Pi} = @{code Pi}
    | floatarith_of_term (@{term Sqrt} $ a) = @{code Sqrt} (floatarith_of_term a)
    | floatarith_of_term (@{term Exp} $ a) = @{code Exp} (floatarith_of_term a)
    | floatarith_of_term (@{term Powr} $ a $ b) = @{code Powr} (floatarith_of_term a, floatarith_of_term b)
    | floatarith_of_term (@{term Ln} $ a) = @{code Ln} (floatarith_of_term a)
    | floatarith_of_term (@{term Power} $ a $ n) =
        @{code Power} (floatarith_of_term a, nat_of_term n)
    | floatarith_of_term (@{term Floor} $ a) = @{code Floor} (floatarith_of_term a)
    | floatarith_of_term (@{term Var} $ n) = @{code Var} (nat_of_term n)
    | floatarith_of_term (@{term Num} $ m) = @{code Num} (float_of_term m)
    | floatarith_of_term t = bad t;

  fun form_of_term (@{term Bound} $ a $ b $ c $ p) = @{code Bound}
        (floatarith_of_term a, floatarith_of_term b, floatarith_of_term c, form_of_term p)
    | form_of_term (@{term Assign} $ a $ b $ p) = @{code Assign}
        (floatarith_of_term a, floatarith_of_term b, form_of_term p)
    | form_of_term (@{term Less} $ a $ b) = @{code Less}
        (floatarith_of_term a, floatarith_of_term b)
    | form_of_term (@{term LessEqual} $ a $ b) = @{code LessEqual}
        (floatarith_of_term a, floatarith_of_term b)
    | form_of_term (@{term Conj} $ a $ b) = @{code Conj}
        (form_of_term a, form_of_term b)
    | form_of_term (@{term Disj} $ a $ b) = @{code Disj}
        (form_of_term a, form_of_term b)
    | form_of_term (@{term AtLeastAtMost} $ a $ b $ c) = @{code AtLeastAtMost}
        (floatarith_of_term a, floatarith_of_term b, floatarith_of_term c)
    | form_of_term t = bad t;

  fun float_float_option_of_term @{term "None :: (float \<times> float) option"} = NONE
    | float_float_option_of_term (@{term "Some :: float \<times> float \<Rightarrow> _"} $ ff) =
        SOME (apply2 float_of_term (HOLogic.dest_prod ff))
    | float_float_option_of_term (@{term approx'} $ n $ a $ ffs) = @{code approx'}
        (nat_of_term n) (floatarith_of_term a) (float_float_option_list_of_term ffs)
    | float_float_option_of_term t = bad t
  and float_float_option_list_of_term
        (@{term "replicate :: _ \<Rightarrow> (float \<times> float) option \<Rightarrow> _"} $ n $ @{term "None :: (float \<times> float) option"}) =
          @{code replicate} (nat_of_term n) NONE
    | float_float_option_list_of_term (@{term approx_form_eval} $ n $ p $ ffs) =
        @{code approx_form_eval} (nat_of_term n) (form_of_term p) (float_float_option_list_of_term ffs)
    | float_float_option_list_of_term t = map float_float_option_of_term
        (HOLogic.dest_list t);

  val nat_list_of_term = map nat_of_term o HOLogic.dest_list ;

  fun bool_of_term (@{term approx_form} $ n $ p $ ffs $ ms) = @{code approx_form}
        (nat_of_term n) (form_of_term p) (float_float_option_list_of_term ffs) (nat_list_of_term ms)
    | bool_of_term (@{term approx_tse_form} $ m $ n $ q $ p) =
        @{code approx_tse_form} (nat_of_term m) (nat_of_term n) (nat_of_term q) (form_of_term p)
    | bool_of_term t = bad t;

  fun eval t = case fastype_of t
   of @{typ bool} =>
        (term_of_bool o bool_of_term) t
    | @{typ "(float \<times> float) option"} =>
        (term_of_float_float_option o float_float_option_of_term) t
    | @{typ "(float \<times> float) option list"} =>
        (term_of_float_float_option_list o float_float_option_list_of_term) t
    | _ => bad t;

  val normalize = eval o Envir.beta_norm o Envir.eta_long [];

in Thm.global_cterm_of thy (Logic.mk_equals (t, normalize t)) end
\<close>

lemma intervalE: "a \<le> x \<and> x \<le> b \<Longrightarrow> \<lbrakk> x \<in> { a .. b } \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by auto

lemma meta_eqE: "x \<equiv> a \<Longrightarrow> \<lbrakk> x = a \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by auto

named_theorems approximation_preproc

lemma approximation_preproc_floatarith[approximation_preproc]:
  "0 = real_of_float 0"
  "1 = real_of_float 1"
  "0 = Float 0 0"
  "1 = Float 1 0"
  "numeral a = Float (numeral a) 0"
  "numeral a = real_of_float (numeral a)"
  "x - y = x + - y"
  "x / y = x * inverse y"
  "ceiling x = - floor (- x)"
  "log x y = ln y * inverse (ln x)"
  "sin x = cos (pi / 2 - x)"
  "tan x = sin x / cos x"
  by (simp_all add: inverse_eq_divide ceiling_def log_def sin_cos_eq tan_def real_of_float_eq)

lemma approximation_preproc_int[approximation_preproc]:
  "real_of_int 0 = real_of_float 0"
  "real_of_int 1 = real_of_float 1"
  "real_of_int (i + j) = real_of_int i + real_of_int j"
  "real_of_int (- i) = - real_of_int i"
  "real_of_int (i - j) = real_of_int i - real_of_int j"
  "real_of_int (i * j) = real_of_int i * real_of_int j"
  "real_of_int (i div j) = real_of_int (floor (real_of_int i / real_of_int j))"
  "real_of_int (min i j) = min (real_of_int i) (real_of_int j)"
  "real_of_int (max i j) = max (real_of_int i) (real_of_int j)"
  "real_of_int (abs i) = abs (real_of_int i)"
  "real_of_int (i ^ n) = (real_of_int i) ^ n"
  "real_of_int (numeral a) = real_of_float (numeral a)"
  "i mod j = i - i div j * j"
  "i = j \<longleftrightarrow> real_of_int i = real_of_int j"
  "i \<le> j \<longleftrightarrow> real_of_int i \<le> real_of_int j"
  "i < j \<longleftrightarrow> real_of_int i < real_of_int j"
  "i \<in> {j .. k} \<longleftrightarrow> real_of_int i \<in> {real_of_int j .. real_of_int k}"
  by (simp_all add: floor_divide_of_int_eq minus_div_mult_eq_mod [symmetric])

lemma approximation_preproc_nat[approximation_preproc]:
  "real 0 = real_of_float 0"
  "real 1 = real_of_float 1"
  "real (i + j) = real i + real j"
  "real (i - j) = max (real i - real j) 0"
  "real (i * j) = real i * real j"
  "real (i div j) = real_of_int (floor (real i / real j))"
  "real (min i j) = min (real i) (real j)"
  "real (max i j) = max (real i) (real j)"
  "real (i ^ n) = (real i) ^ n"
  "real (numeral a) = real_of_float (numeral a)"
  "i mod j = i - i div j * j"
  "n = m \<longleftrightarrow> real n = real m"
  "n \<le> m \<longleftrightarrow> real n \<le> real m"
  "n < m \<longleftrightarrow> real n < real m"
  "n \<in> {m .. l} \<longleftrightarrow> real n \<in> {real m .. real l}"
  by (simp_all add: real_div_nat_eq_floor_of_divide minus_div_mult_eq_mod [symmetric])

ML_file "approximation.ML"

method_setup approximation = \<open>
  let
    val free =
      Args.context -- Args.term >> (fn (_, Free (n, _)) => n | (ctxt, t) =>
        error ("Bad free variable: " ^ Syntax.string_of_term ctxt t));
  in
    Scan.lift Parse.nat --
    Scan.optional (Scan.lift (Args.$$$ "splitting" |-- Args.colon)
      |-- Parse.and_list' (free --| Scan.lift (Args.$$$ "=") -- Scan.lift Parse.nat)) [] --
    Scan.option (Scan.lift (Args.$$$ "taylor" |-- Args.colon) |--
    (free |-- Scan.lift (Args.$$$ "=") |-- Scan.lift Parse.nat)) >>
    (fn ((prec, splitting), taylor) => fn ctxt =>
      SIMPLE_METHOD' (Approximation.approximation_tac prec splitting taylor ctxt))
  end
\<close> "real number approximation"


section "Quickcheck Generator"

lemma approximation_preproc_push_neg[approximation_preproc]:
  fixes a b::real
  shows
    "\<not> (a < b) \<longleftrightarrow> b \<le> a"
    "\<not> (a \<le> b) \<longleftrightarrow> b < a"
    "\<not> (a = b) \<longleftrightarrow> b < a \<or> a < b"
    "\<not> (p \<and> q) \<longleftrightarrow> \<not> p \<or> \<not> q"
    "\<not> (p \<or> q) \<longleftrightarrow> \<not> p \<and> \<not> q"
    "\<not> \<not> q \<longleftrightarrow> q"
  by auto

ML_file "approximation_generator.ML"
setup "Approximation_Generator.setup"

end
