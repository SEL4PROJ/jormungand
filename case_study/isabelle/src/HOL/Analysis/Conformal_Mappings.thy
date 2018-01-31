section \<open>Conformal Mappings. Consequences of Cauchy's integral theorem.\<close>

text\<open>By John Harrison et al.  Ported from HOL Light by L C Paulson (2016)\<close>

text\<open>Also Cauchy's residue theorem by Wenda Li (2016)\<close>

theory Conformal_Mappings
imports "~~/src/HOL/Analysis/Cauchy_Integral_Theorem"

begin

subsection\<open>Cauchy's inequality and more versions of Liouville\<close>

lemma Cauchy_higher_deriv_bound:
    assumes holf: "f holomorphic_on (ball z r)"
        and contf: "continuous_on (cball z r) f"
        and "0 < r" and "0 < n"
        and fin : "\<And>w. w \<in> ball z r \<Longrightarrow> f w \<in> ball y B0"
      shows "norm ((deriv ^^ n) f z) \<le> (fact n) * B0 / r^n"
proof -
  have "0 < B0" using \<open>0 < r\<close> fin [of z]
    by (metis ball_eq_empty ex_in_conv fin not_less)
  have le_B0: "\<And>w. cmod (w - z) \<le> r \<Longrightarrow> cmod (f w - y) \<le> B0"
    apply (rule continuous_on_closure_norm_le [of "ball z r" "\<lambda>w. f w - y"])
    apply (auto simp: \<open>0 < r\<close>  dist_norm norm_minus_commute)
    apply (rule continuous_intros contf)+
    using fin apply (simp add: dist_commute dist_norm less_eq_real_def)
    done
  have "(deriv ^^ n) f z = (deriv ^^ n) (\<lambda>w. f w) z - (deriv ^^ n) (\<lambda>w. y) z"
    using \<open>0 < n\<close> by simp
  also have "... = (deriv ^^ n) (\<lambda>w. f w - y) z"
    by (rule higher_deriv_diff [OF holf, symmetric]) (auto simp: \<open>0 < r\<close>)
  finally have "(deriv ^^ n) f z = (deriv ^^ n) (\<lambda>w. f w - y) z" .
  have contf': "continuous_on (cball z r) (\<lambda>u. f u - y)"
    by (rule contf continuous_intros)+
  have holf': "(\<lambda>u. (f u - y)) holomorphic_on (ball z r)"
    by (simp add: holf holomorphic_on_diff)
  define a where "a = (2 * pi)/(fact n)"
  have "0 < a"  by (simp add: a_def)
  have "B0/r^(Suc n)*2 * pi * r = a*((fact n)*B0/r^n)"
    using \<open>0 < r\<close> by (simp add: a_def divide_simps)
  have der_dif: "(deriv ^^ n) (\<lambda>w. f w - y) z = (deriv ^^ n) f z"
    using \<open>0 < r\<close> \<open>0 < n\<close>
    by (auto simp: higher_deriv_diff [OF holf holomorphic_on_const])
  have "norm ((2 * of_real pi * \<i>)/(fact n) * (deriv ^^ n) (\<lambda>w. f w - y) z)
        \<le> (B0/r^(Suc n)) * (2 * pi * r)"
    apply (rule has_contour_integral_bound_circlepath [of "(\<lambda>u. (f u - y)/(u - z)^(Suc n))" _ z])
    using Cauchy_has_contour_integral_higher_derivative_circlepath [OF contf' holf']
    using \<open>0 < B0\<close> \<open>0 < r\<close>
    apply (auto simp: norm_divide norm_mult norm_power divide_simps le_B0)
    done
  then show ?thesis
    using \<open>0 < r\<close>
    by (auto simp: norm_divide norm_mult norm_power field_simps der_dif le_B0)
qed

proposition Cauchy_inequality:
    assumes holf: "f holomorphic_on (ball \<xi> r)"
        and contf: "continuous_on (cball \<xi> r) f"
        and "0 < r"
        and nof: "\<And>x. norm(\<xi>-x) = r \<Longrightarrow> norm(f x) \<le> B"
      shows "norm ((deriv ^^ n) f \<xi>) \<le> (fact n) * B / r^n"
proof -
  obtain x where "norm (\<xi>-x) = r"
    by (metis abs_of_nonneg add_diff_cancel_left' \<open>0 < r\<close> diff_add_cancel
                 dual_order.strict_implies_order norm_of_real)
  then have "0 \<le> B"
    by (metis nof norm_not_less_zero not_le order_trans)
  have  "((\<lambda>u. f u / (u - \<xi>) ^ Suc n) has_contour_integral (2 * pi) * \<i> / fact n * (deriv ^^ n) f \<xi>)
         (circlepath \<xi> r)"
    apply (rule Cauchy_has_contour_integral_higher_derivative_circlepath [OF contf holf])
    using \<open>0 < r\<close> by simp
  then have "norm ((2 * pi * \<i>)/(fact n) * (deriv ^^ n) f \<xi>) \<le> (B / r^(Suc n)) * (2 * pi * r)"
    apply (rule has_contour_integral_bound_circlepath)
    using \<open>0 \<le> B\<close> \<open>0 < r\<close>
    apply (simp_all add: norm_divide norm_power nof frac_le norm_minus_commute del: power_Suc)
    done
  then show ?thesis using \<open>0 < r\<close>
    by (simp add: norm_divide norm_mult field_simps)
qed

proposition Liouville_polynomial:
    assumes holf: "f holomorphic_on UNIV"
        and nof: "\<And>z. A \<le> norm z \<Longrightarrow> norm(f z) \<le> B * norm z ^ n"
      shows "f \<xi> = (\<Sum>k\<le>n. (deriv^^k) f 0 / fact k * \<xi> ^ k)"
proof (cases rule: le_less_linear [THEN disjE])
  assume "B \<le> 0"
  then have "\<And>z. A \<le> norm z \<Longrightarrow> norm(f z) = 0"
    by (metis nof less_le_trans zero_less_mult_iff neqE norm_not_less_zero norm_power not_le)
  then have f0: "(f \<longlongrightarrow> 0) at_infinity"
    using Lim_at_infinity by force
  then have [simp]: "f = (\<lambda>w. 0)"
    using Liouville_weak [OF holf, of 0]
    by (simp add: eventually_at_infinity f0) meson
  show ?thesis by simp
next
  assume "0 < B"
  have "((\<lambda>k. (deriv ^^ k) f 0 / (fact k) * (\<xi> - 0)^k) sums f \<xi>)"
    apply (rule holomorphic_power_series [where r = "norm \<xi> + 1"])
    using holf holomorphic_on_subset apply auto
    done
  then have sumsf: "((\<lambda>k. (deriv ^^ k) f 0 / (fact k) * \<xi>^k) sums f \<xi>)" by simp
  have "(deriv ^^ k) f 0 / fact k * \<xi> ^ k = 0" if "k>n" for k
  proof (cases "(deriv ^^ k) f 0 = 0")
    case True then show ?thesis by simp
  next
    case False
    define w where "w = complex_of_real (fact k * B / cmod ((deriv ^^ k) f 0) + (\<bar>A\<bar> + 1))"
    have "1 \<le> abs (fact k * B / cmod ((deriv ^^ k) f 0) + (\<bar>A\<bar> + 1))"
      using \<open>0 < B\<close> by simp
    then have wge1: "1 \<le> norm w"
      by (metis norm_of_real w_def)
    then have "w \<noteq> 0" by auto
    have kB: "0 < fact k * B"
      using \<open>0 < B\<close> by simp
    then have "0 \<le> fact k * B / cmod ((deriv ^^ k) f 0)"
      by simp
    then have wgeA: "A \<le> cmod w"
      by (simp only: w_def norm_of_real)
    have "fact k * B / cmod ((deriv ^^ k) f 0) < abs (fact k * B / cmod ((deriv ^^ k) f 0) + (\<bar>A\<bar> + 1))"
      using \<open>0 < B\<close> by simp
    then have wge: "fact k * B / cmod ((deriv ^^ k) f 0) < norm w"
      by (metis norm_of_real w_def)
    then have "fact k * B / norm w < cmod ((deriv ^^ k) f 0)"
      using False by (simp add: divide_simps mult.commute split: if_split_asm)
    also have "... \<le> fact k * (B * norm w ^ n) / norm w ^ k"
      apply (rule Cauchy_inequality)
         using holf holomorphic_on_subset apply force
        using holf holomorphic_on_imp_continuous_on holomorphic_on_subset apply blast
       using \<open>w \<noteq> 0\<close> apply (simp add:)
       by (metis nof wgeA dist_0_norm dist_norm)
    also have "... = fact k * (B * 1 / cmod w ^ (k-n))"
      apply (simp only: mult_cancel_left times_divide_eq_right [symmetric])
      using \<open>k>n\<close> \<open>w \<noteq> 0\<close> \<open>0 < B\<close> apply (simp add: divide_simps semiring_normalization_rules)
      done
    also have "... = fact k * B / cmod w ^ (k-n)"
      by simp
    finally have "fact k * B / cmod w < fact k * B / cmod w ^ (k - n)" .
    then have "1 / cmod w < 1 / cmod w ^ (k - n)"
      by (metis kB divide_inverse inverse_eq_divide mult_less_cancel_left_pos)
    then have "cmod w ^ (k - n) < cmod w"
      by (metis frac_le le_less_trans norm_ge_zero norm_one not_less order_refl wge1 zero_less_one)
    with self_le_power [OF wge1] have False
      by (meson diff_is_0_eq not_gr0 not_le that)
    then show ?thesis by blast
  qed
  then have "(deriv ^^ (k + Suc n)) f 0 / fact (k + Suc n) * \<xi> ^ (k + Suc n) = 0" for k
    using not_less_eq by blast
  then have "(\<lambda>i. (deriv ^^ (i + Suc n)) f 0 / fact (i + Suc n) * \<xi> ^ (i + Suc n)) sums 0"
    by (rule sums_0)
  with sums_split_initial_segment [OF sumsf, where n = "Suc n"]
  show ?thesis
    using atLeast0AtMost lessThan_Suc_atMost sums_unique2 by fastforce
qed

text\<open>Every bounded entire function is a constant function.\<close>
theorem Liouville_theorem:
    assumes holf: "f holomorphic_on UNIV"
        and bf: "bounded (range f)"
    obtains c where "\<And>z. f z = c"
proof -
  obtain B where "\<And>z. cmod (f z) \<le> B"
    by (meson bf bounded_pos rangeI)
  then show ?thesis
    using Liouville_polynomial [OF holf, of 0 B 0, simplified] that by blast
qed



text\<open>A holomorphic function f has only isolated zeros unless f is 0.\<close>

proposition powser_0_nonzero:
  fixes a :: "nat \<Rightarrow> 'a::{real_normed_field,banach}"
  assumes r: "0 < r"
      and sm: "\<And>x. norm (x - \<xi>) < r \<Longrightarrow> (\<lambda>n. a n * (x - \<xi>) ^ n) sums (f x)"
      and [simp]: "f \<xi> = 0"
      and m0: "a m \<noteq> 0" and "m>0"
  obtains s where "0 < s" and "\<And>z. z \<in> cball \<xi> s - {\<xi>} \<Longrightarrow> f z \<noteq> 0"
proof -
  have "r \<le> conv_radius a"
    using sm sums_summable by (auto simp: le_conv_radius_iff [where \<xi>=\<xi>])
  obtain m where am: "a m \<noteq> 0" and az [simp]: "(\<And>n. n<m \<Longrightarrow> a n = 0)"
    apply (rule_tac m = "LEAST n. a n \<noteq> 0" in that)
    using m0
    apply (rule LeastI2)
    apply (fastforce intro:  dest!: not_less_Least)+
    done
  define b where "b i = a (i+m) / a m" for i
  define g where "g x = suminf (\<lambda>i. b i * (x - \<xi>) ^ i)" for x
  have [simp]: "b 0 = 1"
    by (simp add: am b_def)
  { fix x::'a
    assume "norm (x - \<xi>) < r"
    then have "(\<lambda>n. (a m * (x - \<xi>)^m) * (b n * (x - \<xi>)^n)) sums (f x)"
      using am az sm sums_zero_iff_shift [of m "(\<lambda>n. a n * (x - \<xi>) ^ n)" "f x"]
      by (simp add: b_def monoid_mult_class.power_add algebra_simps)
    then have "x \<noteq> \<xi> \<Longrightarrow> (\<lambda>n. b n * (x - \<xi>)^n) sums (f x / (a m * (x - \<xi>)^m))"
      using am by (simp add: sums_mult_D)
  } note bsums = this
  then have  "norm (x - \<xi>) < r \<Longrightarrow> summable (\<lambda>n. b n * (x - \<xi>)^n)" for x
    using sums_summable by (cases "x=\<xi>") auto
  then have "r \<le> conv_radius b"
    by (simp add: le_conv_radius_iff [where \<xi>=\<xi>])
  then have "r/2 < conv_radius b"
    using not_le order_trans r by fastforce
  then have "continuous_on (cball \<xi> (r/2)) g"
    using powser_continuous_suminf [of "r/2" b \<xi>] by (simp add: g_def)
  then obtain s where "s>0"  "\<And>x. \<lbrakk>norm (x - \<xi>) \<le> s; norm (x - \<xi>) \<le> r/2\<rbrakk> \<Longrightarrow> dist (g x) (g \<xi>) < 1/2"
    apply (rule continuous_onE [where x=\<xi> and e = "1/2"])
    using r apply (auto simp: norm_minus_commute dist_norm)
    done
  moreover have "g \<xi> = 1"
    by (simp add: g_def)
  ultimately have gnz: "\<And>x. \<lbrakk>norm (x - \<xi>) \<le> s; norm (x - \<xi>) \<le> r/2\<rbrakk> \<Longrightarrow> (g x) \<noteq> 0"
    by fastforce
  have "f x \<noteq> 0" if "x \<noteq> \<xi>" "norm (x - \<xi>) \<le> s" "norm (x - \<xi>) \<le> r/2" for x
    using bsums [of x] that gnz [of x]
    apply (auto simp: g_def)
    using r sums_iff by fastforce
  then show ?thesis
    apply (rule_tac s="min s (r/2)" in that)
    using \<open>0 < r\<close> \<open>0 < s\<close> by (auto simp: dist_commute dist_norm)
qed

proposition isolated_zeros:
  assumes holf: "f holomorphic_on S"
      and "open S" "connected S" "\<xi> \<in> S" "f \<xi> = 0" "\<beta> \<in> S" "f \<beta> \<noteq> 0"
  obtains r where "0 < r" "ball \<xi> r \<subseteq> S" "\<And>z. z \<in> ball \<xi> r - {\<xi>} \<Longrightarrow> f z \<noteq> 0"
proof -
  obtain r where "0 < r" and r: "ball \<xi> r \<subseteq> S"
    using \<open>open S\<close> \<open>\<xi> \<in> S\<close> open_contains_ball_eq by blast
  have powf: "((\<lambda>n. (deriv ^^ n) f \<xi> / (fact n) * (z - \<xi>)^n) sums f z)" if "z \<in> ball \<xi> r" for z
    apply (rule holomorphic_power_series [OF _ that])
    apply (rule holomorphic_on_subset [OF holf r])
    done
  obtain m where m: "(deriv ^^ m) f \<xi> / (fact m) \<noteq> 0"
    using holomorphic_fun_eq_0_on_connected [OF holf \<open>open S\<close> \<open>connected S\<close> _ \<open>\<xi> \<in> S\<close> \<open>\<beta> \<in> S\<close>] \<open>f \<beta> \<noteq> 0\<close>
    by auto
  then have "m \<noteq> 0" using assms(5) funpow_0 by fastforce
  obtain s where "0 < s" and s: "\<And>z. z \<in> cball \<xi> s - {\<xi>} \<Longrightarrow> f z \<noteq> 0"
    apply (rule powser_0_nonzero [OF \<open>0 < r\<close> powf \<open>f \<xi> = 0\<close> m])
    using \<open>m \<noteq> 0\<close> by (auto simp: dist_commute dist_norm)
  have "0 < min r s"  by (simp add: \<open>0 < r\<close> \<open>0 < s\<close>)
  then show ?thesis
    apply (rule that)
    using r s by auto
qed


proposition analytic_continuation:
  assumes holf: "f holomorphic_on S"
      and S: "open S" "connected S"
      and "U \<subseteq> S" "\<xi> \<in> S"
      and "\<xi> islimpt U"
      and fU0 [simp]: "\<And>z. z \<in> U \<Longrightarrow> f z = 0"
      and "w \<in> S"
    shows "f w = 0"
proof -
  obtain e where "0 < e" and e: "cball \<xi> e \<subseteq> S"
    using \<open>open S\<close> \<open>\<xi> \<in> S\<close> open_contains_cball_eq by blast
  define T where "T = cball \<xi> e \<inter> U"
  have contf: "continuous_on (closure T) f"
    by (metis T_def closed_cball closure_minimal e holf holomorphic_on_imp_continuous_on
              holomorphic_on_subset inf.cobounded1)
  have fT0 [simp]: "\<And>x. x \<in> T \<Longrightarrow> f x = 0"
    by (simp add: T_def)
  have "\<And>r. \<lbrakk>\<forall>e>0. \<exists>x'\<in>U. x' \<noteq> \<xi> \<and> dist x' \<xi> < e; 0 < r\<rbrakk> \<Longrightarrow> \<exists>x'\<in>cball \<xi> e \<inter> U. x' \<noteq> \<xi> \<and> dist x' \<xi> < r"
    by (metis \<open>0 < e\<close> IntI dist_commute less_eq_real_def mem_cball min_less_iff_conj)
  then have "\<xi> islimpt T" using \<open>\<xi> islimpt U\<close>
    by (auto simp: T_def islimpt_approachable)
  then have "\<xi> \<in> closure T"
    by (simp add: closure_def)
  then have "f \<xi> = 0"
    by (auto simp: continuous_constant_on_closure [OF contf])
  show ?thesis
    apply (rule ccontr)
    apply (rule isolated_zeros [OF holf \<open>open S\<close> \<open>connected S\<close> \<open>\<xi> \<in> S\<close> \<open>f \<xi> = 0\<close> \<open>w \<in> S\<close>], assumption)
    by (metis open_ball \<open>\<xi> islimpt T\<close> centre_in_ball fT0 insertE insert_Diff islimptE)
qed


subsection\<open>Open mapping theorem\<close>

lemma holomorphic_contract_to_zero:
  assumes contf: "continuous_on (cball \<xi> r) f"
      and holf: "f holomorphic_on ball \<xi> r"
      and "0 < r"
      and norm_less: "\<And>z. norm(\<xi> - z) = r \<Longrightarrow> norm(f \<xi>) < norm(f z)"
  obtains z where "z \<in> ball \<xi> r" "f z = 0"
proof -
  { assume fnz: "\<And>w. w \<in> ball \<xi> r \<Longrightarrow> f w \<noteq> 0"
    then have "0 < norm (f \<xi>)"
      by (simp add: \<open>0 < r\<close>)
    have fnz': "\<And>w. w \<in> cball \<xi> r \<Longrightarrow> f w \<noteq> 0"
      by (metis norm_less dist_norm fnz less_eq_real_def mem_ball mem_cball norm_not_less_zero norm_zero)
    have "frontier(cball \<xi> r) \<noteq> {}"
      using \<open>0 < r\<close> by simp
    define g where [abs_def]: "g z = inverse (f z)" for z
    have contg: "continuous_on (cball \<xi> r) g"
      unfolding g_def using contf continuous_on_inverse fnz' by blast
    have holg: "g holomorphic_on ball \<xi> r"
      unfolding g_def using fnz holf holomorphic_on_inverse by blast
    have "frontier (cball \<xi> r) \<subseteq> cball \<xi> r"
      by (simp add: subset_iff)
    then have contf': "continuous_on (frontier (cball \<xi> r)) f"
          and contg': "continuous_on (frontier (cball \<xi> r)) g"
      by (blast intro: contf contg continuous_on_subset)+
    have froc: "frontier(cball \<xi> r) \<noteq> {}"
      using \<open>0 < r\<close> by simp
    moreover have "continuous_on (frontier (cball \<xi> r)) (norm o f)"
      using contf' continuous_on_compose continuous_on_norm_id by blast
    ultimately obtain w where w: "w \<in> frontier(cball \<xi> r)"
                          and now: "\<And>x. x \<in> frontier(cball \<xi> r) \<Longrightarrow> norm (f w) \<le> norm (f x)"
      apply (rule bexE [OF continuous_attains_inf [OF compact_frontier [OF compact_cball]]])
      apply (simp add:)
      done
    then have fw: "0 < norm (f w)"
      by (simp add: fnz')
    have "continuous_on (frontier (cball \<xi> r)) (norm o g)"
      using contg' continuous_on_compose continuous_on_norm_id by blast
    then obtain v where v: "v \<in> frontier(cball \<xi> r)"
               and nov: "\<And>x. x \<in> frontier(cball \<xi> r) \<Longrightarrow> norm (g v) \<ge> norm (g x)"
      apply (rule bexE [OF continuous_attains_sup [OF compact_frontier [OF compact_cball] froc]])
      apply (simp add:)
      done
    then have fv: "0 < norm (f v)"
      by (simp add: fnz')
    have "norm ((deriv ^^ 0) g \<xi>) \<le> fact 0 * norm (g v) / r ^ 0"
      by (rule Cauchy_inequality [OF holg contg \<open>0 < r\<close>]) (simp add: dist_norm nov)
    then have "cmod (g \<xi>) \<le> norm (g v)"
      by simp
    with w have wr: "norm (\<xi> - w) = r" and nfw: "norm (f w) \<le> norm (f \<xi>)"
      apply (simp_all add: dist_norm)
      by (metis \<open>0 < cmod (f \<xi>)\<close> g_def less_imp_inverse_less norm_inverse not_le now order_trans v)
    with fw have False
      using norm_less by force
  }
  with that show ?thesis by blast
qed


theorem open_mapping_thm:
  assumes holf: "f holomorphic_on S"
      and S: "open S" "connected S"
      and "open U" "U \<subseteq> S"
      and fne: "~ f constant_on S"
    shows "open (f ` U)"
proof -
  have *: "open (f ` U)"
          if "U \<noteq> {}" and U: "open U" "connected U" and "f holomorphic_on U" and fneU: "\<And>x. \<exists>y \<in> U. f y \<noteq> x"
          for U
  proof (clarsimp simp: open_contains_ball)
    fix \<xi> assume \<xi>: "\<xi> \<in> U"
    show "\<exists>e>0. ball (f \<xi>) e \<subseteq> f ` U"
    proof -
      have hol: "(\<lambda>z. f z - f \<xi>) holomorphic_on U"
        by (rule holomorphic_intros that)+
      obtain s where "0 < s" and sbU: "ball \<xi> s \<subseteq> U"
                 and sne: "\<And>z. z \<in> ball \<xi> s - {\<xi>} \<Longrightarrow> (\<lambda>z. f z - f \<xi>) z \<noteq> 0"
        using isolated_zeros [OF hol U \<xi>]  by (metis fneU right_minus_eq)
      obtain r where "0 < r" and r: "cball \<xi> r \<subseteq> ball \<xi> s"
        apply (rule_tac r="s/2" in that)
        using \<open>0 < s\<close> by auto
      have "cball \<xi> r \<subseteq> U"
        using sbU r by blast
      then have frsbU: "frontier (cball \<xi> r) \<subseteq> U"
        using Diff_subset frontier_def order_trans by fastforce
      then have cof: "compact (frontier(cball \<xi> r))"
        by blast
      have frne: "frontier (cball \<xi> r) \<noteq> {}"
        using \<open>0 < r\<close> by auto
      have contfr: "continuous_on (frontier (cball \<xi> r)) (\<lambda>z. norm (f z - f \<xi>))"
        apply (rule continuous_on_compose2 [OF Complex_Analysis_Basics.continuous_on_norm_id])
        using hol frsbU holomorphic_on_imp_continuous_on holomorphic_on_subset by blast+
      obtain w where "norm (\<xi> - w) = r"
                 and w: "(\<And>z. norm (\<xi> - z) = r \<Longrightarrow> norm (f w - f \<xi>) \<le> norm(f z - f \<xi>))"
        apply (rule bexE [OF continuous_attains_inf [OF cof frne contfr]])
        apply (simp add: dist_norm)
        done
      moreover define \<epsilon> where "\<epsilon> \<equiv> norm (f w - f \<xi>) / 3"
      ultimately have "0 < \<epsilon>"
        using \<open>0 < r\<close> dist_complex_def r sne by auto
      have "ball (f \<xi>) \<epsilon> \<subseteq> f ` U"
      proof
        fix \<gamma>
        assume \<gamma>: "\<gamma> \<in> ball (f \<xi>) \<epsilon>"
        have *: "cmod (\<gamma> - f \<xi>) < cmod (\<gamma> - f z)" if "cmod (\<xi> - z) = r" for z
        proof -
          have lt: "cmod (f w - f \<xi>) / 3 < cmod (\<gamma> - f z)"
            using w [OF that] \<gamma>
            using dist_triangle2 [of "f \<xi>" "\<gamma>"  "f z"] dist_triangle2 [of "f \<xi>" "f z" \<gamma>]
            by (simp add: \<epsilon>_def dist_norm norm_minus_commute)
          show ?thesis
            by (metis \<epsilon>_def dist_commute dist_norm less_trans lt mem_ball \<gamma>)
       qed
       have "continuous_on (cball \<xi> r) (\<lambda>z. \<gamma> - f z)"
          apply (rule continuous_intros)+
          using \<open>cball \<xi> r \<subseteq> U\<close> \<open>f holomorphic_on U\<close>
          apply (blast intro: continuous_on_subset holomorphic_on_imp_continuous_on)
          done
        moreover have "(\<lambda>z. \<gamma> - f z) holomorphic_on ball \<xi> r"
          apply (rule holomorphic_intros)+
          apply (metis \<open>cball \<xi> r \<subseteq> U\<close> \<open>f holomorphic_on U\<close> holomorphic_on_subset interior_cball interior_subset)
          done
        ultimately obtain z where "z \<in> ball \<xi> r" "\<gamma> - f z = 0"
          apply (rule holomorphic_contract_to_zero)
          apply (blast intro!: \<open>0 < r\<close> *)+
          done
        then show "\<gamma> \<in> f ` U"
          using \<open>cball \<xi> r \<subseteq> U\<close> by fastforce
      qed
      then show ?thesis using  \<open>0 < \<epsilon>\<close> by blast
    qed
  qed
  have "open (f ` X)" if "X \<in> components U" for X
  proof -
    have holfU: "f holomorphic_on U"
      using \<open>U \<subseteq> S\<close> holf holomorphic_on_subset by blast
    have "X \<noteq> {}"
      using that by (simp add: in_components_nonempty)
    moreover have "open X"
      using that \<open>open U\<close> open_components by auto
    moreover have "connected X"
      using that in_components_maximal by blast
    moreover have "f holomorphic_on X"
      by (meson that holfU holomorphic_on_subset in_components_maximal)
    moreover have "\<exists>y\<in>X. f y \<noteq> x" for x
    proof (rule ccontr)
      assume not: "\<not> (\<exists>y\<in>X. f y \<noteq> x)"
      have "X \<subseteq> S"
        using \<open>U \<subseteq> S\<close> in_components_subset that by blast
      obtain w where w: "w \<in> X" using \<open>X \<noteq> {}\<close> by blast
      have wis: "w islimpt X"
        using w \<open>open X\<close> interior_eq by auto
      have hol: "(\<lambda>z. f z - x) holomorphic_on S"
        by (simp add: holf holomorphic_on_diff)
      with fne [unfolded constant_on_def] analytic_continuation [OF hol S \<open>X \<subseteq> S\<close> _ wis]
           not \<open>X \<subseteq> S\<close> w
      show False by auto
    qed
    ultimately show ?thesis
      by (rule *)
  qed
  then have "open (f ` \<Union>components U)"
    by (metis (no_types, lifting) imageE image_Union open_Union)
  then show ?thesis
    by force
qed


text\<open>No need for @{term S} to be connected. But the nonconstant condition is stronger.\<close>
corollary open_mapping_thm2:
  assumes holf: "f holomorphic_on S"
      and S: "open S"
      and "open U" "U \<subseteq> S"
      and fnc: "\<And>X. \<lbrakk>open X; X \<subseteq> S; X \<noteq> {}\<rbrakk> \<Longrightarrow> ~ f constant_on X"
    shows "open (f ` U)"
proof -
  have "S = \<Union>(components S)" by simp
  with \<open>U \<subseteq> S\<close> have "U = (\<Union>C \<in> components S. C \<inter> U)" by auto
  then have "f ` U = (\<Union>C \<in> components S. f ` (C \<inter> U))"
    using image_UN by fastforce
  moreover
  { fix C assume "C \<in> components S"
    with S \<open>C \<in> components S\<close> open_components in_components_connected
    have C: "open C" "connected C" by auto
    have "C \<subseteq> S"
      by (metis \<open>C \<in> components S\<close> in_components_maximal)
    have nf: "\<not> f constant_on C"
      apply (rule fnc)
      using C \<open>C \<subseteq> S\<close> \<open>C \<in> components S\<close> in_components_nonempty by auto
    have "f holomorphic_on C"
      by (metis holf holomorphic_on_subset \<open>C \<subseteq> S\<close>)
    then have "open (f ` (C \<inter> U))"
      apply (rule open_mapping_thm [OF _ C _ _ nf])
      apply (simp add: C \<open>open U\<close> open_Int, blast)
      done
  } ultimately show ?thesis
    by force
qed

corollary open_mapping_thm3:
  assumes holf: "f holomorphic_on S"
      and "open S" and injf: "inj_on f S"
    shows  "open (f ` S)"
apply (rule open_mapping_thm2 [OF holf])
using assms
apply (simp_all add:)
using injective_not_constant subset_inj_on by blast



subsection\<open>Maximum Modulus Principle\<close>

text\<open>If @{term f} is holomorphic, then its norm (modulus) cannot exhibit a true local maximum that is
   properly within the domain of @{term f}.\<close>

proposition maximum_modulus_principle:
  assumes holf: "f holomorphic_on S"
      and S: "open S" "connected S"
      and "open U" "U \<subseteq> S" "\<xi> \<in> U"
      and no: "\<And>z. z \<in> U \<Longrightarrow> norm(f z) \<le> norm(f \<xi>)"
    shows "f constant_on S"
proof (rule ccontr)
  assume "\<not> f constant_on S"
  then have "open (f ` U)"
    using open_mapping_thm assms by blast
  moreover have "~ open (f ` U)"
  proof -
    have "\<exists>t. cmod (f \<xi> - t) < e \<and> t \<notin> f ` U" if "0 < e" for e
      apply (rule_tac x="if 0 < Re(f \<xi>) then f \<xi> + (e/2) else f \<xi> - (e/2)" in exI)
      using that
      apply (simp add: dist_norm)
      apply (fastforce simp: cmod_Re_le_iff dest!: no dest: sym)
      done
    then show ?thesis
      unfolding open_contains_ball by (metis \<open>\<xi> \<in> U\<close> contra_subsetD dist_norm imageI mem_ball)
  qed
  ultimately show False
    by blast
qed


proposition maximum_modulus_frontier:
  assumes holf: "f holomorphic_on (interior S)"
      and contf: "continuous_on (closure S) f"
      and bos: "bounded S"
      and leB: "\<And>z. z \<in> frontier S \<Longrightarrow> norm(f z) \<le> B"
      and "\<xi> \<in> S"
    shows "norm(f \<xi>) \<le> B"
proof -
  have "compact (closure S)" using bos
    by (simp add: bounded_closure compact_eq_bounded_closed)
  moreover have "continuous_on (closure S) (cmod \<circ> f)"
    using contf continuous_on_compose continuous_on_norm_id by blast
  ultimately obtain z where zin: "z \<in> closure S" and z: "\<And>y. y \<in> closure S \<Longrightarrow> (cmod \<circ> f) y \<le> (cmod \<circ> f) z"
    using continuous_attains_sup [of "closure S" "norm o f"] \<open>\<xi> \<in> S\<close> by auto
  then consider "z \<in> frontier S" | "z \<in> interior S" using frontier_def by auto
  then have "norm(f z) \<le> B"
  proof cases
    case 1 then show ?thesis using leB by blast
  next
    case 2
    have zin: "z \<in> connected_component_set (interior S) z"
      by (simp add: 2)
    have "f constant_on (connected_component_set (interior S) z)"
      apply (rule maximum_modulus_principle [OF _ _ _ _ _ zin])
      apply (metis connected_component_subset holf holomorphic_on_subset)
      apply (simp_all add: open_connected_component)
      by (metis closure_subset comp_eq_dest_lhs  interior_subset subsetCE z connected_component_in)
    then obtain c where c: "\<And>w. w \<in> connected_component_set (interior S) z \<Longrightarrow> f w = c"
      by (auto simp: constant_on_def)
    have "f ` closure(connected_component_set (interior S) z) \<subseteq> {c}"
      apply (rule image_closure_subset)
      apply (meson closure_mono connected_component_subset contf continuous_on_subset interior_subset)
      using c
      apply auto
      done
    then have cc: "\<And>w. w \<in> closure(connected_component_set (interior S) z) \<Longrightarrow> f w = c" by blast
    have "frontier(connected_component_set (interior S) z) \<noteq> {}"
      apply (simp add: frontier_eq_empty)
      by (metis "2" bos bounded_interior connected_component_eq_UNIV connected_component_refl not_bounded_UNIV)
    then obtain w where w: "w \<in> frontier(connected_component_set (interior S) z)"
       by auto
    then have "norm (f z) = norm (f w)"  by (simp add: "2" c cc frontier_def)
    also have "... \<le> B"
      apply (rule leB)
      using w
using frontier_interior_subset frontier_of_connected_component_subset by blast
    finally show ?thesis .
  qed
  then show ?thesis
    using z \<open>\<xi> \<in> S\<close> closure_subset by fastforce
qed

corollary maximum_real_frontier:
  assumes holf: "f holomorphic_on (interior S)"
      and contf: "continuous_on (closure S) f"
      and bos: "bounded S"
      and leB: "\<And>z. z \<in> frontier S \<Longrightarrow> Re(f z) \<le> B"
      and "\<xi> \<in> S"
    shows "Re(f \<xi>) \<le> B"
using maximum_modulus_frontier [of "exp o f" S "exp B"]
      Transcendental.continuous_on_exp holomorphic_on_compose holomorphic_on_exp assms
by auto


subsection\<open>Factoring out a zero according to its order\<close>

lemma holomorphic_factor_order_of_zero:
  assumes holf: "f holomorphic_on S"
      and os: "open S"
      and "\<xi> \<in> S" "0 < n"
      and dnz: "(deriv ^^ n) f \<xi> \<noteq> 0"
      and dfz: "\<And>i. \<lbrakk>0 < i; i < n\<rbrakk> \<Longrightarrow> (deriv ^^ i) f \<xi> = 0"
   obtains g r where "0 < r"
                "g holomorphic_on ball \<xi> r"
                "\<And>w. w \<in> ball \<xi> r \<Longrightarrow> f w - f \<xi> = (w - \<xi>)^n * g w"
                "\<And>w. w \<in> ball \<xi> r \<Longrightarrow> g w \<noteq> 0"
proof -
  obtain r where "r>0" and r: "ball \<xi> r \<subseteq> S" using assms by (blast elim!: openE)
  then have holfb: "f holomorphic_on ball \<xi> r"
    using holf holomorphic_on_subset by blast
  define g where "g w = suminf (\<lambda>i. (deriv ^^ (i + n)) f \<xi> / (fact(i + n)) * (w - \<xi>)^i)" for w
  have sumsg: "(\<lambda>i. (deriv ^^ (i + n)) f \<xi> / (fact(i + n)) * (w - \<xi>)^i) sums g w"
   and feq: "f w - f \<xi> = (w - \<xi>)^n * g w"
       if w: "w \<in> ball \<xi> r" for w
  proof -
    define powf where "powf = (\<lambda>i. (deriv ^^ i) f \<xi>/(fact i) * (w - \<xi>)^i)"
    have sing: "{..<n} - {i. powf i = 0} = (if f \<xi> = 0 then {} else {0})"
      unfolding powf_def using \<open>0 < n\<close> dfz by (auto simp: dfz; metis funpow_0 not_gr0)
    have "powf sums f w"
      unfolding powf_def by (rule holomorphic_power_series [OF holfb w])
    moreover have "(\<Sum>i<n. powf i) = f \<xi>"
      apply (subst Groups_Big.comm_monoid_add_class.sum.setdiff_irrelevant [symmetric])
      apply (simp add:)
      apply (simp only: dfz sing)
      apply (simp add: powf_def)
      done
    ultimately have fsums: "(\<lambda>i. powf (i+n)) sums (f w - f \<xi>)"
      using w sums_iff_shift' by metis
    then have *: "summable (\<lambda>i. (w - \<xi>) ^ n * ((deriv ^^ (i + n)) f \<xi> * (w - \<xi>) ^ i / fact (i + n)))"
      unfolding powf_def using sums_summable
      by (auto simp: power_add mult_ac)
    have "summable (\<lambda>i. (deriv ^^ (i + n)) f \<xi> * (w - \<xi>) ^ i / fact (i + n))"
    proof (cases "w=\<xi>")
      case False then show ?thesis
        using summable_mult [OF *, of "1 / (w - \<xi>) ^ n"] by (simp add:)
    next
      case True then show ?thesis
        by (auto simp: Power.semiring_1_class.power_0_left intro!: summable_finite [of "{0}"]
                 split: if_split_asm)
    qed
    then show sumsg: "(\<lambda>i. (deriv ^^ (i + n)) f \<xi> / (fact(i + n)) * (w - \<xi>)^i) sums g w"
      by (simp add: summable_sums_iff g_def)
    show "f w - f \<xi> = (w - \<xi>)^n * g w"
      apply (rule sums_unique2)
      apply (rule fsums [unfolded powf_def])
      using sums_mult [OF sumsg, of "(w - \<xi>) ^ n"]
      by (auto simp: power_add mult_ac)
  qed
  then have holg: "g holomorphic_on ball \<xi> r"
    by (meson sumsg power_series_holomorphic)
  then have contg: "continuous_on (ball \<xi> r) g"
    by (blast intro: holomorphic_on_imp_continuous_on)
  have "g \<xi> \<noteq> 0"
    using dnz unfolding g_def
    by (subst suminf_finite [of "{0}"]) auto
  obtain d where "0 < d" and d: "\<And>w. w \<in> ball \<xi> d \<Longrightarrow> g w \<noteq> 0"
    apply (rule exE [OF continuous_on_avoid [OF contg _ \<open>g \<xi> \<noteq> 0\<close>]])
    using \<open>0 < r\<close>
    apply force
    by (metis \<open>0 < r\<close> less_trans mem_ball not_less_iff_gr_or_eq)
  show ?thesis
    apply (rule that [where g=g and r ="min r d"])
    using \<open>0 < r\<close> \<open>0 < d\<close> holg
    apply (auto simp: feq holomorphic_on_subset subset_ball d)
    done
qed


lemma holomorphic_factor_order_of_zero_strong:
  assumes holf: "f holomorphic_on S" "open S"  "\<xi> \<in> S" "0 < n"
      and "(deriv ^^ n) f \<xi> \<noteq> 0"
      and "\<And>i. \<lbrakk>0 < i; i < n\<rbrakk> \<Longrightarrow> (deriv ^^ i) f \<xi> = 0"
   obtains g r where "0 < r"
                "g holomorphic_on ball \<xi> r"
                "\<And>w. w \<in> ball \<xi> r \<Longrightarrow> f w - f \<xi> = ((w - \<xi>) * g w) ^ n"
                "\<And>w. w \<in> ball \<xi> r \<Longrightarrow> g w \<noteq> 0"
proof -
  obtain g r where "0 < r"
               and holg: "g holomorphic_on ball \<xi> r"
               and feq: "\<And>w. w \<in> ball \<xi> r \<Longrightarrow> f w - f \<xi> = (w - \<xi>)^n * g w"
               and gne: "\<And>w. w \<in> ball \<xi> r \<Longrightarrow> g w \<noteq> 0"
    by (auto intro: holomorphic_factor_order_of_zero [OF assms])
  have con: "continuous_on (ball \<xi> r) (\<lambda>z. deriv g z / g z)"
    by (rule continuous_intros) (auto simp: gne holg holomorphic_deriv holomorphic_on_imp_continuous_on)
  have cd: "\<And>x. dist \<xi> x < r \<Longrightarrow> (\<lambda>z. deriv g z / g z) field_differentiable at x"
    apply (rule derivative_intros)+
    using holg mem_ball apply (blast intro: holomorphic_deriv holomorphic_on_imp_differentiable_at)
    apply (metis Topology_Euclidean_Space.open_ball at_within_open holg holomorphic_on_def mem_ball)
    using gne mem_ball by blast
  obtain h where h: "\<And>x. x \<in> ball \<xi> r \<Longrightarrow> (h has_field_derivative deriv g x / g x) (at x)"
    apply (rule exE [OF holomorphic_convex_primitive [of "ball \<xi> r" "{}" "\<lambda>z. deriv g z / g z"]])
    apply (auto simp: con cd)
    apply (metis open_ball at_within_open mem_ball)
    done
  then have "continuous_on (ball \<xi> r) h"
    by (metis open_ball holomorphic_on_imp_continuous_on holomorphic_on_open)
  then have con: "continuous_on (ball \<xi> r) (\<lambda>x. exp (h x) / g x)"
    by (auto intro!: continuous_intros simp add: holg holomorphic_on_imp_continuous_on gne)
  have 0: "dist \<xi> x < r \<Longrightarrow> ((\<lambda>x. exp (h x) / g x) has_field_derivative 0) (at x)" for x
    apply (rule h derivative_eq_intros | simp)+
    apply (rule DERIV_deriv_iff_field_differentiable [THEN iffD2])
    using holg apply (auto simp: holomorphic_on_imp_differentiable_at gne h)
    done
  obtain c where c: "\<And>x. x \<in> ball \<xi> r \<Longrightarrow> exp (h x) / g x = c"
    by (rule DERIV_zero_connected_constant [of "ball \<xi> r" "{}" "\<lambda>x. exp(h x) / g x"]) (auto simp: con 0)
  have hol: "(\<lambda>z. exp ((Ln (inverse c) + h z) / of_nat n)) holomorphic_on ball \<xi> r"
    apply (rule holomorphic_on_compose [unfolded o_def, where g = exp])
    apply (rule holomorphic_intros)+
    using h holomorphic_on_open apply blast
    apply (rule holomorphic_intros)+
    using \<open>0 < n\<close> apply (simp add:)
    apply (rule holomorphic_intros)+
    done
  show ?thesis
    apply (rule that [where g="\<lambda>z. exp((Ln(inverse c) + h z)/n)" and r =r])
    using \<open>0 < r\<close> \<open>0 < n\<close>
    apply (auto simp: feq power_mult_distrib exp_divide_power_eq c [symmetric])
    apply (rule hol)
    apply (simp add: Transcendental.exp_add gne)
    done
qed


lemma
  fixes k :: "'a::wellorder"
  assumes a_def: "a == LEAST x. P x" and P: "P k"
  shows def_LeastI: "P a" and def_Least_le: "a \<le> k"
unfolding a_def
by (rule LeastI Least_le; rule P)+

lemma holomorphic_factor_zero_nonconstant:
  assumes holf: "f holomorphic_on S" and S: "open S" "connected S"
      and "\<xi> \<in> S" "f \<xi> = 0"
      and nonconst: "\<And>c. \<exists>z \<in> S. f z \<noteq> c"
   obtains g r n
      where "0 < n"  "0 < r"  "ball \<xi> r \<subseteq> S"
            "g holomorphic_on ball \<xi> r"
            "\<And>w. w \<in> ball \<xi> r \<Longrightarrow> f w = (w - \<xi>)^n * g w"
            "\<And>w. w \<in> ball \<xi> r \<Longrightarrow> g w \<noteq> 0"
proof (cases "\<forall>n>0. (deriv ^^ n) f \<xi> = 0")
  case True then show ?thesis
    using holomorphic_fun_eq_const_on_connected [OF holf S _ \<open>\<xi> \<in> S\<close>] nonconst by auto
next
  case False
  then obtain n0 where "n0 > 0" and n0: "(deriv ^^ n0) f \<xi> \<noteq> 0" by blast
  obtain r0 where "r0 > 0" "ball \<xi> r0 \<subseteq> S" using S openE \<open>\<xi> \<in> S\<close> by auto
  define n where "n \<equiv> LEAST n. (deriv ^^ n) f \<xi> \<noteq> 0"
  have n_ne: "(deriv ^^ n) f \<xi> \<noteq> 0"
    by (rule def_LeastI [OF n_def]) (rule n0)
  then have "0 < n" using \<open>f \<xi> = 0\<close>
    using funpow_0 by fastforce
  have n_min: "\<And>k. k < n \<Longrightarrow> (deriv ^^ k) f \<xi> = 0"
    using def_Least_le [OF n_def] not_le by blast
  then obtain g r1
    where  "0 < r1" "g holomorphic_on ball \<xi> r1"
           "\<And>w. w \<in> ball \<xi> r1 \<Longrightarrow> f w = (w - \<xi>) ^ n * g w"
           "\<And>w. w \<in> ball \<xi> r1 \<Longrightarrow> g w \<noteq> 0"
    by (auto intro: holomorphic_factor_order_of_zero [OF holf \<open>open S\<close> \<open>\<xi> \<in> S\<close> \<open>n > 0\<close> n_ne] simp: \<open>f \<xi> = 0\<close>)
  then show ?thesis
    apply (rule_tac g=g and r="min r0 r1" and n=n in that)
    using \<open>0 < n\<close> \<open>0 < r0\<close> \<open>0 < r1\<close> \<open>ball \<xi> r0 \<subseteq> S\<close>
    apply (auto simp: subset_ball intro: holomorphic_on_subset)
    done
qed


lemma holomorphic_lower_bound_difference:
  assumes holf: "f holomorphic_on S" and S: "open S" "connected S"
      and "\<xi> \<in> S" and "\<phi> \<in> S"
      and fne: "f \<phi> \<noteq> f \<xi>"
   obtains k n r
      where "0 < k"  "0 < r"
            "ball \<xi> r \<subseteq> S"
            "\<And>w. w \<in> ball \<xi> r \<Longrightarrow> k * norm(w - \<xi>)^n \<le> norm(f w - f \<xi>)"
proof -
  define n where "n = (LEAST n. 0 < n \<and> (deriv ^^ n) f \<xi> \<noteq> 0)"
  obtain n0 where "0 < n0" and n0: "(deriv ^^ n0) f \<xi> \<noteq> 0"
    using fne holomorphic_fun_eq_const_on_connected [OF holf S] \<open>\<xi> \<in> S\<close> \<open>\<phi> \<in> S\<close> by blast
  then have "0 < n" and n_ne: "(deriv ^^ n) f \<xi> \<noteq> 0"
    unfolding n_def by (metis (mono_tags, lifting) LeastI)+
  have n_min: "\<And>k. \<lbrakk>0 < k; k < n\<rbrakk> \<Longrightarrow> (deriv ^^ k) f \<xi> = 0"
    unfolding n_def by (blast dest: not_less_Least)
  then obtain g r
    where "0 < r" and holg: "g holomorphic_on ball \<xi> r"
      and fne: "\<And>w. w \<in> ball \<xi> r \<Longrightarrow> f w - f \<xi> = (w - \<xi>) ^ n * g w"
      and gnz: "\<And>w. w \<in> ball \<xi> r \<Longrightarrow> g w \<noteq> 0"
      by (auto intro: holomorphic_factor_order_of_zero  [OF holf \<open>open S\<close> \<open>\<xi> \<in> S\<close> \<open>n > 0\<close> n_ne])
  obtain e where "e>0" and e: "ball \<xi> e \<subseteq> S" using assms by (blast elim!: openE)
  then have holfb: "f holomorphic_on ball \<xi> e"
    using holf holomorphic_on_subset by blast
  define d where "d = (min e r) / 2"
  have "0 < d" using \<open>0 < r\<close> \<open>0 < e\<close> by (simp add: d_def)
  have "d < r"
    using \<open>0 < r\<close> by (auto simp: d_def)
  then have cbb: "cball \<xi> d \<subseteq> ball \<xi> r"
    by (auto simp: cball_subset_ball_iff)
  then have "g holomorphic_on cball \<xi> d"
    by (rule holomorphic_on_subset [OF holg])
  then have "closed (g ` cball \<xi> d)"
    by (simp add: compact_imp_closed compact_continuous_image holomorphic_on_imp_continuous_on)
  moreover have "g ` cball \<xi> d \<noteq> {}"
    using \<open>0 < d\<close> by auto
  ultimately obtain x where x: "x \<in> g ` cball \<xi> d" and "\<And>y. y \<in> g ` cball \<xi> d \<Longrightarrow> dist 0 x \<le> dist 0 y"
    by (rule distance_attains_inf) blast
  then have leg: "\<And>w. w \<in> cball \<xi> d \<Longrightarrow> norm x \<le> norm (g w)"
    by auto
  have "ball \<xi> d \<subseteq> cball \<xi> d" by auto
  also have "... \<subseteq> ball \<xi> e" using \<open>0 < d\<close> d_def by auto
  also have "... \<subseteq> S" by (rule e)
  finally have dS: "ball \<xi> d \<subseteq> S" .
  moreover have "x \<noteq> 0" using gnz x \<open>d < r\<close> by auto
  ultimately show ?thesis
    apply (rule_tac k="norm x" and n=n and r=d in that)
    using \<open>d < r\<close> leg
    apply (auto simp: \<open>0 < d\<close> fne norm_mult norm_power algebra_simps mult_right_mono)
    done
qed

lemma
  assumes holf: "f holomorphic_on (S - {\<xi>})" and \<xi>: "\<xi> \<in> interior S"
    shows holomorphic_on_extend_lim:
          "(\<exists>g. g holomorphic_on S \<and> (\<forall>z \<in> S - {\<xi>}. g z = f z)) \<longleftrightarrow>
           ((\<lambda>z. (z - \<xi>) * f z) \<longlongrightarrow> 0) (at \<xi>)"
          (is "?P = ?Q")
     and holomorphic_on_extend_bounded:
          "(\<exists>g. g holomorphic_on S \<and> (\<forall>z \<in> S - {\<xi>}. g z = f z)) \<longleftrightarrow>
           (\<exists>B. eventually (\<lambda>z. norm(f z) \<le> B) (at \<xi>))"
          (is "?P = ?R")
proof -
  obtain \<delta> where "0 < \<delta>" and \<delta>: "ball \<xi> \<delta> \<subseteq> S"
    using \<xi> mem_interior by blast
  have "?R" if holg: "g holomorphic_on S" and gf: "\<And>z. z \<in> S - {\<xi>} \<Longrightarrow> g z = f z" for g
  proof -
    have *: "\<forall>\<^sub>F z in at \<xi>. dist (g z) (g \<xi>) < 1 \<longrightarrow> cmod (f z) \<le> cmod (g \<xi>) + 1"
      apply (simp add: eventually_at)
      apply (rule_tac x="\<delta>" in exI)
      using \<delta> \<open>0 < \<delta>\<close>
      apply (clarsimp simp:)
      apply (drule_tac c=x in subsetD)
      apply (simp add: dist_commute)
      by (metis DiffI add.commute diff_le_eq dist_norm gf le_less_trans less_eq_real_def norm_triangle_ineq2 singletonD)
    have "continuous_on (interior S) g"
      by (meson continuous_on_subset holg holomorphic_on_imp_continuous_on interior_subset)
    then have "\<And>x. x \<in> interior S \<Longrightarrow> (g \<longlongrightarrow> g x) (at x)"
      using continuous_on_interior continuous_within holg holomorphic_on_imp_continuous_on by blast
    then have "(g \<longlongrightarrow> g \<xi>) (at \<xi>)"
      by (simp add: \<xi>)
    then show ?thesis
      apply (rule_tac x="norm(g \<xi>) + 1" in exI)
      apply (rule eventually_mp [OF * tendstoD [where e=1]], auto)
      done
  qed
  moreover have "?Q" if "\<forall>\<^sub>F z in at \<xi>. cmod (f z) \<le> B" for B
    by (rule lim_null_mult_right_bounded [OF _ that]) (simp add: LIM_zero)
  moreover have "?P" if "(\<lambda>z. (z - \<xi>) * f z) \<midarrow>\<xi>\<rightarrow> 0"
  proof -
    define h where [abs_def]: "h z = (z - \<xi>)^2 * f z" for z
    have h0: "(h has_field_derivative 0) (at \<xi>)"
      apply (simp add: h_def Derivative.DERIV_within_iff)
      apply (rule Lim_transform_within [OF that, of 1])
      apply (auto simp: divide_simps power2_eq_square)
      done
    have holh: "h holomorphic_on S"
    proof (simp add: holomorphic_on_def, clarify)
      fix z assume "z \<in> S"
      show "h field_differentiable at z within S"
      proof (cases "z = \<xi>")
        case True then show ?thesis
          using field_differentiable_at_within field_differentiable_def h0 by blast
      next
        case False
        then have "f field_differentiable at z within S"
          using holomorphic_onD [OF holf, of z] \<open>z \<in> S\<close>
          unfolding field_differentiable_def DERIV_within_iff
          by (force intro: exI [where x="dist \<xi> z"] elim: Lim_transform_within_set [unfolded eventually_at])
        then show ?thesis
          by (simp add: h_def power2_eq_square derivative_intros)
      qed
    qed
    define g where [abs_def]: "g z = (if z = \<xi> then deriv h \<xi> else (h z - h \<xi>) / (z - \<xi>))" for z
    have holg: "g holomorphic_on S"
      unfolding g_def by (rule pole_lemma [OF holh \<xi>])
    show ?thesis
      apply (rule_tac x="\<lambda>z. if z = \<xi> then deriv g \<xi> else (g z - g \<xi>)/(z - \<xi>)" in exI)
      apply (rule conjI)
      apply (rule pole_lemma [OF holg \<xi>])
      apply (auto simp: g_def power2_eq_square divide_simps)
      using h0 apply (simp add: h0 DERIV_imp_deriv h_def power2_eq_square)
      done
  qed
  ultimately show "?P = ?Q" and "?P = ?R"
    by meson+
qed


proposition pole_at_infinity:
  assumes holf: "f holomorphic_on UNIV" and lim: "((inverse o f) \<longlongrightarrow> l) at_infinity"
  obtains a n where "\<And>z. f z = (\<Sum>i\<le>n. a i * z^i)"
proof (cases "l = 0")
  case False
  with tendsto_inverse [OF lim] show ?thesis
    apply (rule_tac a="(\<lambda>n. inverse l)" and n=0 in that)
    apply (simp add: Liouville_weak [OF holf, of "inverse l"])
    done
next
  case True
  then have [simp]: "l = 0" .
  show ?thesis
  proof (cases "\<exists>r. 0 < r \<and> (\<forall>z \<in> ball 0 r - {0}. f(inverse z) \<noteq> 0)")
    case True
      then obtain r where "0 < r" and r: "\<And>z. z \<in> ball 0 r - {0} \<Longrightarrow> f(inverse z) \<noteq> 0"
             by auto
      have 1: "inverse \<circ> f \<circ> inverse holomorphic_on ball 0 r - {0}"
        by (rule holomorphic_on_compose holomorphic_intros holomorphic_on_subset [OF holf] | force simp: r)+
      have 2: "0 \<in> interior (ball 0 r)"
        using \<open>0 < r\<close> by simp
      have "\<exists>B. 0<B \<and> eventually (\<lambda>z. cmod ((inverse \<circ> f \<circ> inverse) z) \<le> B) (at 0)"
        apply (rule exI [where x=1])
        apply (simp add:)
        using tendstoD [OF lim [unfolded lim_at_infinity_0] zero_less_one]
        apply (rule eventually_mono)
        apply (simp add: dist_norm)
        done
      with holomorphic_on_extend_bounded [OF 1 2]
      obtain g where holg: "g holomorphic_on ball 0 r"
                 and geq: "\<And>z. z \<in> ball 0 r - {0} \<Longrightarrow> g z = (inverse \<circ> f \<circ> inverse) z"
        by meson
      have ifi0: "(inverse \<circ> f \<circ> inverse) \<midarrow>0\<rightarrow> 0"
        using \<open>l = 0\<close> lim lim_at_infinity_0 by blast
      have g2g0: "g \<midarrow>0\<rightarrow> g 0"
        using \<open>0 < r\<close> centre_in_ball continuous_at continuous_on_eq_continuous_at holg
        by (blast intro: holomorphic_on_imp_continuous_on)
      have g2g1: "g \<midarrow>0\<rightarrow> 0"
        apply (rule Lim_transform_within_open [OF ifi0 open_ball [of 0 r]])
        using \<open>0 < r\<close> by (auto simp: geq)
      have [simp]: "g 0 = 0"
        by (rule tendsto_unique [OF _ g2g0 g2g1]) simp
      have "ball 0 r - {0::complex} \<noteq> {}"
        using \<open>0 < r\<close>
        apply (clarsimp simp: ball_def dist_norm)
        apply (drule_tac c="of_real r/2" in subsetD, auto)
        done
      then obtain w::complex where "w \<noteq> 0" and w: "norm w < r" by force
      then have "g w \<noteq> 0" by (simp add: geq r)
      obtain B n e where "0 < B" "0 < e" "e \<le> r"
                     and leg: "\<And>w. norm w < e \<Longrightarrow> B * cmod w ^ n \<le> cmod (g w)"
        apply (rule holomorphic_lower_bound_difference [OF holg open_ball connected_ball, of 0 w])
        using \<open>0 < r\<close> w \<open>g w \<noteq> 0\<close> by (auto simp: ball_subset_ball_iff)
      have "cmod (f z) \<le> cmod z ^ n / B" if "2/e \<le> cmod z" for z
      proof -
        have ize: "inverse z \<in> ball 0 e - {0}" using that \<open>0 < e\<close>
          by (auto simp: norm_divide divide_simps algebra_simps)
        then have [simp]: "z \<noteq> 0" and izr: "inverse z \<in> ball 0 r - {0}" using  \<open>e \<le> r\<close>
          by auto
        then have [simp]: "f z \<noteq> 0"
          using r [of "inverse z"] by simp
        have [simp]: "f z = inverse (g (inverse z))"
          using izr geq [of "inverse z"] by simp
        show ?thesis using ize leg [of "inverse z"]  \<open>0 < B\<close>  \<open>0 < e\<close>
          by (simp add: divide_simps norm_divide algebra_simps)
      qed
      then show ?thesis
        apply (rule_tac a = "\<lambda>k. (deriv ^^ k) f 0 / (fact k)" and n=n in that)
        apply (rule_tac A = "2/e" and B = "1/B" in Liouville_polynomial [OF holf])
        apply (simp add:)
        done
  next
    case False
    then have fi0: "\<And>r. r > 0 \<Longrightarrow> \<exists>z\<in>ball 0 r - {0}. f (inverse z) = 0"
      by simp
    have fz0: "f z = 0" if "0 < r" and lt1: "\<And>x. x \<noteq> 0 \<Longrightarrow> cmod x < r \<Longrightarrow> inverse (cmod (f (inverse x))) < 1"
              for z r
    proof -
      have f0: "(f \<longlongrightarrow> 0) at_infinity"
      proof -
        have DIM_complex[intro]: "2 \<le> DIM(complex)"  \<comment>\<open>should not be necessary!\<close>
          by simp
        have "continuous_on (inverse ` (ball 0 r - {0})) f"
          using continuous_on_subset holf holomorphic_on_imp_continuous_on by blast
        then have "connected ((f \<circ> inverse) ` (ball 0 r - {0}))"
          apply (intro connected_continuous_image continuous_intros)
          apply (force intro: connected_punctured_ball)+
          done
        then have "\<lbrakk>w \<noteq> 0; cmod w < r\<rbrakk> \<Longrightarrow> f (inverse w) = 0" for w
          apply (rule disjE [OF connected_closedD [where A = "{0}" and B = "- ball 0 1"]], auto)
          apply (metis (mono_tags, hide_lams) not_less_iff_gr_or_eq one_less_inverse lt1 zero_less_norm_iff)
          using False \<open>0 < r\<close> apply fastforce
          by (metis (no_types, hide_lams) Compl_iff IntI comp_apply empty_iff image_eqI insert_Diff_single insert_iff mem_ball_0 not_less_iff_gr_or_eq one_less_inverse that(2) zero_less_norm_iff)
        then show ?thesis
          apply (simp add: lim_at_infinity_0)
          apply (rule Lim_eventually)
          apply (simp add: eventually_at)
          apply (rule_tac x=r in exI)
          apply (simp add: \<open>0 < r\<close> dist_norm)
          done
      qed
      obtain w where "w \<in> ball 0 r - {0}" and "f (inverse w) = 0"
        using False \<open>0 < r\<close> by blast
      then show ?thesis
        by (auto simp: f0 Liouville_weak [OF holf, of 0])
    qed
    show ?thesis
      apply (rule that [of "\<lambda>n. 0" 0])
      using lim [unfolded lim_at_infinity_0]
      apply (simp add: Lim_at dist_norm norm_inverse)
      apply (drule_tac x=1 in spec)
      using fz0 apply auto
      done
    qed
qed


subsection\<open>Entire proper functions are precisely the non-trivial polynomials\<close>

proposition proper_map_polyfun:
    fixes c :: "nat \<Rightarrow> 'a::{real_normed_div_algebra,heine_borel}"
  assumes "closed S" and "compact K" and c: "c i \<noteq> 0" "1 \<le> i" "i \<le> n"
    shows "compact (S \<inter> {z. (\<Sum>i\<le>n. c i * z^i) \<in> K})"
proof -
  obtain B where "B > 0" and B: "\<And>x. x \<in> K \<Longrightarrow> norm x \<le> B"
    by (metis compact_imp_bounded \<open>compact K\<close> bounded_pos)
  have *: "norm x \<le> b"
            if "\<And>x. b \<le> norm x \<Longrightarrow> B + 1 \<le> norm (\<Sum>i\<le>n. c i * x ^ i)"
               "(\<Sum>i\<le>n. c i * x ^ i) \<in> K"  for b x
  proof -
    have "norm (\<Sum>i\<le>n. c i * x ^ i) \<le> B"
      using B that by blast
    moreover have "\<not> B + 1 \<le> B"
      by simp
    ultimately show "norm x \<le> b"
      using that by (metis (no_types) less_eq_real_def not_less order_trans)
  qed
  have "bounded {z. (\<Sum>i\<le>n. c i * z ^ i) \<in> K}"
    using polyfun_extremal [where c=c and B="B+1", OF c]
    by (auto simp: bounded_pos eventually_at_infinity_pos *)
  moreover have "closed {z. (\<Sum>i\<le>n. c i * z ^ i) \<in> K}"
    apply (intro allI continuous_closed_preimage_univ continuous_intros)
    using \<open>compact K\<close> compact_eq_bounded_closed by blast
  ultimately show ?thesis
    using closed_Int_compact [OF \<open>closed S\<close>] compact_eq_bounded_closed by blast
qed

corollary proper_map_polyfun_univ:
    fixes c :: "nat \<Rightarrow> 'a::{real_normed_div_algebra,heine_borel}"
  assumes "compact K" "c i \<noteq> 0" "1 \<le> i" "i \<le> n"
    shows "compact ({z. (\<Sum>i\<le>n. c i * z^i) \<in> K})"
using proper_map_polyfun [of UNIV K c i n] assms by simp


proposition proper_map_polyfun_eq:
  assumes "f holomorphic_on UNIV"
    shows "(\<forall>k. compact k \<longrightarrow> compact {z. f z \<in> k}) \<longleftrightarrow>
           (\<exists>c n. 0 < n \<and> (c n \<noteq> 0) \<and> f = (\<lambda>z. \<Sum>i\<le>n. c i * z^i))"
          (is "?lhs = ?rhs")
proof
  assume compf [rule_format]: ?lhs
  have 2: "\<exists>k. 0 < k \<and> a k \<noteq> 0 \<and> f = (\<lambda>z. \<Sum>i \<le> k. a i * z ^ i)"
        if "\<And>z. f z = (\<Sum>i\<le>n. a i * z ^ i)" for a n
  proof (cases "\<forall>i\<le>n. 0<i \<longrightarrow> a i = 0")
    case True
    then have [simp]: "\<And>z. f z = a 0"
      by (simp add: that sum_atMost_shift)
    have False using compf [of "{a 0}"] by simp
    then show ?thesis ..
  next
    case False
    then obtain k where k: "0 < k" "k\<le>n" "a k \<noteq> 0" by force
    define m where "m = (GREATEST k. k\<le>n \<and> a k \<noteq> 0)"
    have m: "m\<le>n \<and> a m \<noteq> 0"
      unfolding m_def
      apply (rule GreatestI [where b = "Suc n"])
      using k apply auto
      done
    have [simp]: "a i = 0" if "m < i" "i \<le> n" for i
      using Greatest_le [where b = "Suc n" and P = "\<lambda>k. k\<le>n \<and> a k \<noteq> 0"]
      using m_def not_le that by auto
    have "k \<le> m"
      unfolding m_def
      apply (rule Greatest_le [where b = "Suc n"])
      using k apply auto
      done
    with k m show ?thesis
      by (rule_tac x=m in exI) (auto simp: that comm_monoid_add_class.sum.mono_neutral_right)
  qed
  have "((inverse \<circ> f) \<longlongrightarrow> 0) at_infinity"
  proof (rule Lim_at_infinityI)
    fix e::real assume "0 < e"
    with compf [of "cball 0 (inverse e)"]
    show "\<exists>B. \<forall>x. B \<le> cmod x \<longrightarrow> dist ((inverse \<circ> f) x) 0 \<le> e"
      apply (simp add:)
      apply (clarsimp simp add: compact_eq_bounded_closed bounded_pos norm_inverse)
      apply (rule_tac x="b+1" in exI)
      apply (metis inverse_inverse_eq less_add_same_cancel2 less_imp_inverse_less add.commute not_le not_less_iff_gr_or_eq order_trans zero_less_one)
      done
  qed
  then show ?rhs
    apply (rule pole_at_infinity [OF assms])
    using 2 apply blast
    done
next
  assume ?rhs
  then obtain c n where "0 < n" "c n \<noteq> 0" "f = (\<lambda>z. \<Sum>i\<le>n. c i * z ^ i)" by blast
  then have "compact {z. f z \<in> k}" if "compact k" for k
    by (auto intro: proper_map_polyfun_univ [OF that])
  then show ?lhs by blast
qed


subsection\<open>Relating invertibility and nonvanishing of derivative\<close>

proposition has_complex_derivative_locally_injective:
  assumes holf: "f holomorphic_on S"
      and S: "\<xi> \<in> S" "open S"
      and dnz: "deriv f \<xi> \<noteq> 0"
  obtains r where "r > 0" "ball \<xi> r \<subseteq> S" "inj_on f (ball \<xi> r)"
proof -
  have *: "\<exists>d>0. \<forall>x. dist \<xi> x < d \<longrightarrow> onorm (\<lambda>v. deriv f x * v - deriv f \<xi> * v) < e" if "e > 0" for e
  proof -
    have contdf: "continuous_on S (deriv f)"
      by (simp add: holf holomorphic_deriv holomorphic_on_imp_continuous_on \<open>open S\<close>)
    obtain \<delta> where "\<delta>>0" and \<delta>: "\<And>x. \<lbrakk>x \<in> S; dist x \<xi> \<le> \<delta>\<rbrakk> \<Longrightarrow> cmod (deriv f x - deriv f \<xi>) \<le> e/2"
      using continuous_onE [OF contdf \<open>\<xi> \<in> S\<close>, of "e/2"] \<open>0 < e\<close>
      by (metis dist_complex_def half_gt_zero less_imp_le)
    obtain \<epsilon> where "\<epsilon>>0" "ball \<xi> \<epsilon> \<subseteq> S"
      by (metis openE [OF \<open>open S\<close> \<open>\<xi> \<in> S\<close>])
    with \<open>\<delta>>0\<close> have "\<exists>\<delta>>0. \<forall>x. dist \<xi> x < \<delta> \<longrightarrow> onorm (\<lambda>v. deriv f x * v - deriv f \<xi> * v) \<le> e/2"
      apply (rule_tac x="min \<delta> \<epsilon>" in exI)
      apply (intro conjI allI impI Operator_Norm.onorm_le)
      apply (simp add:)
      apply (simp only: Rings.ring_class.left_diff_distrib [symmetric] norm_mult)
      apply (rule mult_right_mono [OF \<delta>])
      apply (auto simp: dist_commute Rings.ordered_semiring_class.mult_right_mono \<delta>)
      done
    with \<open>e>0\<close> show ?thesis by force
  qed
  have "inj (op * (deriv f \<xi>))"
    using dnz by simp
  then obtain g' where g': "linear g'" "g' \<circ> op * (deriv f \<xi>) = id"
    using linear_injective_left_inverse [of "op * (deriv f \<xi>)"]
    by (auto simp: linear_times)
  show ?thesis
    apply (rule has_derivative_locally_injective [OF S, where f=f and f' = "\<lambda>z h. deriv f z * h" and g' = g'])
    using g' *
    apply (simp_all add: linear_conv_bounded_linear that)
    using DERIV_deriv_iff_field_differentiable has_field_derivative_imp_has_derivative holf
        holomorphic_on_imp_differentiable_at \<open>open S\<close> apply blast
    done
qed


proposition has_complex_derivative_locally_invertible:
  assumes holf: "f holomorphic_on S"
      and S: "\<xi> \<in> S" "open S"
      and dnz: "deriv f \<xi> \<noteq> 0"
  obtains r where "r > 0" "ball \<xi> r \<subseteq> S" "open (f `  (ball \<xi> r))" "inj_on f (ball \<xi> r)"
proof -
  obtain r where "r > 0" "ball \<xi> r \<subseteq> S" "inj_on f (ball \<xi> r)"
    by (blast intro: that has_complex_derivative_locally_injective [OF assms])
  then have \<xi>: "\<xi> \<in> ball \<xi> r" by simp
  then have nc: "~ f constant_on ball \<xi> r"
    using \<open>inj_on f (ball \<xi> r)\<close> injective_not_constant by fastforce
  have holf': "f holomorphic_on ball \<xi> r"
    using \<open>ball \<xi> r \<subseteq> S\<close> holf holomorphic_on_subset by blast
  have "open (f ` ball \<xi> r)"
    apply (rule open_mapping_thm [OF holf'])
    using nc apply auto
    done
  then show ?thesis
    using \<open>0 < r\<close> \<open>ball \<xi> r \<subseteq> S\<close> \<open>inj_on f (ball \<xi> r)\<close> that  by blast
qed


proposition holomorphic_injective_imp_regular:
  assumes holf: "f holomorphic_on S"
      and "open S" and injf: "inj_on f S"
      and "\<xi> \<in> S"
    shows "deriv f \<xi> \<noteq> 0"
proof -
  obtain r where "r>0" and r: "ball \<xi> r \<subseteq> S" using assms by (blast elim!: openE)
  have holf': "f holomorphic_on ball \<xi> r"
    using \<open>ball \<xi> r \<subseteq> S\<close> holf holomorphic_on_subset by blast
  show ?thesis
  proof (cases "\<forall>n>0. (deriv ^^ n) f \<xi> = 0")
    case True
    have fcon: "f w = f \<xi>" if "w \<in> ball \<xi> r" for w
      apply (rule holomorphic_fun_eq_const_on_connected [OF holf'])
      using True \<open>0 < r\<close> that by auto
    have False
      using fcon [of "\<xi> + r/2"] \<open>0 < r\<close> r injf unfolding inj_on_def
      by (metis \<open>\<xi> \<in> S\<close> contra_subsetD dist_commute fcon mem_ball perfect_choose_dist)
    then show ?thesis ..
  next
    case False
    then obtain n0 where n0: "n0 > 0 \<and> (deriv ^^ n0) f \<xi> \<noteq> 0" by blast
    define n where [abs_def]: "n = (LEAST n. n > 0 \<and> (deriv ^^ n) f \<xi> \<noteq> 0)"
    have n_ne: "n > 0" "(deriv ^^ n) f \<xi> \<noteq> 0"
      using def_LeastI [OF n_def n0] by auto
    have n_min: "\<And>k. 0 < k \<Longrightarrow> k < n \<Longrightarrow> (deriv ^^ k) f \<xi> = 0"
      using def_Least_le [OF n_def] not_le by auto
    obtain g \<delta> where "0 < \<delta>"
             and holg: "g holomorphic_on ball \<xi> \<delta>"
             and fd: "\<And>w. w \<in> ball \<xi> \<delta> \<Longrightarrow> f w - f \<xi> = ((w - \<xi>) * g w) ^ n"
             and gnz: "\<And>w. w \<in> ball \<xi> \<delta> \<Longrightarrow> g w \<noteq> 0"
      apply (rule holomorphic_factor_order_of_zero_strong [OF holf \<open>open S\<close> \<open>\<xi> \<in> S\<close> n_ne])
      apply (blast intro: n_min)+
      done
    show ?thesis
    proof (cases "n=1")
      case True
      with n_ne show ?thesis by auto
    next
      case False
      have holgw: "(\<lambda>w. (w - \<xi>) * g w) holomorphic_on ball \<xi> (min r \<delta>)"
        apply (rule holomorphic_intros)+
        using holg by (simp add: holomorphic_on_subset subset_ball)
      have gd: "\<And>w. dist \<xi> w < \<delta> \<Longrightarrow> (g has_field_derivative deriv g w) (at w)"
        using holg
        by (simp add: DERIV_deriv_iff_field_differentiable holomorphic_on_def at_within_open_NO_MATCH)
      have *: "\<And>w. w \<in> ball \<xi> (min r \<delta>)
            \<Longrightarrow> ((\<lambda>w. (w - \<xi>) * g w) has_field_derivative ((w - \<xi>) * deriv g w + g w))
                (at w)"
        by (rule gd derivative_eq_intros | simp)+
      have [simp]: "deriv (\<lambda>w. (w - \<xi>) * g w) \<xi> \<noteq> 0"
        using * [of \<xi>] \<open>0 < \<delta>\<close> \<open>0 < r\<close> by (simp add: DERIV_imp_deriv gnz)
      obtain T where "\<xi> \<in> T" "open T" and Tsb: "T \<subseteq> ball \<xi> (min r \<delta>)" and oimT: "open ((\<lambda>w. (w - \<xi>) * g w) ` T)"
        apply (rule has_complex_derivative_locally_invertible [OF holgw, of \<xi>])
        using \<open>0 < r\<close> \<open>0 < \<delta>\<close>
        apply (simp_all add:)
        by (meson Topology_Euclidean_Space.open_ball centre_in_ball)
      define U where "U = (\<lambda>w. (w - \<xi>) * g w) ` T"
      have "open U" by (metis oimT U_def)
      have "0 \<in> U"
        apply (auto simp: U_def)
        apply (rule image_eqI [where x = \<xi>])
        apply (auto simp: \<open>\<xi> \<in> T\<close>)
        done
      then obtain \<epsilon> where "\<epsilon>>0" and \<epsilon>: "cball 0 \<epsilon> \<subseteq> U"
        using \<open>open U\<close> open_contains_cball by blast
      then have "\<epsilon> * exp(2 * of_real pi * \<i> * (0/n)) \<in> cball 0 \<epsilon>"
                "\<epsilon> * exp(2 * of_real pi * \<i> * (1/n)) \<in> cball 0 \<epsilon>"
        by (auto simp: norm_mult)
      with \<epsilon> have "\<epsilon> * exp(2 * of_real pi * \<i> * (0/n)) \<in> U"
                  "\<epsilon> * exp(2 * of_real pi * \<i> * (1/n)) \<in> U" by blast+
      then obtain y0 y1 where "y0 \<in> T" and y0: "(y0 - \<xi>) * g y0 = \<epsilon> * exp(2 * of_real pi * \<i> * (0/n))"
                          and "y1 \<in> T" and y1: "(y1 - \<xi>) * g y1 = \<epsilon> * exp(2 * of_real pi * \<i> * (1/n))"
        by (auto simp: U_def)
      then have "y0 \<in> ball \<xi> \<delta>" "y1 \<in> ball \<xi> \<delta>" using Tsb by auto
      moreover have "y0 \<noteq> y1"
        using y0 y1 \<open>\<epsilon> > 0\<close> complex_root_unity_eq_1 [of n 1] \<open>n > 0\<close> False by auto
      moreover have "T \<subseteq> S"
        by (meson Tsb min.cobounded1 order_trans r subset_ball)
      ultimately have False
        using inj_onD [OF injf, of y0 y1] \<open>y0 \<in> T\<close> \<open>y1 \<in> T\<close>
        using fd [of y0] fd [of y1] complex_root_unity [of n 1]
        apply (simp add: y0 y1 power_mult_distrib)
        apply (force simp: algebra_simps)
        done
      then show ?thesis ..
    qed
  qed
qed


text\<open>Hence a nice clean inverse function theorem\<close>

proposition holomorphic_has_inverse:
  assumes holf: "f holomorphic_on S"
      and "open S" and injf: "inj_on f S"
  obtains g where "g holomorphic_on (f ` S)"
                  "\<And>z. z \<in> S \<Longrightarrow> deriv f z * deriv g (f z) = 1"
                  "\<And>z. z \<in> S \<Longrightarrow> g(f z) = z"
proof -
  have ofs: "open (f ` S)"
    by (rule open_mapping_thm3 [OF assms])
  have contf: "continuous_on S f"
    by (simp add: holf holomorphic_on_imp_continuous_on)
  have *: "(the_inv_into S f has_field_derivative inverse (deriv f z)) (at (f z))" if "z \<in> S" for z
  proof -
    have 1: "(f has_field_derivative deriv f z) (at z)"
      using DERIV_deriv_iff_field_differentiable \<open>z \<in> S\<close> \<open>open S\<close> holf holomorphic_on_imp_differentiable_at
      by blast
    have 2: "deriv f z \<noteq> 0"
      using \<open>z \<in> S\<close> \<open>open S\<close> holf holomorphic_injective_imp_regular injf by blast
    show ?thesis
      apply (rule has_complex_derivative_inverse_strong [OF 1 2 \<open>open S\<close> \<open>z \<in> S\<close>])
       apply (simp add: holf holomorphic_on_imp_continuous_on)
      by (simp add: injf the_inv_into_f_f)
  qed
  show ?thesis
    proof
      show "the_inv_into S f holomorphic_on f ` S"
        by (simp add: holomorphic_on_open ofs) (blast intro: *)
    next
      fix z assume "z \<in> S"
      have "deriv f z \<noteq> 0"
        using \<open>z \<in> S\<close> \<open>open S\<close> holf holomorphic_injective_imp_regular injf by blast
      then show "deriv f z * deriv (the_inv_into S f) (f z) = 1"
        using * [OF \<open>z \<in> S\<close>]  by (simp add: DERIV_imp_deriv)
    next
      fix z assume "z \<in> S"
      show "the_inv_into S f (f z) = z"
        by (simp add: \<open>z \<in> S\<close> injf the_inv_into_f_f)
  qed
qed


subsection\<open>The Schwarz Lemma\<close>

lemma Schwarz1:
  assumes holf: "f holomorphic_on S"
      and contf: "continuous_on (closure S) f"
      and S: "open S" "connected S"
      and boS: "bounded S"
      and "S \<noteq> {}"
  obtains w where "w \<in> frontier S"
                  "\<And>z. z \<in> closure S \<Longrightarrow> norm (f z) \<le> norm (f w)"
proof -
  have connf: "continuous_on (closure S) (norm o f)"
    using contf continuous_on_compose continuous_on_norm_id by blast
  have coc: "compact (closure S)"
    by (simp add: \<open>bounded S\<close> bounded_closure compact_eq_bounded_closed)
  then obtain x where x: "x \<in> closure S" and xmax: "\<And>z. z \<in> closure S \<Longrightarrow> norm(f z) \<le> norm(f x)"
    apply (rule bexE [OF continuous_attains_sup [OF _ _ connf]])
    using \<open>S \<noteq> {}\<close> apply auto
    done
  then show ?thesis
  proof (cases "x \<in> frontier S")
    case True
    then show ?thesis using that xmax by blast
  next
    case False
    then have "x \<in> S"
      using \<open>open S\<close> frontier_def interior_eq x by auto
    then have "f constant_on S"
      apply (rule maximum_modulus_principle [OF holf S \<open>open S\<close> order_refl])
      using closure_subset apply (blast intro: xmax)
      done
    then have "f constant_on (closure S)"
      by (rule constant_on_closureI [OF _ contf])
    then obtain c where c: "\<And>x. x \<in> closure S \<Longrightarrow> f x = c"
      by (meson constant_on_def)
    obtain w where "w \<in> frontier S"
      by (metis coc all_not_in_conv assms(6) closure_UNIV frontier_eq_empty not_compact_UNIV)
    then show ?thesis
      by (simp add: c frontier_def that)
  qed
qed

lemma Schwarz2:
 "\<lbrakk>f holomorphic_on ball 0 r;
    0 < s; ball w s \<subseteq> ball 0 r;
    \<And>z. norm (w-z) < s \<Longrightarrow> norm(f z) \<le> norm(f w)\<rbrakk>
    \<Longrightarrow> f constant_on ball 0 r"
by (rule maximum_modulus_principle [where U = "ball w s" and \<xi> = w]) (simp_all add: dist_norm)

lemma Schwarz3:
  assumes holf: "f holomorphic_on (ball 0 r)" and [simp]: "f 0 = 0"
  obtains h where "h holomorphic_on (ball 0 r)" and "\<And>z. norm z < r \<Longrightarrow> f z = z * (h z)" and "deriv f 0 = h 0"
proof -
  define h where "h z = (if z = 0 then deriv f 0 else f z / z)" for z
  have d0: "deriv f 0 = h 0"
    by (simp add: h_def)
  moreover have "h holomorphic_on (ball 0 r)"
    by (rule pole_theorem_open_0 [OF holf, of 0]) (auto simp: h_def)
  moreover have "norm z < r \<Longrightarrow> f z = z * h z" for z
    by (simp add: h_def)
  ultimately show ?thesis
    using that by blast
qed


proposition Schwarz_Lemma:
  assumes holf: "f holomorphic_on (ball 0 1)" and [simp]: "f 0 = 0"
      and no: "\<And>z. norm z < 1 \<Longrightarrow> norm (f z) < 1"
      and \<xi>: "norm \<xi> < 1"
    shows "norm (f \<xi>) \<le> norm \<xi>" and "norm(deriv f 0) \<le> 1"
      and "((\<exists>z. norm z < 1 \<and> z \<noteq> 0 \<and> norm(f z) = norm z) \<or> norm(deriv f 0) = 1)
           \<Longrightarrow> \<exists>\<alpha>. (\<forall>z. norm z < 1 \<longrightarrow> f z = \<alpha> * z) \<and> norm \<alpha> = 1" (is "?P \<Longrightarrow> ?Q")
proof -
  obtain h where holh: "h holomorphic_on (ball 0 1)"
             and fz_eq: "\<And>z. norm z < 1 \<Longrightarrow> f z = z * (h z)" and df0: "deriv f 0 = h 0"
    by (rule Schwarz3 [OF holf]) auto
  have noh_le: "norm (h z) \<le> 1" if z: "norm z < 1" for z
  proof -
    have "norm (h z) < a" if a: "1 < a" for a
    proof -
      have "max (inverse a) (norm z) < 1"
        using z a by (simp_all add: inverse_less_1_iff)
      then obtain r where r: "max (inverse a) (norm z) < r" and "r < 1"
        using Rats_dense_in_real by blast
      then have nzr: "norm z < r" and ira: "inverse r < a"
        using z a less_imp_inverse_less by force+
      then have "0 < r"
        by (meson norm_not_less_zero not_le order.strict_trans2)
      have holh': "h holomorphic_on ball 0 r"
        by (meson holh \<open>r < 1\<close> holomorphic_on_subset less_eq_real_def subset_ball)
      have conth': "continuous_on (cball 0 r) h"
        by (meson \<open>r < 1\<close> dual_order.trans holh holomorphic_on_imp_continuous_on holomorphic_on_subset mem_ball_0 mem_cball_0 not_less subsetI)
      obtain w where w: "norm w = r" and lenw: "\<And>z. norm z < r \<Longrightarrow> norm(h z) \<le> norm(h w)"
        apply (rule Schwarz1 [OF holh']) using conth' \<open>0 < r\<close> by auto
      have "h w = f w / w" using fz_eq \<open>r < 1\<close> nzr w by auto
      then have "cmod (h z) < inverse r"
        by (metis \<open>0 < r\<close> \<open>r < 1\<close> divide_strict_right_mono inverse_eq_divide
                  le_less_trans lenw no norm_divide nzr w)
      then show ?thesis using ira by linarith
    qed
    then show "norm (h z) \<le> 1"
      using not_le by blast
  qed
  show "cmod (f \<xi>) \<le> cmod \<xi>"
  proof (cases "\<xi> = 0")
    case True then show ?thesis by auto
  next
    case False
    then show ?thesis
      by (simp add: noh_le fz_eq \<xi> mult_left_le norm_mult)
  qed
  show no_df0: "norm(deriv f 0) \<le> 1"
    by (simp add: \<open>\<And>z. cmod z < 1 \<Longrightarrow> cmod (h z) \<le> 1\<close> df0)
  show "?Q" if "?P"
    using that
  proof
    assume "\<exists>z. cmod z < 1 \<and> z \<noteq> 0 \<and> cmod (f z) = cmod z"
    then obtain \<gamma> where \<gamma>: "cmod \<gamma> < 1" "\<gamma> \<noteq> 0" "cmod (f \<gamma>) = cmod \<gamma>" by blast
    then have [simp]: "norm (h \<gamma>) = 1"
      by (simp add: fz_eq norm_mult)
    have "ball \<gamma> (1 - cmod \<gamma>) \<subseteq> ball 0 1"
      by (simp add: ball_subset_ball_iff)
    moreover have "\<And>z. cmod (\<gamma> - z) < 1 - cmod \<gamma> \<Longrightarrow> cmod (h z) \<le> cmod (h \<gamma>)"
      apply (simp add: algebra_simps)
      by (metis add_diff_cancel_left' diff_diff_eq2 le_less_trans noh_le norm_triangle_ineq4)
    ultimately obtain c where c: "\<And>z. norm z < 1 \<Longrightarrow> h z = c"
      using Schwarz2 [OF holh, of "1 - norm \<gamma>" \<gamma>, unfolded constant_on_def] \<gamma> by auto
    then have "norm c = 1"
      using \<gamma> by force
    with c show ?thesis
      using fz_eq by auto
  next
    assume [simp]: "cmod (deriv f 0) = 1"
    then obtain c where c: "\<And>z. norm z < 1 \<Longrightarrow> h z = c"
      using Schwarz2 [OF holh zero_less_one, of 0, unfolded constant_on_def] df0 noh_le
      by auto
    moreover have "norm c = 1"  using df0 c by auto
    ultimately show ?thesis
      using fz_eq by auto
  qed
qed

subsection\<open>The Schwarz reflection principle\<close>

lemma hol_pal_lem0:
  assumes "d \<bullet> a \<le> k" "k \<le> d \<bullet> b"
  obtains c where
     "c \<in> closed_segment a b" "d \<bullet> c = k"
     "\<And>z. z \<in> closed_segment a c \<Longrightarrow> d \<bullet> z \<le> k"
     "\<And>z. z \<in> closed_segment c b \<Longrightarrow> k \<le> d \<bullet> z"
proof -
  obtain c where cin: "c \<in> closed_segment a b" and keq: "k = d \<bullet> c"
    using connected_ivt_hyperplane [of "closed_segment a b" a b d k]
    by (auto simp: assms)
  have "closed_segment a c \<subseteq> {z. d \<bullet> z \<le> k}"  "closed_segment c b \<subseteq> {z. k \<le> d \<bullet> z}"
    unfolding segment_convex_hull using assms keq
    by (auto simp: convex_halfspace_le convex_halfspace_ge hull_minimal)
  then show ?thesis using cin that by fastforce
qed

lemma hol_pal_lem1:
  assumes "convex S" "open S"
      and abc: "a \<in> S" "b \<in> S" "c \<in> S"
          "d \<noteq> 0" and lek: "d \<bullet> a \<le> k" "d \<bullet> b \<le> k" "d \<bullet> c \<le> k"
      and holf1: "f holomorphic_on {z. z \<in> S \<and> d \<bullet> z < k}"
      and contf: "continuous_on S f"
    shows "contour_integral (linepath a b) f +
           contour_integral (linepath b c) f +
           contour_integral (linepath c a) f = 0"
proof -
  have "interior (convex hull {a, b, c}) \<subseteq> interior(S \<inter> {x. d \<bullet> x \<le> k})"
    apply (rule interior_mono)
    apply (rule hull_minimal)
     apply (simp add: abc lek)
    apply (rule convex_Int [OF \<open>convex S\<close> convex_halfspace_le])
    done
  also have "... \<subseteq> {z \<in> S. d \<bullet> z < k}"
    by (force simp: interior_open [OF \<open>open S\<close>] \<open>d \<noteq> 0\<close>)
  finally have *: "interior (convex hull {a, b, c}) \<subseteq> {z \<in> S. d \<bullet> z < k}" .
  have "continuous_on (convex hull {a,b,c}) f"
    using \<open>convex S\<close> contf abc continuous_on_subset subset_hull
    by fastforce
  moreover have "f holomorphic_on interior (convex hull {a,b,c})"
    by (rule holomorphic_on_subset [OF holf1 *])
  ultimately show ?thesis
    using Cauchy_theorem_triangle_interior has_chain_integral_chain_integral3
      by blast
qed

lemma hol_pal_lem2:
  assumes S: "convex S" "open S"
      and abc: "a \<in> S" "b \<in> S" "c \<in> S"
      and "d \<noteq> 0" and lek: "d \<bullet> a \<le> k" "d \<bullet> b \<le> k"
      and holf1: "f holomorphic_on {z. z \<in> S \<and> d \<bullet> z < k}"
      and holf2: "f holomorphic_on {z. z \<in> S \<and> k < d \<bullet> z}"
      and contf: "continuous_on S f"
    shows "contour_integral (linepath a b) f +
           contour_integral (linepath b c) f +
           contour_integral (linepath c a) f = 0"
proof (cases "d \<bullet> c \<le> k")
  case True show ?thesis
    by (rule hol_pal_lem1 [OF S abc \<open>d \<noteq> 0\<close> lek True holf1 contf])
next
  case False
  then have "d \<bullet> c > k" by force
  obtain a' where a': "a' \<in> closed_segment b c" and "d \<bullet> a' = k"
     and ba': "\<And>z. z \<in> closed_segment b a' \<Longrightarrow> d \<bullet> z \<le> k"
     and a'c: "\<And>z. z \<in> closed_segment a' c \<Longrightarrow> k \<le> d \<bullet> z"
    apply (rule hol_pal_lem0 [of d b k c, OF \<open>d \<bullet> b \<le> k\<close>])
    using False by auto
  obtain b' where b': "b' \<in> closed_segment a c" and "d \<bullet> b' = k"
     and ab': "\<And>z. z \<in> closed_segment a b' \<Longrightarrow> d \<bullet> z \<le> k"
     and b'c: "\<And>z. z \<in> closed_segment b' c \<Longrightarrow> k \<le> d \<bullet> z"
    apply (rule hol_pal_lem0 [of d a k c, OF \<open>d \<bullet> a \<le> k\<close>])
    using False by auto
  have a'b': "a' \<in> S \<and> b' \<in> S"
    using a' abc b' convex_contains_segment \<open>convex S\<close> by auto
  have "continuous_on (closed_segment c a) f"
    by (meson abc contf continuous_on_subset convex_contains_segment \<open>convex S\<close>)
  then have 1: "contour_integral (linepath c a) f =
                contour_integral (linepath c b') f + contour_integral (linepath b' a) f"
    apply (rule contour_integral_split_linepath)
    using b' by (simp add: closed_segment_commute)
  have "continuous_on (closed_segment b c) f"
    by (meson abc contf continuous_on_subset convex_contains_segment \<open>convex S\<close>)
  then have 2: "contour_integral (linepath b c) f =
                contour_integral (linepath b a') f + contour_integral (linepath a' c) f"
    by (rule contour_integral_split_linepath [OF _ a'])
  have 3: "contour_integral (reversepath (linepath b' a')) f =
                - contour_integral (linepath b' a') f"
    by (rule contour_integral_reversepath [OF valid_path_linepath])
  have fcd_le: "f field_differentiable at x"
               if "x \<in> interior S \<and> x \<in> interior {x. d \<bullet> x \<le> k}" for x
  proof -
    have "f holomorphic_on S \<inter> {c. d \<bullet> c < k}"
      by (metis (no_types) Collect_conj_eq Collect_mem_eq holf1)
    then have "\<exists>C D. x \<in> interior C \<inter> interior D \<and> f holomorphic_on interior C \<inter> interior D"
      using that
      by (metis Collect_mem_eq Int_Collect \<open>d \<noteq> 0\<close> interior_halfspace_le interior_open \<open>open S\<close>)
    then show "f field_differentiable at x"
      by (metis at_within_interior holomorphic_on_def interior_Int interior_interior)
  qed
  have ab_le: "\<And>x. x \<in> closed_segment a b \<Longrightarrow> d \<bullet> x \<le> k"
  proof -
    fix x :: complex
    assume "x \<in> closed_segment a b"
    then have "\<And>C. x \<in> C \<or> b \<notin> C \<or> a \<notin> C \<or> \<not> convex C"
      by (meson contra_subsetD convex_contains_segment)
    then show "d \<bullet> x \<le> k"
      by (metis lek convex_halfspace_le mem_Collect_eq)
  qed
  have "continuous_on (S \<inter> {x. d \<bullet> x \<le> k}) f" using contf
    by (simp add: continuous_on_subset)
  then have "(f has_contour_integral 0)
         (linepath a b +++ linepath b a' +++ linepath a' b' +++ linepath b' a)"
    apply (rule Cauchy_theorem_convex [where k = "{}"])
    apply (simp_all add: path_image_join convex_Int convex_halfspace_le \<open>convex S\<close> fcd_le ab_le
                closed_segment_subset abc a'b' ba')
    by (metis \<open>d \<bullet> a' = k\<close> \<open>d \<bullet> b' = k\<close> convex_contains_segment convex_halfspace_le lek(1) mem_Collect_eq order_refl)
  then have 4: "contour_integral (linepath a b) f +
                contour_integral (linepath b a') f +
                contour_integral (linepath a' b') f +
                contour_integral (linepath b' a) f = 0"
    by (rule has_chain_integral_chain_integral4)
  have fcd_ge: "f field_differentiable at x"
               if "x \<in> interior S \<and> x \<in> interior {x. k \<le> d \<bullet> x}" for x
  proof -
    have f2: "f holomorphic_on S \<inter> {c. k < d \<bullet> c}"
      by (metis (full_types) Collect_conj_eq Collect_mem_eq holf2)
    have f3: "interior S = S"
      by (simp add: interior_open \<open>open S\<close>)
    then have "x \<in> S \<inter> interior {c. k \<le> d \<bullet> c}"
      using that by simp
    then show "f field_differentiable at x"
      using f3 f2 unfolding holomorphic_on_def
      by (metis (no_types) \<open>d \<noteq> 0\<close> at_within_interior interior_Int interior_halfspace_ge interior_interior)
  qed
  have "continuous_on (S \<inter> {x. k \<le> d \<bullet> x}) f" using contf
    by (simp add: continuous_on_subset)
  then have "(f has_contour_integral 0) (linepath a' c +++ linepath c b' +++ linepath b' a')"
    apply (rule Cauchy_theorem_convex [where k = "{}"])
    apply (simp_all add: path_image_join convex_Int convex_halfspace_ge \<open>convex S\<close>
                      fcd_ge closed_segment_subset abc a'b' a'c)
    by (metis \<open>d \<bullet> a' = k\<close> b'c closed_segment_commute convex_contains_segment
              convex_halfspace_ge ends_in_segment(2) mem_Collect_eq order_refl)
  then have 5: "contour_integral (linepath a' c) f + contour_integral (linepath c b') f + contour_integral (linepath b' a') f = 0"
    by (rule has_chain_integral_chain_integral3)
  show ?thesis
    using 1 2 3 4 5 by (metis add.assoc eq_neg_iff_add_eq_0 reversepath_linepath)
qed

lemma hol_pal_lem3:
  assumes S: "convex S" "open S"
      and abc: "a \<in> S" "b \<in> S" "c \<in> S"
      and "d \<noteq> 0" and lek: "d \<bullet> a \<le> k"
      and holf1: "f holomorphic_on {z. z \<in> S \<and> d \<bullet> z < k}"
      and holf2: "f holomorphic_on {z. z \<in> S \<and> k < d \<bullet> z}"
      and contf: "continuous_on S f"
    shows "contour_integral (linepath a b) f +
           contour_integral (linepath b c) f +
           contour_integral (linepath c a) f = 0"
proof (cases "d \<bullet> b \<le> k")
  case True show ?thesis
    by (rule hol_pal_lem2 [OF S abc \<open>d \<noteq> 0\<close> lek True holf1 holf2 contf])
next
  case False
  show ?thesis
  proof (cases "d \<bullet> c \<le> k")
    case True
    have "contour_integral (linepath c a) f +
          contour_integral (linepath a b) f +
          contour_integral (linepath b c) f = 0"
      by (rule hol_pal_lem2 [OF S \<open>c \<in> S\<close> \<open>a \<in> S\<close> \<open>b \<in> S\<close> \<open>d \<noteq> 0\<close> \<open>d \<bullet> c \<le> k\<close> lek holf1 holf2 contf])
    then show ?thesis
      by (simp add: algebra_simps)
  next
    case False
    have "contour_integral (linepath b c) f +
          contour_integral (linepath c a) f +
          contour_integral (linepath a b) f = 0"
      apply (rule hol_pal_lem2 [OF S \<open>b \<in> S\<close> \<open>c \<in> S\<close> \<open>a \<in> S\<close>, of "-d" "-k"])
      using \<open>d \<noteq> 0\<close> \<open>\<not> d \<bullet> b \<le> k\<close> False by (simp_all add: holf1 holf2 contf)
    then show ?thesis
      by (simp add: algebra_simps)
  qed
qed

lemma hol_pal_lem4:
  assumes S: "convex S" "open S"
      and abc: "a \<in> S" "b \<in> S" "c \<in> S" and "d \<noteq> 0"
      and holf1: "f holomorphic_on {z. z \<in> S \<and> d \<bullet> z < k}"
      and holf2: "f holomorphic_on {z. z \<in> S \<and> k < d \<bullet> z}"
      and contf: "continuous_on S f"
    shows "contour_integral (linepath a b) f +
           contour_integral (linepath b c) f +
           contour_integral (linepath c a) f = 0"
proof (cases "d \<bullet> a \<le> k")
  case True show ?thesis
    by (rule hol_pal_lem3 [OF S abc \<open>d \<noteq> 0\<close> True holf1 holf2 contf])
next
  case False
  show ?thesis
    apply (rule hol_pal_lem3 [OF S abc, of "-d" "-k"])
    using \<open>d \<noteq> 0\<close> False by (simp_all add: holf1 holf2 contf)
qed

proposition holomorphic_on_paste_across_line:
  assumes S: "open S" and "d \<noteq> 0"
      and holf1: "f holomorphic_on (S \<inter> {z. d \<bullet> z < k})"
      and holf2: "f holomorphic_on (S \<inter> {z. k < d \<bullet> z})"
      and contf: "continuous_on S f"
    shows "f holomorphic_on S"
proof -
  have *: "\<exists>t. open t \<and> p \<in> t \<and> continuous_on t f \<and>
               (\<forall>a b c. convex hull {a, b, c} \<subseteq> t \<longrightarrow>
                         contour_integral (linepath a b) f +
                         contour_integral (linepath b c) f +
                         contour_integral (linepath c a) f = 0)"
          if "p \<in> S" for p
  proof -
    obtain e where "e>0" and e: "ball p e \<subseteq> S"
      using \<open>p \<in> S\<close> openE S by blast
    then have "continuous_on (ball p e) f"
      using contf continuous_on_subset by blast
    moreover have "f holomorphic_on {z. dist p z < e \<and> d \<bullet> z < k}"
      apply (rule holomorphic_on_subset [OF holf1])
      using e by auto
    moreover have "f holomorphic_on {z. dist p z < e \<and> k < d \<bullet> z}"
      apply (rule holomorphic_on_subset [OF holf2])
      using e by auto
    ultimately show ?thesis
      apply (rule_tac x="ball p e" in exI)
      using \<open>e > 0\<close> e \<open>d \<noteq> 0\<close>
      apply (simp add:, clarify)
      apply (rule hol_pal_lem4 [of "ball p e" _ _ _ d _ k])
      apply (auto simp: subset_hull)
      done
  qed
  show ?thesis
    by (blast intro: * Morera_local_triangle analytic_imp_holomorphic)
qed

proposition Schwarz_reflection:
  assumes "open S" and cnjs: "cnj ` S \<subseteq> S"
      and  holf: "f holomorphic_on (S \<inter> {z. 0 < Im z})"
      and contf: "continuous_on (S \<inter> {z. 0 \<le> Im z}) f"
      and f: "\<And>z. \<lbrakk>z \<in> S; z \<in> \<real>\<rbrakk> \<Longrightarrow> (f z) \<in> \<real>"
    shows "(\<lambda>z. if 0 \<le> Im z then f z else cnj(f(cnj z))) holomorphic_on S"
proof -
  have 1: "(\<lambda>z. if 0 \<le> Im z then f z else cnj (f (cnj z))) holomorphic_on (S \<inter> {z. 0 < Im z})"
    by (force intro: iffD1 [OF holomorphic_cong [OF refl] holf])
  have cont_cfc: "continuous_on (S \<inter> {z. Im z \<le> 0}) (cnj o f o cnj)"
    apply (intro continuous_intros continuous_on_compose continuous_on_subset [OF contf])
    using cnjs apply auto
    done
  have "cnj \<circ> f \<circ> cnj field_differentiable at x within S \<inter> {z. Im z < 0}"
        if "x \<in> S" "Im x < 0" "f field_differentiable at (cnj x) within S \<inter> {z. 0 < Im z}" for x
    using that
    apply (simp add: field_differentiable_def Derivative.DERIV_within_iff Lim_within dist_norm, clarify)
    apply (rule_tac x="cnj f'" in exI)
    apply (elim all_forward ex_forward conj_forward imp_forward asm_rl, clarify)
    apply (drule_tac x="cnj xa" in bspec)
    using cnjs apply force
    apply (metis complex_cnj_cnj complex_cnj_diff complex_cnj_divide complex_mod_cnj)
    done
  then have hol_cfc: "(cnj o f o cnj) holomorphic_on (S \<inter> {z. Im z < 0})"
    using holf cnjs
    by (force simp: holomorphic_on_def)
  have 2: "(\<lambda>z. if 0 \<le> Im z then f z else cnj (f (cnj z))) holomorphic_on (S \<inter> {z. Im z < 0})"
    apply (rule iffD1 [OF holomorphic_cong [OF refl]])
    using hol_cfc by auto
  have [simp]: "(S \<inter> {z. 0 \<le> Im z}) \<union> (S \<inter> {z. Im z \<le> 0}) = S"
    by force
  have "continuous_on ((S \<inter> {z. 0 \<le> Im z}) \<union> (S \<inter> {z. Im z \<le> 0}))
                       (\<lambda>z. if 0 \<le> Im z then f z else cnj (f (cnj z)))"
    apply (rule continuous_on_cases_local)
    using cont_cfc contf
    apply (simp_all add: closedin_closed_Int closed_halfspace_Im_le closed_halfspace_Im_ge)
    using f Reals_cnj_iff complex_is_Real_iff apply auto
    done
  then have 3: "continuous_on S (\<lambda>z. if 0 \<le> Im z then f z else cnj (f (cnj z)))"
    by force
  show ?thesis
    apply (rule holomorphic_on_paste_across_line [OF \<open>open S\<close>, of "- \<i>" _ 0])
    using 1 2 3
    apply auto
    done
qed

subsection\<open>Bloch's theorem\<close>

lemma Bloch_lemma_0:
  assumes holf: "f holomorphic_on cball 0 r" and "0 < r"
      and [simp]: "f 0 = 0"
      and le: "\<And>z. norm z < r \<Longrightarrow> norm(deriv f z) \<le> 2 * norm(deriv f 0)"
    shows "ball 0 ((3 - 2 * sqrt 2) * r * norm(deriv f 0)) \<subseteq> f ` ball 0 r"
proof -
  have "sqrt 2 < 3/2"
    by (rule real_less_lsqrt) (auto simp: power2_eq_square)
  then have sq3: "0 < 3 - 2 * sqrt 2" by simp
  show ?thesis
  proof (cases "deriv f 0 = 0")
    case True then show ?thesis by simp
  next
    case False
    define C where "C = 2 * norm(deriv f 0)"
    have "0 < C" using False by (simp add: C_def)
    have holf': "f holomorphic_on ball 0 r" using holf
      using ball_subset_cball holomorphic_on_subset by blast
    then have holdf': "deriv f holomorphic_on ball 0 r"
      by (rule holomorphic_deriv [OF _ open_ball])
    have "Le1": "norm(deriv f z - deriv f 0) \<le> norm z / (r - norm z) * C"
                if "norm z < r" for z
    proof -
      have T1: "norm(deriv f z - deriv f 0) \<le> norm z / (R - norm z) * C"
              if R: "norm z < R" "R < r" for R
      proof -
        have "0 < R" using R
          by (metis less_trans norm_zero zero_less_norm_iff)
        have df_le: "\<And>x. norm x < r \<Longrightarrow> norm (deriv f x) \<le> C"
          using le by (simp add: C_def)
        have hol_df: "deriv f holomorphic_on cball 0 R"
          apply (rule holomorphic_on_subset) using R holdf' by auto
        have *: "((\<lambda>w. deriv f w / (w - z)) has_contour_integral 2 * pi * \<i> * deriv f z) (circlepath 0 R)"
                 if "norm z < R" for z
          using \<open>0 < R\<close> that Cauchy_integral_formula_convex_simple [OF convex_cball hol_df, of _ "circlepath 0 R"]
          by (force simp: winding_number_circlepath)
        have **: "((\<lambda>x. deriv f x / (x - z) - deriv f x / x) has_contour_integral
                   of_real (2 * pi) * \<i> * (deriv f z - deriv f 0))
                  (circlepath 0 R)"
           using has_contour_integral_diff [OF * [of z] * [of 0]] \<open>0 < R\<close> that
           by (simp add: algebra_simps)
        have [simp]: "\<And>x. norm x = R \<Longrightarrow> x \<noteq> z"  using that(1) by blast
        have "norm (deriv f x / (x - z) - deriv f x / x)
                     \<le> C * norm z / (R * (R - norm z))"
                  if "norm x = R" for x
        proof -
          have [simp]: "norm (deriv f x * x - deriv f x * (x - z)) =
                        norm (deriv f x) * norm z"
            by (simp add: norm_mult right_diff_distrib')
          show ?thesis
            using  \<open>0 < R\<close> \<open>0 < C\<close> R that
            apply (simp add: norm_mult norm_divide divide_simps)
            using df_le norm_triangle_ineq2 \<open>0 < C\<close> apply (auto intro!: mult_mono)
            done
        qed
        then show ?thesis
          using has_contour_integral_bound_circlepath
                  [OF **, of "C * norm z/(R*(R - norm z))"]
                \<open>0 < R\<close> \<open>0 < C\<close> R
          apply (simp add: norm_mult norm_divide)
          apply (simp add: divide_simps mult.commute)
          done
      qed
      obtain r' where r': "norm z < r'" "r' < r"
        using Rats_dense_in_real [of "norm z" r] \<open>norm z < r\<close> by blast
      then have [simp]: "closure {r'<..<r} = {r'..r}" by simp
      show ?thesis
        apply (rule continuous_ge_on_closure
                 [where f = "\<lambda>r. norm z / (r - norm z) * C" and s = "{r'<..<r}",
                  OF _ _ T1])
        apply (intro continuous_intros)
        using that r'
        apply (auto simp: not_le)
        done
    qed
    have "*": "(norm z - norm z^2/(r - norm z)) * norm(deriv f 0) \<le> norm(f z)"
              if r: "norm z < r" for z
    proof -
      have 1: "\<And>x. x \<in> ball 0 r \<Longrightarrow>
              ((\<lambda>z. f z - deriv f 0 * z) has_field_derivative deriv f x - deriv f 0)
               (at x within ball 0 r)"
        by (rule derivative_eq_intros holomorphic_derivI holf' | simp)+
      have 2: "closed_segment 0 z \<subseteq> ball 0 r"
        by (metis \<open>0 < r\<close> convex_ball convex_contains_segment dist_self mem_ball mem_ball_0 that)
      have 3: "(\<lambda>t. (norm z)\<^sup>2 * t / (r - norm z) * C) integrable_on {0..1}"
        apply (rule integrable_on_cmult_right [where 'b=real, simplified])
        apply (rule integrable_on_cdivide [where 'b=real, simplified])
        apply (rule integrable_on_cmult_left [where 'b=real, simplified])
        apply (rule ident_integrable_on)
        done
      have 4: "norm (deriv f (x *\<^sub>R z) - deriv f 0) * norm z \<le> norm z * norm z * x * C / (r - norm z)"
              if x: "0 \<le> x" "x \<le> 1" for x
      proof -
        have [simp]: "x * norm z < r"
          using r x by (meson le_less_trans mult_le_cancel_right2 norm_not_less_zero)
        have "norm (deriv f (x *\<^sub>R z) - deriv f 0) \<le> norm (x *\<^sub>R z) / (r - norm (x *\<^sub>R z)) * C"
          apply (rule Le1) using r x \<open>0 < r\<close> by simp
        also have "... \<le> norm (x *\<^sub>R z) / (r - norm z) * C"
          using r x \<open>0 < r\<close>
          apply (simp add: divide_simps)
          by (simp add: \<open>0 < C\<close> mult.assoc mult_left_le_one_le ordered_comm_semiring_class.comm_mult_left_mono)
        finally have "norm (deriv f (x *\<^sub>R z) - deriv f 0) * norm z \<le> norm (x *\<^sub>R z)  / (r - norm z) * C * norm z"
          by (rule mult_right_mono) simp
        with x show ?thesis by (simp add: algebra_simps)
      qed
      have le_norm: "abc \<le> norm d - e \<Longrightarrow> norm(f - d) \<le> e \<Longrightarrow> abc \<le> norm f" for abc d e and f::complex
        by (metis add_diff_cancel_left' add_diff_eq diff_left_mono norm_diff_ineq order_trans)
      have "norm (integral {0..1} (\<lambda>x. (deriv f (x *\<^sub>R z) - deriv f 0) * z))
            \<le> integral {0..1} (\<lambda>t. (norm z)\<^sup>2 * t / (r - norm z) * C)"
        apply (rule integral_norm_bound_integral)
        using contour_integral_primitive [OF 1, of "linepath 0 z"] 2
        apply (simp add: has_contour_integral_linepath has_integral_integrable_integral)
        apply (rule 3)
        apply (simp add: norm_mult power2_eq_square 4)
        done
      then have int_le: "norm (f z - deriv f 0 * z) \<le> (norm z)\<^sup>2 * norm(deriv f 0) / ((r - norm z))"
        using contour_integral_primitive [OF 1, of "linepath 0 z"] 2
        apply (simp add: has_contour_integral_linepath has_integral_integrable_integral C_def)
        done
      show ?thesis
        apply (rule le_norm [OF _ int_le])
        using \<open>norm z < r\<close>
        apply (simp add: power2_eq_square divide_simps C_def norm_mult)
        proof -
          have "norm z * (norm (deriv f 0) * (r - norm z - norm z)) \<le> norm z * (norm (deriv f 0) * (r - norm z) - norm (deriv f 0) * norm z)"
            by (simp add: linordered_field_class.sign_simps(38))
          then show "(norm z * (r - norm z) - norm z * norm z) * norm (deriv f 0) \<le> norm (deriv f 0) * norm z * (r - norm z) - norm z * norm z * norm (deriv f 0)"
            by (simp add: linordered_field_class.sign_simps(38) mult.commute mult.left_commute)
        qed
    qed
    have sq201 [simp]: "0 < (1 - sqrt 2 / 2)" "(1 - sqrt 2 / 2)  < 1"
      by (auto simp:  sqrt2_less_2)
    have 1: "continuous_on (closure (ball 0 ((1 - sqrt 2 / 2) * r))) f"
      apply (rule continuous_on_subset [OF holomorphic_on_imp_continuous_on [OF holf]])
      apply (subst closure_ball)
      using \<open>0 < r\<close> mult_pos_pos sq201
      apply (auto simp: cball_subset_cball_iff)
      done
    have 2: "open (f ` interior (ball 0 ((1 - sqrt 2 / 2) * r)))"
      apply (rule open_mapping_thm [OF holf' open_ball connected_ball], force)
      using \<open>0 < r\<close> mult_pos_pos sq201 apply (simp add: ball_subset_ball_iff)
      using False \<open>0 < r\<close> centre_in_ball holf' holomorphic_nonconstant by blast
    have "ball 0 ((3 - 2 * sqrt 2) * r * norm (deriv f 0)) =
          ball (f 0) ((3 - 2 * sqrt 2) * r * norm (deriv f 0))"
      by simp
    also have "...  \<subseteq> f ` ball 0 ((1 - sqrt 2 / 2) * r)"
    proof -
      have 3: "(3 - 2 * sqrt 2) * r * norm (deriv f 0) \<le> norm (f z)"
           if "norm z = (1 - sqrt 2 / 2) * r" for z
        apply (rule order_trans [OF _ *])
        using  \<open>0 < r\<close>
        apply (simp_all add: field_simps  power2_eq_square that)
        apply (simp add: mult.assoc [symmetric])
        done
      show ?thesis
        apply (rule ball_subset_open_map_image [OF 1 2 _ bounded_ball])
        using \<open>0 < r\<close> sq201 3 apply simp_all
        using C_def \<open>0 < C\<close> sq3 apply force
        done
     qed
    also have "...  \<subseteq> f ` ball 0 r"
      apply (rule image_subsetI [OF imageI], simp)
      apply (erule less_le_trans)
      using \<open>0 < r\<close> apply (auto simp: field_simps)
      done
    finally show ?thesis .
  qed
qed

lemma Bloch_lemma:
  assumes holf: "f holomorphic_on cball a r" and "0 < r"
      and le: "\<And>z. z \<in> ball a r \<Longrightarrow> norm(deriv f z) \<le> 2 * norm(deriv f a)"
    shows "ball (f a) ((3 - 2 * sqrt 2) * r * norm(deriv f a)) \<subseteq> f ` ball a r"
proof -
  have fz: "(\<lambda>z. f (a + z)) = f o (\<lambda>z. (a + z))"
    by (simp add: o_def)
  have hol0: "(\<lambda>z. f (a + z)) holomorphic_on cball 0 r"
    unfolding fz by (intro holomorphic_intros holf holomorphic_on_compose | simp)+
  then have [simp]: "\<And>x. norm x < r \<Longrightarrow> (\<lambda>z. f (a + z)) field_differentiable at x"
    by (metis Topology_Euclidean_Space.open_ball at_within_open ball_subset_cball diff_0 dist_norm holomorphic_on_def holomorphic_on_subset mem_ball norm_minus_cancel)
  have [simp]: "\<And>z. norm z < r \<Longrightarrow> f field_differentiable at (a + z)"
    by (metis holf open_ball add_diff_cancel_left' dist_complex_def holomorphic_on_imp_differentiable_at holomorphic_on_subset interior_cball interior_subset mem_ball norm_minus_commute)
  then have [simp]: "f field_differentiable at a"
    by (metis add.comm_neutral \<open>0 < r\<close> norm_eq_zero)
  have hol1: "(\<lambda>z. f (a + z) - f a) holomorphic_on cball 0 r"
    by (intro holomorphic_intros hol0)
  then have "ball 0 ((3 - 2 * sqrt 2) * r * norm (deriv (\<lambda>z. f (a + z) - f a) 0))
             \<subseteq> (\<lambda>z. f (a + z) - f a) ` ball 0 r"
    apply (rule Bloch_lemma_0)
    apply (simp_all add: \<open>0 < r\<close>)
    apply (simp add: fz complex_derivative_chain)
    apply (simp add: dist_norm le)
    done
  then show ?thesis
    apply clarify
    apply (drule_tac c="x - f a" in subsetD)
     apply (force simp: fz \<open>0 < r\<close> dist_norm complex_derivative_chain field_differentiable_compose)+
    done
qed

proposition Bloch_unit:
  assumes holf: "f holomorphic_on ball a 1" and [simp]: "deriv f a = 1"
  obtains b r where "1/12 < r" "ball b r \<subseteq> f ` (ball a 1)"
proof -
  define r :: real where "r = 249/256"
  have "0 < r" "r < 1" by (auto simp: r_def)
  define g where "g z = deriv f z * of_real(r - norm(z - a))" for z
  have "deriv f holomorphic_on ball a 1"
    by (rule holomorphic_deriv [OF holf open_ball])
  then have "continuous_on (ball a 1) (deriv f)"
    using holomorphic_on_imp_continuous_on by blast
  then have "continuous_on (cball a r) (deriv f)"
    by (rule continuous_on_subset) (simp add: cball_subset_ball_iff \<open>r < 1\<close>)
  then have "continuous_on (cball a r) g"
    by (simp add: g_def continuous_intros)
  then have 1: "compact (g ` cball a r)"
    by (rule compact_continuous_image [OF _ compact_cball])
  have 2: "g ` cball a r \<noteq> {}"
    using \<open>r > 0\<close> by auto
  obtain p where pr: "p \<in> cball a r"
             and pge: "\<And>y. y \<in> cball a r \<Longrightarrow> norm (g y) \<le> norm (g p)"
    using distance_attains_sup [OF 1 2, of 0] by force
  define t where "t = (r - norm(p - a)) / 2"
  have "norm (p - a) \<noteq> r"
    using pge [of a] \<open>r > 0\<close> by (auto simp: g_def norm_mult)
  then have "norm (p - a) < r" using pr
    by (simp add: norm_minus_commute dist_norm)
  then have "0 < t"
    by (simp add: t_def)
  have cpt: "cball p t \<subseteq> ball a r"
    using \<open>0 < t\<close> by (simp add: cball_subset_ball_iff dist_norm t_def field_simps)
  have gen_le_dfp: "norm (deriv f y) * (r - norm (y - a)) / (r - norm (p - a)) \<le> norm (deriv f p)"
            if "y \<in> cball a r" for y
  proof -
    have [simp]: "norm (y - a) \<le> r"
      using that by (simp add: dist_norm norm_minus_commute)
    have "norm (g y) \<le> norm (g p)"
      using pge [OF that] by simp
    then have "norm (deriv f y) * abs (r - norm (y - a)) \<le> norm (deriv f p) * abs (r - norm (p - a))"
      by (simp only: dist_norm g_def norm_mult norm_of_real)
    with that \<open>norm (p - a) < r\<close> show ?thesis
      by (simp add: dist_norm divide_simps)
  qed
  have le_norm_dfp: "r / (r - norm (p - a)) \<le> norm (deriv f p)"
    using gen_le_dfp [of a] \<open>r > 0\<close> by auto
  have 1: "f holomorphic_on cball p t"
    apply (rule holomorphic_on_subset [OF holf])
    using cpt \<open>r < 1\<close> order_subst1 subset_ball by auto
  have 2: "norm (deriv f z) \<le> 2 * norm (deriv f p)" if "z \<in> ball p t" for z
  proof -
    have z: "z \<in> cball a r"
      by (meson ball_subset_cball subsetD cpt that)
    then have "norm(z - a) < r"
      by (metis ball_subset_cball contra_subsetD cpt dist_norm mem_ball norm_minus_commute that)
    have "norm (deriv f z) * (r - norm (z - a)) / (r - norm (p - a)) \<le> norm (deriv f p)"
      using gen_le_dfp [OF z] by simp
    with \<open>norm (z - a) < r\<close> \<open>norm (p - a) < r\<close>
    have "norm (deriv f z) \<le> (r - norm (p - a)) / (r - norm (z - a)) * norm (deriv f p)"
       by (simp add: field_simps)
    also have "... \<le> 2 * norm (deriv f p)"
      apply (rule mult_right_mono)
      using that \<open>norm (p - a) < r\<close> \<open>norm(z - a) < r\<close>
      apply (simp_all add: field_simps t_def dist_norm [symmetric])
      using dist_triangle3 [of z a p] by linarith
    finally show ?thesis .
  qed
  have sqrt2: "sqrt 2 < 2113/1494"
    by (rule real_less_lsqrt) (auto simp: power2_eq_square)
  then have sq3: "0 < 3 - 2 * sqrt 2" by simp
  have "1 / 12 / ((3 - 2 * sqrt 2) / 2) < r"
    using sq3 sqrt2 by (auto simp: field_simps r_def)
  also have "... \<le> cmod (deriv f p) * (r - cmod (p - a))"
    using \<open>norm (p - a) < r\<close> le_norm_dfp   by (simp add: pos_divide_le_eq)
  finally have "1 / 12 < cmod (deriv f p) * (r - cmod (p - a)) * ((3 - 2 * sqrt 2) / 2)"
    using pos_divide_less_eq half_gt_zero_iff sq3 by blast
  then have **: "1 / 12 < (3 - 2 * sqrt 2) * t * norm (deriv f p)"
    using sq3 by (simp add: mult.commute t_def)
  have "ball (f p) ((3 - 2 * sqrt 2) * t * norm (deriv f p)) \<subseteq> f ` ball p t"
    by (rule Bloch_lemma [OF 1 \<open>0 < t\<close> 2])
  also have "... \<subseteq> f ` ball a 1"
    apply (rule image_mono)
    apply (rule order_trans [OF ball_subset_cball])
    apply (rule order_trans [OF cpt])
    using \<open>0 < t\<close> \<open>r < 1\<close> apply (simp add: ball_subset_ball_iff dist_norm)
    done
  finally have "ball (f p) ((3 - 2 * sqrt 2) * t * norm (deriv f p)) \<subseteq> f ` ball a 1" .
  with ** show ?thesis
    by (rule that)
qed


theorem Bloch:
  assumes holf: "f holomorphic_on ball a r" and "0 < r"
      and r': "r' \<le> r * norm (deriv f a) / 12"
  obtains b where "ball b r' \<subseteq> f ` (ball a r)"
proof (cases "deriv f a = 0")
  case True with r' show ?thesis
    using ball_eq_empty that by fastforce
next
  case False
  define C where "C = deriv f a"
  have "0 < norm C" using False by (simp add: C_def)
  have dfa: "f field_differentiable at a"
    apply (rule holomorphic_on_imp_differentiable_at [OF holf])
    using \<open>0 < r\<close> by auto
  have fo: "(\<lambda>z. f (a + of_real r * z)) = f o (\<lambda>z. (a + of_real r * z))"
    by (simp add: o_def)
  have holf': "f holomorphic_on (\<lambda>z. a + complex_of_real r * z) ` ball 0 1"
    apply (rule holomorphic_on_subset [OF holf])
    using \<open>0 < r\<close> apply (force simp: dist_norm norm_mult)
    done
  have 1: "(\<lambda>z. f (a + r * z) / (C * r)) holomorphic_on ball 0 1"
    apply (rule holomorphic_intros holomorphic_on_compose holf' | simp add: fo)+
    using \<open>0 < r\<close> by (simp add: C_def False)
  have "((\<lambda>z. f (a + of_real r * z) / (C * of_real r)) has_field_derivative
        (deriv f (a + of_real r * z) / C)) (at z)"
       if "norm z < 1" for z
  proof -
    have *: "((\<lambda>x. f (a + of_real r * x)) has_field_derivative
           (deriv f (a + of_real r * z) * of_real r)) (at z)"
      apply (simp add: fo)
      apply (rule DERIV_chain [OF field_differentiable_derivI])
      apply (rule holomorphic_on_imp_differentiable_at [OF holf], simp)
      using \<open>0 < r\<close> apply (simp add: dist_norm norm_mult that)
      apply (rule derivative_eq_intros | simp)+
      done
    show ?thesis
      apply (rule derivative_eq_intros * | simp)+
      using \<open>0 < r\<close> by (auto simp: C_def False)
  qed
  have 2: "deriv (\<lambda>z. f (a + of_real r * z) / (C * of_real r)) 0 = 1"
    apply (subst deriv_cdivide_right)
    apply (simp add: field_differentiable_def fo)
    apply (rule exI)
    apply (rule DERIV_chain [OF field_differentiable_derivI])
    apply (simp add: dfa)
    apply (rule derivative_eq_intros | simp add: C_def False fo)+
    using \<open>0 < r\<close>
    apply (simp add: C_def False fo)
    apply (simp add: derivative_intros dfa complex_derivative_chain)
    done
  have sb1: "op * (C * r) ` (\<lambda>z. f (a + of_real r * z) / (C * r)) ` ball 0 1
             \<subseteq> f ` ball a r"
    using \<open>0 < r\<close> by (auto simp: dist_norm norm_mult C_def False)
  have sb2: "ball (C * r * b) r' \<subseteq> op * (C * r) ` ball b t"
             if "1 / 12 < t" for b t
  proof -
    have *: "r * cmod (deriv f a) / 12 \<le> r * (t * cmod (deriv f a))"
      using that \<open>0 < r\<close> less_eq_real_def mult.commute mult.right_neutral mult_left_mono norm_ge_zero times_divide_eq_right
      by auto
    show ?thesis
      apply clarify
      apply (rule_tac x="x / (C * r)" in image_eqI)
      using \<open>0 < r\<close>
      apply (simp_all add: dist_norm norm_mult norm_divide C_def False field_simps)
      apply (erule less_le_trans)
      apply (rule order_trans [OF r' *])
      done
  qed
  show ?thesis
    apply (rule Bloch_unit [OF 1 2])
    apply (rename_tac t)
    apply (rule_tac b="(C * of_real r) * b" in that)
    apply (drule image_mono [where f = "\<lambda>z. (C * of_real r) * z"])
    using sb1 sb2
    apply force
    done
qed

corollary Bloch_general:
  assumes holf: "f holomorphic_on s" and "a \<in> s"
      and tle: "\<And>z. z \<in> frontier s \<Longrightarrow> t \<le> dist a z"
      and rle: "r \<le> t * norm(deriv f a) / 12"
  obtains b where "ball b r \<subseteq> f ` s"
proof -
  consider "r \<le> 0" | "0 < t * norm(deriv f a) / 12" using rle by force
  then show ?thesis
  proof cases
    case 1 then show ?thesis
      by (simp add: Topology_Euclidean_Space.ball_empty that)
  next
    case 2
    show ?thesis
    proof (cases "deriv f a = 0")
      case True then show ?thesis
        using rle by (simp add: Topology_Euclidean_Space.ball_empty that)
    next
      case False
      then have "t > 0"
        using 2 by (force simp: zero_less_mult_iff)
      have "~ ball a t \<subseteq> s \<Longrightarrow> ball a t \<inter> frontier s \<noteq> {}"
        apply (rule connected_Int_frontier [of "ball a t" s], simp_all)
        using \<open>0 < t\<close> \<open>a \<in> s\<close> centre_in_ball apply blast
        done
      with tle have *: "ball a t \<subseteq> s" by fastforce
      then have 1: "f holomorphic_on ball a t"
        using holf using holomorphic_on_subset by blast
      show ?thesis
        apply (rule Bloch [OF 1 \<open>t > 0\<close> rle])
        apply (rule_tac b=b in that)
        using * apply force
        done
    qed
  qed
qed

subsection \<open>Foundations of Cauchy's residue theorem\<close>

text\<open>Wenda Li and LC Paulson (2016). A Formal Proof of Cauchy's Residue Theorem.
    Interactive Theorem Proving\<close>

definition residue :: "(complex \<Rightarrow> complex) \<Rightarrow> complex \<Rightarrow> complex" where
  "residue f z = (SOME int. \<exists>e>0. \<forall>\<epsilon>>0. \<epsilon><e
    \<longrightarrow> (f has_contour_integral 2*pi* \<i> *int) (circlepath z \<epsilon>))"

lemma contour_integral_circlepath_eq:
  assumes "open s" and f_holo:"f holomorphic_on (s-{z})" and "0<e1" "e1\<le>e2"
    and e2_cball:"cball z e2 \<subseteq> s"
  shows
    "f contour_integrable_on circlepath z e1"
    "f contour_integrable_on circlepath z e2"
    "contour_integral (circlepath z e2) f = contour_integral (circlepath z e1) f"
proof -
  define l where "l \<equiv> linepath (z+e2) (z+e1)"
  have [simp]:"valid_path l" "pathstart l=z+e2" "pathfinish l=z+e1" unfolding l_def by auto
  have "e2>0" using \<open>e1>0\<close> \<open>e1\<le>e2\<close> by auto
  have zl_img:"z\<notin>path_image l"
    proof
      assume "z \<in> path_image l"
      then have "e2 \<le> cmod (e2 - e1)"
        using segment_furthest_le[of z "z+e2" "z+e1" "z+e2",simplified] \<open>e1>0\<close> \<open>e2>0\<close> unfolding l_def
        by (auto simp add:closed_segment_commute)
      thus False using \<open>e2>0\<close> \<open>e1>0\<close> \<open>e1\<le>e2\<close>
        apply (subst (asm) norm_of_real)
        by auto
    qed
  define g where "g \<equiv> circlepath z e2 +++ l +++ reversepath (circlepath z e1) +++ reversepath l"
  show [simp]: "f contour_integrable_on circlepath z e2" "f contour_integrable_on (circlepath z e1)"
    proof -
      show "f contour_integrable_on circlepath z e2"
        apply (intro contour_integrable_continuous_circlepath[OF
                continuous_on_subset[OF holomorphic_on_imp_continuous_on[OF f_holo]]])
        using \<open>e2>0\<close> e2_cball by auto
      show "f contour_integrable_on (circlepath z e1)"
        apply (intro contour_integrable_continuous_circlepath[OF
                      continuous_on_subset[OF holomorphic_on_imp_continuous_on[OF f_holo]]])
        using \<open>e1>0\<close> \<open>e1\<le>e2\<close> e2_cball by auto
    qed
  have [simp]:"f contour_integrable_on l"
    proof -
      have "closed_segment (z + e2) (z + e1) \<subseteq> cball z e2" using \<open>e2>0\<close> \<open>e1>0\<close> \<open>e1\<le>e2\<close>
        by (intro closed_segment_subset,auto simp add:dist_norm)
      hence "closed_segment (z + e2) (z + e1) \<subseteq> s - {z}" using zl_img e2_cball unfolding l_def
        by auto
      then show "f contour_integrable_on l" unfolding l_def
        apply (intro contour_integrable_continuous_linepath[OF
                      continuous_on_subset[OF holomorphic_on_imp_continuous_on[OF f_holo]]])
        by auto
    qed
  let ?ig="\<lambda>g. contour_integral g f"
  have "(f has_contour_integral 0) g"
    proof (rule Cauchy_theorem_global[OF _ f_holo])
      show "open (s - {z})" using \<open>open s\<close> by auto
      show "valid_path g" unfolding g_def l_def by auto
      show "pathfinish g = pathstart g" unfolding g_def l_def by auto
    next
      have path_img:"path_image g \<subseteq> cball z e2"
        proof -
          have "closed_segment (z + e2) (z + e1) \<subseteq> cball z e2" using \<open>e2>0\<close> \<open>e1>0\<close> \<open>e1\<le>e2\<close>
            by (intro closed_segment_subset,auto simp add:dist_norm)
          moreover have "sphere z \<bar>e1\<bar> \<subseteq> cball z e2" using \<open>e2>0\<close> \<open>e1\<le>e2\<close> \<open>e1>0\<close> by auto
          ultimately show ?thesis unfolding g_def l_def using \<open>e2>0\<close>
            by (simp add: path_image_join closed_segment_commute)
        qed
      show "path_image g \<subseteq> s - {z}"
        proof -
          have "z\<notin>path_image g" using zl_img
            unfolding g_def l_def by (auto simp add: path_image_join closed_segment_commute)
          moreover note \<open>cball z e2 \<subseteq> s\<close> and path_img
          ultimately show ?thesis by auto
        qed
      show "winding_number g w = 0" when"w \<notin> s - {z}" for w
        proof -
          have "winding_number g w = 0" when "w\<notin>s" using that e2_cball
            apply (intro winding_number_zero_outside[OF _ _ _ _ path_img])
            by (auto simp add:g_def l_def)
          moreover have "winding_number g z=0"
            proof -
              let ?Wz="\<lambda>g. winding_number g z"
              have "?Wz g = ?Wz (circlepath z e2) + ?Wz l + ?Wz (reversepath (circlepath z e1))
                  + ?Wz (reversepath l)"
                using \<open>e2>0\<close> \<open>e1>0\<close> zl_img unfolding g_def l_def
                by (subst winding_number_join,auto simp add:path_image_join closed_segment_commute)+
              also have "... = ?Wz (circlepath z e2) + ?Wz (reversepath (circlepath z e1))"
                using zl_img
                apply (subst (2) winding_number_reversepath)
                by (auto simp add:l_def closed_segment_commute)
              also have "... = 0"
                proof -
                  have "?Wz (circlepath z e2) = 1" using \<open>e2>0\<close>
                    by (auto intro: winding_number_circlepath_centre)
                  moreover have "?Wz (reversepath (circlepath z e1)) = -1" using \<open>e1>0\<close>
                    apply (subst winding_number_reversepath)
                    by (auto intro: winding_number_circlepath_centre)
                  ultimately show ?thesis by auto
                qed
              finally show ?thesis .
            qed
          ultimately show ?thesis using that by auto
        qed
    qed
  then have "0 = ?ig g" using contour_integral_unique by simp
  also have "... = ?ig (circlepath z e2) + ?ig l + ?ig (reversepath (circlepath z e1))
      + ?ig (reversepath l)"
    unfolding g_def
    by (auto simp add:contour_integrable_reversepath_eq)
  also have "... = ?ig (circlepath z e2)  - ?ig (circlepath z e1)"
    by (auto simp add:contour_integral_reversepath)
  finally show "contour_integral (circlepath z e2) f = contour_integral (circlepath z e1) f"
    by simp
qed

lemma base_residue:
  assumes "open s" "z\<in>s" "r>0" and f_holo:"f holomorphic_on (s - {z})"
    and r_cball:"cball z r \<subseteq> s"
  shows "(f has_contour_integral 2 * pi * \<i> * (residue f z)) (circlepath z r)"
proof -
  obtain e where "e>0" and e_cball:"cball z e \<subseteq> s"
    using open_contains_cball[of s] \<open>open s\<close> \<open>z\<in>s\<close> by auto
  define c where "c \<equiv> 2 * pi * \<i>"
  define i where "i \<equiv> contour_integral (circlepath z e) f / c"
  have "(f has_contour_integral c*i) (circlepath z \<epsilon>)" when "\<epsilon>>0" "\<epsilon><e" for \<epsilon>
    proof -
      have "contour_integral (circlepath z e) f = contour_integral (circlepath z \<epsilon>) f"
          "f contour_integrable_on circlepath z \<epsilon>"
          "f contour_integrable_on circlepath z e"
        using \<open>\<epsilon><e\<close>
        by (intro contour_integral_circlepath_eq[OF \<open>open s\<close> f_holo \<open>\<epsilon>>0\<close> _ e_cball],auto)+
      then show ?thesis unfolding i_def c_def
        by (auto intro:has_contour_integral_integral)
    qed
  then have "\<exists>e>0. \<forall>\<epsilon>>0. \<epsilon><e \<longrightarrow> (f has_contour_integral c * (residue f z)) (circlepath z \<epsilon>)"
    unfolding residue_def c_def
    apply (rule_tac someI[of _ i],intro  exI[where x=e])
    by (auto simp add:\<open>e>0\<close> c_def)
  then obtain e' where "e'>0"
      and e'_def:"\<forall>\<epsilon>>0. \<epsilon><e' \<longrightarrow> (f has_contour_integral c * (residue f z)) (circlepath z \<epsilon>)"
    by auto
  let ?int="\<lambda>e. contour_integral (circlepath z e) f"
  def \<epsilon>\<equiv>"Min {r,e'} / 2"
  have "\<epsilon>>0" "\<epsilon>\<le>r" "\<epsilon><e'" using \<open>r>0\<close> \<open>e'>0\<close> unfolding \<epsilon>_def by auto
  have "(f has_contour_integral c * (residue f z)) (circlepath z \<epsilon>)"
    using e'_def[rule_format,OF \<open>\<epsilon>>0\<close> \<open>\<epsilon><e'\<close>] .
  then show ?thesis unfolding c_def
    using contour_integral_circlepath_eq[OF \<open>open s\<close> f_holo \<open>\<epsilon>>0\<close> \<open>\<epsilon>\<le>r\<close> r_cball]
    by (auto elim: has_contour_integral_eqpath[of _ _ "circlepath z \<epsilon>" "circlepath z r"])
qed


lemma residue_holo:
  assumes "open s" "z \<in> s" and f_holo: "f holomorphic_on s"
  shows "residue f z = 0"
proof -
  define c where "c \<equiv> 2 * pi * \<i>"
  obtain e where "e>0" and e_cball:"cball z e \<subseteq> s" using \<open>open s\<close> \<open>z\<in>s\<close>
    using open_contains_cball_eq by blast
  have "(f has_contour_integral c*residue f z) (circlepath z e)"
    using f_holo
    by (auto intro: base_residue[OF \<open>open s\<close> \<open>z\<in>s\<close> \<open>e>0\<close> _ e_cball,folded c_def])
  moreover have "(f has_contour_integral 0) (circlepath z e)"
    using f_holo e_cball \<open>e>0\<close>
    by (auto intro: Cauchy_theorem_convex_simple[of _ "cball z e"])
  ultimately have "c*residue f z =0"
    using has_contour_integral_unique by blast
  thus ?thesis unfolding c_def  by auto
qed


lemma residue_const:"residue (\<lambda>_. c) z = 0"
  by (intro residue_holo[of "UNIV::complex set"],auto intro:holomorphic_intros)


lemma residue_add:
  assumes "open s" "z \<in> s" and f_holo: "f holomorphic_on s - {z}"
      and g_holo:"g holomorphic_on s - {z}"
  shows "residue (\<lambda>z. f z + g z) z= residue f z + residue g z"
proof -
  define c where "c \<equiv> 2 * pi * \<i>"
  define fg where "fg \<equiv> (\<lambda>z. f z+g z)"
  obtain e where "e>0" and e_cball:"cball z e \<subseteq> s" using \<open>open s\<close> \<open>z\<in>s\<close>
    using open_contains_cball_eq by blast
  have "(fg has_contour_integral c * residue fg z) (circlepath z e)"
    unfolding fg_def using f_holo g_holo
    apply (intro base_residue[OF \<open>open s\<close> \<open>z\<in>s\<close> \<open>e>0\<close> _ e_cball,folded c_def])
    by (auto intro:holomorphic_intros)
  moreover have "(fg has_contour_integral c*residue f z + c* residue g z) (circlepath z e)"
    unfolding fg_def using f_holo g_holo
    by (auto intro: has_contour_integral_add base_residue[OF \<open>open s\<close> \<open>z\<in>s\<close> \<open>e>0\<close> _ e_cball,folded c_def])
  ultimately have "c*(residue f z + residue g z) = c * residue fg z"
    using has_contour_integral_unique by (auto simp add:distrib_left)
  thus ?thesis unfolding fg_def
    by (auto simp add:c_def)
qed


lemma residue_lmul:
  assumes "open s" "z \<in> s" and f_holo: "f holomorphic_on s - {z}"
  shows "residue (\<lambda>z. c * (f z)) z= c * residue f z"
proof (cases "c=0")
  case True
  thus ?thesis using residue_const by auto
next
  case False
  def c'\<equiv>"2 * pi * \<i>"
  def f'\<equiv>"(\<lambda>z. c * (f z))"
  obtain e where "e>0" and e_cball:"cball z e \<subseteq> s" using \<open>open s\<close> \<open>z\<in>s\<close>
    using open_contains_cball_eq by blast
  have "(f' has_contour_integral c' * residue f' z) (circlepath z e)"
    unfolding f'_def using f_holo
    apply (intro base_residue[OF \<open>open s\<close> \<open>z\<in>s\<close> \<open>e>0\<close> _ e_cball,folded c'_def])
    by (auto intro:holomorphic_intros)
  moreover have "(f' has_contour_integral c * (c' * residue f z)) (circlepath z e)"
    unfolding f'_def using f_holo
    by (auto intro: has_contour_integral_lmul
      base_residue[OF \<open>open s\<close> \<open>z\<in>s\<close> \<open>e>0\<close> _ e_cball,folded c'_def])
  ultimately have "c' * residue f' z  = c * (c' * residue f z)"
    using has_contour_integral_unique by auto
  thus ?thesis unfolding f'_def c'_def using False
    by (auto simp add:field_simps)
qed

lemma residue_rmul:
  assumes "open s" "z \<in> s" and f_holo: "f holomorphic_on s - {z}"
  shows "residue (\<lambda>z. (f z) * c) z= residue f z * c"
using residue_lmul[OF assms,of c] by (auto simp add:algebra_simps)

lemma residue_div:
  assumes "open s" "z \<in> s" and f_holo: "f holomorphic_on s - {z}"
  shows "residue (\<lambda>z. (f z) / c) z= residue f z / c "
using residue_lmul[OF assms,of "1/c"] by (auto simp add:algebra_simps)

lemma residue_neg:
  assumes "open s" "z \<in> s" and f_holo: "f holomorphic_on s - {z}"
  shows "residue (\<lambda>z. - (f z)) z= - residue f z"
using residue_lmul[OF assms,of "-1"] by auto

lemma residue_diff:
  assumes "open s" "z \<in> s" and f_holo: "f holomorphic_on s - {z}"
      and g_holo:"g holomorphic_on s - {z}"
  shows "residue (\<lambda>z. f z - g z) z= residue f z - residue g z"
using residue_add[OF assms(1,2,3),of "\<lambda>z. - g z"] residue_neg[OF assms(1,2,4)]
by (auto intro:holomorphic_intros g_holo)

lemma residue_simple:
  assumes "open s" "z\<in>s" and f_holo:"f holomorphic_on s"
  shows "residue (\<lambda>w. f w / (w - z)) z = f z"
proof -
  define c where "c \<equiv> 2 * pi * \<i>"
  def f'\<equiv>"\<lambda>w. f w / (w - z)"
  obtain e where "e>0" and e_cball:"cball z e \<subseteq> s" using \<open>open s\<close> \<open>z\<in>s\<close>
    using open_contains_cball_eq by blast
  have "(f' has_contour_integral c * f z) (circlepath z e)"
    unfolding f'_def c_def using \<open>e>0\<close> f_holo e_cball
    by (auto intro!: Cauchy_integral_circlepath_simple holomorphic_intros)
  moreover have "(f' has_contour_integral c * residue f' z) (circlepath z e)"
    unfolding f'_def using f_holo
    apply (intro base_residue[OF \<open>open s\<close> \<open>z\<in>s\<close> \<open>e>0\<close> _ e_cball,folded c_def])
    by (auto intro!:holomorphic_intros)
  ultimately have "c * f z = c * residue f' z"
    using has_contour_integral_unique by blast
  thus ?thesis unfolding c_def f'_def  by auto
qed



subsubsection \<open>Cauchy's residue theorem\<close>

lemma get_integrable_path:
  assumes "open s" "connected (s-pts)" "finite pts" "f holomorphic_on (s-pts) " "a\<in>s-pts" "b\<in>s-pts"
  obtains g where "valid_path g" "pathstart g = a" "pathfinish g = b"
    "path_image g \<subseteq> s-pts" "f contour_integrable_on g" using assms
proof (induct arbitrary:s thesis a rule:finite_induct[OF \<open>finite pts\<close>])
  case 1
  obtain g where "valid_path g" "path_image g \<subseteq> s" "pathstart g = a" "pathfinish g = b"
    using connected_open_polynomial_connected[OF \<open>open s\<close>,of a b ] \<open>connected (s - {})\<close>
      valid_path_polynomial_function "1.prems"(6) "1.prems"(7) by auto
  moreover have "f contour_integrable_on g"
    using contour_integrable_holomorphic_simple[OF _ \<open>open s\<close> \<open>valid_path g\<close> \<open>path_image g \<subseteq> s\<close>,of f]
      \<open>f holomorphic_on s - {}\<close>
    by auto
  ultimately show ?case using "1"(1)[of g] by auto
next
  case idt:(2 p pts)
  obtain e where "e>0" and e:"\<forall>w\<in>ball a e. w \<in> s \<and> (w \<noteq> a \<longrightarrow> w \<notin> insert p pts)"
    using finite_ball_avoid[OF \<open>open s\<close> \<open>finite (insert p pts)\<close>, of a]
      \<open>a \<in> s - insert p pts\<close>
    by auto
  define a' where "a' \<equiv> a+e/2"
  have "a'\<in>s-{p} -pts"  using e[rule_format,of "a+e/2"] \<open>e>0\<close>
    by (auto simp add:dist_complex_def a'_def)
  then obtain g' where g'[simp]:"valid_path g'" "pathstart g' = a'" "pathfinish g' = b"
    "path_image g' \<subseteq> s - {p} - pts" "f contour_integrable_on g'"
    using idt.hyps(3)[of a' "s-{p}"] idt.prems idt.hyps(1)
    by (metis Diff_insert2 open_delete)
  define g where "g \<equiv> linepath a a' +++ g'"
  have "valid_path g" unfolding g_def by (auto intro: valid_path_join)
  moreover have "pathstart g = a" and  "pathfinish g = b" unfolding g_def by auto
  moreover have "path_image g \<subseteq> s - insert p pts" unfolding g_def
    proof (rule subset_path_image_join)
      have "closed_segment a a' \<subseteq> ball a e" using \<open>e>0\<close>
        by (auto dest!:segment_bound1 simp:a'_def dist_complex_def norm_minus_commute)
      then show "path_image (linepath a a') \<subseteq> s - insert p pts" using e idt(9)
        by auto
    next
      show "path_image g' \<subseteq> s - insert p pts" using g'(4) by blast
    qed
  moreover have "f contour_integrable_on g"
    proof -
      have "closed_segment a a' \<subseteq> ball a e" using \<open>e>0\<close>
        by (auto dest!:segment_bound1 simp:a'_def dist_complex_def norm_minus_commute)
      then have "continuous_on (closed_segment a a') f"
        using e idt.prems(6) holomorphic_on_imp_continuous_on[OF idt.prems(5)]
        apply (elim continuous_on_subset)
        by auto
      then have "f contour_integrable_on linepath a a'"
        using contour_integrable_continuous_linepath by auto
      then show ?thesis unfolding g_def
        apply (rule contour_integrable_joinI)
        by (auto simp add: \<open>e>0\<close>)
    qed
  ultimately show ?case using idt.prems(1)[of g] by auto
qed

lemma Cauchy_theorem_aux:
  assumes "open s" "connected (s-pts)" "finite pts" "pts \<subseteq> s" "f holomorphic_on s-pts"
          "valid_path g" "pathfinish g = pathstart g" "path_image g \<subseteq> s-pts"
          "\<forall>z. (z \<notin> s) \<longrightarrow> winding_number g z  = 0"
          "\<forall>p\<in>s. h p>0 \<and> (\<forall>w\<in>cball p (h p). w\<in>s \<and> (w\<noteq>p \<longrightarrow> w \<notin> pts))"
  shows "contour_integral g f = (\<Sum>p\<in>pts. winding_number g p * contour_integral (circlepath p (h p)) f)"
    using assms
proof (induct arbitrary:s g rule:finite_induct[OF \<open>finite pts\<close>])
  case 1
  then show ?case by (simp add: Cauchy_theorem_global contour_integral_unique)
next
  case (2 p pts)
  note fin[simp] = \<open>finite (insert p pts)\<close>
    and connected = \<open>connected (s - insert p pts)\<close>
    and valid[simp] = \<open>valid_path g\<close>
    and g_loop[simp] = \<open>pathfinish g = pathstart g\<close>
    and holo[simp]= \<open>f holomorphic_on s - insert p pts\<close>
    and path_img = \<open>path_image g \<subseteq> s - insert p pts\<close>
    and winding = \<open>\<forall>z. z \<notin> s \<longrightarrow> winding_number g z = 0\<close>
    and h = \<open>\<forall>pa\<in>s. 0 < h pa \<and> (\<forall>w\<in>cball pa (h pa). w \<in> s \<and> (w \<noteq> pa \<longrightarrow> w \<notin> insert p pts))\<close>
  have "h p>0" and "p\<in>s"
    and h_p: "\<forall>w\<in>cball p (h p). w \<in> s \<and> (w \<noteq> p \<longrightarrow> w \<notin> insert p pts)"
    using h \<open>insert p pts \<subseteq> s\<close> by auto
  obtain pg where pg[simp]: "valid_path pg" "pathstart pg = pathstart g" "pathfinish pg=p+h p"
      "path_image pg \<subseteq> s-insert p pts" "f contour_integrable_on pg"
    proof -
      have "p + h p\<in>cball p (h p)" using h[rule_format,of p]
        by (simp add: \<open>p \<in> s\<close> dist_norm)
      then have "p + h p \<in> s - insert p pts" using h[rule_format,of p] \<open>insert p pts \<subseteq> s\<close>
        by fastforce
      moreover have "pathstart g \<in> s - insert p pts " using path_img by auto
      ultimately show ?thesis
        using get_integrable_path[OF \<open>open s\<close> connected fin holo,of "pathstart g" "p+h p"] that
        by blast
    qed
  obtain n::int where "n=winding_number g p"
    using integer_winding_number[OF _ g_loop,of p] valid path_img
    by (metis DiffD2 Ints_cases insertI1 subset_eq valid_path_imp_path)
  define p_circ where "p_circ \<equiv> circlepath p (h p)"
  define p_circ_pt where "p_circ_pt \<equiv> linepath (p+h p) (p+h p)"
  define n_circ where "n_circ \<equiv> \<lambda>n. (op +++ p_circ ^^ n) p_circ_pt"
  define cp where "cp \<equiv> if n\<ge>0 then reversepath (n_circ (nat n)) else n_circ (nat (- n))"
  have n_circ:"valid_path (n_circ k)"
      "winding_number (n_circ k) p = k"
      "pathstart (n_circ k) = p + h p" "pathfinish (n_circ k) = p + h p"
      "path_image (n_circ k) =  (if k=0 then {p + h p} else sphere p (h p))"
      "p \<notin> path_image (n_circ k)"
      "\<And>p'. p'\<notin>s - pts \<Longrightarrow> winding_number (n_circ k) p'=0 \<and> p'\<notin>path_image (n_circ k)"
      "f contour_integrable_on (n_circ k)"
      "contour_integral (n_circ k) f = k *  contour_integral p_circ f"
      for k
    proof (induct k)
      case 0
      show "valid_path (n_circ 0)"
        and "path_image (n_circ 0) =  (if 0=0 then {p + h p} else sphere p (h p))"
        and "winding_number (n_circ 0) p = of_nat 0"
        and "pathstart (n_circ 0) = p + h p"
        and "pathfinish (n_circ 0) = p + h p"
        and "p \<notin> path_image (n_circ 0)"
        unfolding n_circ_def p_circ_pt_def using \<open>h p > 0\<close>
        by (auto simp add: dist_norm)
      show "winding_number (n_circ 0) p'=0 \<and> p'\<notin>path_image (n_circ 0)" when "p'\<notin>s- pts" for p'
        unfolding n_circ_def p_circ_pt_def
        apply (auto intro!:winding_number_trivial)
        by (metis Diff_iff pathfinish_in_path_image pg(3) pg(4) subsetCE subset_insertI that)+
      show "f contour_integrable_on (n_circ 0)"
        unfolding n_circ_def p_circ_pt_def
        by (auto intro!:contour_integrable_continuous_linepath simp add:continuous_on_sing)
      show "contour_integral (n_circ 0) f = of_nat 0  *  contour_integral p_circ f"
        unfolding n_circ_def p_circ_pt_def by auto
    next
      case (Suc k)
      have n_Suc:"n_circ (Suc k) = p_circ +++ n_circ k" unfolding n_circ_def by auto
      have pcirc:"p \<notin> path_image p_circ" "valid_path p_circ" "pathfinish p_circ = pathstart (n_circ k)"
        using Suc(3) unfolding p_circ_def using \<open>h p > 0\<close> by (auto simp add: p_circ_def)
      have pcirc_image:"path_image p_circ \<subseteq> s - insert p pts"
        proof -
          have "path_image p_circ \<subseteq> cball p (h p)" using \<open>0 < h p\<close> p_circ_def by auto
          then show ?thesis using h_p pcirc(1) by auto
        qed
      have pcirc_integrable:"f contour_integrable_on p_circ"
        by (auto simp add:p_circ_def intro!: pcirc_image[unfolded p_circ_def]
          contour_integrable_continuous_circlepath holomorphic_on_imp_continuous_on
          holomorphic_on_subset[OF holo])
      show "valid_path (n_circ (Suc k))"
        using valid_path_join[OF pcirc(2) Suc(1) pcirc(3)] unfolding n_circ_def by auto
      show "path_image (n_circ (Suc k))
          = (if Suc k = 0 then {p + complex_of_real (h p)} else sphere p (h p))"
        proof -
          have "path_image p_circ = sphere p (h p)"
            unfolding p_circ_def using \<open>0 < h p\<close> by auto
          then show ?thesis unfolding n_Suc  using Suc.hyps(5)  \<open>h p>0\<close>
            by (auto simp add:  path_image_join[OF pcirc(3)]  dist_norm)
        qed
      then show "p \<notin> path_image (n_circ (Suc k))" using \<open>h p>0\<close> by auto
      show "winding_number (n_circ (Suc k)) p = of_nat (Suc k)"
        proof -
          have "winding_number p_circ p = 1"
            by (simp add: \<open>h p > 0\<close> p_circ_def winding_number_circlepath_centre)
          moreover have "p \<notin> path_image (n_circ k)" using Suc(5) \<open>h p>0\<close> by auto
          then have "winding_number (p_circ +++ n_circ k) p
              = winding_number p_circ p + winding_number (n_circ k) p"
            using  valid_path_imp_path Suc.hyps(1) Suc.hyps(2) pcirc
            apply (intro winding_number_join)
            by auto
          ultimately show ?thesis using Suc(2) unfolding n_circ_def
            by auto
        qed
      show "pathstart (n_circ (Suc k)) = p + h p"
        by (simp add: n_circ_def p_circ_def)
      show "pathfinish (n_circ (Suc k)) = p + h p"
        using Suc(4) unfolding n_circ_def by auto
      show "winding_number (n_circ (Suc k)) p'=0 \<and>  p'\<notin>path_image (n_circ (Suc k))" when "p'\<notin>s-pts" for p'
        proof -
          have " p' \<notin> path_image p_circ" using \<open>p \<in> s\<close> h p_circ_def that using pcirc_image by blast
          moreover have "p' \<notin> path_image (n_circ k)"
            using Suc.hyps(7) that by blast
          moreover have "winding_number p_circ p' = 0"
            proof -
              have "path_image p_circ \<subseteq> cball p (h p)"
                using h unfolding p_circ_def using \<open>p \<in> s\<close> by fastforce
              moreover have "p'\<notin>cball p (h p)" using \<open>p \<in> s\<close> h that "2.hyps"(2) by fastforce
              ultimately show ?thesis unfolding p_circ_def
                apply (intro winding_number_zero_outside)
                by auto
            qed
          ultimately show ?thesis
            unfolding n_Suc
            apply (subst winding_number_join)
            by (auto simp: valid_path_imp_path pcirc Suc that not_in_path_image_join Suc.hyps(7)[OF that])
        qed
      show "f contour_integrable_on (n_circ (Suc k))"
        unfolding n_Suc
        by (rule contour_integrable_joinI[OF pcirc_integrable Suc(8) pcirc(2) Suc(1)])
      show "contour_integral (n_circ (Suc k)) f = (Suc k) *  contour_integral p_circ f"
        unfolding n_Suc
        by (auto simp add:contour_integral_join[OF pcirc_integrable Suc(8) pcirc(2) Suc(1)]
          Suc(9) algebra_simps)
    qed
  have cp[simp]:"pathstart cp = p + h p"  "pathfinish cp = p + h p"
         "valid_path cp" "path_image cp \<subseteq> s - insert p pts"
         "winding_number cp p = - n"
         "\<And>p'. p'\<notin>s - pts \<Longrightarrow> winding_number cp p'=0 \<and> p' \<notin> path_image cp"
         "f contour_integrable_on cp"
         "contour_integral cp f = - n * contour_integral p_circ f"
    proof -
      show "pathstart cp = p + h p" and "pathfinish cp = p + h p" and "valid_path cp"
        using n_circ unfolding cp_def by auto
    next
      have "sphere p (h p) \<subseteq>  s - insert p pts"
        using h[rule_format,of p] \<open>insert p pts \<subseteq> s\<close> by force
      moreover  have "p + complex_of_real (h p) \<in> s - insert p pts"
        using pg(3) pg(4) by (metis pathfinish_in_path_image subsetCE)
      ultimately show "path_image cp \<subseteq>  s - insert p pts" unfolding cp_def
        using n_circ(5)  by auto
    next
      show "winding_number cp p = - n"
        unfolding cp_def using winding_number_reversepath n_circ \<open>h p>0\<close>
        by (auto simp: valid_path_imp_path)
    next
      show "winding_number cp p'=0 \<and> p' \<notin> path_image cp" when "p'\<notin>s - pts" for p'
        unfolding cp_def
        apply (auto)
        apply (subst winding_number_reversepath)
        by (auto simp add: valid_path_imp_path n_circ(7)[OF that] n_circ(1))
    next
      show "f contour_integrable_on cp" unfolding cp_def
        using contour_integrable_reversepath_eq n_circ(1,8) by auto
    next
      show "contour_integral cp f = - n * contour_integral p_circ f"
        unfolding cp_def using contour_integral_reversepath[OF n_circ(1)] n_circ(9)
        by auto
    qed
  def g'\<equiv>"g +++ pg +++ cp +++ (reversepath pg)"
  have "contour_integral g' f = (\<Sum>p\<in>pts. winding_number g' p * contour_integral (circlepath p (h p)) f)"
    proof (rule "2.hyps"(3)[of "s-{p}" "g'",OF _ _ \<open>finite pts\<close> ])
      show "connected (s - {p} - pts)" using connected by (metis Diff_insert2)
      show "open (s - {p})" using \<open>open s\<close> by auto
      show " pts \<subseteq> s - {p}" using \<open>insert p pts \<subseteq> s\<close> \<open> p \<notin> pts\<close>  by blast
      show "f holomorphic_on s - {p} - pts" using holo \<open>p \<notin> pts\<close> by (metis Diff_insert2)
      show "valid_path g'"
        unfolding g'_def cp_def using n_circ valid pg g_loop
        by (auto intro!:valid_path_join )
      show "pathfinish g' = pathstart g'"
        unfolding g'_def cp_def using pg(2) by simp
      show "path_image g' \<subseteq> s - {p} - pts"
        proof -
          def s'\<equiv>"s - {p} - pts"
          have s':"s' = s-insert p pts " unfolding s'_def by auto
          then show ?thesis using path_img pg(4) cp(4)
            unfolding g'_def
            apply (fold s'_def s')
            apply (intro subset_path_image_join)
            by auto
        qed
      note path_join_imp[simp]
      show "\<forall>z. z \<notin> s - {p} \<longrightarrow> winding_number g' z = 0"
        proof clarify
          fix z assume z:"z\<notin>s - {p}"
          have "winding_number (g +++ pg +++ cp +++ reversepath pg) z = winding_number g z
              + winding_number (pg +++ cp +++ (reversepath pg)) z"
            proof (rule winding_number_join)
              show "path g" using \<open>valid_path g\<close> by (simp add: valid_path_imp_path)
              show "z \<notin> path_image g" using z path_img by auto
              show "path (pg +++ cp +++ reversepath pg)" using pg(3) cp
                by (simp add: valid_path_imp_path)
            next
              have "path_image (pg +++ cp +++ reversepath pg) \<subseteq> s - insert p pts"
                using pg(4) cp(4) by (auto simp:subset_path_image_join)
              then show "z \<notin> path_image (pg +++ cp +++ reversepath pg)" using z by auto
            next
              show "pathfinish g = pathstart (pg +++ cp +++ reversepath pg)" using g_loop by auto
            qed
          also have "... = winding_number g z + (winding_number pg z
              + winding_number (cp +++ (reversepath pg)) z)"
            proof (subst add_left_cancel,rule winding_number_join)
              show "path pg" and "path (cp +++ reversepath pg)"
               and "pathfinish pg = pathstart (cp +++ reversepath pg)"
                by (auto simp add: valid_path_imp_path)
              show "z \<notin> path_image pg" using pg(4) z by blast
              show "z \<notin> path_image (cp +++ reversepath pg)" using z
                by (metis Diff_iff \<open>z \<notin> path_image pg\<close> contra_subsetD cp(4) insertI1
                  not_in_path_image_join path_image_reversepath singletonD)
            qed
          also have "... = winding_number g z + (winding_number pg z
              + (winding_number cp z + winding_number (reversepath pg) z))"
            apply (auto intro!:winding_number_join simp: valid_path_imp_path)
            apply (metis Diff_iff contra_subsetD cp(4) insertI1 singletonD z)
            by (metis Diff_insert2 Diff_subset contra_subsetD pg(4) z)
          also have "... = winding_number g z + winding_number cp z"
            apply (subst winding_number_reversepath)
            apply (auto simp: valid_path_imp_path)
            by (metis Diff_iff contra_subsetD insertI1 pg(4) singletonD z)
          finally have "winding_number g' z = winding_number g z + winding_number cp z"
            unfolding g'_def .
          moreover have "winding_number g z + winding_number cp z = 0"
            using winding z \<open>n=winding_number g p\<close> by auto
          ultimately show "winding_number g' z = 0" unfolding g'_def by auto
        qed
      show "\<forall>pa\<in>s - {p}. 0 < h pa \<and> (\<forall>w\<in>cball pa (h pa). w \<in> s - {p} \<and> (w \<noteq> pa \<longrightarrow> w \<notin> pts))"
        using h by fastforce
    qed
  moreover have "contour_integral g' f = contour_integral g f
      - winding_number g p * contour_integral p_circ f"
    proof -
      have "contour_integral g' f =  contour_integral g f
        + contour_integral (pg +++ cp +++ reversepath pg) f"
        unfolding g'_def
        apply (subst contour_integral_join)
        by (auto simp add:open_Diff[OF \<open>open s\<close>,OF finite_imp_closed[OF fin]]
          intro!: contour_integrable_holomorphic_simple[OF holo _ _ path_img]
          contour_integrable_reversepath)
      also have "... = contour_integral g f + contour_integral pg f
          + contour_integral (cp +++ reversepath pg) f"
        apply (subst contour_integral_join)
        by (auto simp add:contour_integrable_reversepath)
      also have "... = contour_integral g f + contour_integral pg f
          + contour_integral cp f + contour_integral (reversepath pg) f"
        apply (subst contour_integral_join)
        by (auto simp add:contour_integrable_reversepath)
      also have "... = contour_integral g f + contour_integral cp f"
        using contour_integral_reversepath
        by (auto simp add:contour_integrable_reversepath)
      also have "... = contour_integral g f - winding_number g p * contour_integral p_circ f"
        using \<open>n=winding_number g p\<close> by auto
      finally show ?thesis .
    qed
  moreover have "winding_number g' p' = winding_number g p'" when "p'\<in>pts" for p'
    proof -
      have [simp]: "p' \<notin> path_image g" "p' \<notin> path_image pg" "p'\<notin>path_image cp"
        using "2.prems"(8) that
        apply blast
        apply (metis Diff_iff Diff_insert2 contra_subsetD pg(4) that)
        by (meson DiffD2 cp(4) set_rev_mp subset_insertI that)
      have "winding_number g' p' = winding_number g p'
          + winding_number (pg +++ cp +++ reversepath pg) p'" unfolding g'_def
        apply (subst winding_number_join)
        apply (simp_all add: valid_path_imp_path)
        apply (intro not_in_path_image_join)
        by auto
      also have "... = winding_number g p' + winding_number pg p'
          + winding_number (cp +++ reversepath pg) p'"
        apply (subst winding_number_join)
        apply (simp_all add: valid_path_imp_path)
        apply (intro not_in_path_image_join)
        by auto
      also have "... = winding_number g p' + winding_number pg p'+ winding_number cp p'
          + winding_number (reversepath pg) p'"
        apply (subst winding_number_join)
        by (simp_all add: valid_path_imp_path)
      also have "... = winding_number g p' + winding_number cp p'"
        apply (subst winding_number_reversepath)
        by (simp_all add: valid_path_imp_path)
      also have "... = winding_number g p'" using that by auto
      finally show ?thesis .
    qed
  ultimately show ?case unfolding p_circ_def
    apply (subst (asm) sum.cong[OF refl,
        of pts _ "\<lambda>p. winding_number g p * contour_integral (circlepath p (h p)) f"])
    by (auto simp add:sum.insert[OF \<open>finite pts\<close> \<open>p\<notin>pts\<close>] algebra_simps)
qed

lemma Cauchy_theorem_singularities:
  assumes "open s" "connected s" "finite pts" and
          holo:"f holomorphic_on s-pts" and
          "valid_path g" and
          loop:"pathfinish g = pathstart g" and
          "path_image g \<subseteq> s-pts" and
          homo:"\<forall>z. (z \<notin> s) \<longrightarrow> winding_number g z  = 0" and
          avoid:"\<forall>p\<in>s. h p>0 \<and> (\<forall>w\<in>cball p (h p). w\<in>s \<and> (w\<noteq>p \<longrightarrow> w \<notin> pts))"
  shows "contour_integral g f = (\<Sum>p\<in>pts. winding_number g p * contour_integral (circlepath p (h p)) f)"
    (is "?L=?R")
proof -
  define circ where "circ \<equiv> \<lambda>p. winding_number g p * contour_integral (circlepath p (h p)) f"
  define pts1 where "pts1 \<equiv> pts \<inter> s"
  define pts2 where "pts2 \<equiv> pts - pts1"
  have "pts=pts1 \<union> pts2" "pts1 \<inter> pts2 = {}" "pts2 \<inter> s={}" "pts1\<subseteq>s"
    unfolding pts1_def pts2_def by auto
  have "contour_integral g f =  (\<Sum>p\<in>pts1. circ p)" unfolding circ_def
    proof (rule Cauchy_theorem_aux[OF \<open>open s\<close> _ _ \<open>pts1\<subseteq>s\<close> _ \<open>valid_path g\<close> loop _ homo])
      have "finite pts1" unfolding pts1_def using \<open>finite pts\<close> by auto
      then show "connected (s - pts1)"
        using \<open>open s\<close> \<open>connected s\<close> connected_open_delete_finite[of s] by auto
    next
      show "finite pts1" using \<open>pts = pts1 \<union> pts2\<close> assms(3) by auto
      show "f holomorphic_on s - pts1" by (metis Diff_Int2 Int_absorb holo pts1_def)
      show "path_image g \<subseteq> s - pts1" using assms(7) pts1_def by auto
      show "\<forall>p\<in>s. 0 < h p \<and> (\<forall>w\<in>cball p (h p). w \<in> s \<and> (w \<noteq> p \<longrightarrow> w \<notin> pts1))"
        by (simp add: avoid pts1_def)
    qed
  moreover have "sum circ pts2=0"
    proof -
      have "winding_number g p=0" when "p\<in>pts2" for p
        using  \<open>pts2 \<inter> s={}\<close> that homo[rule_format,of p] by auto
      thus ?thesis unfolding circ_def
        apply (intro sum.neutral)
        by auto
    qed
  moreover have "?R=sum circ pts1 + sum circ pts2"
    unfolding circ_def
    using sum.union_disjoint[OF _ _ \<open>pts1 \<inter> pts2 = {}\<close>] \<open>finite pts\<close> \<open>pts=pts1 \<union> pts2\<close>
    by blast
  ultimately show ?thesis
    apply (fold circ_def)
    by auto
qed

lemma Residue_theorem:
  fixes s pts::"complex set" and f::"complex \<Rightarrow> complex"
    and g::"real \<Rightarrow> complex"
  assumes "open s" "connected s" "finite pts" and
          holo:"f holomorphic_on s-pts" and
          "valid_path g" and
          loop:"pathfinish g = pathstart g" and
          "path_image g \<subseteq> s-pts" and
          homo:"\<forall>z. (z \<notin> s) \<longrightarrow> winding_number g z  = 0"
  shows "contour_integral g f = 2 * pi * \<i> *(\<Sum>p\<in>pts. winding_number g p * residue f p)"
proof -
  define c where "c \<equiv>  2 * pi * \<i>"
  obtain h where avoid:"\<forall>p\<in>s. h p>0 \<and> (\<forall>w\<in>cball p (h p). w\<in>s \<and> (w\<noteq>p \<longrightarrow> w \<notin> pts))"
    using finite_cball_avoid[OF \<open>open s\<close> \<open>finite pts\<close>] by metis
  have "contour_integral g f
      = (\<Sum>p\<in>pts. winding_number g p * contour_integral (circlepath p (h p)) f)"
    using Cauchy_theorem_singularities[OF assms avoid] .
  also have "... = (\<Sum>p\<in>pts.  c * winding_number g p * residue f p)"
    proof (intro sum.cong)
      show "pts = pts" by simp
    next
      fix x assume "x \<in> pts"
      show "winding_number g x * contour_integral (circlepath x (h x)) f
          = c * winding_number g x * residue f x"
        proof (cases "x\<in>s")
          case False
          then have "winding_number g x=0" using homo by auto
          thus ?thesis by auto
        next
          case True
          have "contour_integral (circlepath x (h x)) f = c* residue f x"
            using \<open>x\<in>pts\<close> \<open>finite pts\<close> avoid[rule_format,OF True]
            apply (intro base_residue[of "s-(pts-{x})",THEN contour_integral_unique,folded c_def])
            by (auto intro:holomorphic_on_subset[OF holo] open_Diff[OF \<open>open s\<close> finite_imp_closed])
          then show ?thesis by auto
        qed
    qed
  also have "... = c * (\<Sum>p\<in>pts. winding_number g p * residue f p)"
    by (simp add: sum_distrib_left algebra_simps)
  finally show ?thesis unfolding c_def .
qed

subsection \<open>The argument principle\<close>

definition is_pole :: "('a::topological_space \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'a \<Rightarrow> bool" where
  "is_pole f a =  (LIM x (at a). f x :> at_infinity)"

lemma is_pole_tendsto:
  fixes f::"('a::topological_space \<Rightarrow> 'b::real_normed_div_algebra)"
  shows "is_pole f x \<Longrightarrow> ((inverse o f) \<longlongrightarrow> 0) (at x)"
unfolding is_pole_def
by (auto simp add:filterlim_inverse_at_iff[symmetric] comp_def filterlim_at)

lemma is_pole_inverse_holomorphic:
  assumes "open s"
    and f_holo:"f holomorphic_on (s-{z})"
    and pole:"is_pole f z"
    and non_z:"\<forall>x\<in>s-{z}. f x\<noteq>0"
  shows "(\<lambda>x. if x=z then 0 else inverse (f x)) holomorphic_on s"
proof -
  define g where "g \<equiv> \<lambda>x. if x=z then 0 else inverse (f x)"
  have "isCont g z" unfolding isCont_def  using is_pole_tendsto[OF pole]
    apply (subst Lim_cong_at[where b=z and y=0 and g="inverse \<circ> f"])
    by (simp_all add:g_def)
  moreover have "continuous_on (s-{z}) f" using f_holo holomorphic_on_imp_continuous_on by auto
  hence "continuous_on (s-{z}) (inverse o f)" unfolding comp_def
    by (auto elim!:continuous_on_inverse simp add:non_z)
  hence "continuous_on (s-{z}) g" unfolding g_def
    apply (subst continuous_on_cong[where t="s-{z}" and g="inverse o f"])
    by auto
  ultimately have "continuous_on s g" using open_delete[OF \<open>open s\<close>] \<open>open s\<close>
    by (auto simp add:continuous_on_eq_continuous_at)
  moreover have "(inverse o f) holomorphic_on (s-{z})"
    unfolding comp_def using f_holo
    by (auto elim!:holomorphic_on_inverse simp add:non_z)
  hence "g holomorphic_on (s-{z})"
    apply (subst holomorphic_cong[where t="s-{z}" and g="inverse o f"])
    by (auto simp add:g_def)
  ultimately show ?thesis unfolding g_def using \<open>open s\<close>
    by (auto elim!: no_isolated_singularity)
qed


(*order of the zero of f at z*)
definition zorder::"(complex \<Rightarrow> complex) \<Rightarrow> complex \<Rightarrow> nat" where
  "zorder f z = (THE n. n>0 \<and> (\<exists>h r. r>0 \<and> h holomorphic_on cball z r
                    \<and> (\<forall>w\<in>cball z r. f w =  h w * (w-z)^n \<and> h w \<noteq>0)))"

definition zer_poly::"[complex \<Rightarrow> complex,complex]\<Rightarrow>complex \<Rightarrow> complex" where
  "zer_poly f z = (SOME h. \<exists>r . r>0 \<and> h holomorphic_on cball z r
                    \<and> (\<forall>w\<in>cball z r. f w =  h w * (w-z)^(zorder f z) \<and> h w \<noteq>0))"

(*order of the pole of f at z*)
definition porder::"(complex \<Rightarrow> complex) \<Rightarrow> complex \<Rightarrow> nat" where
  "porder f z = (let f'=(\<lambda>x. if x=z then 0 else inverse (f x)) in zorder f' z)"

definition pol_poly::"[complex \<Rightarrow> complex,complex]\<Rightarrow>complex \<Rightarrow> complex" where
  "pol_poly f z = (let f'=(\<lambda> x. if x=z then 0 else inverse (f x))
      in inverse o zer_poly f' z)"


lemma holomorphic_factor_zero_unique:
  fixes f::"complex \<Rightarrow> complex" and z::complex and r::real
  assumes "r>0"
    and asm:"\<forall>w\<in>ball z r. f w = (w-z)^n * g w \<and> g w\<noteq>0 \<and> f w = (w - z)^m * h w \<and> h w\<noteq>0"
    and g_holo:"g holomorphic_on ball z r" and h_holo:"h holomorphic_on ball z r"
  shows "n=m"
proof -
  have "n>m \<Longrightarrow> False"
    proof -
      assume "n>m"
      have "(h \<longlongrightarrow> 0) (at z within ball z r)"
        proof (rule Lim_transform_within[OF _ \<open>r>0\<close>, where f="\<lambda>w. (w - z) ^ (n - m) * g w"])
          have "\<forall>w\<in>ball z r. w\<noteq>z \<longrightarrow> h w = (w-z)^(n-m) * g w" using \<open>n>m\<close> asm
            by (auto simp add:field_simps power_diff)
          then show "\<lbrakk>x' \<in> ball z r; 0 < dist x' z;dist x' z < r\<rbrakk>
            \<Longrightarrow> (x' - z) ^ (n - m) * g x' = h x'" for x' by auto
        next
          define F where "F \<equiv> at z within ball z r"
          define f' where "f' \<equiv> \<lambda>x. (x - z) ^ (n-m)"
          have "f' z=0" using \<open>n>m\<close> unfolding f'_def by auto
          moreover have "continuous F f'" unfolding f'_def F_def
            by (intro continuous_intros)
          ultimately have "(f' \<longlongrightarrow> 0) F" unfolding F_def
            by (simp add: continuous_within)
          moreover have "(g \<longlongrightarrow> g z) F"
            using holomorphic_on_imp_continuous_on[OF g_holo,unfolded continuous_on_def] \<open>r>0\<close>
            unfolding F_def by auto
          ultimately show " ((\<lambda>w. f' w * g w) \<longlongrightarrow> 0) F" using tendsto_mult by fastforce
        qed
      moreover have "(h \<longlongrightarrow> h z) (at z within ball z r)"
        using holomorphic_on_imp_continuous_on[OF h_holo]
        by (auto simp add:continuous_on_def \<open>r>0\<close>)
      moreover have "at z within ball z r \<noteq> bot" using \<open>r>0\<close>
        by (auto simp add:trivial_limit_within islimpt_ball)
      ultimately have "h z=0" by (auto intro: tendsto_unique)
      thus False using asm \<open>r>0\<close> by auto
    qed
  moreover have "m>n \<Longrightarrow> False"
    proof -
      assume "m>n"
      have "(g \<longlongrightarrow> 0) (at z within ball z r)"
        proof (rule Lim_transform_within[OF _ \<open>r>0\<close>, where f="\<lambda>w. (w - z) ^ (m - n) * h w"])
          have "\<forall>w\<in>ball z r. w\<noteq>z \<longrightarrow> g w = (w-z)^(m-n) * h w" using \<open>m>n\<close> asm
            by (auto simp add:field_simps power_diff)
          then show "\<lbrakk>x' \<in> ball z r; 0 < dist x' z;dist x' z < r\<rbrakk>
            \<Longrightarrow> (x' - z) ^ (m - n) * h x' = g x'" for x' by auto
        next
          define F where "F \<equiv> at z within ball z r"
          define f' where "f' \<equiv>\<lambda>x. (x - z) ^ (m-n)"
          have "f' z=0" using \<open>m>n\<close> unfolding f'_def by auto
          moreover have "continuous F f'" unfolding f'_def F_def
            by (intro continuous_intros)
          ultimately have "(f' \<longlongrightarrow> 0) F" unfolding F_def
            by (simp add: continuous_within)
          moreover have "(h \<longlongrightarrow> h z) F"
            using holomorphic_on_imp_continuous_on[OF h_holo,unfolded continuous_on_def] \<open>r>0\<close>
            unfolding F_def by auto
          ultimately show " ((\<lambda>w. f' w * h w) \<longlongrightarrow> 0) F" using tendsto_mult by fastforce
        qed
      moreover have "(g \<longlongrightarrow> g z) (at z within ball z r)"
        using holomorphic_on_imp_continuous_on[OF g_holo]
        by (auto simp add:continuous_on_def \<open>r>0\<close>)
      moreover have "at z within ball z r \<noteq> bot" using \<open>r>0\<close>
        by (auto simp add:trivial_limit_within islimpt_ball)
      ultimately have "g z=0" by (auto intro: tendsto_unique)
      thus False using asm \<open>r>0\<close> by auto
    qed
  ultimately show "n=m" by fastforce
qed


lemma holomorphic_factor_zero_Ex1:
  assumes "open s" "connected s" "z \<in> s" and
        holo:"f holomorphic_on s"
        and "f z = 0" and "\<exists>w\<in>s. f w \<noteq> 0"
  shows "\<exists>!n. \<exists>g r. 0 < n \<and> 0 < r \<and>
                g holomorphic_on cball z r
                \<and> (\<forall>w\<in>cball z r. f w = (w-z)^n * g w \<and> g w\<noteq>0)"
proof (rule ex_ex1I)
  obtain g r n where "0 < n" "0 < r" "ball z r \<subseteq> s" and
          g:"g holomorphic_on ball z r"
          "\<And>w. w \<in> ball z r \<Longrightarrow> f w = (w - z) ^ n * g w"
          "\<And>w. w \<in> ball z r \<Longrightarrow> g w \<noteq> 0"
    using holomorphic_factor_zero_nonconstant[OF holo \<open>open s\<close> \<open>connected s\<close> \<open>z\<in>s\<close> \<open>f z=0\<close>]
    by (metis assms(3) assms(5) assms(6))
  def r'\<equiv>"r/2"
  have "cball z r' \<subseteq> ball z r" unfolding r'_def by (simp add: \<open>0 < r\<close> cball_subset_ball_iff)
  hence "cball z r' \<subseteq> s" "g holomorphic_on cball z r'"
      "(\<forall>w\<in>cball z r'. f w = (w - z) ^ n * g w \<and> g w \<noteq> 0)"
    using g \<open>ball z r \<subseteq> s\<close> by auto
  moreover have "r'>0" unfolding r'_def using \<open>0<r\<close> by auto
  ultimately show "\<exists>n g r. 0 < n \<and> 0 < r  \<and> g holomorphic_on cball z r
          \<and> (\<forall>w\<in>cball z r. f w = (w - z) ^ n * g w \<and> g w \<noteq> 0)"
    apply (intro exI[of _ n] exI[of _ g] exI[of _ r'])
    by (simp add:\<open>0 < n\<close>)
next
  fix m n
  define fac where "fac \<equiv> \<lambda>n g r. \<forall>w\<in>cball z r. f w = (w - z) ^ n * g w \<and> g w \<noteq> 0"
  assume n_asm:"\<exists>g r1. 0 < n \<and> 0 < r1 \<and> g holomorphic_on cball z r1 \<and> fac n g r1"
     and m_asm:"\<exists>h r2. 0 < m \<and> 0 < r2  \<and> h holomorphic_on cball z r2 \<and> fac m h r2"
  obtain g r1 where "0 < n" "0 < r1" and g_holo: "g holomorphic_on cball z r1"
    and "fac n g r1" using n_asm by auto
  obtain h r2 where "0 < m" "0 < r2" and h_holo: "h holomorphic_on cball z r2"
    and "fac m h r2" using m_asm by auto
  define r where "r \<equiv> min r1 r2"
  have "r>0" using \<open>r1>0\<close> \<open>r2>0\<close> unfolding r_def by auto
  moreover have "\<forall>w\<in>ball z r. f w = (w-z)^n * g w \<and> g w\<noteq>0 \<and> f w = (w - z)^m * h w \<and> h w\<noteq>0"
    using \<open>fac m h r2\<close> \<open>fac n g r1\<close>   unfolding fac_def r_def
    by fastforce
  ultimately show "m=n" using g_holo h_holo
    apply (elim holomorphic_factor_zero_unique[of r z f n g m h,symmetric,rotated])
    by (auto simp add:r_def)
qed

lemma zorder_exist:
  fixes f::"complex \<Rightarrow> complex" and z::complex
  defines "n\<equiv>zorder f z" and "h\<equiv>zer_poly f z"
  assumes  "open s" "connected s" "z\<in>s"
    and holo: "f holomorphic_on s"
    and  "f z=0" "\<exists>w\<in>s. f w\<noteq>0"
  shows "\<exists>r. n>0 \<and> r>0 \<and> cball z r \<subseteq> s \<and> h holomorphic_on cball z r
    \<and> (\<forall>w\<in>cball z r. f w  = h w * (w-z)^n \<and> h w \<noteq>0) "
proof -
  define P where "P \<equiv> \<lambda>h r n. r>0 \<and> h holomorphic_on cball z r
    \<and> (\<forall>w\<in>cball z r. ( f w  = h w * (w-z)^n) \<and> h w \<noteq>0)"
  have "(\<exists>!n. n>0 \<and> (\<exists> h r. P h r n))"
    proof -
      have "\<exists>!n. \<exists>h r. n>0 \<and> P h r n"
        using holomorphic_factor_zero_Ex1[OF \<open>open s\<close> \<open>connected s\<close> \<open>z\<in>s\<close> holo \<open>f z=0\<close>
          \<open>\<exists>w\<in>s. f w\<noteq>0\<close>] unfolding P_def
        apply (subst mult.commute)
        by auto
      thus ?thesis by auto
    qed
  moreover have n:"n=(THE n. n>0 \<and> (\<exists>h r. P h r n))"
    unfolding n_def zorder_def P_def by simp
  ultimately have "n>0 \<and> (\<exists>h r. P h r n)"
    apply (drule_tac theI')
    by simp
  then have "n>0" and "\<exists>h r. P h r n" by auto
  moreover have "h=(SOME h. \<exists>r. P h r n)"
    unfolding h_def P_def zer_poly_def[of f z,folded n_def P_def] by simp
  ultimately have "\<exists>r. P h r n"
    apply (drule_tac someI_ex)
    by simp
  then obtain r1 where "P h r1 n" by auto
  obtain r2 where "r2>0" "cball z r2 \<subseteq> s"
    using assms(3) assms(5) open_contains_cball_eq by blast
  define r3 where "r3 \<equiv> min r1 r2"
  have "P h r3 n" using \<open>P h r1 n\<close> \<open>r2>0\<close> unfolding P_def r3_def
    by auto
  moreover have "cball z r3 \<subseteq> s" using \<open>cball z r2 \<subseteq> s\<close> unfolding r3_def by auto
  ultimately show ?thesis using \<open>n>0\<close> unfolding P_def by auto
qed

lemma porder_exist:
  fixes f::"complex \<Rightarrow> complex" and z::complex
  defines "n \<equiv> porder f z" and "h \<equiv> pol_poly f z"
  assumes "open s" "z \<in> s"
    and holo:"f holomorphic_on s-{z}"
    and "is_pole f z"
  shows "\<exists>r. n>0 \<and> r>0 \<and> cball z r \<subseteq> s \<and> h holomorphic_on cball z r
    \<and> (\<forall>w\<in>cball z r. (w\<noteq>z \<longrightarrow> f w  = h w / (w-z)^n) \<and> h w \<noteq>0)"
proof -
  obtain e where "e>0" and e_ball:"ball z e \<subseteq> s"and e_def: "\<forall>x\<in>ball z e-{z}. f x\<noteq>0"
    proof -
      have "\<forall>\<^sub>F z in at z. f z \<noteq> 0"
        using \<open>is_pole f z\<close> filterlim_at_infinity_imp_eventually_ne unfolding is_pole_def
        by auto
      then obtain e1 where "e1>0" and e1_def: "\<forall>x. x \<noteq> z \<and> dist x z < e1 \<longrightarrow> f x \<noteq> 0"
        using eventually_at[of "\<lambda>x. f x\<noteq>0" z,simplified] by auto
      obtain e2 where "e2>0" and "ball z e2 \<subseteq>s" using \<open>open s\<close> \<open>z\<in>s\<close> openE by auto
      define e where "e \<equiv> min e1 e2"
      have "e>0" using \<open>e1>0\<close> \<open>e2>0\<close> unfolding e_def by auto
      moreover have "ball z e \<subseteq> s" unfolding e_def using \<open>ball z e2 \<subseteq> s\<close> by auto
      moreover have "\<forall>x\<in>ball z e-{z}. f x\<noteq>0" using e1_def \<open>e1>0\<close> \<open>e2>0\<close> unfolding e_def
        by (simp add: DiffD1 DiffD2 dist_commute singletonI)
      ultimately show ?thesis using that by auto
    qed
  define g where "g \<equiv> \<lambda>x. if x=z then 0 else inverse (f x)"
  define zo where "zo \<equiv> zorder g z"
  define zp where "zp \<equiv> zer_poly g z"
  have "\<exists>w\<in>ball z e. g w \<noteq> 0"
    proof -
      obtain w where w:"w\<in>ball z e-{z}" using \<open>0 < e\<close>
        by (metis open_ball all_not_in_conv centre_in_ball insert_Diff_single
          insert_absorb not_open_singleton)
      hence "w\<noteq>z" "f w\<noteq>0" using e_def[rule_format,of w] mem_ball
        by (auto simp add:dist_commute)
      then show ?thesis unfolding g_def using w by auto
    qed
  moreover have "g holomorphic_on ball z e"
    apply (intro is_pole_inverse_holomorphic[of "ball z e",OF _ _ \<open>is_pole f z\<close> e_def,folded g_def])
    using holo e_ball by auto
  moreover have "g z=0" unfolding g_def by auto
  ultimately obtain r where "0 < zo" "0 < r" "cball z r \<subseteq> ball z e"
      and zp_holo: "zp holomorphic_on cball z r" and
      zp_fac: "\<forall>w\<in>cball z r. g w = zp w * (w - z) ^ zo \<and> zp w \<noteq> 0"
    using zorder_exist[of "ball z e" z g,simplified,folded zo_def zp_def] \<open>e>0\<close>
    by auto
  have n:"n=zo" and h:"h=inverse o zp"
    unfolding n_def zo_def porder_def h_def zp_def pol_poly_def g_def by simp_all
  have "h holomorphic_on cball z r"
    using zp_holo zp_fac holomorphic_on_inverse  unfolding h comp_def by blast
  moreover have "\<forall>w\<in>cball z r. (w\<noteq>z \<longrightarrow> f w  = h w / (w-z)^n) \<and> h w \<noteq>0"
    using zp_fac unfolding h n comp_def g_def
    by (metis divide_inverse_commute field_class.field_inverse_zero inverse_inverse_eq
      inverse_mult_distrib mult.commute)
  moreover have "0 < n" unfolding n using \<open>zo>0\<close> by simp
  ultimately show ?thesis using \<open>0 < r\<close> \<open>cball z r \<subseteq> ball z e\<close> e_ball by auto
qed

lemma residue_porder:
  fixes f::"complex \<Rightarrow> complex" and z::complex
  defines "n \<equiv> porder f z" and "h \<equiv> pol_poly f z"
  assumes "open s" "z \<in> s"
    and holo:"f holomorphic_on s - {z}"
    and pole:"is_pole f z"
  shows "residue f z = ((deriv ^^ (n - 1)) h z / fact (n-1))"
proof -
  define g where "g \<equiv> \<lambda>x. if x=z then 0 else inverse (f x)"
  obtain r where "0 < n" "0 < r" and r_cball:"cball z r \<subseteq> s" and h_holo: "h holomorphic_on cball z r"
      and h_divide:"(\<forall>w\<in>cball z r. (w\<noteq>z \<longrightarrow> f w = h w / (w - z) ^ n) \<and> h w \<noteq> 0)"
    using porder_exist[OF \<open>open s\<close> \<open>z \<in> s\<close> holo pole, folded n_def h_def] by blast
  have r_nonzero:"\<And>w. w \<in> ball z r - {z} \<Longrightarrow> f w \<noteq> 0"
    using h_divide by simp
  define c where "c \<equiv> 2 * pi * \<i>"
  define der_f where "der_f \<equiv> ((deriv ^^ (n - 1)) h z / fact (n-1))"
  def h'\<equiv>"\<lambda>u. h u / (u - z) ^ n"
  have "(h' has_contour_integral c / fact (n - 1) * (deriv ^^ (n - 1)) h z) (circlepath z r)"
    unfolding h'_def
    proof (rule Cauchy_has_contour_integral_higher_derivative_circlepath[of z r h z "n-1",
        folded c_def Suc_pred'[OF \<open>n>0\<close>]])
      show "continuous_on (cball z r) h" using holomorphic_on_imp_continuous_on h_holo by simp
      show "h holomorphic_on ball z r" using h_holo by auto
      show " z \<in> ball z r" using \<open>r>0\<close> by auto
    qed
  then have "(h' has_contour_integral c * der_f) (circlepath z r)" unfolding der_f_def by auto
  then have "(f has_contour_integral c * der_f) (circlepath z r)"
    proof (elim has_contour_integral_eq)
      fix x assume "x \<in> path_image (circlepath z r)"
      hence "x\<in>cball z r - {z}" using \<open>r>0\<close> by auto
      then show "h' x = f x" using h_divide unfolding h'_def by auto
    qed
  moreover have "(f has_contour_integral c * residue f z) (circlepath z r)"
    using base_residue[OF \<open>open s\<close> \<open>z\<in>s\<close> \<open>r>0\<close> holo r_cball,folded c_def] .
  ultimately have "c * der_f =  c * residue f z" using has_contour_integral_unique by blast
  hence "der_f = residue f z" unfolding c_def by auto
  thus ?thesis unfolding der_f_def by auto
qed

theorem argument_principle:
  fixes f::"complex \<Rightarrow> complex" and poles s:: "complex set"
  defines "zeros\<equiv>{p. f p=0} - poles"
  assumes "open s" and
          "connected s" and
          f_holo:"f holomorphic_on s-poles" and
          h_holo:"h holomorphic_on s" and
          "valid_path g" and
          loop:"pathfinish g = pathstart g" and
          path_img:"path_image g \<subseteq> s - (zeros \<union> poles)" and
          homo:"\<forall>z. (z \<notin> s) \<longrightarrow> winding_number g z = 0" and
          finite:"finite (zeros \<union> poles)" and
          poles:"\<forall>p\<in>poles. is_pole f p"
  shows "contour_integral g (\<lambda>x. deriv f x * h x / f x) = 2 * pi * \<i> *
          ((\<Sum>p\<in>zeros. winding_number g p * h p * zorder f p)
           - (\<Sum>p\<in>poles. winding_number g p * h p * porder f p))"
    (is "?L=?R")
proof -
  define c where "c \<equiv> 2 * complex_of_real pi * \<i> "
  define ff where "ff \<equiv> (\<lambda>x. deriv f x * h x / f x)"
  define cont_pole where "cont_pole \<equiv> \<lambda>ff p e. (ff has_contour_integral - c  * porder f p * h p) (circlepath p e)"
  define cont_zero where "cont_zero \<equiv> \<lambda>ff p e. (ff has_contour_integral c * zorder f p * h p ) (circlepath p e)"
  define avoid where "avoid \<equiv> \<lambda>p e. \<forall>w\<in>cball p e. w \<in> s \<and> (w \<noteq> p \<longrightarrow> w \<notin> zeros \<union> poles)"
  have "\<exists>e>0. avoid p e \<and> (p\<in>poles \<longrightarrow> cont_pole ff p e) \<and> (p\<in>zeros \<longrightarrow> cont_zero ff p e)"
      when "p\<in>s" for p
    proof -
      obtain e1 where "e1>0" and e1_avoid:"avoid p e1"
        using finite_cball_avoid[OF \<open>open s\<close> finite] \<open>p\<in>s\<close> unfolding avoid_def by auto
      have "\<exists>e2>0. cball p e2 \<subseteq> ball p e1 \<and> cont_pole ff p e2"
        when "p\<in>poles"
        proof -
          define po where "po \<equiv> porder f p"
          define pp where "pp \<equiv> pol_poly f p"
          def f'\<equiv>"\<lambda>w. pp w / (w - p) ^ po"
          def ff'\<equiv>"(\<lambda>x. deriv f' x * h x / f' x)"
          have "f holomorphic_on ball p e1 - {p}"
            apply (intro holomorphic_on_subset[OF f_holo])
            using e1_avoid \<open>p\<in>poles\<close> unfolding avoid_def by auto
          then obtain r where
              "0 < po" "r>0"
              "cball p r \<subseteq> ball p e1" and
              pp_holo:"pp holomorphic_on cball p r" and
              pp_po:"(\<forall>w\<in>cball p r. (w\<noteq>p \<longrightarrow> f w = pp w / (w - p) ^ po) \<and> pp w \<noteq> 0)"
            using porder_exist[of "ball p e1" p f,simplified,OF \<open>e1>0\<close>] poles \<open>p\<in>poles\<close>
            unfolding po_def pp_def
            by auto
          define e2 where "e2 \<equiv> r/2"
          have "e2>0" using \<open>r>0\<close> unfolding e2_def by auto
          define anal where "anal \<equiv> \<lambda>w. deriv pp w * h w / pp w"
          define prin where "prin \<equiv> \<lambda>w. - of_nat po * h w / (w - p)"
          have "((\<lambda>w.  prin w + anal w) has_contour_integral - c * po * h p) (circlepath p e2)"
            proof (rule  has_contour_integral_add[of _ _ _ _ 0,simplified])
              have "ball p r \<subseteq> s"
                using \<open>cball p r \<subseteq> ball p e1\<close> avoid_def ball_subset_cball e1_avoid by blast
              then have "cball p e2 \<subseteq> s"
                using \<open>r>0\<close> unfolding e2_def by auto
              then have "(\<lambda>w. - of_nat po * h w) holomorphic_on cball p e2"
                using h_holo
                by (auto intro!: holomorphic_intros)
              then show "(prin has_contour_integral - c * of_nat po * h p ) (circlepath p e2)"
                using Cauchy_integral_circlepath_simple[folded c_def, of "\<lambda>w. - of_nat po * h w"]
                  \<open>e2>0\<close>
                unfolding prin_def
                by (auto simp add: mult.assoc)
              have "anal holomorphic_on ball p r" unfolding anal_def
                using pp_holo h_holo pp_po \<open>ball p r \<subseteq> s\<close>
                by (auto intro!: holomorphic_intros)
              then show "(anal has_contour_integral 0) (circlepath p e2)"
                using e2_def \<open>r>0\<close>
                by (auto elim!: Cauchy_theorem_disc_simple)
            qed
          then have "cont_pole ff' p e2" unfolding cont_pole_def po_def
            proof (elim has_contour_integral_eq)
              fix w assume "w \<in> path_image (circlepath p e2)"
              then have "w\<in>ball p r" and "w\<noteq>p" unfolding e2_def using \<open>r>0\<close> by auto
              define wp where "wp \<equiv> w-p"
              have "wp\<noteq>0" and "pp w \<noteq>0"
                unfolding wp_def using \<open>w\<noteq>p\<close> \<open>w\<in>ball p r\<close> pp_po by auto
              moreover have der_f':"deriv f' w = - po * pp w / (w-p)^(po+1) + deriv pp w / (w-p)^po"
                proof (rule DERIV_imp_deriv)
                  define der where "der \<equiv> - po * pp w / (w-p)^(po+1) + deriv pp w / (w-p)^po"
                  have po:"po = Suc (po - Suc 0) " using \<open>po>0\<close> by auto
                  have "(pp has_field_derivative (deriv pp w)) (at w)"
                    using DERIV_deriv_iff_has_field_derivative pp_holo \<open>w\<noteq>p\<close>
                      by (meson open_ball \<open>w \<in> ball p r\<close> ball_subset_cball holomorphic_derivI holomorphic_on_subset)
                  then show "(f' has_field_derivative  der) (at w)"
                    using \<open>w\<noteq>p\<close> \<open>po>0\<close> unfolding der_def f'_def
                    apply (auto intro!: derivative_eq_intros simp add:field_simps)
                    apply (subst (4) po)
                    apply (subst power_Suc)
                    by (auto simp add:field_simps)
                qed
              ultimately show "prin w + anal w = ff' w"
                unfolding ff'_def prin_def anal_def
                apply simp
                apply (unfold f'_def)
                apply (fold wp_def)
                by (auto simp add:field_simps)
            qed
          then have "cont_pole ff p e2" unfolding cont_pole_def
            proof (elim has_contour_integral_eq)
              fix w assume "w \<in> path_image (circlepath p e2)"
              then have "w\<in>ball p r" and "w\<noteq>p" unfolding e2_def using \<open>r>0\<close> by auto
              have "deriv f' w =  deriv f w"
                proof (rule complex_derivative_transform_within_open[where s="ball p r - {p}"])
                  show "f' holomorphic_on ball p r - {p}" unfolding f'_def using pp_holo
                    by (auto intro!: holomorphic_intros)
                next
                  have "ball p e1 - {p} \<subseteq> s - poles"
                    using avoid_def ball_subset_cball e1_avoid
                    by auto
                  then have "ball p r - {p} \<subseteq> s - poles" using \<open>cball p r \<subseteq> ball p e1\<close>
                    using ball_subset_cball by blast
                  then show "f holomorphic_on ball p r - {p}" using f_holo
                    by auto
                next
                  show "open (ball p r - {p})" by auto
                next
                  show "w \<in> ball p r - {p}" using \<open>w\<in>ball p r\<close> \<open>w\<noteq>p\<close> by auto
                next
                  fix x assume "x \<in> ball p r - {p}"
                  then show "f' x = f x"
                    using pp_po unfolding f'_def by auto
                qed
              moreover have " f' w  =  f w "
                using \<open>w \<in> ball p r\<close> ball_subset_cball subset_iff pp_po \<open>w\<noteq>p\<close>
                unfolding f'_def by auto
              ultimately show "ff' w = ff w"
                unfolding ff'_def ff_def by simp
            qed
          moreover have "cball p e2 \<subseteq> ball p e1"
            using \<open>0 < r\<close> \<open>cball p r \<subseteq> ball p e1\<close> e2_def by auto
          ultimately show ?thesis using \<open>e2>0\<close> by auto
        qed
      then obtain e2 where e2:"p\<in>poles \<longrightarrow> e2>0 \<and> cball p e2 \<subseteq> ball p e1 \<and> cont_pole ff p e2"
        by auto
      have "\<exists>e3>0. cball p e3 \<subseteq> ball p e1 \<and> cont_zero ff p e3"
        when "p\<in>zeros"
        proof -
          define zo where "zo \<equiv> zorder f p"
          define zp where "zp \<equiv> zer_poly f p"
          def f'\<equiv>"\<lambda>w. zp w * (w - p) ^ zo"
          def ff'\<equiv>"(\<lambda>x. deriv f' x * h x / f' x)"
          have "f holomorphic_on ball p e1"
            proof -
              have "ball p e1 \<subseteq> s - poles"
                using avoid_def ball_subset_cball e1_avoid that zeros_def by fastforce
              thus ?thesis using f_holo by auto
            qed
          moreover have "f p = 0" using \<open>p\<in>zeros\<close>
            using DiffD1 mem_Collect_eq zeros_def by blast
          moreover have "\<exists>w\<in>ball p e1. f w \<noteq> 0"
            proof -
              def p'\<equiv>"p+e1/2"
              have "p'\<in>ball p e1" and "p'\<noteq>p" using \<open>e1>0\<close> unfolding p'_def by (auto simp add:dist_norm)
              then show "\<exists>w\<in>ball p e1. f w \<noteq> 0" using e1_avoid unfolding avoid_def
                apply (rule_tac x=p' in bexI)
                by (auto simp add:zeros_def)
            qed
          ultimately obtain r where
              "0 < zo" "r>0"
              "cball p r \<subseteq> ball p e1" and
              pp_holo:"zp holomorphic_on cball p r" and
              pp_po:"(\<forall>w\<in>cball p r. f w = zp w * (w - p) ^ zo \<and> zp w \<noteq> 0)"
            using zorder_exist[of "ball p e1" p f,simplified,OF \<open>e1>0\<close>] unfolding zo_def zp_def
            by auto
          define e2 where "e2 \<equiv> r/2"
          have "e2>0" using \<open>r>0\<close> unfolding e2_def by auto
          define anal where "anal \<equiv> \<lambda>w. deriv zp w * h w / zp w"
          define prin where "prin \<equiv> \<lambda>w. of_nat zo * h w / (w - p)"
          have "((\<lambda>w.  prin w + anal w) has_contour_integral c * zo * h p) (circlepath p e2)"
            proof (rule  has_contour_integral_add[of _ _ _ _ 0,simplified])
              have "ball p r \<subseteq> s"
                using \<open>cball p r \<subseteq> ball p e1\<close> avoid_def ball_subset_cball e1_avoid by blast
              then have "cball p e2 \<subseteq> s"
                using \<open>r>0\<close> unfolding e2_def by auto
              then have "(\<lambda>w. of_nat zo * h w) holomorphic_on cball p e2"
                using h_holo
                by (auto intro!: holomorphic_intros)
              then show "(prin has_contour_integral c * of_nat zo * h p ) (circlepath p e2)"
                using Cauchy_integral_circlepath_simple[folded c_def, of "\<lambda>w. of_nat zo * h w"]
                  \<open>e2>0\<close>
                unfolding prin_def
                by (auto simp add: mult.assoc)
              have "anal holomorphic_on ball p r" unfolding anal_def
                using pp_holo h_holo pp_po \<open>ball p r \<subseteq> s\<close>
                by (auto intro!: holomorphic_intros)
              then show "(anal has_contour_integral 0) (circlepath p e2)"
                using e2_def \<open>r>0\<close>
                by (auto elim!: Cauchy_theorem_disc_simple)
            qed
          then have "cont_zero ff' p e2" unfolding cont_zero_def zo_def
            proof (elim has_contour_integral_eq)
              fix w assume "w \<in> path_image (circlepath p e2)"
              then have "w\<in>ball p r" and "w\<noteq>p" unfolding e2_def using \<open>r>0\<close> by auto
              define wp where "wp \<equiv> w-p"
              have "wp\<noteq>0" and "zp w \<noteq>0"
                unfolding wp_def using \<open>w\<noteq>p\<close> \<open>w\<in>ball p r\<close> pp_po by auto
              moreover have der_f':"deriv f' w = zo * zp w * (w-p)^(zo-1) + deriv zp w * (w-p)^zo"
                proof (rule DERIV_imp_deriv)
                  define der where "der \<equiv> zo * zp w * (w-p)^(zo-1) + deriv zp w * (w-p)^zo"
                  have po:"zo = Suc (zo - Suc 0) " using \<open>zo>0\<close> by auto
                  have "(zp has_field_derivative (deriv zp w)) (at w)"
                    using DERIV_deriv_iff_has_field_derivative pp_holo
                    by (meson Topology_Euclidean_Space.open_ball \<open>w \<in> ball p r\<close> ball_subset_cball holomorphic_derivI holomorphic_on_subset)
                  then show "(f' has_field_derivative  der) (at w)"
                    using \<open>w\<noteq>p\<close> \<open>zo>0\<close> unfolding der_def f'_def
                    by (auto intro!: derivative_eq_intros simp add:field_simps)
                qed
              ultimately show "prin w + anal w = ff' w"
                unfolding ff'_def prin_def anal_def
                apply simp
                apply (unfold f'_def)
                apply (fold wp_def)
                apply (auto simp add:field_simps)
                by (metis Suc_diff_Suc minus_nat.diff_0 power_Suc)
            qed
          then have "cont_zero ff p e2" unfolding cont_zero_def
            proof (elim has_contour_integral_eq)
              fix w assume "w \<in> path_image (circlepath p e2)"
              then have "w\<in>ball p r" and "w\<noteq>p" unfolding e2_def using \<open>r>0\<close> by auto
              have "deriv f' w =  deriv f w"
                proof (rule complex_derivative_transform_within_open[where s="ball p r - {p}"])
                  show "f' holomorphic_on ball p r - {p}" unfolding f'_def using pp_holo
                    by (auto intro!: holomorphic_intros)
                next
                  have "ball p e1 - {p} \<subseteq> s - poles"
                    using avoid_def ball_subset_cball e1_avoid by auto
                  then have "ball p r - {p} \<subseteq> s - poles" using \<open>cball p r \<subseteq> ball p e1\<close>
                    using ball_subset_cball by blast
                  then show "f holomorphic_on ball p r - {p}" using f_holo
                    by auto
                next
                  show "open (ball p r - {p})" by auto
                next
                  show "w \<in> ball p r - {p}" using \<open>w\<in>ball p r\<close> \<open>w\<noteq>p\<close> by auto
                next
                  fix x assume "x \<in> ball p r - {p}"
                  then show "f' x = f x"
                    using pp_po unfolding f'_def by auto
                qed
              moreover have " f' w  =  f w "
                using \<open>w \<in> ball p r\<close> ball_subset_cball subset_iff pp_po unfolding f'_def by auto
              ultimately show "ff' w = ff w"
                unfolding ff'_def ff_def by simp
            qed
          moreover have "cball p e2 \<subseteq> ball p e1"
            using \<open>0 < r\<close> \<open>cball p r \<subseteq> ball p e1\<close> e2_def by auto
          ultimately show ?thesis using \<open>e2>0\<close> by auto
        qed
      then obtain e3 where e3:"p\<in>zeros \<longrightarrow> e3>0 \<and> cball p e3 \<subseteq> ball p e1 \<and> cont_zero ff p e3"
        by auto
      define e4 where "e4 \<equiv> if p\<in>poles then e2 else if p\<in>zeros then e3 else e1"
      have "e4>0" using e2 e3 \<open>e1>0\<close> unfolding e4_def by auto
      moreover have "avoid p e4" using e2 e3 \<open>e1>0\<close> e1_avoid unfolding e4_def avoid_def by auto
      moreover have "p\<in>poles \<longrightarrow> cont_pole ff p e4" and "p\<in>zeros \<longrightarrow> cont_zero ff p e4"
        by (auto simp add: e2 e3 e4_def zeros_def)
      ultimately show ?thesis by auto
    qed
  then obtain get_e where get_e:"\<forall>p\<in>s. get_e p>0 \<and> avoid p (get_e p)
      \<and> (p\<in>poles \<longrightarrow> cont_pole ff p (get_e p)) \<and> (p\<in>zeros \<longrightarrow> cont_zero ff p (get_e p))"
    by metis
  define cont where "cont \<equiv> \<lambda>p. contour_integral (circlepath p (get_e p)) ff"
  define w where "w \<equiv> \<lambda>p. winding_number g p"
  have "contour_integral g ff = (\<Sum>p\<in>zeros \<union> poles. w p * cont p)"
    unfolding cont_def w_def
    proof (rule Cauchy_theorem_singularities[OF \<open>open s\<close> \<open>connected s\<close> finite _ \<open>valid_path g\<close> loop
        path_img homo])
      have "open (s - (zeros \<union> poles))" using open_Diff[OF _ finite_imp_closed[OF finite]] \<open>open s\<close> by auto
      then show "ff holomorphic_on s - (zeros \<union> poles)" unfolding ff_def using f_holo h_holo
        by (auto intro!: holomorphic_intros simp add:zeros_def)
    next
      show "\<forall>p\<in>s. 0 < get_e p \<and> (\<forall>w\<in>cball p (get_e p). w \<in> s \<and> (w \<noteq> p \<longrightarrow> w \<notin> zeros \<union> poles))"
        using get_e using avoid_def by blast
    qed
  also have "... = (\<Sum>p\<in>zeros. w p * cont p) + (\<Sum>p\<in>poles. w p * cont p)"
    using finite
    apply (subst sum.union_disjoint)
    by (auto simp add:zeros_def)
  also have "... = c * ((\<Sum>p\<in>zeros. w p *  h p * zorder f p) - (\<Sum>p\<in>poles. w p *  h p * porder f p))"
    proof -
      have "(\<Sum>p\<in>zeros. w p * cont p) = (\<Sum>p\<in>zeros. c * w p *  h p * zorder f p)"
        proof (rule sum.cong[of zeros zeros,simplified])
          fix p assume "p \<in> zeros"
          show "w p * cont p = c * w p * h p * (zorder f p)"
            proof (cases "p\<in>s")
              assume "p \<in> s"
              have "cont p = c * h p * (zorder f p)" unfolding cont_def
                apply (rule contour_integral_unique)
                using get_e \<open>p\<in>s\<close> \<open>p\<in>zeros\<close> unfolding cont_zero_def
                by (metis mult.assoc mult.commute)
              thus ?thesis by auto
            next
              assume "p\<notin>s"
              then have "w p=0" using homo unfolding w_def by auto
              then show ?thesis by auto
            qed
        qed
      then have "(\<Sum>p\<in>zeros. w p * cont p) = c * (\<Sum>p\<in>zeros.  w p *  h p * zorder f p)"
        apply (subst sum_distrib_left)
        by (simp add:algebra_simps)
      moreover have "(\<Sum>p\<in>poles. w p * cont p) = (\<Sum>p\<in>poles.  - c * w p *  h p * porder f p)"
        proof (rule sum.cong[of poles poles,simplified])
          fix p assume "p \<in> poles"
          show "w p * cont p = - c * w p * h p * (porder f p)"
            proof (cases "p\<in>s")
              assume "p \<in> s"
              have "cont p = - c * h p * (porder f p)" unfolding cont_def
                apply (rule contour_integral_unique)
                using get_e \<open>p\<in>s\<close> \<open>p\<in>poles\<close> unfolding cont_pole_def
                by (metis mult.assoc mult.commute)
              thus ?thesis by auto
            next
              assume "p\<notin>s"
              then have "w p=0" using homo unfolding w_def by auto
              then show ?thesis by auto
            qed
        qed
      then have "(\<Sum>p\<in>poles. w p * cont p) = - c * (\<Sum>p\<in>poles. w p *  h p * porder f p)"
        apply (subst sum_distrib_left)
        by (simp add:algebra_simps)
      ultimately show ?thesis by (simp add: right_diff_distrib)
    qed
  finally show ?thesis unfolding w_def ff_def c_def by auto
qed

subsection \<open>Rouche's theorem \<close>

theorem Rouche_theorem:
  fixes f g::"complex \<Rightarrow> complex" and s:: "complex set"
  defines "fg\<equiv>(\<lambda>p. f p+ g p)"
  defines "zeros_fg\<equiv>{p. fg p =0}" and "zeros_f\<equiv>{p. f p=0}"
  assumes
    "open s" and "connected s" and
    "finite zeros_fg" and
    "finite zeros_f" and
    f_holo:"f holomorphic_on s" and
    g_holo:"g holomorphic_on s" and
    "valid_path \<gamma>" and
    loop:"pathfinish \<gamma> = pathstart \<gamma>" and
    path_img:"path_image \<gamma> \<subseteq> s " and
    path_less:"\<forall>z\<in>path_image \<gamma>. cmod(f z) > cmod(g z)" and
    homo:"\<forall>z. (z \<notin> s) \<longrightarrow> winding_number \<gamma> z = 0"
  shows "(\<Sum>p\<in>zeros_fg. winding_number \<gamma> p * zorder fg p)
          = (\<Sum>p\<in>zeros_f. winding_number \<gamma> p * zorder f p)"
proof -
  have path_fg:"path_image \<gamma> \<subseteq> s - zeros_fg"
    proof -
      have False when "z\<in>path_image \<gamma>" and "f z + g z=0" for z
        proof -
          have "cmod (f z) > cmod (g z)" using \<open>z\<in>path_image \<gamma>\<close> path_less by auto
          moreover have "f z = - g z"  using \<open>f z + g z =0\<close> by (simp add: eq_neg_iff_add_eq_0)
          then have "cmod (f z) = cmod (g z)" by auto
          ultimately show False by auto
        qed
      then show ?thesis unfolding zeros_fg_def fg_def using path_img by auto
    qed
  have path_f:"path_image \<gamma> \<subseteq> s - zeros_f"
    proof -
      have False when "z\<in>path_image \<gamma>" and "f z =0" for z
        proof -
          have "cmod (g z) < cmod (f z) " using \<open>z\<in>path_image \<gamma>\<close> path_less by auto
          then have "cmod (g z) < 0" using \<open>f z=0\<close> by auto
          then show False by auto
        qed
      then show ?thesis unfolding zeros_f_def using path_img by auto
    qed
  define w where "w \<equiv> \<lambda>p. winding_number \<gamma> p"
  define c where "c \<equiv> 2 * complex_of_real pi * \<i>"
  define h where "h \<equiv> \<lambda>p. g p / f p + 1"
  obtain spikes
    where "finite spikes" and spikes: "\<forall>x\<in>{0..1} - spikes. \<gamma> differentiable at x"
    using \<open>valid_path \<gamma>\<close>
    by (auto simp: valid_path_def piecewise_C1_differentiable_on_def C1_differentiable_on_eq)
  have h_contour:"((\<lambda>x. deriv h x / h x) has_contour_integral 0) \<gamma>"
    proof -
      have outside_img:"0 \<in> outside (path_image (h o \<gamma>))"
        proof -
          have "h p \<in> ball 1 1" when "p\<in>path_image \<gamma>" for p
            proof -
              have "cmod (g p/f p) <1" using path_less[rule_format,OF that]
                apply (cases "cmod (f p) = 0")
                by (auto simp add: norm_divide)
              then show ?thesis unfolding h_def by (auto simp add:dist_complex_def)
            qed
          then have "path_image (h o \<gamma>) \<subseteq> ball 1 1"
            by (simp add: image_subset_iff path_image_compose)
          moreover have " (0::complex) \<notin> ball 1 1" by (simp add: dist_norm)
          ultimately show "?thesis"
            using  convex_in_outside[of "ball 1 1" 0] outside_mono by blast
        qed
      have valid_h:"valid_path (h \<circ> \<gamma>)"
        proof (rule valid_path_compose_holomorphic[OF \<open>valid_path \<gamma>\<close> _ _ path_f])
          show "h holomorphic_on s - zeros_f"
            unfolding h_def using f_holo g_holo
            by (auto intro!: holomorphic_intros simp add:zeros_f_def)
        next
          show "open (s - zeros_f)" using \<open>finite zeros_f\<close> \<open>open s\<close> finite_imp_closed
            by auto
        qed
      have "((\<lambda>z. 1/z) has_contour_integral 0) (h \<circ> \<gamma>)"
        proof -
          have "0 \<notin> path_image (h \<circ> \<gamma>)" using outside_img by (simp add: outside_def)
          then have "((\<lambda>z. 1/z) has_contour_integral c * winding_number (h \<circ> \<gamma>) 0) (h \<circ> \<gamma>)"
            using has_contour_integral_winding_number[of "h o \<gamma>" 0,simplified] valid_h
            unfolding c_def by auto
          moreover have "winding_number (h o \<gamma>) 0 = 0"
            proof -
              have "0 \<in> outside (path_image (h \<circ> \<gamma>))" using outside_img .
              moreover have "path (h o \<gamma>)"
                using valid_h  by (simp add: valid_path_imp_path)
              moreover have "pathfinish (h o \<gamma>) = pathstart (h o \<gamma>)"
                by (simp add: loop pathfinish_compose pathstart_compose)
              ultimately show ?thesis using winding_number_zero_in_outside by auto
            qed
          ultimately show ?thesis by auto
        qed
      moreover have "vector_derivative (h \<circ> \<gamma>) (at x) = vector_derivative \<gamma> (at x) * deriv h (\<gamma> x)"
          when "x\<in>{0..1} - spikes" for x
        proof (rule vector_derivative_chain_at_general)
          show "\<gamma> differentiable at x" using that \<open>valid_path \<gamma>\<close> spikes by auto
        next
          define der where "der \<equiv> \<lambda>p. (deriv g p * f p - g p * deriv f p)/(f p * f p)"
          define t where "t \<equiv> \<gamma> x"
          have "f t\<noteq>0" unfolding zeros_f_def t_def
            by (metis DiffD1 image_eqI norm_not_less_zero norm_zero path_defs(4) path_less that)
          moreover have "t\<in>s"
            using contra_subsetD path_image_def path_fg t_def that by fastforce
          ultimately have "(h has_field_derivative der t) (at t)"
            unfolding h_def der_def using g_holo f_holo \<open>open s\<close>
            by (auto intro!: holomorphic_derivI derivative_eq_intros)
          then show "h field_differentiable at (\<gamma> x)" 
            unfolding t_def field_differentiable_def by blast
        qed
      then have " (op / 1 has_contour_integral 0) (h \<circ> \<gamma>)
          = ((\<lambda>x. deriv h x / h x) has_contour_integral 0) \<gamma>"
        unfolding has_contour_integral
        apply (intro has_integral_spike_eq[OF negligible_finite, OF \<open>finite spikes\<close>])
        by auto
      ultimately show ?thesis by auto
    qed
  then have "contour_integral \<gamma> (\<lambda>x. deriv h x / h x) = 0"
    using  contour_integral_unique by simp
  moreover have "contour_integral \<gamma> (\<lambda>x. deriv fg x / fg x) = contour_integral \<gamma> (\<lambda>x. deriv f x / f x)
      + contour_integral \<gamma> (\<lambda>p. deriv h p / h p)"
    proof -
      have "(\<lambda>p. deriv f p / f p) contour_integrable_on \<gamma>"
        proof (rule contour_integrable_holomorphic_simple[OF _ _ \<open>valid_path \<gamma>\<close> path_f])
          show "open (s - zeros_f)" using finite_imp_closed[OF \<open>finite zeros_f\<close>] \<open>open s\<close>
            by auto
          then show "(\<lambda>p. deriv f p / f p) holomorphic_on s - zeros_f"
            using f_holo
            by (auto intro!: holomorphic_intros simp add:zeros_f_def)
        qed
      moreover have "(\<lambda>p. deriv h p / h p) contour_integrable_on \<gamma>"
        using h_contour
        by (simp add: has_contour_integral_integrable)
      ultimately have "contour_integral \<gamma> (\<lambda>x. deriv f x / f x + deriv h x / h x) =
          contour_integral \<gamma> (\<lambda>p. deriv f p / f p) + contour_integral \<gamma> (\<lambda>p. deriv h p / h p)"
        using contour_integral_add[of "(\<lambda>p. deriv f p / f p)" \<gamma> "(\<lambda>p. deriv h p / h p)" ]
        by auto
      moreover have "deriv fg p / fg p =  deriv f p / f p + deriv h p / h p"
          when "p\<in> path_image \<gamma>" for p
        proof -
          have "fg p\<noteq>0" and "f p\<noteq>0" using path_f path_fg that unfolding zeros_f_def zeros_fg_def
            by auto
          have "h p\<noteq>0"
            proof (rule ccontr)
              assume "\<not> h p \<noteq> 0"
              then have "g p / f p= -1" unfolding h_def by (simp add: add_eq_0_iff2)
              then have "cmod (g p/f p) = 1" by auto
              moreover have "cmod (g p/f p) <1" using path_less[rule_format,OF that]
                apply (cases "cmod (f p) = 0")
                by (auto simp add: norm_divide)
              ultimately show False by auto
            qed
          have der_fg:"deriv fg p =  deriv f p + deriv g p" unfolding fg_def
            using f_holo g_holo holomorphic_on_imp_differentiable_at[OF _  \<open>open s\<close>] path_img that
            by auto
          have der_h:"deriv h p = (deriv g p * f p - g p * deriv f p)/(f p * f p)"
            proof -
              define der where "der \<equiv> \<lambda>p. (deriv g p * f p - g p * deriv f p)/(f p * f p)"
              have "p\<in>s" using path_img that by auto
              then have "(h has_field_derivative der p) (at p)"
                unfolding h_def der_def using g_holo f_holo \<open>open s\<close> \<open>f p\<noteq>0\<close>
                by (auto intro!: derivative_eq_intros holomorphic_derivI)
              then show ?thesis unfolding der_def using DERIV_imp_deriv by auto
            qed
          show ?thesis
            apply (simp only:der_fg der_h)
            apply (auto simp add:field_simps \<open>h p\<noteq>0\<close> \<open>f p\<noteq>0\<close> \<open>fg p\<noteq>0\<close>)
            by (auto simp add:field_simps h_def \<open>f p\<noteq>0\<close> fg_def)
        qed
      then have "contour_integral \<gamma> (\<lambda>p. deriv fg p / fg p)
          = contour_integral \<gamma> (\<lambda>p. deriv f p / f p + deriv h p / h p)"
        by (elim contour_integral_eq)
      ultimately show ?thesis by auto
    qed
  moreover have "contour_integral \<gamma> (\<lambda>x. deriv fg x / fg x) = c * (\<Sum>p\<in>zeros_fg. w p * zorder fg p)"
    unfolding c_def zeros_fg_def w_def
    proof (rule argument_principle[OF \<open>open s\<close> \<open>connected s\<close> _ _ \<open>valid_path \<gamma>\<close> loop _ homo
        , of _ "{}" "\<lambda>_. 1",simplified])
      show "fg holomorphic_on s" unfolding fg_def using f_holo g_holo holomorphic_on_add by auto
      show "path_image \<gamma> \<subseteq> s - {p. fg p = 0}" using path_fg unfolding zeros_fg_def .
      show " finite {p. fg p = 0}" using \<open>finite zeros_fg\<close> unfolding zeros_fg_def .
    qed
  moreover have "contour_integral \<gamma> (\<lambda>x. deriv f x / f x) = c * (\<Sum>p\<in>zeros_f. w p * zorder f p)"
    unfolding c_def zeros_f_def w_def
    proof (rule argument_principle[OF \<open>open s\<close> \<open>connected s\<close> _ _ \<open>valid_path \<gamma>\<close> loop _ homo
        , of _ "{}" "\<lambda>_. 1",simplified])
      show "f holomorphic_on s" using f_holo g_holo holomorphic_on_add by auto
      show "path_image \<gamma> \<subseteq> s - {p. f p = 0}" using path_f unfolding zeros_f_def .
      show " finite {p. f p = 0}" using \<open>finite zeros_f\<close> unfolding zeros_f_def .
    qed
  ultimately have " c* (\<Sum>p\<in>zeros_fg. w p * (zorder fg p)) = c* (\<Sum>p\<in>zeros_f. w p * (zorder f p))"
    by auto
  then show ?thesis unfolding c_def using w_def by auto
qed

end
