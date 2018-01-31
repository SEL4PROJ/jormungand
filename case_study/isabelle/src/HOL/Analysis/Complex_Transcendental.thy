section \<open>Complex Transcendental Functions\<close>

text\<open>By John Harrison et al.  Ported from HOL Light by L C Paulson (2015)\<close>

theory Complex_Transcendental
imports
  Complex_Analysis_Basics
  Summation_Tests
begin

(* TODO: Figure out what to do with Möbius transformations *)
definition "moebius a b c d = (\<lambda>z. (a*z+b) / (c*z+d :: 'a :: field))"

lemma moebius_inverse:
  assumes "a * d \<noteq> b * c" "c * z + d \<noteq> 0"
  shows   "moebius d (-b) (-c) a (moebius a b c d z) = z"
proof -
  from assms have "(-c) * moebius a b c d z + a \<noteq> 0" unfolding moebius_def
    by (simp add: field_simps)
  with assms show ?thesis
    unfolding moebius_def by (simp add: moebius_def divide_simps) (simp add: algebra_simps)?
qed

lemma moebius_inverse':
  assumes "a * d \<noteq> b * c" "c * z - a \<noteq> 0"
  shows   "moebius a b c d (moebius d (-b) (-c) a z) = z"
  using assms moebius_inverse[of d a "-b" "-c" z]
  by (auto simp: algebra_simps)

lemma cmod_add_real_less:
  assumes "Im z \<noteq> 0" "r\<noteq>0"
    shows "cmod (z + r) < cmod z + \<bar>r\<bar>"
proof (cases z)
  case (Complex x y)
  have "r * x / \<bar>r\<bar> < sqrt (x*x + y*y)"
    apply (rule real_less_rsqrt)
    using assms
    apply (simp add: Complex power2_eq_square)
    using not_real_square_gt_zero by blast
  then show ?thesis using assms Complex
    apply (auto simp: cmod_def)
    apply (rule power2_less_imp_less, auto)
    apply (simp add: power2_eq_square field_simps)
    done
qed

lemma cmod_diff_real_less: "Im z \<noteq> 0 \<Longrightarrow> x\<noteq>0 \<Longrightarrow> cmod (z - x) < cmod z + \<bar>x\<bar>"
  using cmod_add_real_less [of z "-x"]
  by simp

lemma cmod_square_less_1_plus:
  assumes "Im z = 0 \<Longrightarrow> \<bar>Re z\<bar> < 1"
    shows "(cmod z)\<^sup>2 < 1 + cmod (1 - z\<^sup>2)"
  using assms
  apply (cases "Im z = 0 \<or> Re z = 0")
  using abs_square_less_1
    apply (force simp add: Re_power2 Im_power2 cmod_def)
  using cmod_diff_real_less [of "1 - z\<^sup>2" "1"]
  apply (simp add: norm_power Im_power2)
  done

subsection\<open>The Exponential Function is Differentiable and Continuous\<close>

lemma field_differentiable_within_exp: "exp field_differentiable (at z within s)"
  using DERIV_exp field_differentiable_at_within field_differentiable_def by blast

lemma continuous_within_exp:
  fixes z::"'a::{real_normed_field,banach}"
  shows "continuous (at z within s) exp"
by (simp add: continuous_at_imp_continuous_within)

lemma holomorphic_on_exp [holomorphic_intros]: "exp holomorphic_on s"
  by (simp add: field_differentiable_within_exp holomorphic_on_def)

subsection\<open>Euler and de Moivre formulas.\<close>

text\<open>The sine series times @{term i}\<close>
lemma sin_ii_eq: "(\<lambda>n. (\<i> * sin_coeff n) * z^n) sums (\<i> * sin z)"
proof -
  have "(\<lambda>n. \<i> * sin_coeff n *\<^sub>R z^n) sums (\<i> * sin z)"
    using sin_converges sums_mult by blast
  then show ?thesis
    by (simp add: scaleR_conv_of_real field_simps)
qed

theorem exp_Euler: "exp(\<i> * z) = cos(z) + \<i> * sin(z)"
proof -
  have "(\<lambda>n. (cos_coeff n + \<i> * sin_coeff n) * z^n)
        = (\<lambda>n. (\<i> * z) ^ n /\<^sub>R (fact n))"
  proof
    fix n
    show "(cos_coeff n + \<i> * sin_coeff n) * z^n = (\<i> * z) ^ n /\<^sub>R (fact n)"
      by (auto simp: cos_coeff_def sin_coeff_def scaleR_conv_of_real field_simps elim!: evenE oddE)
  qed
  also have "... sums (exp (\<i> * z))"
    by (rule exp_converges)
  finally have "(\<lambda>n. (cos_coeff n + \<i> * sin_coeff n) * z^n) sums (exp (\<i> * z))" .
  moreover have "(\<lambda>n. (cos_coeff n + \<i> * sin_coeff n) * z^n) sums (cos z + \<i> * sin z)"
    using sums_add [OF cos_converges [of z] sin_ii_eq [of z]]
    by (simp add: field_simps scaleR_conv_of_real)
  ultimately show ?thesis
    using sums_unique2 by blast
qed

corollary exp_minus_Euler: "exp(-(\<i> * z)) = cos(z) - \<i> * sin(z)"
  using exp_Euler [of "-z"]
  by simp

lemma sin_exp_eq: "sin z = (exp(\<i> * z) - exp(-(\<i> * z))) / (2*\<i>)"
  by (simp add: exp_Euler exp_minus_Euler)

lemma sin_exp_eq': "sin z = \<i> * (exp(-(\<i> * z)) - exp(\<i> * z)) / 2"
  by (simp add: exp_Euler exp_minus_Euler)

lemma cos_exp_eq:  "cos z = (exp(\<i> * z) + exp(-(\<i> * z))) / 2"
  by (simp add: exp_Euler exp_minus_Euler)

subsection\<open>Relationships between real and complex trig functions\<close>

lemma real_sin_eq [simp]:
  fixes x::real
  shows "Re(sin(of_real x)) = sin x"
  by (simp add: sin_of_real)

lemma real_cos_eq [simp]:
  fixes x::real
  shows "Re(cos(of_real x)) = cos x"
  by (simp add: cos_of_real)

lemma DeMoivre: "(cos z + \<i> * sin z) ^ n = cos(n * z) + \<i> * sin(n * z)"
  apply (simp add: exp_Euler [symmetric])
  by (metis exp_of_nat_mult mult.left_commute)

lemma exp_cnj:
  fixes z::complex
  shows "cnj (exp z) = exp (cnj z)"
proof -
  have "(\<lambda>n. cnj (z ^ n /\<^sub>R (fact n))) = (\<lambda>n. (cnj z)^n /\<^sub>R (fact n))"
    by auto
  also have "... sums (exp (cnj z))"
    by (rule exp_converges)
  finally have "(\<lambda>n. cnj (z ^ n /\<^sub>R (fact n))) sums (exp (cnj z))" .
  moreover have "(\<lambda>n. cnj (z ^ n /\<^sub>R (fact n))) sums (cnj (exp z))"
    by (metis exp_converges sums_cnj)
  ultimately show ?thesis
    using sums_unique2
    by blast
qed

lemma cnj_sin: "cnj(sin z) = sin(cnj z)"
  by (simp add: sin_exp_eq exp_cnj field_simps)

lemma cnj_cos: "cnj(cos z) = cos(cnj z)"
  by (simp add: cos_exp_eq exp_cnj field_simps)

lemma field_differentiable_at_sin: "sin field_differentiable at z"
  using DERIV_sin field_differentiable_def by blast

lemma field_differentiable_within_sin: "sin field_differentiable (at z within s)"
  by (simp add: field_differentiable_at_sin field_differentiable_at_within)

lemma field_differentiable_at_cos: "cos field_differentiable at z"
  using DERIV_cos field_differentiable_def by blast

lemma field_differentiable_within_cos: "cos field_differentiable (at z within s)"
  by (simp add: field_differentiable_at_cos field_differentiable_at_within)

lemma holomorphic_on_sin: "sin holomorphic_on s"
  by (simp add: field_differentiable_within_sin holomorphic_on_def)

lemma holomorphic_on_cos: "cos holomorphic_on s"
  by (simp add: field_differentiable_within_cos holomorphic_on_def)

subsection\<open>Get a nice real/imaginary separation in Euler's formula.\<close>

lemma Euler: "exp(z) = of_real(exp(Re z)) *
              (of_real(cos(Im z)) + \<i> * of_real(sin(Im z)))"
by (cases z) (simp add: exp_add exp_Euler cos_of_real exp_of_real sin_of_real)

lemma Re_sin: "Re(sin z) = sin(Re z) * (exp(Im z) + exp(-(Im z))) / 2"
  by (simp add: sin_exp_eq field_simps Re_divide Im_exp)

lemma Im_sin: "Im(sin z) = cos(Re z) * (exp(Im z) - exp(-(Im z))) / 2"
  by (simp add: sin_exp_eq field_simps Im_divide Re_exp)

lemma Re_cos: "Re(cos z) = cos(Re z) * (exp(Im z) + exp(-(Im z))) / 2"
  by (simp add: cos_exp_eq field_simps Re_divide Re_exp)

lemma Im_cos: "Im(cos z) = sin(Re z) * (exp(-(Im z)) - exp(Im z)) / 2"
  by (simp add: cos_exp_eq field_simps Im_divide Im_exp)

lemma Re_sin_pos: "0 < Re z \<Longrightarrow> Re z < pi \<Longrightarrow> Re (sin z) > 0"
  by (auto simp: Re_sin Im_sin add_pos_pos sin_gt_zero)

lemma Im_sin_nonneg: "Re z = 0 \<Longrightarrow> 0 \<le> Im z \<Longrightarrow> 0 \<le> Im (sin z)"
  by (simp add: Re_sin Im_sin algebra_simps)

lemma Im_sin_nonneg2: "Re z = pi \<Longrightarrow> Im z \<le> 0 \<Longrightarrow> 0 \<le> Im (sin z)"
  by (simp add: Re_sin Im_sin algebra_simps)

subsection\<open>More on the Polar Representation of Complex Numbers\<close>

lemma exp_Complex: "exp(Complex r t) = of_real(exp r) * Complex (cos t) (sin t)"
  by (simp add: exp_add exp_Euler exp_of_real sin_of_real cos_of_real)

lemma exp_eq_1: "exp z = 1 \<longleftrightarrow> Re(z) = 0 \<and> (\<exists>n::int. Im(z) = of_int (2 * n) * pi)"
apply auto
apply (metis exp_eq_one_iff norm_exp_eq_Re norm_one)
apply (metis Re_exp cos_one_2pi_int mult.commute mult.left_neutral norm_exp_eq_Re norm_one one_complex.simps(1))
by (metis Im_exp Re_exp complex_Re_Im_cancel_iff cos_one_2pi_int sin_double Re_complex_of_real complex_Re_numeral exp_zero mult.assoc mult.left_commute mult_eq_0_iff mult_numeral_1 numeral_One of_real_0 sin_zero_iff_int2)

lemma exp_eq: "exp w = exp z \<longleftrightarrow> (\<exists>n::int. w = z + (of_int (2 * n) * pi) * \<i>)"
                (is "?lhs = ?rhs")
proof -
  have "exp w = exp z \<longleftrightarrow> exp (w-z) = 1"
    by (simp add: exp_diff)
  also have "... \<longleftrightarrow> (Re w = Re z \<and> (\<exists>n::int. Im w - Im z = of_int (2 * n) * pi))"
    by (simp add: exp_eq_1)
  also have "... \<longleftrightarrow> ?rhs"
    by (auto simp: algebra_simps intro!: complex_eqI)
  finally show ?thesis .
qed

lemma exp_complex_eqI: "\<bar>Im w - Im z\<bar> < 2*pi \<Longrightarrow> exp w = exp z \<Longrightarrow> w = z"
  by (auto simp: exp_eq abs_mult)

lemma exp_integer_2pi:
  assumes "n \<in> \<int>"
  shows "exp((2 * n * pi) * \<i>) = 1"
proof -
  have "exp((2 * n * pi) * \<i>) = exp 0"
    using assms
    by (simp only: Ints_def exp_eq) auto
  also have "... = 1"
    by simp
  finally show ?thesis .
qed

lemma exp_plus_2pin [simp]: "exp (z + \<i> * (of_int n * (of_real pi * 2))) = exp z"
  by (simp add: exp_eq)

lemma inj_on_exp_pi:
  fixes z::complex shows "inj_on exp (ball z pi)"
proof (clarsimp simp: inj_on_def exp_eq)
  fix y n
  assume "dist z (y + 2 * of_int n * of_real pi * \<i>) < pi"
         "dist z y < pi"
  then have "dist y (y + 2 * of_int n * of_real pi * \<i>) < pi+pi"
    using dist_commute_lessI dist_triangle_less_add by blast
  then have "norm (2 * of_int n * of_real pi * \<i>) < 2*pi"
    by (simp add: dist_norm)
  then show "n = 0"
    by (auto simp: norm_mult)
qed

lemma sin_cos_eq_iff: "sin y = sin x \<and> cos y = cos x \<longleftrightarrow> (\<exists>n::int. y = x + 2 * n * pi)"
proof -
  { assume "sin y = sin x" "cos y = cos x"
    then have "cos (y-x) = 1"
      using cos_add [of y "-x"] by simp
    then have "\<exists>n::int. y-x = n * 2 * pi"
      using cos_one_2pi_int by blast }
  then show ?thesis
  apply (auto simp: sin_add cos_add)
  apply (metis add.commute diff_add_cancel mult.commute)
  done
qed

lemma exp_i_ne_1:
  assumes "0 < x" "x < 2*pi"
  shows "exp(\<i> * of_real x) \<noteq> 1"
proof
  assume "exp (\<i> * of_real x) = 1"
  then have "exp (\<i> * of_real x) = exp 0"
    by simp
  then obtain n where "\<i> * of_real x = (of_int (2 * n) * pi) * \<i>"
    by (simp only: Ints_def exp_eq) auto
  then have  "of_real x = (of_int (2 * n) * pi)"
    by (metis complex_i_not_zero mult.commute mult_cancel_left of_real_eq_iff real_scaleR_def scaleR_conv_of_real)
  then have  "x = (of_int (2 * n) * pi)"
    by simp
  then show False using assms
    by (cases n) (auto simp: zero_less_mult_iff mult_less_0_iff)
qed

lemma sin_eq_0:
  fixes z::complex
  shows "sin z = 0 \<longleftrightarrow> (\<exists>n::int. z = of_real(n * pi))"
  by (simp add: sin_exp_eq exp_eq of_real_numeral)

lemma cos_eq_0:
  fixes z::complex
  shows "cos z = 0 \<longleftrightarrow> (\<exists>n::int. z = of_real(n * pi) + of_real pi/2)"
  using sin_eq_0 [of "z - of_real pi/2"]
  by (simp add: sin_diff algebra_simps)

lemma cos_eq_1:
  fixes z::complex
  shows "cos z = 1 \<longleftrightarrow> (\<exists>n::int. z = of_real(2 * n * pi))"
proof -
  have "cos z = cos (2*(z/2))"
    by simp
  also have "... = 1 - 2 * sin (z/2) ^ 2"
    by (simp only: cos_double_sin)
  finally have [simp]: "cos z = 1 \<longleftrightarrow> sin (z/2) = 0"
    by simp
  show ?thesis
    by (auto simp: sin_eq_0 of_real_numeral)
qed

lemma csin_eq_1:
  fixes z::complex
  shows "sin z = 1 \<longleftrightarrow> (\<exists>n::int. z = of_real(2 * n * pi) + of_real pi/2)"
  using cos_eq_1 [of "z - of_real pi/2"]
  by (simp add: cos_diff algebra_simps)

lemma csin_eq_minus1:
  fixes z::complex
  shows "sin z = -1 \<longleftrightarrow> (\<exists>n::int. z = of_real(2 * n * pi) + 3/2*pi)"
        (is "_ = ?rhs")
proof -
  have "sin z = -1 \<longleftrightarrow> sin (-z) = 1"
    by (simp add: equation_minus_iff)
  also have "...  \<longleftrightarrow> (\<exists>n::int. -z = of_real(2 * n * pi) + of_real pi/2)"
    by (simp only: csin_eq_1)
  also have "...  \<longleftrightarrow> (\<exists>n::int. z = - of_real(2 * n * pi) - of_real pi/2)"
    apply (rule iff_exI)
    by (metis (no_types)  is_num_normalize(8) minus_minus of_real_def real_vector.scale_minus_left uminus_add_conv_diff)
  also have "... = ?rhs"
    apply (auto simp: of_real_numeral)
    apply (rule_tac [2] x="-(x+1)" in exI)
    apply (rule_tac x="-(x+1)" in exI)
    apply (simp_all add: algebra_simps)
    done
  finally show ?thesis .
qed

lemma ccos_eq_minus1:
  fixes z::complex
  shows "cos z = -1 \<longleftrightarrow> (\<exists>n::int. z = of_real(2 * n * pi) + pi)"
  using csin_eq_1 [of "z - of_real pi/2"]
  apply (simp add: sin_diff)
  apply (simp add: algebra_simps of_real_numeral equation_minus_iff)
  done

lemma sin_eq_1: "sin x = 1 \<longleftrightarrow> (\<exists>n::int. x = (2 * n + 1 / 2) * pi)"
                (is "_ = ?rhs")
proof -
  have "sin x = 1 \<longleftrightarrow> sin (complex_of_real x) = 1"
    by (metis of_real_1 one_complex.simps(1) real_sin_eq sin_of_real)
  also have "...  \<longleftrightarrow> (\<exists>n::int. complex_of_real x = of_real(2 * n * pi) + of_real pi/2)"
    by (simp only: csin_eq_1)
  also have "...  \<longleftrightarrow> (\<exists>n::int. x = of_real(2 * n * pi) + of_real pi/2)"
    apply (rule iff_exI)
    apply (auto simp: algebra_simps of_real_numeral)
    apply (rule injD [OF inj_of_real [where 'a = complex]])
    apply (auto simp: of_real_numeral)
    done
  also have "... = ?rhs"
    by (auto simp: algebra_simps)
  finally show ?thesis .
qed

lemma sin_eq_minus1: "sin x = -1 \<longleftrightarrow> (\<exists>n::int. x = (2*n + 3/2) * pi)"  (is "_ = ?rhs")
proof -
  have "sin x = -1 \<longleftrightarrow> sin (complex_of_real x) = -1"
    by (metis Re_complex_of_real of_real_def scaleR_minus1_left sin_of_real)
  also have "...  \<longleftrightarrow> (\<exists>n::int. complex_of_real x = of_real(2 * n * pi) + 3/2*pi)"
    by (simp only: csin_eq_minus1)
  also have "...  \<longleftrightarrow> (\<exists>n::int. x = of_real(2 * n * pi) + 3/2*pi)"
    apply (rule iff_exI)
    apply (auto simp: algebra_simps)
    apply (rule injD [OF inj_of_real [where 'a = complex]], auto)
    done
  also have "... = ?rhs"
    by (auto simp: algebra_simps)
  finally show ?thesis .
qed

lemma cos_eq_minus1: "cos x = -1 \<longleftrightarrow> (\<exists>n::int. x = (2*n + 1) * pi)"
                      (is "_ = ?rhs")
proof -
  have "cos x = -1 \<longleftrightarrow> cos (complex_of_real x) = -1"
    by (metis Re_complex_of_real of_real_def scaleR_minus1_left cos_of_real)
  also have "...  \<longleftrightarrow> (\<exists>n::int. complex_of_real x = of_real(2 * n * pi) + pi)"
    by (simp only: ccos_eq_minus1)
  also have "...  \<longleftrightarrow> (\<exists>n::int. x = of_real(2 * n * pi) + pi)"
    apply (rule iff_exI)
    apply (auto simp: algebra_simps)
    apply (rule injD [OF inj_of_real [where 'a = complex]], auto)
    done
  also have "... = ?rhs"
    by (auto simp: algebra_simps)
  finally show ?thesis .
qed

lemma dist_exp_ii_1: "norm(exp(\<i> * of_real t) - 1) = 2 * \<bar>sin(t / 2)\<bar>"
  apply (simp add: exp_Euler cmod_def power2_diff sin_of_real cos_of_real algebra_simps)
  using cos_double_sin [of "t/2"]
  apply (simp add: real_sqrt_mult)
  done

lemma sinh_complex:
  fixes z :: complex
  shows "(exp z - inverse (exp z)) / 2 = -\<i> * sin(\<i> * z)"
  by (simp add: sin_exp_eq divide_simps exp_minus of_real_numeral)

lemma sin_ii_times:
  fixes z :: complex
  shows "sin(\<i> * z) = \<i> * ((exp z - inverse (exp z)) / 2)"
  using sinh_complex by auto

lemma sinh_real:
  fixes x :: real
  shows "of_real((exp x - inverse (exp x)) / 2) = -\<i> * sin(\<i> * of_real x)"
  by (simp add: exp_of_real sin_ii_times of_real_numeral)

lemma cosh_complex:
  fixes z :: complex
  shows "(exp z + inverse (exp z)) / 2 = cos(\<i> * z)"
  by (simp add: cos_exp_eq divide_simps exp_minus of_real_numeral exp_of_real)

lemma cosh_real:
  fixes x :: real
  shows "of_real((exp x + inverse (exp x)) / 2) = cos(\<i> * of_real x)"
  by (simp add: cos_exp_eq divide_simps exp_minus of_real_numeral exp_of_real)

lemmas cos_ii_times = cosh_complex [symmetric]

lemma norm_cos_squared:
    "norm(cos z) ^ 2 = cos(Re z) ^ 2 + (exp(Im z) - inverse(exp(Im z))) ^ 2 / 4"
  apply (cases z)
  apply (simp add: cos_add cmod_power2 cos_of_real sin_of_real)
  apply (simp add: cos_exp_eq sin_exp_eq exp_minus exp_of_real Re_divide Im_divide power_divide)
  apply (simp only: left_diff_distrib [symmetric] power_mult_distrib)
  apply (simp add: sin_squared_eq)
  apply (simp add: power2_eq_square algebra_simps divide_simps)
  done

lemma norm_sin_squared:
    "norm(sin z) ^ 2 = (exp(2 * Im z) + inverse(exp(2 * Im z)) - 2 * cos(2 * Re z)) / 4"
  apply (cases z)
  apply (simp add: sin_add cmod_power2 cos_of_real sin_of_real cos_double_cos exp_double)
  apply (simp add: cos_exp_eq sin_exp_eq exp_minus exp_of_real Re_divide Im_divide power_divide)
  apply (simp only: left_diff_distrib [symmetric] power_mult_distrib)
  apply (simp add: cos_squared_eq)
  apply (simp add: power2_eq_square algebra_simps divide_simps)
  done

lemma exp_uminus_Im: "exp (- Im z) \<le> exp (cmod z)"
  using abs_Im_le_cmod linear order_trans by fastforce

lemma norm_cos_le:
  fixes z::complex
  shows "norm(cos z) \<le> exp(norm z)"
proof -
  have "Im z \<le> cmod z"
    using abs_Im_le_cmod abs_le_D1 by auto
  with exp_uminus_Im show ?thesis
    apply (simp add: cos_exp_eq norm_divide)
    apply (rule order_trans [OF norm_triangle_ineq], simp)
    apply (metis add_mono exp_le_cancel_iff mult_2_right)
    done
qed

lemma norm_cos_plus1_le:
  fixes z::complex
  shows "norm(1 + cos z) \<le> 2 * exp(norm z)"
proof -
  have mono: "\<And>u w z::real. (1 \<le> w | 1 \<le> z) \<Longrightarrow> (w \<le> u & z \<le> u) \<Longrightarrow> 2 + w + z \<le> 4 * u"
      by arith
  have *: "Im z \<le> cmod z"
    using abs_Im_le_cmod abs_le_D1 by auto
  have triangle3: "\<And>x y z. norm(x + y + z) \<le> norm(x) + norm(y) + norm(z)"
    by (simp add: norm_add_rule_thm)
  have "norm(1 + cos z) = cmod (1 + (exp (\<i> * z) + exp (- (\<i> * z))) / 2)"
    by (simp add: cos_exp_eq)
  also have "... = cmod ((2 + exp (\<i> * z) + exp (- (\<i> * z))) / 2)"
    by (simp add: field_simps)
  also have "... = cmod (2 + exp (\<i> * z) + exp (- (\<i> * z))) / 2"
    by (simp add: norm_divide)
  finally show ?thesis
    apply (rule ssubst, simp)
    apply (rule order_trans [OF triangle3], simp)
    using exp_uminus_Im *
    apply (auto intro: mono)
    done
qed

subsection\<open>Taylor series for complex exponential, sine and cosine.\<close>

declare power_Suc [simp del]

lemma Taylor_exp:
  "norm(exp z - (\<Sum>k\<le>n. z ^ k / (fact k))) \<le> exp\<bar>Re z\<bar> * (norm z) ^ (Suc n) / (fact n)"
proof (rule complex_taylor [of _ n "\<lambda>k. exp" "exp\<bar>Re z\<bar>" 0 z, simplified])
  show "convex (closed_segment 0 z)"
    by (rule convex_closed_segment [of 0 z])
next
  fix k x
  assume "x \<in> closed_segment 0 z" "k \<le> n"
  show "(exp has_field_derivative exp x) (at x within closed_segment 0 z)"
    using DERIV_exp DERIV_subset by blast
next
  fix x
  assume "x \<in> closed_segment 0 z"
  then show "Re x \<le> \<bar>Re z\<bar>"
    apply (auto simp: closed_segment_def scaleR_conv_of_real)
    by (meson abs_ge_self abs_ge_zero linear mult_left_le_one_le mult_nonneg_nonpos order_trans)
next
  show "0 \<in> closed_segment 0 z"
    by (auto simp: closed_segment_def)
next
  show "z \<in> closed_segment 0 z"
    apply (simp add: closed_segment_def scaleR_conv_of_real)
    using of_real_1 zero_le_one by blast
qed

lemma
  assumes "0 \<le> u" "u \<le> 1"
  shows cmod_sin_le_exp: "cmod (sin (u *\<^sub>R z)) \<le> exp \<bar>Im z\<bar>"
    and cmod_cos_le_exp: "cmod (cos (u *\<^sub>R z)) \<le> exp \<bar>Im z\<bar>"
proof -
  have mono: "\<And>u w z::real. w \<le> u \<Longrightarrow> z \<le> u \<Longrightarrow> w + z \<le> u*2"
    by arith
  show "cmod (sin (u *\<^sub>R z)) \<le> exp \<bar>Im z\<bar>" using assms
    apply (auto simp: scaleR_conv_of_real norm_mult norm_power sin_exp_eq norm_divide)
    apply (rule order_trans [OF norm_triangle_ineq4])
    apply (rule mono)
    apply (auto simp: abs_if mult_left_le_one_le)
    apply (meson mult_nonneg_nonneg neg_le_0_iff_le not_le order_trans)
    apply (meson less_eq_real_def mult_nonneg_nonpos neg_0_le_iff_le order_trans)
    done
  show "cmod (cos (u *\<^sub>R z)) \<le> exp \<bar>Im z\<bar>" using assms
    apply (auto simp: scaleR_conv_of_real norm_mult norm_power cos_exp_eq norm_divide)
    apply (rule order_trans [OF norm_triangle_ineq])
    apply (rule mono)
    apply (auto simp: abs_if mult_left_le_one_le)
    apply (meson mult_nonneg_nonneg neg_le_0_iff_le not_le order_trans)
    apply (meson less_eq_real_def mult_nonneg_nonpos neg_0_le_iff_le order_trans)
    done
qed

lemma Taylor_sin:
  "norm(sin z - (\<Sum>k\<le>n. complex_of_real (sin_coeff k) * z ^ k))
   \<le> exp\<bar>Im z\<bar> * (norm z) ^ (Suc n) / (fact n)"
proof -
  have mono: "\<And>u w z::real. w \<le> u \<Longrightarrow> z \<le> u \<Longrightarrow> w + z \<le> u*2"
      by arith
  have *: "cmod (sin z -
                 (\<Sum>i\<le>n. (-1) ^ (i div 2) * (if even i then sin 0 else cos 0) * z ^ i / (fact i)))
           \<le> exp \<bar>Im z\<bar> * cmod z ^ Suc n / (fact n)"
  proof (rule complex_taylor [of "closed_segment 0 z" n
                                 "\<lambda>k x. (-1)^(k div 2) * (if even k then sin x else cos x)"
                                 "exp\<bar>Im z\<bar>" 0 z,  simplified])
    fix k x
    show "((\<lambda>x. (- 1) ^ (k div 2) * (if even k then sin x else cos x)) has_field_derivative
            (- 1) ^ (Suc k div 2) * (if odd k then sin x else cos x))
            (at x within closed_segment 0 z)"
      apply (auto simp: power_Suc)
      apply (intro derivative_eq_intros | simp)+
      done
  next
    fix x
    assume "x \<in> closed_segment 0 z"
    then show "cmod ((- 1) ^ (Suc n div 2) * (if odd n then sin x else cos x)) \<le> exp \<bar>Im z\<bar>"
      by (auto simp: closed_segment_def norm_mult norm_power cmod_sin_le_exp cmod_cos_le_exp)
  qed
  have **: "\<And>k. complex_of_real (sin_coeff k) * z ^ k
            = (-1)^(k div 2) * (if even k then sin 0 else cos 0) * z^k / of_nat (fact k)"
    by (auto simp: sin_coeff_def elim!: oddE)
  show ?thesis
    apply (rule order_trans [OF _ *])
    apply (simp add: **)
    done
qed

lemma Taylor_cos:
  "norm(cos z - (\<Sum>k\<le>n. complex_of_real (cos_coeff k) * z ^ k))
   \<le> exp\<bar>Im z\<bar> * (norm z) ^ Suc n / (fact n)"
proof -
  have mono: "\<And>u w z::real. w \<le> u \<Longrightarrow> z \<le> u \<Longrightarrow> w + z \<le> u*2"
      by arith
  have *: "cmod (cos z -
                 (\<Sum>i\<le>n. (-1) ^ (Suc i div 2) * (if even i then cos 0 else sin 0) * z ^ i / (fact i)))
           \<le> exp \<bar>Im z\<bar> * cmod z ^ Suc n / (fact n)"
  proof (rule complex_taylor [of "closed_segment 0 z" n "\<lambda>k x. (-1)^(Suc k div 2) * (if even k then cos x else sin x)" "exp\<bar>Im z\<bar>" 0 z,
simplified])
    fix k x
    assume "x \<in> closed_segment 0 z" "k \<le> n"
    show "((\<lambda>x. (- 1) ^ (Suc k div 2) * (if even k then cos x else sin x)) has_field_derivative
            (- 1) ^ Suc (k div 2) * (if odd k then cos x else sin x))
             (at x within closed_segment 0 z)"
      apply (auto simp: power_Suc)
      apply (intro derivative_eq_intros | simp)+
      done
  next
    fix x
    assume "x \<in> closed_segment 0 z"
    then show "cmod ((- 1) ^ Suc (n div 2) * (if odd n then cos x else sin x)) \<le> exp \<bar>Im z\<bar>"
      by (auto simp: closed_segment_def norm_mult norm_power cmod_sin_le_exp cmod_cos_le_exp)
  qed
  have **: "\<And>k. complex_of_real (cos_coeff k) * z ^ k
            = (-1)^(Suc k div 2) * (if even k then cos 0 else sin 0) * z^k / of_nat (fact k)"
    by (auto simp: cos_coeff_def elim!: evenE)
  show ?thesis
    apply (rule order_trans [OF _ *])
    apply (simp add: **)
    done
qed

declare power_Suc [simp]

text\<open>32-bit Approximation to e\<close>
lemma e_approx_32: "\<bar>exp(1) - 5837465777 / 2147483648\<bar> \<le> (inverse(2 ^ 32)::real)"
  using Taylor_exp [of 1 14] exp_le
  apply (simp add: sum_distrib_right in_Reals_norm Re_exp atMost_nat_numeral fact_numeral)
  apply (simp only: pos_le_divide_eq [symmetric], linarith)
  done

lemma e_less_3: "exp 1 < (3::real)"
  using e_approx_32
  by (simp add: abs_if split: if_split_asm)

lemma ln3_gt_1: "ln 3 > (1::real)"
  by (metis e_less_3 exp_less_cancel_iff exp_ln_iff less_trans ln_exp)


subsection\<open>The argument of a complex number\<close>

definition Arg :: "complex \<Rightarrow> real" where
 "Arg z \<equiv> if z = 0 then 0
           else THE t. 0 \<le> t \<and> t < 2*pi \<and>
                    z = of_real(norm z) * exp(\<i> * of_real t)"

lemma Arg_0 [simp]: "Arg(0) = 0"
  by (simp add: Arg_def)

lemma Arg_unique_lemma:
  assumes z:  "z = of_real(norm z) * exp(\<i> * of_real t)"
      and z': "z = of_real(norm z) * exp(\<i> * of_real t')"
      and t:  "0 \<le> t"  "t < 2*pi"
      and t': "0 \<le> t'" "t' < 2*pi"
      and nz: "z \<noteq> 0"
  shows "t' = t"
proof -
  have [dest]: "\<And>x y z::real. x\<ge>0 \<Longrightarrow> x+y < z \<Longrightarrow> y<z"
    by arith
  have "of_real (cmod z) * exp (\<i> * of_real t') = of_real (cmod z) * exp (\<i> * of_real t)"
    by (metis z z')
  then have "exp (\<i> * of_real t') = exp (\<i> * of_real t)"
    by (metis nz mult_left_cancel mult_zero_left z)
  then have "sin t' = sin t \<and> cos t' = cos t"
    apply (simp add: exp_Euler sin_of_real cos_of_real)
    by (metis Complex_eq complex.sel)
  then obtain n::int where n: "t' = t + 2 * n * pi"
    by (auto simp: sin_cos_eq_iff)
  then have "n=0"
    apply (rule_tac z=n in int_cases)
    using t t'
    apply (auto simp: mult_less_0_iff algebra_simps)
    done
  then show "t' = t"
      by (simp add: n)
qed

lemma Arg: "0 \<le> Arg z & Arg z < 2*pi & z = of_real(norm z) * exp(\<i> * of_real(Arg z))"
proof (cases "z=0")
  case True then show ?thesis
    by (simp add: Arg_def)
next
  case False
  obtain t where t: "0 \<le> t" "t < 2*pi"
             and ReIm: "Re z / cmod z = cos t" "Im z / cmod z = sin t"
    using sincos_total_2pi [OF complex_unit_circle [OF False]]
    by blast
  have z: "z = of_real(norm z) * exp(\<i> * of_real t)"
    apply (rule complex_eqI)
    using t False ReIm
    apply (auto simp: exp_Euler sin_of_real cos_of_real divide_simps)
    done
  show ?thesis
    apply (simp add: Arg_def False)
    apply (rule theI [where a=t])
    using t z False
    apply (auto intro: Arg_unique_lemma)
    done
qed

corollary
  shows Arg_ge_0: "0 \<le> Arg z"
    and Arg_lt_2pi: "Arg z < 2*pi"
    and Arg_eq: "z = of_real(norm z) * exp(\<i> * of_real(Arg z))"
  using Arg by auto

lemma complex_norm_eq_1_exp: "norm z = 1 \<longleftrightarrow> exp(\<i> * of_real (Arg z)) = z"
  by (metis Arg_eq cis_conv_exp mult.left_neutral norm_cis of_real_1)

lemma Arg_unique: "\<lbrakk>of_real r * exp(\<i> * of_real a) = z; 0 < r; 0 \<le> a; a < 2*pi\<rbrakk> \<Longrightarrow> Arg z = a"
  apply (rule Arg_unique_lemma [OF _ Arg_eq])
  using Arg [of z]
  apply (auto simp: norm_mult)
  done

lemma Arg_minus: "z \<noteq> 0 \<Longrightarrow> Arg (-z) = (if Arg z < pi then Arg z + pi else Arg z - pi)"
  apply (rule Arg_unique [of "norm z"])
  apply (rule complex_eqI)
  using Arg_ge_0 [of z] Arg_eq [of z] Arg_lt_2pi [of z] Arg_eq [of z]
  apply auto
  apply (auto simp: Re_exp Im_exp cos_diff sin_diff cis_conv_exp [symmetric])
  apply (metis Re_rcis Im_rcis rcis_def)+
  done

lemma Arg_times_of_real [simp]: "0 < r \<Longrightarrow> Arg (of_real r * z) = Arg z"
  apply (cases "z=0", simp)
  apply (rule Arg_unique [of "r * norm z"])
  using Arg
  apply auto
  done

lemma Arg_times_of_real2 [simp]: "0 < r \<Longrightarrow> Arg (z * of_real r) = Arg z"
  by (metis Arg_times_of_real mult.commute)

lemma Arg_divide_of_real [simp]: "0 < r \<Longrightarrow> Arg (z / of_real r) = Arg z"
  by (metis Arg_times_of_real2 less_numeral_extra(3) nonzero_eq_divide_eq of_real_eq_0_iff)

lemma Arg_le_pi: "Arg z \<le> pi \<longleftrightarrow> 0 \<le> Im z"
proof (cases "z=0")
  case True then show ?thesis
    by simp
next
  case False
  have "0 \<le> Im z \<longleftrightarrow> 0 \<le> Im (of_real (cmod z) * exp (\<i> * complex_of_real (Arg z)))"
    by (metis Arg_eq)
  also have "... = (0 \<le> Im (exp (\<i> * complex_of_real (Arg z))))"
    using False
    by (simp add: zero_le_mult_iff)
  also have "... \<longleftrightarrow> Arg z \<le> pi"
    by (simp add: Im_exp) (metis Arg_ge_0 Arg_lt_2pi sin_lt_zero sin_ge_zero not_le)
  finally show ?thesis
    by blast
qed

lemma Arg_lt_pi: "0 < Arg z \<and> Arg z < pi \<longleftrightarrow> 0 < Im z"
proof (cases "z=0")
  case True then show ?thesis
    by simp
next
  case False
  have "0 < Im z \<longleftrightarrow> 0 < Im (of_real (cmod z) * exp (\<i> * complex_of_real (Arg z)))"
    by (metis Arg_eq)
  also have "... = (0 < Im (exp (\<i> * complex_of_real (Arg z))))"
    using False
    by (simp add: zero_less_mult_iff)
  also have "... \<longleftrightarrow> 0 < Arg z \<and> Arg z < pi"
    using Arg_ge_0  Arg_lt_2pi sin_le_zero sin_gt_zero
    apply (auto simp: Im_exp)
    using le_less apply fastforce
    using not_le by blast
  finally show ?thesis
    by blast
qed

lemma Arg_eq_0: "Arg z = 0 \<longleftrightarrow> z \<in> \<real> \<and> 0 \<le> Re z"
proof (cases "z=0")
  case True then show ?thesis
    by simp
next
  case False
  have "z \<in> \<real> \<and> 0 \<le> Re z \<longleftrightarrow> z \<in> \<real> \<and> 0 \<le> Re (of_real (cmod z) * exp (\<i> * complex_of_real (Arg z)))"
    by (metis Arg_eq)
  also have "... \<longleftrightarrow> z \<in> \<real> \<and> 0 \<le> Re (exp (\<i> * complex_of_real (Arg z)))"
    using False
    by (simp add: zero_le_mult_iff)
  also have "... \<longleftrightarrow> Arg z = 0"
    apply (auto simp: Re_exp)
    apply (metis Arg_lt_pi Arg_ge_0 Arg_le_pi cos_pi complex_is_Real_iff leD less_linear less_minus_one_simps(2) minus_minus neg_less_eq_nonneg order_refl)
    using Arg_eq [of z]
    apply (auto simp: Reals_def)
    done
  finally show ?thesis
    by blast
qed

corollary Arg_gt_0:
  assumes "z \<in> \<real> \<Longrightarrow> Re z < 0"
    shows "Arg z > 0"
  using Arg_eq_0 Arg_ge_0 assms dual_order.strict_iff_order by fastforce

lemma Arg_of_real: "Arg(of_real x) = 0 \<longleftrightarrow> 0 \<le> x"
  by (simp add: Arg_eq_0)

lemma Arg_eq_pi: "Arg z = pi \<longleftrightarrow> z \<in> \<real> \<and> Re z < 0"
  apply  (cases "z=0", simp)
  using Arg_eq_0 [of "-z"]
  apply (auto simp: complex_is_Real_iff Arg_minus)
  apply (simp add: complex_Re_Im_cancel_iff)
  apply (metis Arg_minus pi_gt_zero add.left_neutral minus_minus minus_zero)
  done

lemma Arg_eq_0_pi: "Arg z = 0 \<or> Arg z = pi \<longleftrightarrow> z \<in> \<real>"
  using Arg_eq_0 Arg_eq_pi not_le by auto

lemma Arg_inverse: "Arg(inverse z) = (if z \<in> \<real> \<and> 0 \<le> Re z then Arg z else 2*pi - Arg z)"
  apply (cases "z=0", simp)
  apply (rule Arg_unique [of "inverse (norm z)"])
  using Arg_ge_0 [of z] Arg_lt_2pi [of z] Arg_eq [of z] Arg_eq_0 [of z] exp_two_pi_i
  apply (auto simp: of_real_numeral algebra_simps exp_diff divide_simps)
  done

lemma Arg_eq_iff:
  assumes "w \<noteq> 0" "z \<noteq> 0"
     shows "Arg w = Arg z \<longleftrightarrow> (\<exists>x. 0 < x & w = of_real x * z)"
  using assms Arg_eq [of z] Arg_eq [of w]
  apply auto
  apply (rule_tac x="norm w / norm z" in exI)
  apply (simp add: divide_simps)
  by (metis mult.commute mult.left_commute)

lemma Arg_inverse_eq_0: "Arg(inverse z) = 0 \<longleftrightarrow> Arg z = 0"
  using complex_is_Real_iff
  apply (simp add: Arg_eq_0)
  apply (auto simp: divide_simps not_sum_power2_lt_zero)
  done

lemma Arg_divide:
  assumes "w \<noteq> 0" "z \<noteq> 0" "Arg w \<le> Arg z"
    shows "Arg(z / w) = Arg z - Arg w"
  apply (rule Arg_unique [of "norm(z / w)"])
  using assms Arg_eq [of z] Arg_eq [of w] Arg_ge_0 [of w] Arg_lt_2pi [of z]
  apply (auto simp: exp_diff norm_divide algebra_simps divide_simps)
  done

lemma Arg_le_div_sum:
  assumes "w \<noteq> 0" "z \<noteq> 0" "Arg w \<le> Arg z"
    shows "Arg z = Arg w + Arg(z / w)"
  by (simp add: Arg_divide assms)

lemma Arg_le_div_sum_eq:
  assumes "w \<noteq> 0" "z \<noteq> 0"
    shows "Arg w \<le> Arg z \<longleftrightarrow> Arg z = Arg w + Arg(z / w)"
  using assms
  by (auto simp: Arg_ge_0 intro: Arg_le_div_sum)

lemma Arg_diff:
  assumes "w \<noteq> 0" "z \<noteq> 0"
    shows "Arg w - Arg z = (if Arg z \<le> Arg w then Arg(w / z) else Arg(w/z) - 2*pi)"
  using assms
  apply (auto simp: Arg_ge_0 Arg_divide not_le)
  using Arg_divide [of w z] Arg_inverse [of "w/z"]
  apply auto
  by (metis Arg_eq_0 less_irrefl minus_diff_eq right_minus_eq)

lemma Arg_add:
  assumes "w \<noteq> 0" "z \<noteq> 0"
    shows "Arg w + Arg z = (if Arg w + Arg z < 2*pi then Arg(w * z) else Arg(w * z) + 2*pi)"
  using assms
  using Arg_diff [of "w*z" z] Arg_le_div_sum_eq [of z "w*z"]
  apply (auto simp: Arg_ge_0 Arg_divide not_le)
  apply (metis Arg_lt_2pi add.commute)
  apply (metis (no_types) Arg add.commute diff_0 diff_add_cancel diff_less_eq diff_minus_eq_add not_less)
  done

lemma Arg_times:
  assumes "w \<noteq> 0" "z \<noteq> 0"
    shows "Arg (w * z) = (if Arg w + Arg z < 2*pi then Arg w + Arg z
                            else (Arg w + Arg z) - 2*pi)"
  using Arg_add [OF assms]
  by auto

lemma Arg_cnj: "Arg(cnj z) = (if z \<in> \<real> \<and> 0 \<le> Re z then Arg z else 2*pi - Arg z)"
  apply (cases "z=0", simp)
  apply (rule trans [of _ "Arg(inverse z)"])
  apply (simp add: Arg_eq_iff divide_simps complex_norm_square [symmetric] mult.commute)
  apply (metis norm_eq_zero of_real_power zero_less_power2)
  apply (auto simp: of_real_numeral Arg_inverse)
  done

lemma Arg_real: "z \<in> \<real> \<Longrightarrow> Arg z = (if 0 \<le> Re z then 0 else pi)"
  using Arg_eq_0 Arg_eq_0_pi
  by auto

lemma Arg_exp: "0 \<le> Im z \<Longrightarrow> Im z < 2*pi \<Longrightarrow> Arg(exp z) = Im z"
  by (rule Arg_unique [of  "exp(Re z)"]) (auto simp: exp_eq_polar)

lemma complex_split_polar:
  obtains r a::real where "z = complex_of_real r * (cos a + \<i> * sin a)" "0 \<le> r" "0 \<le> a" "a < 2*pi"
  using Arg cis.ctr cis_conv_exp by fastforce

lemma Re_Im_le_cmod: "Im w * sin \<phi> + Re w * cos \<phi> \<le> cmod w"
proof (cases w rule: complex_split_polar)
  case (1 r a) with sin_cos_le1 [of a \<phi>] show ?thesis
    apply (simp add: norm_mult cmod_unit_one)
    by (metis (no_types, hide_lams) abs_le_D1 distrib_left mult.commute mult.left_commute mult_left_le)
qed

subsection\<open>Analytic properties of tangent function\<close>

lemma cnj_tan: "cnj(tan z) = tan(cnj z)"
  by (simp add: cnj_cos cnj_sin tan_def)

lemma field_differentiable_at_tan: "~(cos z = 0) \<Longrightarrow> tan field_differentiable at z"
  unfolding field_differentiable_def
  using DERIV_tan by blast

lemma field_differentiable_within_tan: "~(cos z = 0)
         \<Longrightarrow> tan field_differentiable (at z within s)"
  using field_differentiable_at_tan field_differentiable_at_within by blast

lemma continuous_within_tan: "~(cos z = 0) \<Longrightarrow> continuous (at z within s) tan"
  using continuous_at_imp_continuous_within isCont_tan by blast

lemma continuous_on_tan [continuous_intros]: "(\<And>z. z \<in> s \<Longrightarrow> ~(cos z = 0)) \<Longrightarrow> continuous_on s tan"
  by (simp add: continuous_at_imp_continuous_on)

lemma holomorphic_on_tan: "(\<And>z. z \<in> s \<Longrightarrow> ~(cos z = 0)) \<Longrightarrow> tan holomorphic_on s"
  by (simp add: field_differentiable_within_tan holomorphic_on_def)


subsection\<open>Complex logarithms (the conventional principal value)\<close>

instantiation complex :: ln
begin

definition ln_complex :: "complex \<Rightarrow> complex"
  where "ln_complex \<equiv> \<lambda>z. THE w. exp w = z & -pi < Im(w) & Im(w) \<le> pi"

lemma
  assumes "z \<noteq> 0"
    shows exp_Ln [simp]:  "exp(ln z) = z"
      and mpi_less_Im_Ln: "-pi < Im(ln z)"
      and Im_Ln_le_pi:    "Im(ln z) \<le> pi"
proof -
  obtain \<psi> where z: "z / (cmod z) = Complex (cos \<psi>) (sin \<psi>)"
    using complex_unimodular_polar [of "z / (norm z)"] assms
    by (auto simp: norm_divide divide_simps)
  obtain \<phi> where \<phi>: "- pi < \<phi>" "\<phi> \<le> pi" "sin \<phi> = sin \<psi>" "cos \<phi> = cos \<psi>"
    using sincos_principal_value [of "\<psi>"] assms
    by (auto simp: norm_divide divide_simps)
  have "exp(ln z) = z & -pi < Im(ln z) & Im(ln z) \<le> pi" unfolding ln_complex_def
    apply (rule theI [where a = "Complex (ln(norm z)) \<phi>"])
    using z assms \<phi>
    apply (auto simp: field_simps exp_complex_eqI exp_eq_polar cis.code)
    done
  then show "exp(ln z) = z" "-pi < Im(ln z)" "Im(ln z) \<le> pi"
    by auto
qed

lemma Ln_exp [simp]:
  assumes "-pi < Im(z)" "Im(z) \<le> pi"
    shows "ln(exp z) = z"
  apply (rule exp_complex_eqI)
  using assms mpi_less_Im_Ln  [of "exp z"] Im_Ln_le_pi [of "exp z"]
  apply auto
  done

subsection\<open>Relation to Real Logarithm\<close>

lemma Ln_of_real:
  assumes "0 < z"
    shows "ln(of_real z::complex) = of_real(ln z)"
proof -
  have "ln(of_real (exp (ln z))::complex) = ln (exp (of_real (ln z)))"
    by (simp add: exp_of_real)
  also have "... = of_real(ln z)"
    using assms
    by (subst Ln_exp) auto
  finally show ?thesis
    using assms by simp
qed

corollary Ln_in_Reals [simp]: "z \<in> \<real> \<Longrightarrow> Re z > 0 \<Longrightarrow> ln z \<in> \<real>"
  by (auto simp: Ln_of_real elim: Reals_cases)

corollary Im_Ln_of_real [simp]: "r > 0 \<Longrightarrow> Im (ln (of_real r)) = 0"
  by (simp add: Ln_of_real)

lemma cmod_Ln_Reals [simp]: "z \<in> \<real> \<Longrightarrow> 0 < Re z \<Longrightarrow> cmod (ln z) = norm (ln (Re z))"
  using Ln_of_real by force

lemma Ln_1: "ln 1 = (0::complex)"
proof -
  have "ln (exp 0) = (0::complex)"
    by (metis (mono_tags, hide_lams) Ln_of_real exp_zero ln_one of_real_0 of_real_1 zero_less_one)
  then show ?thesis
    by simp
qed

instance
  by intro_classes (rule ln_complex_def Ln_1)

end

abbreviation Ln :: "complex \<Rightarrow> complex"
  where "Ln \<equiv> ln"

lemma Ln_eq_iff: "w \<noteq> 0 \<Longrightarrow> z \<noteq> 0 \<Longrightarrow> (Ln w = Ln z \<longleftrightarrow> w = z)"
  by (metis exp_Ln)

lemma Ln_unique: "exp(z) = w \<Longrightarrow> -pi < Im(z) \<Longrightarrow> Im(z) \<le> pi \<Longrightarrow> Ln w = z"
  using Ln_exp by blast

lemma Re_Ln [simp]: "z \<noteq> 0 \<Longrightarrow> Re(Ln z) = ln(norm z)"
  by (metis exp_Ln ln_exp norm_exp_eq_Re)

corollary ln_cmod_le:
  assumes z: "z \<noteq> 0"
    shows "ln (cmod z) \<le> cmod (Ln z)"
  using norm_exp [of "Ln z", simplified exp_Ln [OF z]]
  by (metis Re_Ln complex_Re_le_cmod z)

proposition exists_complex_root:
  fixes z :: complex
  assumes "n \<noteq> 0"  obtains w where "z = w ^ n"
  apply (cases "z=0")
  using assms apply (simp add: power_0_left)
  apply (rule_tac w = "exp(Ln z / n)" in that)
  apply (auto simp: assms exp_of_nat_mult [symmetric])
  done

corollary exists_complex_root_nonzero:
  fixes z::complex
  assumes "z \<noteq> 0" "n \<noteq> 0"
  obtains w where "w \<noteq> 0" "z = w ^ n"
  by (metis exists_complex_root [of n z] assms power_0_left)

subsection\<open>The Unwinding Number and the Ln-product Formula\<close>

text\<open>Note that in this special case the unwinding number is -1, 0 or 1.\<close>

definition unwinding :: "complex \<Rightarrow> complex" where
   "unwinding(z) = (z - Ln(exp z)) / (of_real(2*pi) * \<i>)"

lemma unwinding_2pi: "(2*pi) * \<i> * unwinding(z) = z - Ln(exp z)"
  by (simp add: unwinding_def)

lemma Ln_times_unwinding:
    "w \<noteq> 0 \<Longrightarrow> z \<noteq> 0 \<Longrightarrow> Ln(w * z) = Ln(w) + Ln(z) - (2*pi) * \<i> * unwinding(Ln w + Ln z)"
  using unwinding_2pi by (simp add: exp_add)


subsection\<open>Derivative of Ln away from the branch cut\<close>

lemma
  assumes "z \<notin> \<real>\<^sub>\<le>\<^sub>0"
    shows has_field_derivative_Ln: "(Ln has_field_derivative inverse(z)) (at z)"
      and Im_Ln_less_pi:           "Im (Ln z) < pi"
proof -
  have znz: "z \<noteq> 0"
    using assms by auto
  then have "Im (Ln z) \<noteq> pi"
    by (metis (no_types) Im_exp Ln_in_Reals assms complex_nonpos_Reals_iff complex_is_Real_iff exp_Ln mult_zero_right not_less pi_neq_zero sin_pi znz)
  then show *: "Im (Ln z) < pi" using assms Im_Ln_le_pi
    by (simp add: le_neq_trans znz)
  have "(exp has_field_derivative z) (at (Ln z))"
    by (metis znz DERIV_exp exp_Ln)
  then show "(Ln has_field_derivative inverse(z)) (at z)"
    apply (rule has_complex_derivative_inverse_strong_x
              [where s = "{w. -pi < Im(w) \<and> Im(w) < pi}"])
    using znz *
    apply (auto simp: Transcendental.continuous_on_exp [OF continuous_on_id] open_Collect_conj open_halfspace_Im_gt open_halfspace_Im_lt mpi_less_Im_Ln)
    done
qed

declare has_field_derivative_Ln [derivative_intros]
declare has_field_derivative_Ln [THEN DERIV_chain2, derivative_intros]

lemma field_differentiable_at_Ln: "z \<notin> \<real>\<^sub>\<le>\<^sub>0 \<Longrightarrow> Ln field_differentiable at z"
  using field_differentiable_def has_field_derivative_Ln by blast

lemma field_differentiable_within_Ln: "z \<notin> \<real>\<^sub>\<le>\<^sub>0
         \<Longrightarrow> Ln field_differentiable (at z within s)"
  using field_differentiable_at_Ln field_differentiable_within_subset by blast

lemma continuous_at_Ln: "z \<notin> \<real>\<^sub>\<le>\<^sub>0 \<Longrightarrow> continuous (at z) Ln"
  by (simp add: field_differentiable_imp_continuous_at field_differentiable_within_Ln)

lemma isCont_Ln' [simp]:
   "\<lbrakk>isCont f z; f z \<notin> \<real>\<^sub>\<le>\<^sub>0\<rbrakk> \<Longrightarrow> isCont (\<lambda>x. Ln (f x)) z"
  by (blast intro: isCont_o2 [OF _ continuous_at_Ln])

lemma continuous_within_Ln: "z \<notin> \<real>\<^sub>\<le>\<^sub>0 \<Longrightarrow> continuous (at z within s) Ln"
  using continuous_at_Ln continuous_at_imp_continuous_within by blast

lemma continuous_on_Ln [continuous_intros]: "(\<And>z. z \<in> s \<Longrightarrow> z \<notin> \<real>\<^sub>\<le>\<^sub>0) \<Longrightarrow> continuous_on s Ln"
  by (simp add: continuous_at_imp_continuous_on continuous_within_Ln)

lemma holomorphic_on_Ln: "(\<And>z. z \<in> s \<Longrightarrow> z \<notin> \<real>\<^sub>\<le>\<^sub>0) \<Longrightarrow> Ln holomorphic_on s"
  by (simp add: field_differentiable_within_Ln holomorphic_on_def)


subsection\<open>Quadrant-type results for Ln\<close>

lemma cos_lt_zero_pi: "pi/2 < x \<Longrightarrow> x < 3*pi/2 \<Longrightarrow> cos x < 0"
  using cos_minus_pi cos_gt_zero_pi [of "x-pi"]
  by simp

lemma Re_Ln_pos_lt:
  assumes "z \<noteq> 0"
    shows "\<bar>Im(Ln z)\<bar> < pi/2 \<longleftrightarrow> 0 < Re(z)"
proof -
  { fix w
    assume "w = Ln z"
    then have w: "Im w \<le> pi" "- pi < Im w"
      using Im_Ln_le_pi [of z]  mpi_less_Im_Ln [of z]  assms
      by auto
    then have "\<bar>Im w\<bar> < pi/2 \<longleftrightarrow> 0 < Re(exp w)"
      apply (auto simp: Re_exp zero_less_mult_iff cos_gt_zero_pi)
      using cos_lt_zero_pi [of "-(Im w)"] cos_lt_zero_pi [of "(Im w)"]
      apply (simp add: abs_if split: if_split_asm)
      apply (metis (no_types) cos_minus cos_pi_half eq_divide_eq_numeral1(1) eq_numeral_simps(4)
               less_numeral_extra(3) linorder_neqE_linordered_idom minus_mult_minus minus_mult_right
               mult_numeral_1_right)
      done
  }
  then show ?thesis using assms
    by auto
qed

lemma Re_Ln_pos_le:
  assumes "z \<noteq> 0"
    shows "\<bar>Im(Ln z)\<bar> \<le> pi/2 \<longleftrightarrow> 0 \<le> Re(z)"
proof -
  { fix w
    assume "w = Ln z"
    then have w: "Im w \<le> pi" "- pi < Im w"
      using Im_Ln_le_pi [of z]  mpi_less_Im_Ln [of z]  assms
      by auto
    then have "\<bar>Im w\<bar> \<le> pi/2 \<longleftrightarrow> 0 \<le> Re(exp w)"
      apply (auto simp: Re_exp zero_le_mult_iff cos_ge_zero)
      using cos_lt_zero_pi [of "- (Im w)"] cos_lt_zero_pi [of "(Im w)"] not_le
      apply (auto simp: abs_if split: if_split_asm)
      done
  }
  then show ?thesis using assms
    by auto
qed

lemma Im_Ln_pos_lt:
  assumes "z \<noteq> 0"
    shows "0 < Im(Ln z) \<and> Im(Ln z) < pi \<longleftrightarrow> 0 < Im(z)"
proof -
  { fix w
    assume "w = Ln z"
    then have w: "Im w \<le> pi" "- pi < Im w"
      using Im_Ln_le_pi [of z]  mpi_less_Im_Ln [of z]  assms
      by auto
    then have "0 < Im w \<and> Im w < pi \<longleftrightarrow> 0 < Im(exp w)"
      using sin_gt_zero [of "- (Im w)"] sin_gt_zero [of "(Im w)"]
      apply (auto simp: Im_exp zero_less_mult_iff)
      using less_linear apply fastforce
      using less_linear apply fastforce
      done
  }
  then show ?thesis using assms
    by auto
qed

lemma Im_Ln_pos_le:
  assumes "z \<noteq> 0"
    shows "0 \<le> Im(Ln z) \<and> Im(Ln z) \<le> pi \<longleftrightarrow> 0 \<le> Im(z)"
proof -
  { fix w
    assume "w = Ln z"
    then have w: "Im w \<le> pi" "- pi < Im w"
      using Im_Ln_le_pi [of z]  mpi_less_Im_Ln [of z]  assms
      by auto
    then have "0 \<le> Im w \<and> Im w \<le> pi \<longleftrightarrow> 0 \<le> Im(exp w)"
      using sin_ge_zero [of "- (Im w)"] sin_ge_zero [of "(Im w)"]
      apply (auto simp: Im_exp zero_le_mult_iff sin_ge_zero)
      apply (metis not_le not_less_iff_gr_or_eq pi_not_less_zero sin_eq_0_pi)
      done }
  then show ?thesis using assms
    by auto
qed

lemma Re_Ln_pos_lt_imp: "0 < Re(z) \<Longrightarrow> \<bar>Im(Ln z)\<bar> < pi/2"
  by (metis Re_Ln_pos_lt less_irrefl zero_complex.simps(1))

lemma Im_Ln_pos_lt_imp: "0 < Im(z) \<Longrightarrow> 0 < Im(Ln z) \<and> Im(Ln z) < pi"
  by (metis Im_Ln_pos_lt not_le order_refl zero_complex.simps(2))

text\<open>A reference to the set of positive real numbers\<close>
lemma Im_Ln_eq_0: "z \<noteq> 0 \<Longrightarrow> (Im(Ln z) = 0 \<longleftrightarrow> 0 < Re(z) \<and> Im(z) = 0)"
by (metis Im_complex_of_real Im_exp Ln_in_Reals Re_Ln_pos_lt Re_Ln_pos_lt_imp
          Re_complex_of_real complex_is_Real_iff exp_Ln exp_of_real pi_gt_zero)

lemma Im_Ln_eq_pi: "z \<noteq> 0 \<Longrightarrow> (Im(Ln z) = pi \<longleftrightarrow> Re(z) < 0 \<and> Im(z) = 0)"
by (metis Im_Ln_eq_0 Im_Ln_pos_le Im_Ln_pos_lt add.left_neutral complex_eq less_eq_real_def
    mult_zero_right not_less_iff_gr_or_eq pi_ge_zero pi_neq_zero rcis_zero_arg rcis_zero_mod)


subsection\<open>More Properties of Ln\<close>

lemma cnj_Ln: "z \<notin> \<real>\<^sub>\<le>\<^sub>0 \<Longrightarrow> cnj(Ln z) = Ln(cnj z)"
  apply (cases "z=0", auto)
  apply (rule exp_complex_eqI)
  apply (auto simp: abs_if split: if_split_asm)
  using Im_Ln_less_pi Im_Ln_le_pi apply force
  apply (metis complex_cnj_zero_iff diff_minus_eq_add diff_strict_mono minus_less_iff
          mpi_less_Im_Ln mult.commute mult_2_right)
  by (metis exp_Ln exp_cnj)

lemma Ln_inverse: "z \<notin> \<real>\<^sub>\<le>\<^sub>0 \<Longrightarrow> Ln(inverse z) = -(Ln z)"
  apply (cases "z=0", auto)
  apply (rule exp_complex_eqI)
  using mpi_less_Im_Ln [of z] mpi_less_Im_Ln [of "inverse z"]
  apply (auto simp: abs_if exp_minus split: if_split_asm)
  apply (metis Im_Ln_less_pi Im_Ln_le_pi add.commute add_mono_thms_linordered_field(3) inverse_nonzero_iff_nonzero mult_2)
  done

lemma Ln_minus1 [simp]: "Ln(-1) = \<i> * pi"
  apply (rule exp_complex_eqI)
  using Im_Ln_le_pi [of "-1"] mpi_less_Im_Ln [of "-1"] cis_conv_exp cis_pi
  apply (auto simp: abs_if)
  done

lemma Ln_ii [simp]: "Ln \<i> = \<i> * of_real pi/2"
  using Ln_exp [of "\<i> * (of_real pi/2)"]
  unfolding exp_Euler
  by simp

lemma Ln_minus_ii [simp]: "Ln(-\<i>) = - (\<i> * pi/2)"
proof -
  have  "Ln(-\<i>) = Ln(inverse \<i>)"    by simp
  also have "... = - (Ln \<i>)"         using Ln_inverse by blast
  also have "... = - (\<i> * pi/2)"     by simp
  finally show ?thesis .
qed

lemma Ln_times:
  assumes "w \<noteq> 0" "z \<noteq> 0"
    shows "Ln(w * z) =
                (if Im(Ln w + Ln z) \<le> -pi then
                  (Ln(w) + Ln(z)) + \<i> * of_real(2*pi)
                else if Im(Ln w + Ln z) > pi then
                  (Ln(w) + Ln(z)) - \<i> * of_real(2*pi)
                else Ln(w) + Ln(z))"
  using pi_ge_zero Im_Ln_le_pi [of w] Im_Ln_le_pi [of z]
  using assms mpi_less_Im_Ln [of w] mpi_less_Im_Ln [of z]
  by (auto simp: exp_add exp_diff sin_double cos_double exp_Euler intro!: Ln_unique)

corollary Ln_times_simple:
    "\<lbrakk>w \<noteq> 0; z \<noteq> 0; -pi < Im(Ln w) + Im(Ln z); Im(Ln w) + Im(Ln z) \<le> pi\<rbrakk>
         \<Longrightarrow> Ln(w * z) = Ln(w) + Ln(z)"
  by (simp add: Ln_times)

corollary Ln_times_of_real:
    "\<lbrakk>r > 0; z \<noteq> 0\<rbrakk> \<Longrightarrow> Ln(of_real r * z) = ln r + Ln(z)"
  using mpi_less_Im_Ln Im_Ln_le_pi
  by (force simp: Ln_times)

corollary Ln_divide_of_real:
    "\<lbrakk>r > 0; z \<noteq> 0\<rbrakk> \<Longrightarrow> Ln(z / of_real r) = Ln(z) - ln r"
using Ln_times_of_real [of "inverse r" z]
by (simp add: ln_inverse Ln_of_real mult.commute divide_inverse of_real_inverse [symmetric]
         del: of_real_inverse)

lemma Ln_minus:
  assumes "z \<noteq> 0"
    shows "Ln(-z) = (if Im(z) \<le> 0 \<and> ~(Re(z) < 0 \<and> Im(z) = 0)
                     then Ln(z) + \<i> * pi
                     else Ln(z) - \<i> * pi)" (is "_ = ?rhs")
  using Im_Ln_le_pi [of z] mpi_less_Im_Ln [of z] assms
        Im_Ln_eq_pi [of z] Im_Ln_pos_lt [of z]
    by (fastforce simp: exp_add exp_diff exp_Euler intro!: Ln_unique)

lemma Ln_inverse_if:
  assumes "z \<noteq> 0"
    shows "Ln (inverse z) = (if z \<in> \<real>\<^sub>\<le>\<^sub>0 then -(Ln z) + \<i> * 2 * complex_of_real pi else -(Ln z))"
proof (cases "z \<in> \<real>\<^sub>\<le>\<^sub>0")
  case False then show ?thesis
    by (simp add: Ln_inverse)
next
  case True
  then have z: "Im z = 0" "Re z < 0"
    using assms
    apply (auto simp: complex_nonpos_Reals_iff)
    by (metis complex_is_Real_iff le_imp_less_or_eq of_real_0 of_real_Re)
  have "Ln(inverse z) = Ln(- (inverse (-z)))"
    by simp
  also have "... = Ln (inverse (-z)) + \<i> * complex_of_real pi"
    using assms z
    apply (simp add: Ln_minus)
    apply (simp add: field_simps)
    done
  also have "... = - Ln (- z) + \<i> * complex_of_real pi"
    apply (subst Ln_inverse)
    using z by (auto simp add: complex_nonneg_Reals_iff)
  also have "... = - (Ln z) + \<i> * 2 * complex_of_real pi"
    apply (subst Ln_minus [OF assms])
    using assms z
    apply simp
    done
  finally show ?thesis by (simp add: True)
qed

lemma Ln_times_ii:
  assumes "z \<noteq> 0"
    shows  "Ln(\<i> * z) = (if 0 \<le> Re(z) | Im(z) < 0
                          then Ln(z) + \<i> * of_real pi/2
                          else Ln(z) - \<i> * of_real(3 * pi/2))"
  using Im_Ln_le_pi [of z] mpi_less_Im_Ln [of z] assms
        Im_Ln_eq_pi [of z] Im_Ln_pos_lt [of z] Re_Ln_pos_le [of z]
  by (auto simp: Ln_times)

lemma Ln_of_nat: "0 < n \<Longrightarrow> Ln (of_nat n) = of_real (ln (of_nat n))"
  by (subst of_real_of_nat_eq[symmetric], subst Ln_of_real[symmetric]) simp_all

lemma Ln_of_nat_over_of_nat:
  assumes "m > 0" "n > 0"
  shows   "Ln (of_nat m / of_nat n) = of_real (ln (of_nat m) - ln (of_nat n))"
proof -
  have "of_nat m / of_nat n = (of_real (of_nat m / of_nat n) :: complex)" by simp
  also from assms have "Ln ... = of_real (ln (of_nat m / of_nat n))"
    by (simp add: Ln_of_real[symmetric])
  also from assms have "... = of_real (ln (of_nat m) - ln (of_nat n))"
    by (simp add: ln_div)
  finally show ?thesis .
qed


subsection\<open>Relation between Ln and Arg, and hence continuity of Arg\<close>

lemma Arg_Ln:
  assumes "0 < Arg z" shows "Arg z = Im(Ln(-z)) + pi"
proof (cases "z = 0")
  case True
  with assms show ?thesis
    by simp
next
  case False
  then have "z / of_real(norm z) = exp(\<i> * of_real(Arg z))"
    using Arg [of z]
    by (metis abs_norm_cancel nonzero_mult_div_cancel_left norm_of_real zero_less_norm_iff)
  then have "- z / of_real(norm z) = exp (\<i> * (of_real (Arg z) - pi))"
    using cis_conv_exp cis_pi
    by (auto simp: exp_diff algebra_simps)
  then have "ln (- z / of_real(norm z)) = ln (exp (\<i> * (of_real (Arg z) - pi)))"
    by simp
  also have "... = \<i> * (of_real(Arg z) - pi)"
    using Arg [of z] assms pi_not_less_zero
    by auto
  finally have "Arg z =  Im (Ln (- z / of_real (cmod z))) + pi"
    by simp
  also have "... = Im (Ln (-z) - ln (cmod z)) + pi"
    by (metis diff_0_right minus_diff_eq zero_less_norm_iff Ln_divide_of_real False)
  also have "... = Im (Ln (-z)) + pi"
    by simp
  finally show ?thesis .
qed

lemma continuous_at_Arg:
  assumes "z \<notin> \<real>\<^sub>\<ge>\<^sub>0"
    shows "continuous (at z) Arg"
proof -
  have *: "isCont (\<lambda>z. Im (Ln (- z)) + pi) z"
    by (rule Complex.isCont_Im isCont_Ln' continuous_intros | simp add: assms complex_is_Real_iff)+
  have [simp]: "\<And>x. \<lbrakk>Im x \<noteq> 0\<rbrakk> \<Longrightarrow> Im (Ln (- x)) + pi = Arg x"
      using Arg_Ln Arg_gt_0 complex_is_Real_iff by auto
  consider "Re z < 0" | "Im z \<noteq> 0" using assms
    using complex_nonneg_Reals_iff not_le by blast
  then have [simp]: "(\<lambda>z. Im (Ln (- z)) + pi) \<midarrow>z\<rightarrow> Arg z"
      using "*"  by (simp add: isCont_def) (metis Arg_Ln Arg_gt_0 complex_is_Real_iff)
  show ?thesis
      apply (simp add: continuous_at)
      apply (rule Lim_transform_within_open [where s= "-\<real>\<^sub>\<ge>\<^sub>0" and f = "\<lambda>z. Im(Ln(-z)) + pi"])
      apply (auto simp add: not_le Arg_Ln [OF Arg_gt_0] complex_nonneg_Reals_iff closed_def [symmetric])
      using assms apply (force simp add: complex_nonneg_Reals_iff)
      done
qed

lemma Ln_series:
  fixes z :: complex
  assumes "norm z < 1"
  shows   "(\<lambda>n. (-1)^Suc n / of_nat n * z^n) sums ln (1 + z)" (is "(\<lambda>n. ?f n * z^n) sums _")
proof -
  let ?F = "\<lambda>z. \<Sum>n. ?f n * z^n" and ?F' = "\<lambda>z. \<Sum>n. diffs ?f n * z^n"
  have r: "conv_radius ?f = 1"
    by (intro conv_radius_ratio_limit_nonzero[of _ 1])
       (simp_all add: norm_divide LIMSEQ_Suc_n_over_n del: of_nat_Suc)

  have "\<exists>c. \<forall>z\<in>ball 0 1. ln (1 + z) - ?F z = c"
  proof (rule has_field_derivative_zero_constant)
    fix z :: complex assume z': "z \<in> ball 0 1"
    hence z: "norm z < 1" by (simp add: dist_0_norm)
    define t :: complex where "t = of_real (1 + norm z) / 2"
    from z have t: "norm z < norm t" "norm t < 1" unfolding t_def
      by (simp_all add: field_simps norm_divide del: of_real_add)

    have "Re (-z) \<le> norm (-z)" by (rule complex_Re_le_cmod)
    also from z have "... < 1" by simp
    finally have "((\<lambda>z. ln (1 + z)) has_field_derivative inverse (1+z)) (at z)"
      by (auto intro!: derivative_eq_intros simp: complex_nonpos_Reals_iff)
    moreover have "(?F has_field_derivative ?F' z) (at z)" using t r
      by (intro termdiffs_strong[of _ t] summable_in_conv_radius) simp_all
    ultimately have "((\<lambda>z. ln (1 + z) - ?F z) has_field_derivative (inverse (1 + z) - ?F' z))
                       (at z within ball 0 1)"
      by (intro derivative_intros) (simp_all add: at_within_open[OF z'])
    also have "(\<lambda>n. of_nat n * ?f n * z ^ (n - Suc 0)) sums ?F' z" using t r
      by (intro diffs_equiv termdiff_converges[OF t(1)] summable_in_conv_radius) simp_all
    from sums_split_initial_segment[OF this, of 1]
      have "(\<lambda>i. (-z) ^ i) sums ?F' z" by (simp add: power_minus[of z] del: of_nat_Suc)
    hence "?F' z = inverse (1 + z)" using z by (simp add: sums_iff suminf_geometric divide_inverse)
    also have "inverse (1 + z) - inverse (1 + z) = 0" by simp
    finally show "((\<lambda>z. ln (1 + z) - ?F z) has_field_derivative 0) (at z within ball 0 1)" .
  qed simp_all
  then obtain c where c: "\<And>z. z \<in> ball 0 1 \<Longrightarrow> ln (1 + z) - ?F z = c" by blast
  from c[of 0] have "c = 0" by (simp only: powser_zero) simp
  with c[of z] assms have "ln (1 + z) = ?F z" by (simp add: dist_0_norm)
  moreover have "summable (\<lambda>n. ?f n * z^n)" using assms r
    by (intro summable_in_conv_radius) simp_all
  ultimately show ?thesis by (simp add: sums_iff)
qed

lemma Ln_series': "cmod z < 1 \<Longrightarrow> (\<lambda>n. - ((-z)^n) / of_nat n) sums ln (1 + z)"
  by (drule Ln_series) (simp add: power_minus')

lemma ln_series': 
  assumes "abs (x::real) < 1"
  shows   "(\<lambda>n. - ((-x)^n) / of_nat n) sums ln (1 + x)"
proof -
  from assms have "(\<lambda>n. - ((-of_real x)^n) / of_nat n) sums ln (1 + complex_of_real x)"
    by (intro Ln_series') simp_all
  also have "(\<lambda>n. - ((-of_real x)^n) / of_nat n) = (\<lambda>n. complex_of_real (- ((-x)^n) / of_nat n))"
    by (rule ext) simp
  also from assms have "ln (1 + complex_of_real x) = of_real (ln (1 + x))" 
    by (subst Ln_of_real [symmetric]) simp_all
  finally show ?thesis by (subst (asm) sums_of_real_iff)
qed

lemma Ln_approx_linear:
  fixes z :: complex
  assumes "norm z < 1"
  shows   "norm (ln (1 + z) - z) \<le> norm z^2 / (1 - norm z)"
proof -
  let ?f = "\<lambda>n. (-1)^Suc n / of_nat n"
  from assms have "(\<lambda>n. ?f n * z^n) sums ln (1 + z)" using Ln_series by simp
  moreover have "(\<lambda>n. (if n = 1 then 1 else 0) * z^n) sums z" using powser_sums_if[of 1] by simp
  ultimately have "(\<lambda>n. (?f n - (if n = 1 then 1 else 0)) * z^n) sums (ln (1 + z) - z)"
    by (subst left_diff_distrib, intro sums_diff) simp_all
  from sums_split_initial_segment[OF this, of "Suc 1"]
    have "(\<lambda>i. (-(z^2)) * inverse (2 + of_nat i) * (- z)^i) sums (Ln (1 + z) - z)"
    by (simp add: power2_eq_square mult_ac power_minus[of z] divide_inverse)
  hence "(Ln (1 + z) - z) = (\<Sum>i. (-(z^2)) * inverse (of_nat (i+2)) * (-z)^i)"
    by (simp add: sums_iff)
  also have A: "summable (\<lambda>n. norm z^2 * (inverse (real_of_nat (Suc (Suc n))) * cmod z ^ n))"
    by (rule summable_mult, rule summable_comparison_test_ev[OF _ summable_geometric[of "norm z"]])
       (auto simp: assms field_simps intro!: always_eventually)
  hence "norm (\<Sum>i. (-(z^2)) * inverse (of_nat (i+2)) * (-z)^i) \<le>
             (\<Sum>i. norm (-(z^2) * inverse (of_nat (i+2)) * (-z)^i))"
    by (intro summable_norm)
       (auto simp: norm_power norm_inverse norm_mult mult_ac simp del: of_nat_add of_nat_Suc)
  also have "norm ((-z)^2 * (-z)^i) * inverse (of_nat (i+2)) \<le> norm ((-z)^2 * (-z)^i) * 1" for i
    by (intro mult_left_mono) (simp_all add: divide_simps)
  hence "(\<Sum>i. norm (-(z^2) * inverse (of_nat (i+2)) * (-z)^i)) \<le>
           (\<Sum>i. norm (-(z^2) * (-z)^i))" using A assms
    apply (simp_all only: norm_power norm_inverse norm_divide norm_mult)
    apply (intro suminf_le summable_mult summable_geometric)
    apply (auto simp: norm_power field_simps simp del: of_nat_add of_nat_Suc)
    done
  also have "... = norm z^2 * (\<Sum>i. norm z^i)" using assms
    by (subst suminf_mult [symmetric]) (auto intro!: summable_geometric simp: norm_mult norm_power)
  also have "(\<Sum>i. norm z^i) = inverse (1 - norm z)" using assms
    by (subst suminf_geometric) (simp_all add: divide_inverse)
  also have "norm z^2 * ... = norm z^2 / (1 - norm z)" by (simp add: divide_inverse)
  finally show ?thesis .
qed


text\<open>Relation between Arg and arctangent in upper halfplane\<close>
lemma Arg_arctan_upperhalf:
  assumes "0 < Im z"
    shows "Arg z = pi/2 - arctan(Re z / Im z)"
proof (cases "z = 0")
  case True with assms show ?thesis
    by simp
next
  case False
  show ?thesis
    apply (rule Arg_unique [of "norm z"])
    using False assms arctan [of "Re z / Im z"] pi_ge_two pi_half_less_two
    apply (auto simp: exp_Euler cos_diff sin_diff)
    using norm_complex_def [of z, symmetric]
    apply (simp add: sin_of_real cos_of_real sin_arctan cos_arctan field_simps real_sqrt_divide)
    apply (metis complex_eq mult.assoc ring_class.ring_distribs(2))
    done
qed

lemma Arg_eq_Im_Ln:
  assumes "0 \<le> Im z" "0 < Re z"
    shows "Arg z = Im (Ln z)"
proof (cases "z = 0 \<or> Im z = 0")
  case True then show ?thesis
    using assms Arg_eq_0 complex_is_Real_iff
    apply auto
    by (metis Arg_eq_0_pi Arg_eq_pi Im_Ln_eq_0 Im_Ln_eq_pi less_numeral_extra(3) zero_complex.simps(1))
next
  case False
  then have "Arg z > 0"
    using Arg_gt_0 complex_is_Real_iff by blast
  then show ?thesis
    using assms False
    by (subst Arg_Ln) (auto simp: Ln_minus)
qed

lemma continuous_within_upperhalf_Arg:
  assumes "z \<noteq> 0"
    shows "continuous (at z within {z. 0 \<le> Im z}) Arg"
proof (cases "z \<in> \<real>\<^sub>\<ge>\<^sub>0")
  case False then show ?thesis
    using continuous_at_Arg continuous_at_imp_continuous_within by auto
next
  case True
  then have z: "z \<in> \<real>" "0 < Re z"
    using assms  by (auto simp: complex_nonneg_Reals_iff complex_is_Real_iff complex_neq_0)
  then have [simp]: "Arg z = 0" "Im (Ln z) = 0"
    by (auto simp: Arg_eq_0 Im_Ln_eq_0 assms complex_is_Real_iff)
  show ?thesis
  proof (clarsimp simp add: continuous_within Lim_within dist_norm)
    fix e::real
    assume "0 < e"
    moreover have "continuous (at z) (\<lambda>x. Im (Ln x))"
      using z by (simp add: continuous_at_Ln complex_nonpos_Reals_iff)
    ultimately
    obtain d where d: "d>0" "\<And>x. x \<noteq> z \<Longrightarrow> cmod (x - z) < d \<Longrightarrow> \<bar>Im (Ln x)\<bar> < e"
      by (auto simp: continuous_within Lim_within dist_norm)
    { fix x
      assume "cmod (x - z) < Re z / 2"
      then have "\<bar>Re x - Re z\<bar> < Re z / 2"
        by (metis le_less_trans abs_Re_le_cmod minus_complex.simps(1))
      then have "0 < Re x"
        using z by linarith
    }
    then show "\<exists>d>0. \<forall>x. 0 \<le> Im x \<longrightarrow> x \<noteq> z \<and> cmod (x - z) < d \<longrightarrow> \<bar>Arg x\<bar> < e"
      apply (rule_tac x="min d (Re z / 2)" in exI)
      using z d
      apply (auto simp: Arg_eq_Im_Ln)
      done
  qed
qed

lemma continuous_on_upperhalf_Arg: "continuous_on ({z. 0 \<le> Im z} - {0}) Arg"
  apply (auto simp: continuous_on_eq_continuous_within)
  by (metis Diff_subset continuous_within_subset continuous_within_upperhalf_Arg)

lemma open_Arg_less_Int:
  assumes "0 \<le> s" "t \<le> 2*pi"
    shows "open ({y. s < Arg y} \<inter> {y. Arg y < t})"
proof -
  have 1: "continuous_on (UNIV - \<real>\<^sub>\<ge>\<^sub>0) Arg"
    using continuous_at_Arg continuous_at_imp_continuous_within
    by (auto simp: continuous_on_eq_continuous_within)
  have 2: "open (UNIV - \<real>\<^sub>\<ge>\<^sub>0 :: complex set)"  by (simp add: open_Diff)
  have "open ({z. s < z} \<inter> {z. z < t})"
    using open_lessThan [of t] open_greaterThan [of s]
    by (metis greaterThan_def lessThan_def open_Int)
  moreover have "{y. s < Arg y} \<inter> {y. Arg y < t} \<subseteq> - \<real>\<^sub>\<ge>\<^sub>0"
    using assms by (auto simp: Arg_real complex_nonneg_Reals_iff complex_is_Real_iff)
  ultimately show ?thesis
    using continuous_imp_open_vimage [OF 1 2, of  "{z. Re z > s} \<inter> {z. Re z < t}"]
    by auto
qed

lemma open_Arg_gt: "open {z. t < Arg z}"
proof (cases "t < 0")
  case True then have "{z. t < Arg z} = UNIV"
    using Arg_ge_0 less_le_trans by auto
  then show ?thesis
    by simp
next
  case False then show ?thesis
    using open_Arg_less_Int [of t "2*pi"] Arg_lt_2pi
    by auto
qed

lemma closed_Arg_le: "closed {z. Arg z \<le> t}"
  using open_Arg_gt [of t]
  by (simp add: closed_def Set.Collect_neg_eq [symmetric] not_le)

subsection\<open>Complex Powers\<close>

lemma powr_to_1 [simp]: "z powr 1 = (z::complex)"
  by (simp add: powr_def)

lemma powr_nat:
  fixes n::nat and z::complex shows "z powr n = (if z = 0 then 0 else z^n)"
  by (simp add: exp_of_nat_mult powr_def)

lemma powr_add_complex:
  fixes w::complex shows "w powr (z1 + z2) = w powr z1 * w powr z2"
  by (simp add: powr_def algebra_simps exp_add)

lemma powr_minus_complex:
  fixes w::complex shows  "w powr (-z) = inverse(w powr z)"
  by (simp add: powr_def exp_minus)

lemma powr_diff_complex:
  fixes w::complex shows  "w powr (z1 - z2) = w powr z1 / w powr z2"
  by (simp add: powr_def algebra_simps exp_diff)

lemma norm_powr_real: "w \<in> \<real> \<Longrightarrow> 0 < Re w \<Longrightarrow> norm(w powr z) = exp(Re z * ln(Re w))"
  apply (simp add: powr_def)
  using Im_Ln_eq_0 complex_is_Real_iff norm_complex_def
  by auto

lemma cnj_powr:
  assumes "Im a = 0 \<Longrightarrow> Re a \<ge> 0"
  shows   "cnj (a powr b) = cnj a powr cnj b"
proof (cases "a = 0")
  case False
  with assms have "a \<notin> \<real>\<^sub>\<le>\<^sub>0" by (auto simp: complex_eq_iff complex_nonpos_Reals_iff)
  with False show ?thesis by (simp add: powr_def exp_cnj cnj_Ln)
qed simp

lemma powr_real_real:
    "\<lbrakk>w \<in> \<real>; z \<in> \<real>; 0 < Re w\<rbrakk> \<Longrightarrow> w powr z = exp(Re z * ln(Re w))"
  apply (simp add: powr_def)
  by (metis complex_eq complex_is_Real_iff diff_0 diff_0_right diff_minus_eq_add exp_ln exp_not_eq_zero
       exp_of_real Ln_of_real mult_zero_right of_real_0 of_real_mult)

lemma powr_of_real:
  fixes x::real and y::real
  shows "0 \<le> x \<Longrightarrow> of_real x powr (of_real y::complex) = of_real (x powr y)"
  by (simp_all add: powr_def exp_eq_polar)

lemma norm_powr_real_mono:
    "\<lbrakk>w \<in> \<real>; 1 < Re w\<rbrakk>
     \<Longrightarrow> cmod(w powr z1) \<le> cmod(w powr z2) \<longleftrightarrow> Re z1 \<le> Re z2"
  by (auto simp: powr_def algebra_simps Reals_def Ln_of_real)

lemma powr_times_real:
    "\<lbrakk>x \<in> \<real>; y \<in> \<real>; 0 \<le> Re x; 0 \<le> Re y\<rbrakk>
           \<Longrightarrow> (x * y) powr z = x powr z * y powr z"
  by (auto simp: Reals_def powr_def Ln_times exp_add algebra_simps less_eq_real_def Ln_of_real)

lemma powr_neg_real_complex:
  shows   "(- of_real x) powr a = (-1) powr (of_real (sgn x) * a) * of_real x powr (a :: complex)"
proof (cases "x = 0")
  assume x: "x \<noteq> 0"
  hence "(-x) powr a = exp (a * ln (-of_real x))" by (simp add: powr_def)
  also from x have "ln (-of_real x) = Ln (of_real x) + of_real (sgn x) * pi * \<i>"
    by (simp add: Ln_minus Ln_of_real)
  also from x have "exp (a * ...) = cis pi powr (of_real (sgn x) * a) * of_real x powr a"
    by (simp add: powr_def exp_add algebra_simps Ln_of_real cis_conv_exp)
  also note cis_pi
  finally show ?thesis by simp
qed simp_all

lemma has_field_derivative_powr:
  fixes z :: complex
  shows "z \<notin> \<real>\<^sub>\<le>\<^sub>0 \<Longrightarrow> ((\<lambda>z. z powr s) has_field_derivative (s * z powr (s - 1))) (at z)"
  apply (cases "z=0", auto)
  apply (simp add: powr_def)
  apply (rule DERIV_transform_at [where d = "norm z" and f = "\<lambda>z. exp (s * Ln z)"])
  apply (auto simp: dist_complex_def)
  apply (intro derivative_eq_intros | simp)+
  apply (simp add: field_simps exp_diff)
  done

declare has_field_derivative_powr[THEN DERIV_chain2, derivative_intros]


lemma has_field_derivative_powr_right:
    "w \<noteq> 0 \<Longrightarrow> ((\<lambda>z. w powr z) has_field_derivative Ln w * w powr z) (at z)"
  apply (simp add: powr_def)
  apply (intro derivative_eq_intros | simp)+
  done

lemma field_differentiable_powr_right:
  fixes w::complex
  shows
    "w \<noteq> 0 \<Longrightarrow> (\<lambda>z. w powr z) field_differentiable (at z)"
using field_differentiable_def has_field_derivative_powr_right by blast

lemma holomorphic_on_powr_right:
    "f holomorphic_on s \<Longrightarrow> w \<noteq> 0 \<Longrightarrow> (\<lambda>z. w powr (f z)) holomorphic_on s"
    unfolding holomorphic_on_def field_differentiable_def
by (metis (full_types) DERIV_chain' has_field_derivative_powr_right)

lemma norm_powr_real_powr:
  "w \<in> \<real> \<Longrightarrow> 0 \<le> Re w \<Longrightarrow> cmod (w powr z) = Re w powr Re z"
  by (cases "w = 0") (auto simp add: norm_powr_real powr_def Im_Ln_eq_0
                                     complex_is_Real_iff in_Reals_norm complex_eq_iff)

lemma tendsto_ln_complex [tendsto_intros]:
  assumes "(f \<longlongrightarrow> a) F" "a \<notin> \<real>\<^sub>\<le>\<^sub>0"
  shows   "((\<lambda>z. ln (f z :: complex)) \<longlongrightarrow> ln a) F"
  using tendsto_compose[OF continuous_at_Ln[of a, unfolded isCont_def] assms(1)] assms(2) by simp

lemma tendsto_powr_complex:
  fixes f g :: "_ \<Rightarrow> complex"
  assumes a: "a \<notin> \<real>\<^sub>\<le>\<^sub>0"
  assumes f: "(f \<longlongrightarrow> a) F" and g: "(g \<longlongrightarrow> b) F"
  shows   "((\<lambda>z. f z powr g z) \<longlongrightarrow> a powr b) F"
proof -
  from a have [simp]: "a \<noteq> 0" by auto
  from f g a have "((\<lambda>z. exp (g z * ln (f z))) \<longlongrightarrow> a powr b) F" (is ?P)
    by (auto intro!: tendsto_intros simp: powr_def)
  also {
    have "eventually (\<lambda>z. z \<noteq> 0) (nhds a)"
      by (intro t1_space_nhds) simp_all
    with f have "eventually (\<lambda>z. f z \<noteq> 0) F" using filterlim_iff by blast
  }
  hence "?P \<longleftrightarrow> ((\<lambda>z. f z powr g z) \<longlongrightarrow> a powr b) F"
    by (intro tendsto_cong refl) (simp_all add: powr_def mult_ac)
  finally show ?thesis .
qed

lemma tendsto_powr_complex_0:
  fixes f g :: "'a \<Rightarrow> complex"
  assumes f: "(f \<longlongrightarrow> 0) F" and g: "(g \<longlongrightarrow> b) F" and b: "Re b > 0"
  shows   "((\<lambda>z. f z powr g z) \<longlongrightarrow> 0) F"
proof (rule tendsto_norm_zero_cancel)
  define h where
    "h = (\<lambda>z. if f z = 0 then 0 else exp (Re (g z) * ln (cmod (f z)) + abs (Im (g z)) * pi))"
  {
    fix z :: 'a assume z: "f z \<noteq> 0"
    define c where "c = abs (Im (g z)) * pi"
    from mpi_less_Im_Ln[OF z] Im_Ln_le_pi[OF z]
      have "abs (Im (Ln (f z))) \<le> pi" by simp
    from mult_left_mono[OF this, of "abs (Im (g z))"]
      have "abs (Im (g z) * Im (ln (f z))) \<le> c" by (simp add: abs_mult c_def)
    hence "-Im (g z) * Im (ln (f z)) \<le> c" by simp
    hence "norm (f z powr g z) \<le> h z" by (simp add: powr_def field_simps h_def c_def)
  }
  hence le: "norm (f z powr g z) \<le> h z" for z by (cases "f x = 0") (simp_all add: h_def)

  have g': "(g \<longlongrightarrow> b) (inf F (principal {z. f z \<noteq> 0}))"
    by (rule tendsto_mono[OF _ g]) simp_all
  have "((\<lambda>x. norm (f x)) \<longlongrightarrow> 0) (inf F (principal {z. f z \<noteq> 0}))"
    by (subst tendsto_norm_zero_iff, rule tendsto_mono[OF _ f]) simp_all
  moreover {
    have "filterlim (\<lambda>x. norm (f x)) (principal {0<..}) (principal {z. f z \<noteq> 0})"
      by (auto simp: filterlim_def)
    hence "filterlim (\<lambda>x. norm (f x)) (principal {0<..})
             (inf F (principal {z. f z \<noteq> 0}))"
      by (rule filterlim_mono) simp_all
  }
  ultimately have norm: "filterlim (\<lambda>x. norm (f x)) (at_right 0) (inf F (principal {z. f z \<noteq> 0}))"
    by (simp add: filterlim_inf at_within_def)

  have A: "LIM x inf F (principal {z. f z \<noteq> 0}). Re (g x) * -ln (cmod (f x)) :> at_top"
    by (rule filterlim_tendsto_pos_mult_at_top tendsto_intros g' b
          filterlim_compose[OF filterlim_uminus_at_top_at_bot] filterlim_compose[OF ln_at_0] norm)+
  have B: "LIM x inf F (principal {z. f z \<noteq> 0}).
          -\<bar>Im (g x)\<bar> * pi + -(Re (g x) * ln (cmod (f x))) :> at_top"
    by (rule filterlim_tendsto_add_at_top tendsto_intros g')+ (insert A, simp_all)
  have C: "(h \<longlongrightarrow> 0) F" unfolding h_def
    by (intro filterlim_If tendsto_const filterlim_compose[OF exp_at_bot])
       (insert B, auto simp: filterlim_uminus_at_bot algebra_simps)
  show "((\<lambda>x. norm (f x powr g x)) \<longlongrightarrow> 0) F"
    by (rule Lim_null_comparison[OF always_eventually C]) (insert le, auto)
qed

lemma tendsto_powr_complex' [tendsto_intros]:
  fixes f g :: "_ \<Rightarrow> complex"
  assumes fz: "a \<notin> \<real>\<^sub>\<le>\<^sub>0 \<or> (a = 0 \<and> Re b > 0)"
  assumes fg: "(f \<longlongrightarrow> a) F" "(g \<longlongrightarrow> b) F"
  shows   "((\<lambda>z. f z powr g z) \<longlongrightarrow> a powr b) F"
proof (cases "a = 0")
  case True
  with assms show ?thesis by (auto intro!: tendsto_powr_complex_0)
next
  case False
  with assms show ?thesis by (auto intro!: tendsto_powr_complex elim!: nonpos_Reals_cases)
qed

lemma continuous_powr_complex:
  assumes "f (netlimit F) \<notin> \<real>\<^sub>\<le>\<^sub>0" "continuous F f" "continuous F g"
  shows   "continuous F (\<lambda>z. f z powr g z :: complex)"
  using assms unfolding continuous_def by (intro tendsto_powr_complex) simp_all

lemma isCont_powr_complex [continuous_intros]:
  assumes "f z \<notin> \<real>\<^sub>\<le>\<^sub>0" "isCont f z" "isCont g z"
  shows   "isCont (\<lambda>z. f z powr g z :: complex) z"
  using assms unfolding isCont_def by (intro tendsto_powr_complex) simp_all

lemma continuous_on_powr_complex [continuous_intros]:
  assumes "A \<subseteq> {z. Re (f z) \<ge> 0 \<or> Im (f z) \<noteq> 0}"
  assumes "\<And>z. z \<in> A \<Longrightarrow> f z = 0 \<Longrightarrow> Re (g z) > 0"
  assumes "continuous_on A f" "continuous_on A g"
  shows   "continuous_on A (\<lambda>z. f z powr g z)"
  unfolding continuous_on_def
proof
  fix z assume z: "z \<in> A"
  show "((\<lambda>z. f z powr g z) \<longlongrightarrow> f z powr g z) (at z within A)"
  proof (cases "f z = 0")
    case False
    from assms(1,2) z have "Re (f z) \<ge> 0 \<or> Im (f z) \<noteq> 0" "f z = 0 \<longrightarrow> Re (g z) > 0" by auto
    with assms(3,4) z show ?thesis
      by (intro tendsto_powr_complex')
         (auto elim!: nonpos_Reals_cases simp: complex_eq_iff continuous_on_def)
  next
    case True
    with assms z show ?thesis
      by (auto intro!: tendsto_powr_complex_0 simp: continuous_on_def)
  qed
qed


subsection\<open>Some Limits involving Logarithms\<close>

lemma lim_Ln_over_power:
  fixes s::complex
  assumes "0 < Re s"
    shows "((\<lambda>n. Ln n / (n powr s)) \<longlongrightarrow> 0) sequentially"
proof (simp add: lim_sequentially dist_norm, clarify)
  fix e::real
  assume e: "0 < e"
  have "\<exists>xo>0. \<forall>x\<ge>xo. 0 < e * 2 + (e * Re s * 2 - 2) * x + e * (Re s)\<^sup>2 * x\<^sup>2"
  proof (rule_tac x="2/(e * (Re s)\<^sup>2)" in exI, safe)
    show "0 < 2 / (e * (Re s)\<^sup>2)"
      using e assms by (simp add: field_simps)
  next
    fix x::real
    assume x: "2 / (e * (Re s)\<^sup>2) \<le> x"
    then have "x>0"
    using e assms
      by (metis less_le_trans mult_eq_0_iff mult_pos_pos pos_less_divide_eq power2_eq_square
                zero_less_numeral)
    then show "0 < e * 2 + (e * Re s * 2 - 2) * x + e * (Re s)\<^sup>2 * x\<^sup>2"
      using e assms x
      apply (auto simp: field_simps)
      apply (rule_tac y = "e * (x\<^sup>2 * (Re s)\<^sup>2)" in le_less_trans)
      apply (auto simp: power2_eq_square field_simps add_pos_pos)
      done
  qed
  then have "\<exists>xo>0. \<forall>x\<ge>xo. x / e < 1 + (Re s * x) + (1/2) * (Re s * x)^2"
    using e  by (simp add: field_simps)
  then have "\<exists>xo>0. \<forall>x\<ge>xo. x / e < exp (Re s * x)"
    using assms
    by (force intro: less_le_trans [OF _ exp_lower_taylor_quadratic])
  then have "\<exists>xo>0. \<forall>x\<ge>xo. x < e * exp (Re s * x)"
    using e   by (auto simp: field_simps)
  with e show "\<exists>no. \<forall>n\<ge>no. norm (Ln (of_nat n) / of_nat n powr s) < e"
    apply (auto simp: norm_divide norm_powr_real divide_simps)
    apply (rule_tac x="nat \<lceil>exp xo\<rceil>" in exI)
    apply clarify
    apply (drule_tac x="ln n" in spec)
    apply (auto simp: exp_less_mono nat_ceiling_le_eq not_le)
    apply (metis exp_less_mono exp_ln not_le of_nat_0_less_iff)
    done
qed

lemma lim_Ln_over_n: "((\<lambda>n. Ln(of_nat n) / of_nat n) \<longlongrightarrow> 0) sequentially"
  using lim_Ln_over_power [of 1]
  by simp

lemma Ln_Reals_eq: "x \<in> \<real> \<Longrightarrow> Re x > 0 \<Longrightarrow> Ln x = of_real (ln (Re x))"
  using Ln_of_real by force

lemma powr_Reals_eq: "x \<in> \<real> \<Longrightarrow> Re x > 0 \<Longrightarrow> x powr complex_of_real y = of_real (x powr y)"
  by (simp add: powr_of_real)

lemma lim_ln_over_power:
  fixes s :: real
  assumes "0 < s"
    shows "((\<lambda>n. ln n / (n powr s)) \<longlongrightarrow> 0) sequentially"
  using lim_Ln_over_power [of "of_real s", THEN filterlim_sequentially_Suc [THEN iffD2]] assms
  apply (subst filterlim_sequentially_Suc [symmetric])
  apply (simp add: lim_sequentially dist_norm
          Ln_Reals_eq norm_powr_real_powr norm_divide)
  done

lemma lim_ln_over_n: "((\<lambda>n. ln(real_of_nat n) / of_nat n) \<longlongrightarrow> 0) sequentially"
  using lim_ln_over_power [of 1, THEN filterlim_sequentially_Suc [THEN iffD2]]
  apply (subst filterlim_sequentially_Suc [symmetric])
  apply (simp add: lim_sequentially dist_norm)
  done

lemma lim_1_over_complex_power:
  assumes "0 < Re s"
    shows "((\<lambda>n. 1 / (of_nat n powr s)) \<longlongrightarrow> 0) sequentially"
proof -
  have "\<forall>n>0. 3 \<le> n \<longrightarrow> 1 \<le> ln (real_of_nat n)"
    using ln3_gt_1
    by (force intro: order_trans [of _ "ln 3"] ln3_gt_1)
  moreover have "(\<lambda>n. cmod (Ln (of_nat n) / of_nat n powr s)) \<longlonglongrightarrow> 0"
    using lim_Ln_over_power [OF assms]
    by (metis tendsto_norm_zero_iff)
  ultimately show ?thesis
    apply (auto intro!: Lim_null_comparison [where g = "\<lambda>n. norm (Ln(of_nat n) / of_nat n powr s)"])
    apply (auto simp: norm_divide divide_simps eventually_sequentially)
    done
qed

lemma lim_1_over_real_power:
  fixes s :: real
  assumes "0 < s"
    shows "((\<lambda>n. 1 / (of_nat n powr s)) \<longlongrightarrow> 0) sequentially"
  using lim_1_over_complex_power [of "of_real s", THEN filterlim_sequentially_Suc [THEN iffD2]] assms
  apply (subst filterlim_sequentially_Suc [symmetric])
  apply (simp add: lim_sequentially dist_norm)
  apply (simp add: Ln_Reals_eq norm_powr_real_powr norm_divide)
  done

lemma lim_1_over_Ln: "((\<lambda>n. 1 / Ln(of_nat n)) \<longlongrightarrow> 0) sequentially"
proof (clarsimp simp add: lim_sequentially dist_norm norm_divide divide_simps)
  fix r::real
  assume "0 < r"
  have ir: "inverse (exp (inverse r)) > 0"
    by simp
  obtain n where n: "1 < of_nat n * inverse (exp (inverse r))"
    using ex_less_of_nat_mult [of _ 1, OF ir]
    by auto
  then have "exp (inverse r) < of_nat n"
    by (simp add: divide_simps)
  then have "ln (exp (inverse r)) < ln (of_nat n)"
    by (metis exp_gt_zero less_trans ln_exp ln_less_cancel_iff)
  with \<open>0 < r\<close> have "1 < r * ln (real_of_nat n)"
    by (simp add: field_simps)
  moreover have "n > 0" using n
    using neq0_conv by fastforce
  ultimately show "\<exists>no. \<forall>n. Ln (of_nat n) \<noteq> 0 \<longrightarrow> no \<le> n \<longrightarrow> 1 < r * cmod (Ln (of_nat n))"
    using n \<open>0 < r\<close>
    apply (rule_tac x=n in exI)
    apply (auto simp: divide_simps)
    apply (erule less_le_trans, auto)
    done
qed

lemma lim_1_over_ln: "((\<lambda>n. 1 / ln(real_of_nat n)) \<longlongrightarrow> 0) sequentially"
  using lim_1_over_Ln [THEN filterlim_sequentially_Suc [THEN iffD2]]
  apply (subst filterlim_sequentially_Suc [symmetric])
  apply (simp add: lim_sequentially dist_norm)
  apply (simp add: Ln_Reals_eq norm_powr_real_powr norm_divide)
  done


subsection\<open>Relation between Square Root and exp/ln, hence its derivative\<close>

lemma csqrt_exp_Ln:
  assumes "z \<noteq> 0"
    shows "csqrt z = exp(Ln(z) / 2)"
proof -
  have "(exp (Ln z / 2))\<^sup>2 = (exp (Ln z))"
    by (metis exp_double nonzero_mult_div_cancel_left times_divide_eq_right zero_neq_numeral)
  also have "... = z"
    using assms exp_Ln by blast
  finally have "csqrt z = csqrt ((exp (Ln z / 2))\<^sup>2)"
    by simp
  also have "... = exp (Ln z / 2)"
    apply (subst csqrt_square)
    using cos_gt_zero_pi [of "(Im (Ln z) / 2)"] Im_Ln_le_pi mpi_less_Im_Ln assms
    apply (auto simp: Re_exp Im_exp zero_less_mult_iff zero_le_mult_iff, fastforce+)
    done
  finally show ?thesis using assms csqrt_square
    by simp
qed

lemma csqrt_inverse:
  assumes "z \<notin> \<real>\<^sub>\<le>\<^sub>0"
    shows "csqrt (inverse z) = inverse (csqrt z)"
proof (cases "z=0", simp)
  assume "z \<noteq> 0"
  then show ?thesis
    using assms csqrt_exp_Ln Ln_inverse exp_minus
    by (simp add: csqrt_exp_Ln Ln_inverse exp_minus)
qed

lemma cnj_csqrt:
  assumes "z \<notin> \<real>\<^sub>\<le>\<^sub>0"
    shows "cnj(csqrt z) = csqrt(cnj z)"
proof (cases "z=0", simp)
  assume "z \<noteq> 0"
  then show ?thesis
     by (simp add: assms cnj_Ln csqrt_exp_Ln exp_cnj)
qed

lemma has_field_derivative_csqrt:
  assumes "z \<notin> \<real>\<^sub>\<le>\<^sub>0"
    shows "(csqrt has_field_derivative inverse(2 * csqrt z)) (at z)"
proof -
  have z: "z \<noteq> 0"
    using assms by auto
  then have *: "inverse z = inverse (2*z) * 2"
    by (simp add: divide_simps)
  have [simp]: "exp (Ln z / 2) * inverse z = inverse (csqrt z)"
    by (simp add: z field_simps csqrt_exp_Ln [symmetric]) (metis power2_csqrt power2_eq_square)
  have "Im z = 0 \<Longrightarrow> 0 < Re z"
    using assms complex_nonpos_Reals_iff not_less by blast
  with z have "((\<lambda>z. exp (Ln z / 2)) has_field_derivative inverse (2 * csqrt z)) (at z)"
    by (force intro: derivative_eq_intros * simp add: assms)
  then show ?thesis
    apply (rule DERIV_transform_at[where d = "norm z"])
    apply (intro z derivative_eq_intros | simp add: assms)+
    using z
    apply (metis csqrt_exp_Ln dist_0_norm less_irrefl)
    done
qed

lemma field_differentiable_at_csqrt:
    "z \<notin> \<real>\<^sub>\<le>\<^sub>0 \<Longrightarrow> csqrt field_differentiable at z"
  using field_differentiable_def has_field_derivative_csqrt by blast

lemma field_differentiable_within_csqrt:
    "z \<notin> \<real>\<^sub>\<le>\<^sub>0 \<Longrightarrow> csqrt field_differentiable (at z within s)"
  using field_differentiable_at_csqrt field_differentiable_within_subset by blast

lemma continuous_at_csqrt:
    "z \<notin> \<real>\<^sub>\<le>\<^sub>0 \<Longrightarrow> continuous (at z) csqrt"
  by (simp add: field_differentiable_within_csqrt field_differentiable_imp_continuous_at)

corollary isCont_csqrt' [simp]:
   "\<lbrakk>isCont f z; f z \<notin> \<real>\<^sub>\<le>\<^sub>0\<rbrakk> \<Longrightarrow> isCont (\<lambda>x. csqrt (f x)) z"
  by (blast intro: isCont_o2 [OF _ continuous_at_csqrt])

lemma continuous_within_csqrt:
    "z \<notin> \<real>\<^sub>\<le>\<^sub>0 \<Longrightarrow> continuous (at z within s) csqrt"
  by (simp add: field_differentiable_imp_continuous_at field_differentiable_within_csqrt)

lemma continuous_on_csqrt [continuous_intros]:
    "(\<And>z. z \<in> s \<Longrightarrow> z \<notin> \<real>\<^sub>\<le>\<^sub>0) \<Longrightarrow> continuous_on s csqrt"
  by (simp add: continuous_at_imp_continuous_on continuous_within_csqrt)

lemma holomorphic_on_csqrt:
    "(\<And>z. z \<in> s \<Longrightarrow> z \<notin> \<real>\<^sub>\<le>\<^sub>0) \<Longrightarrow> csqrt holomorphic_on s"
  by (simp add: field_differentiable_within_csqrt holomorphic_on_def)

lemma continuous_within_closed_nontrivial:
    "closed s \<Longrightarrow> a \<notin> s ==> continuous (at a within s) f"
  using open_Compl
  by (force simp add: continuous_def eventually_at_topological filterlim_iff open_Collect_neg)

lemma continuous_within_csqrt_posreal:
    "continuous (at z within (\<real> \<inter> {w. 0 \<le> Re(w)})) csqrt"
proof (cases "z \<in> \<real>\<^sub>\<le>\<^sub>0")
  case True
  then have "Im z = 0" "Re z < 0 \<or> z = 0"
    using cnj.code complex_cnj_zero_iff  by (auto simp: complex_nonpos_Reals_iff) fastforce
  then show ?thesis
    apply (auto simp: continuous_within_closed_nontrivial [OF closed_Real_halfspace_Re_ge])
    apply (auto simp: continuous_within_eps_delta norm_conv_dist [symmetric])
    apply (rule_tac x="e^2" in exI)
    apply (auto simp: Reals_def)
    by (metis linear not_less real_sqrt_less_iff real_sqrt_pow2_iff real_sqrt_power)
next
  case False
    then show ?thesis   by (blast intro: continuous_within_csqrt)
qed

subsection\<open>Complex arctangent\<close>

text\<open>The branch cut gives standard bounds in the real case.\<close>

definition Arctan :: "complex \<Rightarrow> complex" where
    "Arctan \<equiv> \<lambda>z. (\<i>/2) * Ln((1 - \<i>*z) / (1 + \<i>*z))"

lemma Arctan_def_moebius: "Arctan z = \<i>/2 * Ln (moebius (-\<i>) 1 \<i> 1 z)"
  by (simp add: Arctan_def moebius_def add_ac)

lemma Ln_conv_Arctan:
  assumes "z \<noteq> -1"
  shows   "Ln z = -2*\<i> * Arctan (moebius 1 (- 1) (- \<i>) (- \<i>) z)"
proof -
  have "Arctan (moebius 1 (- 1) (- \<i>) (- \<i>) z) =
             \<i>/2 * Ln (moebius (- \<i>) 1 \<i> 1 (moebius 1 (- 1) (- \<i>) (- \<i>) z))"
    by (simp add: Arctan_def_moebius)
  also from assms have "\<i> * z \<noteq> \<i> * (-1)" by (subst mult_left_cancel) simp
  hence "\<i> * z - -\<i> \<noteq> 0" by (simp add: eq_neg_iff_add_eq_0)
  from moebius_inverse'[OF _ this, of 1 1]
    have "moebius (- \<i>) 1 \<i> 1 (moebius 1 (- 1) (- \<i>) (- \<i>) z) = z" by simp
  finally show ?thesis by (simp add: field_simps)
qed

lemma Arctan_0 [simp]: "Arctan 0 = 0"
  by (simp add: Arctan_def)

lemma Im_complex_div_lemma: "Im((1 - \<i>*z) / (1 + \<i>*z)) = 0 \<longleftrightarrow> Re z = 0"
  by (auto simp: Im_complex_div_eq_0 algebra_simps)

lemma Re_complex_div_lemma: "0 < Re((1 - \<i>*z) / (1 + \<i>*z)) \<longleftrightarrow> norm z < 1"
  by (simp add: Re_complex_div_gt_0 algebra_simps cmod_def power2_eq_square)

lemma tan_Arctan:
  assumes "z\<^sup>2 \<noteq> -1"
    shows [simp]:"tan(Arctan z) = z"
proof -
  have "1 + \<i>*z \<noteq> 0"
    by (metis assms complex_i_mult_minus i_squared minus_unique power2_eq_square power2_minus)
  moreover
  have "1 - \<i>*z \<noteq> 0"
    by (metis assms complex_i_mult_minus i_squared power2_eq_square power2_minus right_minus_eq)
  ultimately
  show ?thesis
    by (simp add: Arctan_def tan_def sin_exp_eq cos_exp_eq exp_minus csqrt_exp_Ln [symmetric]
                  divide_simps power2_eq_square [symmetric])
qed

lemma Arctan_tan [simp]:
  assumes "\<bar>Re z\<bar> < pi/2"
    shows "Arctan(tan z) = z"
proof -
  have ge_pi2: "\<And>n::int. \<bar>of_int (2*n + 1) * pi/2\<bar> \<ge> pi/2"
    by (case_tac n rule: int_cases) (auto simp: abs_mult)
  have "exp (\<i>*z)*exp (\<i>*z) = -1 \<longleftrightarrow> exp (2*\<i>*z) = -1"
    by (metis distrib_right exp_add mult_2)
  also have "... \<longleftrightarrow> exp (2*\<i>*z) = exp (\<i>*pi)"
    using cis_conv_exp cis_pi by auto
  also have "... \<longleftrightarrow> exp (2*\<i>*z - \<i>*pi) = 1"
    by (metis (no_types) diff_add_cancel diff_minus_eq_add exp_add exp_minus_inverse mult.commute)
  also have "... \<longleftrightarrow> Re(\<i>*2*z - \<i>*pi) = 0 \<and> (\<exists>n::int. Im(\<i>*2*z - \<i>*pi) = of_int (2 * n) * pi)"
    by (simp add: exp_eq_1)
  also have "... \<longleftrightarrow> Im z = 0 \<and> (\<exists>n::int. 2 * Re z = of_int (2*n + 1) * pi)"
    by (simp add: algebra_simps)
  also have "... \<longleftrightarrow> False"
    using assms ge_pi2
    apply (auto simp: algebra_simps)
    by (metis abs_mult_pos not_less of_nat_less_0_iff of_nat_numeral)
  finally have *: "exp (\<i>*z)*exp (\<i>*z) + 1 \<noteq> 0"
    by (auto simp: add.commute minus_unique)
  show ?thesis
    using assms *
    apply (simp add: Arctan_def tan_def sin_exp_eq cos_exp_eq exp_minus divide_simps
                     ii_times_eq_iff power2_eq_square [symmetric])
    apply (rule Ln_unique)
    apply (auto simp: divide_simps exp_minus)
    apply (simp add: algebra_simps exp_double [symmetric])
    done
qed

lemma
  assumes "Re z = 0 \<Longrightarrow> \<bar>Im z\<bar> < 1"
  shows Re_Arctan_bounds: "\<bar>Re(Arctan z)\<bar> < pi/2"
    and has_field_derivative_Arctan: "(Arctan has_field_derivative inverse(1 + z\<^sup>2)) (at z)"
proof -
  have nz0: "1 + \<i>*z \<noteq> 0"
    using assms
    by (metis abs_one complex_i_mult_minus diff_0_right diff_minus_eq_add ii.simps(1) ii.simps(2)
              less_irrefl minus_diff_eq mult.right_neutral right_minus_eq)
  have "z \<noteq> -\<i>" using assms
    by auto
  then have zz: "1 + z * z \<noteq> 0"
    by (metis abs_one assms i_squared ii.simps less_irrefl minus_unique square_eq_iff)
  have nz1: "1 - \<i>*z \<noteq> 0"
    using assms by (force simp add: ii_times_eq_iff)
  have nz2: "inverse (1 + \<i>*z) \<noteq> 0"
    using assms
    by (metis Im_complex_div_lemma Re_complex_div_lemma cmod_eq_Im divide_complex_def
              less_irrefl mult_zero_right zero_complex.simps(1) zero_complex.simps(2))
  have nzi: "((1 - \<i>*z) * inverse (1 + \<i>*z)) \<noteq> 0"
    using nz1 nz2 by auto
  have "Im ((1 - \<i>*z) / (1 + \<i>*z)) = 0 \<Longrightarrow> 0 < Re ((1 - \<i>*z) / (1 + \<i>*z))"
    apply (simp add: divide_complex_def)
    apply (simp add: divide_simps split: if_split_asm)
    using assms
    apply (auto simp: algebra_simps abs_square_less_1 [unfolded power2_eq_square])
    done
  then have *: "((1 - \<i>*z) / (1 + \<i>*z)) \<notin> \<real>\<^sub>\<le>\<^sub>0"
    by (auto simp add: complex_nonpos_Reals_iff)
  show "\<bar>Re(Arctan z)\<bar> < pi/2"
    unfolding Arctan_def divide_complex_def
    using mpi_less_Im_Ln [OF nzi]
    apply (auto simp: abs_if intro!: Im_Ln_less_pi * [unfolded divide_complex_def])
    done
  show "(Arctan has_field_derivative inverse(1 + z\<^sup>2)) (at z)"
    unfolding Arctan_def scaleR_conv_of_real
    apply (rule DERIV_cong)
    apply (intro derivative_eq_intros | simp add: nz0 *)+
    using nz0 nz1 zz
    apply (simp add: divide_simps power2_eq_square)
    apply (auto simp: algebra_simps)
    done
qed

lemma field_differentiable_at_Arctan: "(Re z = 0 \<Longrightarrow> \<bar>Im z\<bar> < 1) \<Longrightarrow> Arctan field_differentiable at z"
  using has_field_derivative_Arctan
  by (auto simp: field_differentiable_def)

lemma field_differentiable_within_Arctan:
    "(Re z = 0 \<Longrightarrow> \<bar>Im z\<bar> < 1) \<Longrightarrow> Arctan field_differentiable (at z within s)"
  using field_differentiable_at_Arctan field_differentiable_at_within by blast

declare has_field_derivative_Arctan [derivative_intros]
declare has_field_derivative_Arctan [THEN DERIV_chain2, derivative_intros]

lemma continuous_at_Arctan:
    "(Re z = 0 \<Longrightarrow> \<bar>Im z\<bar> < 1) \<Longrightarrow> continuous (at z) Arctan"
  by (simp add: field_differentiable_imp_continuous_at field_differentiable_within_Arctan)

lemma continuous_within_Arctan:
    "(Re z = 0 \<Longrightarrow> \<bar>Im z\<bar> < 1) \<Longrightarrow> continuous (at z within s) Arctan"
  using continuous_at_Arctan continuous_at_imp_continuous_within by blast

lemma continuous_on_Arctan [continuous_intros]:
    "(\<And>z. z \<in> s \<Longrightarrow> Re z = 0 \<Longrightarrow> \<bar>Im z\<bar> < 1) \<Longrightarrow> continuous_on s Arctan"
  by (auto simp: continuous_at_imp_continuous_on continuous_within_Arctan)

lemma holomorphic_on_Arctan:
    "(\<And>z. z \<in> s \<Longrightarrow> Re z = 0 \<Longrightarrow> \<bar>Im z\<bar> < 1) \<Longrightarrow> Arctan holomorphic_on s"
  by (simp add: field_differentiable_within_Arctan holomorphic_on_def)

lemma Arctan_series:
  assumes z: "norm (z :: complex) < 1"
  defines "g \<equiv> \<lambda>n. if odd n then -\<i>*\<i>^n / n else 0"
  defines "h \<equiv> \<lambda>z n. (-1)^n / of_nat (2*n+1) * (z::complex)^(2*n+1)"
  shows   "(\<lambda>n. g n * z^n) sums Arctan z"
  and     "h z sums Arctan z"
proof -
  define G where [abs_def]: "G z = (\<Sum>n. g n * z^n)" for z
  have summable: "summable (\<lambda>n. g n * u^n)" if "norm u < 1" for u
  proof (cases "u = 0")
    assume u: "u \<noteq> 0"
    have "(\<lambda>n. ereal (norm (h u n) / norm (h u (Suc n)))) = (\<lambda>n. ereal (inverse (norm u)^2) *
              ereal ((2 + inverse (real (Suc n))) / (2 - inverse (real (Suc n)))))"
    proof
      fix n
      have "ereal (norm (h u n) / norm (h u (Suc n))) =
             ereal (inverse (norm u)^2) * ereal ((of_nat (2*Suc n+1) / of_nat (Suc n)) /
                 (of_nat (2*Suc n-1) / of_nat (Suc n)))"
      by (simp add: h_def norm_mult norm_power norm_divide divide_simps
                    power2_eq_square eval_nat_numeral del: of_nat_add of_nat_Suc)
      also have "of_nat (2*Suc n+1) / of_nat (Suc n) = (2::real) + inverse (real (Suc n))"
        by (auto simp: divide_simps simp del: of_nat_Suc) simp_all?
      also have "of_nat (2*Suc n-1) / of_nat (Suc n) = (2::real) - inverse (real (Suc n))"
        by (auto simp: divide_simps simp del: of_nat_Suc) simp_all?
      finally show "ereal (norm (h u n) / norm (h u (Suc n))) = ereal (inverse (norm u)^2) *
              ereal ((2 + inverse (real (Suc n))) / (2 - inverse (real (Suc n))))" .
    qed
    also have "\<dots> \<longlonglongrightarrow> ereal (inverse (norm u)^2) * ereal ((2 + 0) / (2 - 0))"
      by (intro tendsto_intros LIMSEQ_inverse_real_of_nat) simp_all
    finally have "liminf (\<lambda>n. ereal (cmod (h u n) / cmod (h u (Suc n)))) = inverse (norm u)^2"
      by (intro lim_imp_Liminf) simp_all
    moreover from power_strict_mono[OF that, of 2] u have "inverse (norm u)^2 > 1"
      by (simp add: divide_simps)
    ultimately have A: "liminf (\<lambda>n. ereal (cmod (h u n) / cmod (h u (Suc n)))) > 1" by simp
    from u have "summable (h u)"
      by (intro summable_norm_cancel[OF ratio_test_convergence[OF _ A]])
         (auto simp: h_def norm_divide norm_mult norm_power simp del: of_nat_Suc
               intro!: mult_pos_pos divide_pos_pos always_eventually)
    thus "summable (\<lambda>n. g n * u^n)"
      by (subst summable_mono_reindex[of "\<lambda>n. 2*n+1", symmetric])
         (auto simp: power_mult subseq_def g_def h_def elim!: oddE)
  qed (simp add: h_def)

  have "\<exists>c. \<forall>u\<in>ball 0 1. Arctan u - G u = c"
  proof (rule has_field_derivative_zero_constant)
    fix u :: complex assume "u \<in> ball 0 1"
    hence u: "norm u < 1" by (simp add: dist_0_norm)
    define K where "K = (norm u + 1) / 2"
    from u and abs_Im_le_cmod[of u] have Im_u: "\<bar>Im u\<bar> < 1" by linarith
    from u have K: "0 \<le> K" "norm u < K" "K < 1" by (simp_all add: K_def)
    hence "(G has_field_derivative (\<Sum>n. diffs g n * u ^ n)) (at u)" unfolding G_def
      by (intro termdiffs_strong[of _ "of_real K"] summable) simp_all
    also have "(\<lambda>n. diffs g n * u^n) = (\<lambda>n. if even n then (\<i>*u)^n else 0)"
      by (intro ext) (simp_all del: of_nat_Suc add: g_def diffs_def power_mult_distrib)
    also have "suminf \<dots> = (\<Sum>n. (-(u^2))^n)"
      by (subst suminf_mono_reindex[of "\<lambda>n. 2*n", symmetric])
         (auto elim!: evenE simp: subseq_def power_mult power_mult_distrib)
    also from u have "norm u^2 < 1^2" by (intro power_strict_mono) simp_all
    hence "(\<Sum>n. (-(u^2))^n) = inverse (1 + u^2)"
      by (subst suminf_geometric) (simp_all add: norm_power inverse_eq_divide)
    finally have "(G has_field_derivative inverse (1 + u\<^sup>2)) (at u)" .
    from DERIV_diff[OF has_field_derivative_Arctan this] Im_u u
      show "((\<lambda>u. Arctan u - G u) has_field_derivative 0) (at u within ball 0 1)"
      by (simp_all add: dist_0_norm at_within_open[OF _ open_ball])
  qed simp_all
  then obtain c where c: "\<And>u. norm u < 1 \<Longrightarrow> Arctan u - G u = c" by (auto simp: dist_0_norm)
  from this[of 0] have "c = 0" by (simp add: G_def g_def powser_zero)
  with c z have "Arctan z = G z" by simp
  with summable[OF z] show "(\<lambda>n. g n * z^n) sums Arctan z" unfolding G_def by (simp add: sums_iff)
  thus "h z sums Arctan z" by (subst (asm) sums_mono_reindex[of "\<lambda>n. 2*n+1", symmetric])
                              (auto elim!: oddE simp: subseq_def power_mult g_def h_def)
qed

text \<open>A quickly-converging series for the logarithm, based on the arctangent.\<close>
lemma ln_series_quadratic:
  assumes x: "x > (0::real)"
  shows "(\<lambda>n. (2*((x - 1) / (x + 1)) ^ (2*n+1) / of_nat (2*n+1))) sums ln x"
proof -
  define y :: complex where "y = of_real ((x-1)/(x+1))"
  from x have x': "complex_of_real x \<noteq> of_real (-1)"  by (subst of_real_eq_iff) auto
  from x have "\<bar>x - 1\<bar> < \<bar>x + 1\<bar>" by linarith
  hence "norm (complex_of_real (x - 1) / complex_of_real (x + 1)) < 1"
    by (simp add: norm_divide del: of_real_add of_real_diff)
  hence "norm (\<i> * y) < 1" unfolding y_def by (subst norm_mult) simp
  hence "(\<lambda>n. (-2*\<i>) * ((-1)^n / of_nat (2*n+1) * (\<i>*y)^(2*n+1))) sums ((-2*\<i>) * Arctan (\<i>*y))"
    by (intro Arctan_series sums_mult) simp_all
  also have "(\<lambda>n. (-2*\<i>) * ((-1)^n / of_nat (2*n+1) * (\<i>*y)^(2*n+1))) =
                 (\<lambda>n. (-2*\<i>) * ((-1)^n * (\<i>*y*(-y\<^sup>2)^n)/of_nat (2*n+1)))"
    by (intro ext) (simp_all add: power_mult power_mult_distrib)
  also have "\<dots> = (\<lambda>n. 2*y* ((-1) * (-y\<^sup>2))^n/of_nat (2*n+1))"
    by (intro ext, subst power_mult_distrib) (simp add: algebra_simps power_mult)
  also have "\<dots> = (\<lambda>n. 2*y^(2*n+1) / of_nat (2*n+1))"
    by (subst power_add, subst power_mult) (simp add: mult_ac)
  also have "\<dots> = (\<lambda>n. of_real (2*((x-1)/(x+1))^(2*n+1) / of_nat (2*n+1)))"
    by (intro ext) (simp add: y_def)
  also have "\<i> * y = (of_real x - 1) / (-\<i> * (of_real x + 1))"
    by (subst divide_divide_eq_left [symmetric]) (simp add: y_def)
  also have "\<dots> = moebius 1 (-1) (-\<i>) (-\<i>) (of_real x)" by (simp add: moebius_def algebra_simps)
  also from x' have "-2*\<i>*Arctan \<dots> = Ln (of_real x)" by (intro Ln_conv_Arctan [symmetric]) simp_all
  also from x have "\<dots> = ln x" by (rule Ln_of_real)
  finally show ?thesis by (subst (asm) sums_of_real_iff)
qed

subsection \<open>Real arctangent\<close>

lemma norm_exp_ii_times [simp]: "norm (exp(\<i> * of_real y)) = 1"
  by simp

lemma norm_exp_imaginary: "norm(exp z) = 1 \<Longrightarrow> Re z = 0"
  by simp

lemma Im_Arctan_of_real [simp]: "Im (Arctan (of_real x)) = 0"
  unfolding Arctan_def divide_complex_def
  apply (simp add: complex_eq_iff)
  apply (rule norm_exp_imaginary)
  apply (subst exp_Ln, auto)
  apply (simp_all add: cmod_def complex_eq_iff)
  apply (auto simp: divide_simps)
  apply (metis power_one sum_power2_eq_zero_iff zero_neq_one, algebra)
  done

lemma arctan_eq_Re_Arctan: "arctan x = Re (Arctan (of_real x))"
proof (rule arctan_unique)
  show "- (pi / 2) < Re (Arctan (complex_of_real x))"
    apply (simp add: Arctan_def)
    apply (rule Im_Ln_less_pi)
    apply (auto simp: Im_complex_div_lemma complex_nonpos_Reals_iff)
    done
next
  have *: " (1 - \<i>*x) / (1 + \<i>*x) \<noteq> 0"
    by (simp add: divide_simps) ( simp add: complex_eq_iff)
  show "Re (Arctan (complex_of_real x)) < pi / 2"
    using mpi_less_Im_Ln [OF *]
    by (simp add: Arctan_def)
next
  have "tan (Re (Arctan (of_real x))) = Re (tan (Arctan (of_real x)))"
    apply (auto simp: tan_def Complex.Re_divide Re_sin Re_cos Im_sin Im_cos)
    apply (simp add: field_simps)
    by (simp add: power2_eq_square)
  also have "... = x"
    apply (subst tan_Arctan, auto)
    by (metis diff_0_right minus_diff_eq mult_zero_left not_le of_real_1 of_real_eq_iff of_real_minus of_real_power power2_eq_square real_minus_mult_self_le zero_less_one)
  finally show "tan (Re (Arctan (complex_of_real x))) = x" .
qed

lemma Arctan_of_real: "Arctan (of_real x) = of_real (arctan x)"
  unfolding arctan_eq_Re_Arctan divide_complex_def
  by (simp add: complex_eq_iff)

lemma Arctan_in_Reals [simp]: "z \<in> \<real> \<Longrightarrow> Arctan z \<in> \<real>"
  by (metis Reals_cases Reals_of_real Arctan_of_real)

declare arctan_one [simp]

lemma arctan_less_pi4_pos: "x < 1 \<Longrightarrow> arctan x < pi/4"
  by (metis arctan_less_iff arctan_one)

lemma arctan_less_pi4_neg: "-1 < x \<Longrightarrow> -(pi/4) < arctan x"
  by (metis arctan_less_iff arctan_minus arctan_one)

lemma arctan_less_pi4: "\<bar>x\<bar> < 1 \<Longrightarrow> \<bar>arctan x\<bar> < pi/4"
  by (metis abs_less_iff arctan_less_pi4_pos arctan_minus)

lemma arctan_le_pi4: "\<bar>x\<bar> \<le> 1 \<Longrightarrow> \<bar>arctan x\<bar> \<le> pi/4"
  by (metis abs_le_iff arctan_le_iff arctan_minus arctan_one)

lemma abs_arctan: "\<bar>arctan x\<bar> = arctan \<bar>x\<bar>"
  by (simp add: abs_if arctan_minus)

lemma arctan_add_raw:
  assumes "\<bar>arctan x + arctan y\<bar> < pi/2"
    shows "arctan x + arctan y = arctan((x + y) / (1 - x * y))"
proof (rule arctan_unique [symmetric])
  show 12: "- (pi / 2) < arctan x + arctan y" "arctan x + arctan y < pi / 2"
    using assms by linarith+
  show "tan (arctan x + arctan y) = (x + y) / (1 - x * y)"
    using cos_gt_zero_pi [OF 12]
    by (simp add: arctan tan_add)
qed

lemma arctan_inverse:
  assumes "0 < x"
    shows "arctan(inverse x) = pi/2 - arctan x"
proof -
  have "arctan(inverse x) = arctan(inverse(tan(arctan x)))"
    by (simp add: arctan)
  also have "... = arctan (tan (pi / 2 - arctan x))"
    by (simp add: tan_cot)
  also have "... = pi/2 - arctan x"
  proof -
    have "0 < pi - arctan x"
    using arctan_ubound [of x] pi_gt_zero by linarith
    with assms show ?thesis
      by (simp add: Transcendental.arctan_tan)
  qed
  finally show ?thesis .
qed

lemma arctan_add_small:
  assumes "\<bar>x * y\<bar> < 1"
    shows "(arctan x + arctan y = arctan((x + y) / (1 - x * y)))"
proof (cases "x = 0 \<or> y = 0")
  case True then show ?thesis
    by auto
next
  case False
  then have *: "\<bar>arctan x\<bar> < pi / 2 - \<bar>arctan y\<bar>" using assms
    apply (auto simp add: abs_arctan arctan_inverse [symmetric] arctan_less_iff)
    apply (simp add: divide_simps abs_mult)
    done
  show ?thesis
    apply (rule arctan_add_raw)
    using * by linarith
qed

lemma abs_arctan_le:
  fixes x::real shows "\<bar>arctan x\<bar> \<le> \<bar>x\<bar>"
proof -
  { fix w::complex and z::complex
    assume *: "w \<in> \<real>" "z \<in> \<real>"
    have "cmod (Arctan w - Arctan z) \<le> 1 * cmod (w-z)"
      apply (rule field_differentiable_bound [OF convex_Reals, of Arctan _ 1])
      apply (rule has_field_derivative_at_within [OF has_field_derivative_Arctan])
      apply (force simp add: Reals_def)
      apply (simp add: norm_divide divide_simps in_Reals_norm complex_is_Real_iff power2_eq_square)
      using * by auto
  }
  then have "cmod (Arctan (of_real x) - Arctan 0) \<le> 1 * cmod (of_real x -0)"
    using Reals_0 Reals_of_real by blast
  then show ?thesis
    by (simp add: Arctan_of_real)
qed

lemma arctan_le_self: "0 \<le> x \<Longrightarrow> arctan x \<le> x"
  by (metis abs_arctan_le abs_of_nonneg zero_le_arctan_iff)

lemma abs_tan_ge: "\<bar>x\<bar> < pi/2 \<Longrightarrow> \<bar>x\<bar> \<le> \<bar>tan x\<bar>"
  by (metis abs_arctan_le abs_less_iff arctan_tan minus_less_iff)

lemma arctan_bounds:
  assumes "0 \<le> x" "x < 1"
  shows arctan_lower_bound:
    "(\<Sum>k<2 * n. (- 1) ^ k * (1 / real (k * 2 + 1) * x ^ (k * 2 + 1))) \<le> arctan x"
    (is "(\<Sum>k<_. (- 1)^ k * ?a k) \<le> _")
    and arctan_upper_bound:
    "arctan x \<le> (\<Sum>k<2 * n + 1. (- 1) ^ k * (1 / real (k * 2 + 1) * x ^ (k * 2 + 1)))"
proof -
  have tendsto_zero: "?a \<longlonglongrightarrow> 0"
    using assms
    apply -
    apply (rule tendsto_eq_rhs[where x="0 * 0"])
    subgoal by (intro tendsto_mult real_tendsto_divide_at_top)
        (auto simp: filterlim_real_sequentially filterlim_sequentially_iff_filterlim_real
          intro!: real_tendsto_divide_at_top tendsto_power_zero filterlim_real_sequentially
           tendsto_eq_intros filterlim_at_top_mult_tendsto_pos filterlim_tendsto_add_at_top)
    subgoal by simp
    done
  have nonneg: "0 \<le> ?a n" for n
    by (force intro!: divide_nonneg_nonneg mult_nonneg_nonneg zero_le_power assms)
  have le: "?a (Suc n) \<le> ?a n" for n
    by (rule mult_mono[OF _ power_decreasing]) (auto simp: divide_simps assms less_imp_le)
  from summable_Leibniz'(4)[of ?a, OF tendsto_zero nonneg le, of n]
    summable_Leibniz'(2)[of ?a, OF tendsto_zero nonneg le, of n]
    assms
  show "(\<Sum>k<2*n. (- 1)^ k * ?a k) \<le> arctan x" "arctan x \<le> (\<Sum>k<2 * n + 1. (- 1)^ k * ?a k)"
    by (auto simp: arctan_series)
qed

subsection \<open>Bounds on pi using real arctangent\<close>

lemma pi_machin: "pi = 16 * arctan (1 / 5) - 4 * arctan (1 / 239)"
  using machin
  by simp

lemma pi_approx: "3.141592653588 \<le> pi" "pi \<le> 3.1415926535899"
  unfolding pi_machin
  using arctan_bounds[of "1/5"   4]
        arctan_bounds[of "1/239" 4]
  by (simp_all add: eval_nat_numeral)


subsection\<open>Inverse Sine\<close>

definition Arcsin :: "complex \<Rightarrow> complex" where
   "Arcsin \<equiv> \<lambda>z. -\<i> * Ln(\<i> * z + csqrt(1 - z\<^sup>2))"

lemma Arcsin_body_lemma: "\<i> * z + csqrt(1 - z\<^sup>2) \<noteq> 0"
  using power2_csqrt [of "1 - z\<^sup>2"]
  apply auto
  by (metis complex_i_mult_minus diff_add_cancel diff_minus_eq_add diff_self mult.assoc mult.left_commute numeral_One power2_csqrt power2_eq_square zero_neq_numeral)

lemma Arcsin_range_lemma: "\<bar>Re z\<bar> < 1 \<Longrightarrow> 0 < Re(\<i> * z + csqrt(1 - z\<^sup>2))"
  using Complex.cmod_power2 [of z, symmetric]
  by (simp add: real_less_rsqrt algebra_simps Re_power2 cmod_square_less_1_plus)

lemma Re_Arcsin: "Re(Arcsin z) = Im (Ln (\<i> * z + csqrt(1 - z\<^sup>2)))"
  by (simp add: Arcsin_def)

lemma Im_Arcsin: "Im(Arcsin z) = - ln (cmod (\<i> * z + csqrt (1 - z\<^sup>2)))"
  by (simp add: Arcsin_def Arcsin_body_lemma)

lemma one_minus_z2_notin_nonpos_Reals:
  assumes "(Im z = 0 \<Longrightarrow> \<bar>Re z\<bar> < 1)"
  shows "1 - z\<^sup>2 \<notin> \<real>\<^sub>\<le>\<^sub>0"
    using assms
    apply (auto simp: complex_nonpos_Reals_iff Re_power2 Im_power2)
    using power2_less_0 [of "Im z"] apply force
    using abs_square_less_1 not_le by blast

lemma isCont_Arcsin_lemma:
  assumes le0: "Re (\<i> * z + csqrt (1 - z\<^sup>2)) \<le> 0" and "(Im z = 0 \<Longrightarrow> \<bar>Re z\<bar> < 1)"
    shows False
proof (cases "Im z = 0")
  case True
  then show ?thesis
    using assms by (fastforce simp: cmod_def abs_square_less_1 [symmetric])
next
  case False
  have neq: "(cmod z)\<^sup>2 \<noteq> 1 + cmod (1 - z\<^sup>2)"
  proof (clarsimp simp add: cmod_def)
    assume "(Re z)\<^sup>2 + (Im z)\<^sup>2 = 1 + sqrt ((1 - Re (z\<^sup>2))\<^sup>2 + (Im (z\<^sup>2))\<^sup>2)"
    then have "((Re z)\<^sup>2 + (Im z)\<^sup>2 - 1)\<^sup>2 = ((1 - Re (z\<^sup>2))\<^sup>2 + (Im (z\<^sup>2))\<^sup>2)"
      by simp
    then show False using False
      by (simp add: power2_eq_square algebra_simps)
  qed
  moreover have 2: "(Im z)\<^sup>2 = (1 + ((Im z)\<^sup>2 + cmod (1 - z\<^sup>2)) - (Re z)\<^sup>2) / 2"
    using le0
    apply simp
    apply (drule sqrt_le_D)
    using cmod_power2 [of z] norm_triangle_ineq2 [of "z^2" 1]
    apply (simp add: norm_power Re_power2 norm_minus_commute [of 1])
    done
  ultimately show False
    by (simp add: Re_power2 Im_power2 cmod_power2)
qed

lemma isCont_Arcsin:
  assumes "(Im z = 0 \<Longrightarrow> \<bar>Re z\<bar> < 1)"
    shows "isCont Arcsin z"
proof -
  have *: "\<i> * z + csqrt (1 - z\<^sup>2) \<notin> \<real>\<^sub>\<le>\<^sub>0"
    by (metis isCont_Arcsin_lemma assms complex_nonpos_Reals_iff)
  show ?thesis
    using assms
    apply (simp add: Arcsin_def)
    apply (rule isCont_Ln' isCont_csqrt' continuous_intros)+
    apply (simp add: one_minus_z2_notin_nonpos_Reals assms)
    apply (rule *)
    done
qed

lemma isCont_Arcsin' [simp]:
  shows "isCont f z \<Longrightarrow> (Im (f z) = 0 \<Longrightarrow> \<bar>Re (f z)\<bar> < 1) \<Longrightarrow> isCont (\<lambda>x. Arcsin (f x)) z"
  by (blast intro: isCont_o2 [OF _ isCont_Arcsin])

lemma sin_Arcsin [simp]: "sin(Arcsin z) = z"
proof -
  have "\<i>*z*2 + csqrt (1 - z\<^sup>2)*2 = 0 \<longleftrightarrow> (\<i>*z)*2 + csqrt (1 - z\<^sup>2)*2 = 0"
    by (simp add: algebra_simps)  \<comment>\<open>Cancelling a factor of 2\<close>
  moreover have "... \<longleftrightarrow> (\<i>*z) + csqrt (1 - z\<^sup>2) = 0"
    by (metis Arcsin_body_lemma distrib_right no_zero_divisors zero_neq_numeral)
  ultimately show ?thesis
    apply (simp add: sin_exp_eq Arcsin_def Arcsin_body_lemma exp_minus divide_simps)
    apply (simp add: algebra_simps)
    apply (simp add: power2_eq_square [symmetric] algebra_simps)
    done
qed

lemma Re_eq_pihalf_lemma:
    "\<bar>Re z\<bar> = pi/2 \<Longrightarrow> Im z = 0 \<Longrightarrow>
      Re ((exp (\<i>*z) + inverse (exp (\<i>*z))) / 2) = 0 \<and> 0 \<le> Im ((exp (\<i>*z) + inverse (exp (\<i>*z))) / 2)"
  apply (simp add: cos_ii_times [symmetric] Re_cos Im_cos abs_if del: eq_divide_eq_numeral1)
  by (metis cos_minus cos_pi_half)

lemma Re_less_pihalf_lemma:
  assumes "\<bar>Re z\<bar> < pi / 2"
    shows "0 < Re ((exp (\<i>*z) + inverse (exp (\<i>*z))) / 2)"
proof -
  have "0 < cos (Re z)" using assms
    using cos_gt_zero_pi by auto
  then show ?thesis
    by (simp add: cos_ii_times [symmetric] Re_cos Im_cos add_pos_pos)
qed

lemma Arcsin_sin:
    assumes "\<bar>Re z\<bar> < pi/2 \<or> (\<bar>Re z\<bar> = pi/2 \<and> Im z = 0)"
      shows "Arcsin(sin z) = z"
proof -
  have "Arcsin(sin z) = - (\<i> * Ln (csqrt (1 - (\<i> * (exp (\<i>*z) - inverse (exp (\<i>*z))))\<^sup>2 / 4) - (inverse (exp (\<i>*z)) - exp (\<i>*z)) / 2))"
    by (simp add: sin_exp_eq Arcsin_def exp_minus power_divide)
  also have "... = - (\<i> * Ln (csqrt (((exp (\<i>*z) + inverse (exp (\<i>*z)))/2)\<^sup>2) - (inverse (exp (\<i>*z)) - exp (\<i>*z)) / 2))"
    by (simp add: field_simps power2_eq_square)
  also have "... = - (\<i> * Ln (((exp (\<i>*z) + inverse (exp (\<i>*z)))/2) - (inverse (exp (\<i>*z)) - exp (\<i>*z)) / 2))"
    apply (subst csqrt_square)
    using assms Re_eq_pihalf_lemma Re_less_pihalf_lemma
    apply auto
    done
  also have "... =  - (\<i> * Ln (exp (\<i>*z)))"
    by (simp add: field_simps power2_eq_square)
  also have "... = z"
    apply (subst Complex_Transcendental.Ln_exp)
    using assms
    apply (auto simp: abs_if simp del: eq_divide_eq_numeral1 split: if_split_asm)
    done
  finally show ?thesis .
qed

lemma Arcsin_unique:
    "\<lbrakk>sin z = w; \<bar>Re z\<bar> < pi/2 \<or> (\<bar>Re z\<bar> = pi/2 \<and> Im z = 0)\<rbrakk> \<Longrightarrow> Arcsin w = z"
  by (metis Arcsin_sin)

lemma Arcsin_0 [simp]: "Arcsin 0 = 0"
  by (metis Arcsin_sin norm_zero pi_half_gt_zero real_norm_def sin_zero zero_complex.simps(1))

lemma Arcsin_1 [simp]: "Arcsin 1 = pi/2"
  by (metis Arcsin_sin Im_complex_of_real Re_complex_of_real numeral_One of_real_numeral pi_half_ge_zero real_sqrt_abs real_sqrt_pow2 real_sqrt_power sin_of_real sin_pi_half)

lemma Arcsin_minus_1 [simp]: "Arcsin(-1) = - (pi/2)"
  by (metis Arcsin_1 Arcsin_sin Im_complex_of_real Re_complex_of_real abs_of_nonneg of_real_minus pi_half_ge_zero power2_minus real_sqrt_abs sin_Arcsin sin_minus)

lemma has_field_derivative_Arcsin:
  assumes "(Im z = 0 \<Longrightarrow> \<bar>Re z\<bar> < 1)"
    shows "(Arcsin has_field_derivative inverse(cos(Arcsin z))) (at z)"
proof -
  have "(sin (Arcsin z))\<^sup>2 \<noteq> 1"
    using assms
    apply atomize
    apply (auto simp: complex_eq_iff Re_power2 Im_power2 abs_square_eq_1)
    apply (metis abs_minus_cancel abs_one abs_power2 numeral_One numeral_neq_neg_one)
    by (metis abs_minus_cancel abs_one abs_power2 one_neq_neg_one)
  then have "cos (Arcsin z) \<noteq> 0"
    by (metis diff_0_right power_zero_numeral sin_squared_eq)
  then show ?thesis
    apply (rule has_complex_derivative_inverse_basic [OF DERIV_sin _ _ open_ball [of z 1]])
    apply (auto intro: isCont_Arcsin assms)
    done
qed

declare has_field_derivative_Arcsin [derivative_intros]
declare has_field_derivative_Arcsin [THEN DERIV_chain2, derivative_intros]

lemma field_differentiable_at_Arcsin:
    "(Im z = 0 \<Longrightarrow> \<bar>Re z\<bar> < 1) \<Longrightarrow> Arcsin field_differentiable at z"
  using field_differentiable_def has_field_derivative_Arcsin by blast

lemma field_differentiable_within_Arcsin:
    "(Im z = 0 \<Longrightarrow> \<bar>Re z\<bar> < 1) \<Longrightarrow> Arcsin field_differentiable (at z within s)"
  using field_differentiable_at_Arcsin field_differentiable_within_subset by blast

lemma continuous_within_Arcsin:
    "(Im z = 0 \<Longrightarrow> \<bar>Re z\<bar> < 1) \<Longrightarrow> continuous (at z within s) Arcsin"
  using continuous_at_imp_continuous_within isCont_Arcsin by blast

lemma continuous_on_Arcsin [continuous_intros]:
    "(\<And>z. z \<in> s \<Longrightarrow> Im z = 0 \<Longrightarrow> \<bar>Re z\<bar> < 1) \<Longrightarrow> continuous_on s Arcsin"
  by (simp add: continuous_at_imp_continuous_on)

lemma holomorphic_on_Arcsin: "(\<And>z. z \<in> s \<Longrightarrow> Im z = 0 \<Longrightarrow> \<bar>Re z\<bar> < 1) \<Longrightarrow> Arcsin holomorphic_on s"
  by (simp add: field_differentiable_within_Arcsin holomorphic_on_def)


subsection\<open>Inverse Cosine\<close>

definition Arccos :: "complex \<Rightarrow> complex" where
   "Arccos \<equiv> \<lambda>z. -\<i> * Ln(z + \<i> * csqrt(1 - z\<^sup>2))"

lemma Arccos_range_lemma: "\<bar>Re z\<bar> < 1 \<Longrightarrow> 0 < Im(z + \<i> * csqrt(1 - z\<^sup>2))"
  using Arcsin_range_lemma [of "-z"]
  by simp

lemma Arccos_body_lemma: "z + \<i> * csqrt(1 - z\<^sup>2) \<noteq> 0"
  using Arcsin_body_lemma [of z]
  by (metis complex_i_mult_minus diff_add_cancel minus_diff_eq minus_unique mult.assoc mult.left_commute
           power2_csqrt power2_eq_square zero_neq_one)

lemma Re_Arccos: "Re(Arccos z) = Im (Ln (z + \<i> * csqrt(1 - z\<^sup>2)))"
  by (simp add: Arccos_def)

lemma Im_Arccos: "Im(Arccos z) = - ln (cmod (z + \<i> * csqrt (1 - z\<^sup>2)))"
  by (simp add: Arccos_def Arccos_body_lemma)

text\<open>A very tricky argument to find!\<close>
lemma isCont_Arccos_lemma:
  assumes eq0: "Im (z + \<i> * csqrt (1 - z\<^sup>2)) = 0" and "(Im z = 0 \<Longrightarrow> \<bar>Re z\<bar> < 1)"
    shows False
proof (cases "Im z = 0")
  case True
  then show ?thesis
    using assms by (fastforce simp add: cmod_def abs_square_less_1 [symmetric])
next
  case False
  have Imz: "Im z = - sqrt ((1 + ((Im z)\<^sup>2 + cmod (1 - z\<^sup>2)) - (Re z)\<^sup>2) / 2)"
    using eq0 abs_Re_le_cmod [of "1-z\<^sup>2"]
    by (simp add: Re_power2 algebra_simps)
  have "(cmod z)\<^sup>2 - 1 \<noteq> cmod (1 - z\<^sup>2)"
  proof (clarsimp simp add: cmod_def)
    assume "(Re z)\<^sup>2 + (Im z)\<^sup>2 - 1 = sqrt ((1 - Re (z\<^sup>2))\<^sup>2 + (Im (z\<^sup>2))\<^sup>2)"
    then have "((Re z)\<^sup>2 + (Im z)\<^sup>2 - 1)\<^sup>2 = ((1 - Re (z\<^sup>2))\<^sup>2 + (Im (z\<^sup>2))\<^sup>2)"
      by simp
    then show False using False
      by (simp add: power2_eq_square algebra_simps)
  qed
  moreover have "(Im z)\<^sup>2 = ((1 + ((Im z)\<^sup>2 + cmod (1 - z\<^sup>2)) - (Re z)\<^sup>2) / 2)"
    apply (subst Imz)
    using abs_Re_le_cmod [of "1-z\<^sup>2"]
    apply (simp add: Re_power2)
    done
  ultimately show False
    by (simp add: cmod_power2)
qed

lemma isCont_Arccos:
  assumes "(Im z = 0 \<Longrightarrow> \<bar>Re z\<bar> < 1)"
    shows "isCont Arccos z"
proof -
  have "z + \<i> * csqrt (1 - z\<^sup>2) \<notin> \<real>\<^sub>\<le>\<^sub>0"
    by (metis complex_nonpos_Reals_iff isCont_Arccos_lemma assms)
  with assms show ?thesis
    apply (simp add: Arccos_def)
    apply (rule isCont_Ln' isCont_csqrt' continuous_intros)+
    apply (simp_all add: one_minus_z2_notin_nonpos_Reals assms)
    done
qed

lemma isCont_Arccos' [simp]:
  shows "isCont f z \<Longrightarrow> (Im (f z) = 0 \<Longrightarrow> \<bar>Re (f z)\<bar> < 1) \<Longrightarrow> isCont (\<lambda>x. Arccos (f x)) z"
  by (blast intro: isCont_o2 [OF _ isCont_Arccos])

lemma cos_Arccos [simp]: "cos(Arccos z) = z"
proof -
  have "z*2 + \<i> * (2 * csqrt (1 - z\<^sup>2)) = 0 \<longleftrightarrow> z*2 + \<i> * csqrt (1 - z\<^sup>2)*2 = 0"
    by (simp add: algebra_simps)  \<comment>\<open>Cancelling a factor of 2\<close>
  moreover have "... \<longleftrightarrow> z + \<i> * csqrt (1 - z\<^sup>2) = 0"
    by (metis distrib_right mult_eq_0_iff zero_neq_numeral)
  ultimately show ?thesis
    apply (simp add: cos_exp_eq Arccos_def Arccos_body_lemma exp_minus field_simps)
    apply (simp add: power2_eq_square [symmetric])
    done
qed

lemma Arccos_cos:
    assumes "0 < Re z & Re z < pi \<or>
             Re z = 0 & 0 \<le> Im z \<or>
             Re z = pi & Im z \<le> 0"
      shows "Arccos(cos z) = z"
proof -
  have *: "((\<i> - (exp (\<i> * z))\<^sup>2 * \<i>) / (2 * exp (\<i> * z))) = sin z"
    by (simp add: sin_exp_eq exp_minus field_simps power2_eq_square)
  have "1 - (exp (\<i> * z) + inverse (exp (\<i> * z)))\<^sup>2 / 4 = ((\<i> - (exp (\<i> * z))\<^sup>2 * \<i>) / (2 * exp (\<i> * z)))\<^sup>2"
    by (simp add: field_simps power2_eq_square)
  then have "Arccos(cos z) = - (\<i> * Ln ((exp (\<i> * z) + inverse (exp (\<i> * z))) / 2 +
                           \<i> * csqrt (((\<i> - (exp (\<i> * z))\<^sup>2 * \<i>) / (2 * exp (\<i> * z)))\<^sup>2)))"
    by (simp add: cos_exp_eq Arccos_def exp_minus power_divide)
  also have "... = - (\<i> * Ln ((exp (\<i> * z) + inverse (exp (\<i> * z))) / 2 +
                              \<i> * ((\<i> - (exp (\<i> * z))\<^sup>2 * \<i>) / (2 * exp (\<i> * z)))))"
    apply (subst csqrt_square)
    using assms Re_sin_pos [of z] Im_sin_nonneg [of z] Im_sin_nonneg2 [of z]
    apply (auto simp: * Re_sin Im_sin)
    done
  also have "... =  - (\<i> * Ln (exp (\<i>*z)))"
    by (simp add: field_simps power2_eq_square)
  also have "... = z"
    using assms
    apply (subst Complex_Transcendental.Ln_exp, auto)
    done
  finally show ?thesis .
qed

lemma Arccos_unique:
    "\<lbrakk>cos z = w;
      0 < Re z \<and> Re z < pi \<or>
      Re z = 0 \<and> 0 \<le> Im z \<or>
      Re z = pi \<and> Im z \<le> 0\<rbrakk> \<Longrightarrow> Arccos w = z"
  using Arccos_cos by blast

lemma Arccos_0 [simp]: "Arccos 0 = pi/2"
  by (rule Arccos_unique) (auto simp: of_real_numeral)

lemma Arccos_1 [simp]: "Arccos 1 = 0"
  by (rule Arccos_unique) auto

lemma Arccos_minus1: "Arccos(-1) = pi"
  by (rule Arccos_unique) auto

lemma has_field_derivative_Arccos:
  assumes "(Im z = 0 \<Longrightarrow> \<bar>Re z\<bar> < 1)"
    shows "(Arccos has_field_derivative - inverse(sin(Arccos z))) (at z)"
proof -
  have "(cos (Arccos z))\<^sup>2 \<noteq> 1"
    using assms
    apply atomize
    apply (auto simp: complex_eq_iff Re_power2 Im_power2 abs_square_eq_1)
    apply (metis abs_minus_cancel abs_one abs_power2 numeral_One numeral_neq_neg_one)
    apply (metis left_minus less_irrefl power_one sum_power2_gt_zero_iff zero_neq_neg_one)
    done
  then have "- sin (Arccos z) \<noteq> 0"
    by (metis cos_squared_eq diff_0_right mult_zero_left neg_0_equal_iff_equal power2_eq_square)
  then have "(Arccos has_field_derivative inverse(- sin(Arccos z))) (at z)"
    apply (rule has_complex_derivative_inverse_basic [OF DERIV_cos _ _ open_ball [of z 1]])
    apply (auto intro: isCont_Arccos assms)
    done
  then show ?thesis
    by simp
qed

declare has_field_derivative_Arcsin [derivative_intros]
declare has_field_derivative_Arcsin [THEN DERIV_chain2, derivative_intros]

lemma field_differentiable_at_Arccos:
    "(Im z = 0 \<Longrightarrow> \<bar>Re z\<bar> < 1) \<Longrightarrow> Arccos field_differentiable at z"
  using field_differentiable_def has_field_derivative_Arccos by blast

lemma field_differentiable_within_Arccos:
    "(Im z = 0 \<Longrightarrow> \<bar>Re z\<bar> < 1) \<Longrightarrow> Arccos field_differentiable (at z within s)"
  using field_differentiable_at_Arccos field_differentiable_within_subset by blast

lemma continuous_within_Arccos:
    "(Im z = 0 \<Longrightarrow> \<bar>Re z\<bar> < 1) \<Longrightarrow> continuous (at z within s) Arccos"
  using continuous_at_imp_continuous_within isCont_Arccos by blast

lemma continuous_on_Arccos [continuous_intros]:
    "(\<And>z. z \<in> s \<Longrightarrow> Im z = 0 \<Longrightarrow> \<bar>Re z\<bar> < 1) \<Longrightarrow> continuous_on s Arccos"
  by (simp add: continuous_at_imp_continuous_on)

lemma holomorphic_on_Arccos: "(\<And>z. z \<in> s \<Longrightarrow> Im z = 0 \<Longrightarrow> \<bar>Re z\<bar> < 1) \<Longrightarrow> Arccos holomorphic_on s"
  by (simp add: field_differentiable_within_Arccos holomorphic_on_def)


subsection\<open>Upper and Lower Bounds for Inverse Sine and Cosine\<close>

lemma Arcsin_bounds: "\<bar>Re z\<bar> < 1 \<Longrightarrow> \<bar>Re(Arcsin z)\<bar> < pi/2"
  unfolding Re_Arcsin
  by (blast intro: Re_Ln_pos_lt_imp Arcsin_range_lemma)

lemma Arccos_bounds: "\<bar>Re z\<bar> < 1 \<Longrightarrow> 0 < Re(Arccos z) \<and> Re(Arccos z) < pi"
  unfolding Re_Arccos
  by (blast intro!: Im_Ln_pos_lt_imp Arccos_range_lemma)

lemma Re_Arccos_bounds: "-pi < Re(Arccos z) \<and> Re(Arccos z) \<le> pi"
  unfolding Re_Arccos
  by (blast intro!: mpi_less_Im_Ln Im_Ln_le_pi Arccos_body_lemma)

lemma Re_Arccos_bound: "\<bar>Re(Arccos z)\<bar> \<le> pi"
  by (meson Re_Arccos_bounds abs_le_iff less_eq_real_def minus_less_iff)

lemma Re_Arcsin_bounds: "-pi < Re(Arcsin z) & Re(Arcsin z) \<le> pi"
  unfolding Re_Arcsin
  by (blast intro!: mpi_less_Im_Ln Im_Ln_le_pi Arcsin_body_lemma)

lemma Re_Arcsin_bound: "\<bar>Re(Arcsin z)\<bar> \<le> pi"
  by (meson Re_Arcsin_bounds abs_le_iff less_eq_real_def minus_less_iff)


subsection\<open>Interrelations between Arcsin and Arccos\<close>

lemma cos_Arcsin_nonzero:
  assumes "z\<^sup>2 \<noteq> 1" shows "cos(Arcsin z) \<noteq> 0"
proof -
  have eq: "(\<i> * z * (csqrt (1 - z\<^sup>2)))\<^sup>2 = z\<^sup>2 * (z\<^sup>2 - 1)"
    by (simp add: power_mult_distrib algebra_simps)
  have "\<i> * z * (csqrt (1 - z\<^sup>2)) \<noteq> z\<^sup>2 - 1"
  proof
    assume "\<i> * z * (csqrt (1 - z\<^sup>2)) = z\<^sup>2 - 1"
    then have "(\<i> * z * (csqrt (1 - z\<^sup>2)))\<^sup>2 = (z\<^sup>2 - 1)\<^sup>2"
      by simp
    then have "z\<^sup>2 * (z\<^sup>2 - 1) = (z\<^sup>2 - 1)*(z\<^sup>2 - 1)"
      using eq power2_eq_square by auto
    then show False
      using assms by simp
  qed
  then have "1 + \<i> * z * (csqrt (1 - z * z)) \<noteq> z\<^sup>2"
    by (metis add_minus_cancel power2_eq_square uminus_add_conv_diff)
  then have "2*(1 + \<i> * z * (csqrt (1 - z * z))) \<noteq> 2*z\<^sup>2"  (*FIXME cancel_numeral_factor*)
    by (metis mult_cancel_left zero_neq_numeral)
  then have "(\<i> * z + csqrt (1 - z\<^sup>2))\<^sup>2 \<noteq> -1"
    using assms
    apply (auto simp: power2_sum)
    apply (simp add: power2_eq_square algebra_simps)
    done
  then show ?thesis
    apply (simp add: cos_exp_eq Arcsin_def exp_minus)
    apply (simp add: divide_simps Arcsin_body_lemma)
    apply (metis add.commute minus_unique power2_eq_square)
    done
qed

lemma sin_Arccos_nonzero:
  assumes "z\<^sup>2 \<noteq> 1" shows "sin(Arccos z) \<noteq> 0"
proof -
  have eq: "(\<i> * z * (csqrt (1 - z\<^sup>2)))\<^sup>2 = -(z\<^sup>2) * (1 - z\<^sup>2)"
    by (simp add: power_mult_distrib algebra_simps)
  have "\<i> * z * (csqrt (1 - z\<^sup>2)) \<noteq> 1 - z\<^sup>2"
  proof
    assume "\<i> * z * (csqrt (1 - z\<^sup>2)) = 1 - z\<^sup>2"
    then have "(\<i> * z * (csqrt (1 - z\<^sup>2)))\<^sup>2 = (1 - z\<^sup>2)\<^sup>2"
      by simp
    then have "-(z\<^sup>2) * (1 - z\<^sup>2) = (1 - z\<^sup>2)*(1 - z\<^sup>2)"
      using eq power2_eq_square by auto
    then have "-(z\<^sup>2) = (1 - z\<^sup>2)"
      using assms
      by (metis add.commute add.right_neutral diff_add_cancel mult_right_cancel)
    then show False
      using assms by simp
  qed
  then have "z\<^sup>2 + \<i> * z * (csqrt (1 - z\<^sup>2)) \<noteq> 1"
    by (simp add: algebra_simps)
  then have "2*(z\<^sup>2 + \<i> * z * (csqrt (1 - z\<^sup>2))) \<noteq> 2*1"
    by (metis mult_cancel_left2 zero_neq_numeral)  (*FIXME cancel_numeral_factor*)
  then have "(z + \<i> * csqrt (1 - z\<^sup>2))\<^sup>2 \<noteq> 1"
    using assms
    apply (auto simp: Power.comm_semiring_1_class.power2_sum power_mult_distrib)
    apply (simp add: power2_eq_square algebra_simps)
    done
  then show ?thesis
    apply (simp add: sin_exp_eq Arccos_def exp_minus)
    apply (simp add: divide_simps Arccos_body_lemma)
    apply (simp add: power2_eq_square)
    done
qed

lemma cos_sin_csqrt:
  assumes "0 < cos(Re z)  \<or>  cos(Re z) = 0 \<and> Im z * sin(Re z) \<le> 0"
    shows "cos z = csqrt(1 - (sin z)\<^sup>2)"
  apply (rule csqrt_unique [THEN sym])
  apply (simp add: cos_squared_eq)
  using assms
  apply (auto simp: Re_cos Im_cos add_pos_pos mult_le_0_iff zero_le_mult_iff)
  done

lemma sin_cos_csqrt:
  assumes "0 < sin(Re z)  \<or>  sin(Re z) = 0 \<and> 0 \<le> Im z * cos(Re z)"
    shows "sin z = csqrt(1 - (cos z)\<^sup>2)"
  apply (rule csqrt_unique [THEN sym])
  apply (simp add: sin_squared_eq)
  using assms
  apply (auto simp: Re_sin Im_sin add_pos_pos mult_le_0_iff zero_le_mult_iff)
  done

lemma Arcsin_Arccos_csqrt_pos:
    "(0 < Re z | Re z = 0 & 0 \<le> Im z) \<Longrightarrow> Arcsin z = Arccos(csqrt(1 - z\<^sup>2))"
  by (simp add: Arcsin_def Arccos_def Complex.csqrt_square add.commute)

lemma Arccos_Arcsin_csqrt_pos:
    "(0 < Re z | Re z = 0 & 0 \<le> Im z) \<Longrightarrow> Arccos z = Arcsin(csqrt(1 - z\<^sup>2))"
  by (simp add: Arcsin_def Arccos_def Complex.csqrt_square add.commute)

lemma sin_Arccos:
    "0 < Re z | Re z = 0 & 0 \<le> Im z \<Longrightarrow> sin(Arccos z) = csqrt(1 - z\<^sup>2)"
  by (simp add: Arccos_Arcsin_csqrt_pos)

lemma cos_Arcsin:
    "0 < Re z | Re z = 0 & 0 \<le> Im z \<Longrightarrow> cos(Arcsin z) = csqrt(1 - z\<^sup>2)"
  by (simp add: Arcsin_Arccos_csqrt_pos)


subsection\<open>Relationship with Arcsin on the Real Numbers\<close>

lemma Im_Arcsin_of_real:
  assumes "\<bar>x\<bar> \<le> 1"
    shows "Im (Arcsin (of_real x)) = 0"
proof -
  have "csqrt (1 - (of_real x)\<^sup>2) = (if x^2 \<le> 1 then sqrt (1 - x^2) else \<i> * sqrt (x^2 - 1))"
    by (simp add: of_real_sqrt del: csqrt_of_real_nonneg)
  then have "cmod (\<i> * of_real x + csqrt (1 - (of_real x)\<^sup>2))^2 = 1"
    using assms abs_square_le_1
    by (force simp add: Complex.cmod_power2)
  then have "cmod (\<i> * of_real x + csqrt (1 - (of_real x)\<^sup>2)) = 1"
    by (simp add: norm_complex_def)
  then show ?thesis
    by (simp add: Im_Arcsin exp_minus)
qed

corollary Arcsin_in_Reals [simp]: "z \<in> \<real> \<Longrightarrow> \<bar>Re z\<bar> \<le> 1 \<Longrightarrow> Arcsin z \<in> \<real>"
  by (metis Im_Arcsin_of_real Re_complex_of_real Reals_cases complex_is_Real_iff)

lemma arcsin_eq_Re_Arcsin:
  assumes "\<bar>x\<bar> \<le> 1"
    shows "arcsin x = Re (Arcsin (of_real x))"
unfolding arcsin_def
proof (rule the_equality, safe)
  show "- (pi / 2) \<le> Re (Arcsin (complex_of_real x))"
    using Re_Ln_pos_le [OF Arcsin_body_lemma, of "of_real x"]
    by (auto simp: Complex.in_Reals_norm Re_Arcsin)
next
  show "Re (Arcsin (complex_of_real x)) \<le> pi / 2"
    using Re_Ln_pos_le [OF Arcsin_body_lemma, of "of_real x"]
    by (auto simp: Complex.in_Reals_norm Re_Arcsin)
next
  show "sin (Re (Arcsin (complex_of_real x))) = x"
    using Re_sin [of "Arcsin (of_real x)"] Arcsin_body_lemma [of "of_real x"]
    by (simp add: Im_Arcsin_of_real assms)
next
  fix x'
  assume "- (pi / 2) \<le> x'" "x' \<le> pi / 2" "x = sin x'"
  then show "x' = Re (Arcsin (complex_of_real (sin x')))"
    apply (simp add: sin_of_real [symmetric])
    apply (subst Arcsin_sin)
    apply (auto simp: )
    done
qed

lemma of_real_arcsin: "\<bar>x\<bar> \<le> 1 \<Longrightarrow> of_real(arcsin x) = Arcsin(of_real x)"
  by (metis Im_Arcsin_of_real add.right_neutral arcsin_eq_Re_Arcsin complex_eq mult_zero_right of_real_0)


subsection\<open>Relationship with Arccos on the Real Numbers\<close>

lemma Im_Arccos_of_real:
  assumes "\<bar>x\<bar> \<le> 1"
    shows "Im (Arccos (of_real x)) = 0"
proof -
  have "csqrt (1 - (of_real x)\<^sup>2) = (if x^2 \<le> 1 then sqrt (1 - x^2) else \<i> * sqrt (x^2 - 1))"
    by (simp add: of_real_sqrt del: csqrt_of_real_nonneg)
  then have "cmod (of_real x + \<i> * csqrt (1 - (of_real x)\<^sup>2))^2 = 1"
    using assms abs_square_le_1
    by (force simp add: Complex.cmod_power2)
  then have "cmod (of_real x + \<i> * csqrt (1 - (of_real x)\<^sup>2)) = 1"
    by (simp add: norm_complex_def)
  then show ?thesis
    by (simp add: Im_Arccos exp_minus)
qed

corollary Arccos_in_Reals [simp]: "z \<in> \<real> \<Longrightarrow> \<bar>Re z\<bar> \<le> 1 \<Longrightarrow> Arccos z \<in> \<real>"
  by (metis Im_Arccos_of_real Re_complex_of_real Reals_cases complex_is_Real_iff)

lemma arccos_eq_Re_Arccos:
  assumes "\<bar>x\<bar> \<le> 1"
    shows "arccos x = Re (Arccos (of_real x))"
unfolding arccos_def
proof (rule the_equality, safe)
  show "0 \<le> Re (Arccos (complex_of_real x))"
    using Im_Ln_pos_le [OF Arccos_body_lemma, of "of_real x"]
    by (auto simp: Complex.in_Reals_norm Re_Arccos)
next
  show "Re (Arccos (complex_of_real x)) \<le> pi"
    using Im_Ln_pos_le [OF Arccos_body_lemma, of "of_real x"]
    by (auto simp: Complex.in_Reals_norm Re_Arccos)
next
  show "cos (Re (Arccos (complex_of_real x))) = x"
    using Re_cos [of "Arccos (of_real x)"] Arccos_body_lemma [of "of_real x"]
    by (simp add: Im_Arccos_of_real assms)
next
  fix x'
  assume "0 \<le> x'" "x' \<le> pi" "x = cos x'"
  then show "x' = Re (Arccos (complex_of_real (cos x')))"
    apply (simp add: cos_of_real [symmetric])
    apply (subst Arccos_cos)
    apply (auto simp: )
    done
qed

lemma of_real_arccos: "\<bar>x\<bar> \<le> 1 \<Longrightarrow> of_real(arccos x) = Arccos(of_real x)"
  by (metis Im_Arccos_of_real add.right_neutral arccos_eq_Re_Arccos complex_eq mult_zero_right of_real_0)

subsection\<open>Some interrelationships among the real inverse trig functions.\<close>

lemma arccos_arctan:
  assumes "-1 < x" "x < 1"
    shows "arccos x = pi/2 - arctan(x / sqrt(1 - x\<^sup>2))"
proof -
  have "arctan(x / sqrt(1 - x\<^sup>2)) - (pi/2 - arccos x) = 0"
  proof (rule sin_eq_0_pi)
    show "- pi < arctan (x / sqrt (1 - x\<^sup>2)) - (pi / 2 - arccos x)"
      using arctan_lbound [of "x / sqrt(1 - x\<^sup>2)"]  arccos_bounded [of x] assms
      by (simp add: algebra_simps)
  next
    show "arctan (x / sqrt (1 - x\<^sup>2)) - (pi / 2 - arccos x) < pi"
      using arctan_ubound [of "x / sqrt(1 - x\<^sup>2)"]  arccos_bounded [of x] assms
      by (simp add: algebra_simps)
  next
    show "sin (arctan (x / sqrt (1 - x\<^sup>2)) - (pi / 2 - arccos x)) = 0"
      using assms
      by (simp add: algebra_simps sin_diff cos_add sin_arccos sin_arctan cos_arctan
                    power2_eq_square square_eq_1_iff)
  qed
  then show ?thesis
    by simp
qed

lemma arcsin_plus_arccos:
  assumes "-1 \<le> x" "x \<le> 1"
    shows "arcsin x + arccos x = pi/2"
proof -
  have "arcsin x = pi/2 - arccos x"
    apply (rule sin_inj_pi)
    using assms arcsin [OF assms] arccos [OF assms]
    apply (auto simp: algebra_simps sin_diff)
    done
  then show ?thesis
    by (simp add: algebra_simps)
qed

lemma arcsin_arccos_eq: "-1 \<le> x \<Longrightarrow> x \<le> 1 \<Longrightarrow> arcsin x = pi/2 - arccos x"
  using arcsin_plus_arccos by force

lemma arccos_arcsin_eq: "-1 \<le> x \<Longrightarrow> x \<le> 1 \<Longrightarrow> arccos x = pi/2 - arcsin x"
  using arcsin_plus_arccos by force

lemma arcsin_arctan: "-1 < x \<Longrightarrow> x < 1 \<Longrightarrow> arcsin x = arctan(x / sqrt(1 - x\<^sup>2))"
  by (simp add: arccos_arctan arcsin_arccos_eq)

lemma csqrt_1_diff_eq: "csqrt (1 - (of_real x)\<^sup>2) = (if x^2 \<le> 1 then sqrt (1 - x^2) else \<i> * sqrt (x^2 - 1))"
  by ( simp add: of_real_sqrt del: csqrt_of_real_nonneg)

lemma arcsin_arccos_sqrt_pos: "0 \<le> x \<Longrightarrow> x \<le> 1 \<Longrightarrow> arcsin x = arccos(sqrt(1 - x\<^sup>2))"
  apply (simp add: abs_square_le_1 arcsin_eq_Re_Arcsin arccos_eq_Re_Arccos)
  apply (subst Arcsin_Arccos_csqrt_pos)
  apply (auto simp: power_le_one csqrt_1_diff_eq)
  done

lemma arcsin_arccos_sqrt_neg: "-1 \<le> x \<Longrightarrow> x \<le> 0 \<Longrightarrow> arcsin x = -arccos(sqrt(1 - x\<^sup>2))"
  using arcsin_arccos_sqrt_pos [of "-x"]
  by (simp add: arcsin_minus)

lemma arccos_arcsin_sqrt_pos: "0 \<le> x \<Longrightarrow> x \<le> 1 \<Longrightarrow> arccos x = arcsin(sqrt(1 - x\<^sup>2))"
  apply (simp add: abs_square_le_1 arcsin_eq_Re_Arcsin arccos_eq_Re_Arccos)
  apply (subst Arccos_Arcsin_csqrt_pos)
  apply (auto simp: power_le_one csqrt_1_diff_eq)
  done

lemma arccos_arcsin_sqrt_neg: "-1 \<le> x \<Longrightarrow> x \<le> 0 \<Longrightarrow> arccos x = pi - arcsin(sqrt(1 - x\<^sup>2))"
  using arccos_arcsin_sqrt_pos [of "-x"]
  by (simp add: arccos_minus)

subsection\<open>continuity results for arcsin and arccos.\<close>

lemma continuous_on_Arcsin_real [continuous_intros]:
    "continuous_on {w \<in> \<real>. \<bar>Re w\<bar> \<le> 1} Arcsin"
proof -
  have "continuous_on {w \<in> \<real>. \<bar>Re w\<bar> \<le> 1} (\<lambda>x. complex_of_real (arcsin (Re x))) =
        continuous_on {w \<in> \<real>. \<bar>Re w\<bar> \<le> 1} (\<lambda>x. complex_of_real (Re (Arcsin (of_real (Re x)))))"
    by (rule continuous_on_cong [OF refl]) (simp add: arcsin_eq_Re_Arcsin)
  also have "... = ?thesis"
    by (rule continuous_on_cong [OF refl]) simp
  finally show ?thesis
    using continuous_on_arcsin [OF continuous_on_Re [OF continuous_on_id], of "{w \<in> \<real>. \<bar>Re w\<bar> \<le> 1}"]
          continuous_on_of_real
    by fastforce
qed

lemma continuous_within_Arcsin_real:
    "continuous (at z within {w \<in> \<real>. \<bar>Re w\<bar> \<le> 1}) Arcsin"
proof (cases "z \<in> {w \<in> \<real>. \<bar>Re w\<bar> \<le> 1}")
  case True then show ?thesis
    using continuous_on_Arcsin_real continuous_on_eq_continuous_within
    by blast
next
  case False
  with closed_real_abs_le [of 1] show ?thesis
    by (rule continuous_within_closed_nontrivial)
qed

lemma continuous_on_Arccos_real:
    "continuous_on {w \<in> \<real>. \<bar>Re w\<bar> \<le> 1} Arccos"
proof -
  have "continuous_on {w \<in> \<real>. \<bar>Re w\<bar> \<le> 1} (\<lambda>x. complex_of_real (arccos (Re x))) =
        continuous_on {w \<in> \<real>. \<bar>Re w\<bar> \<le> 1} (\<lambda>x. complex_of_real (Re (Arccos (of_real (Re x)))))"
    by (rule continuous_on_cong [OF refl]) (simp add: arccos_eq_Re_Arccos)
  also have "... = ?thesis"
    by (rule continuous_on_cong [OF refl]) simp
  finally show ?thesis
    using continuous_on_arccos [OF continuous_on_Re [OF continuous_on_id], of "{w \<in> \<real>. \<bar>Re w\<bar> \<le> 1}"]
          continuous_on_of_real
    by fastforce
qed

lemma continuous_within_Arccos_real:
    "continuous (at z within {w \<in> \<real>. \<bar>Re w\<bar> \<le> 1}) Arccos"
proof (cases "z \<in> {w \<in> \<real>. \<bar>Re w\<bar> \<le> 1}")
  case True then show ?thesis
    using continuous_on_Arccos_real continuous_on_eq_continuous_within
    by blast
next
  case False
  with closed_real_abs_le [of 1] show ?thesis
    by (rule continuous_within_closed_nontrivial)
qed


subsection\<open>Roots of unity\<close>

lemma complex_root_unity:
  fixes j::nat
  assumes "n \<noteq> 0"
    shows "exp(2 * of_real pi * \<i> * of_nat j / of_nat n)^n = 1"
proof -
  have *: "of_nat j * (complex_of_real pi * 2) = complex_of_real (2 * real j * pi)"
    by (simp add: of_real_numeral)
  then show ?thesis
    apply (simp add: exp_of_nat_mult [symmetric] mult_ac exp_Euler)
    apply (simp only: * cos_of_real sin_of_real)
    apply (simp add: )
    done
qed

lemma complex_root_unity_eq:
  fixes j::nat and k::nat
  assumes "1 \<le> n"
    shows "(exp(2 * of_real pi * \<i> * of_nat j / of_nat n) = exp(2 * of_real pi * \<i> * of_nat k / of_nat n)
           \<longleftrightarrow> j mod n = k mod n)"
proof -
    have "(\<exists>z::int. \<i> * (of_nat j * (of_real pi * 2)) =
               \<i> * (of_nat k * (of_real pi * 2)) + \<i> * (of_int z * (of_nat n * (of_real pi * 2)))) \<longleftrightarrow>
          (\<exists>z::int. of_nat j * (\<i> * (of_real pi * 2)) =
              (of_nat k + of_nat n * of_int z) * (\<i> * (of_real pi * 2)))"
      by (simp add: algebra_simps)
    also have "... \<longleftrightarrow> (\<exists>z::int. of_nat j = of_nat k + of_nat n * (of_int z :: complex))"
      by simp
    also have "... \<longleftrightarrow> (\<exists>z::int. of_nat j = of_nat k + of_nat n * z)"
      apply (rule HOL.iff_exI)
      apply (auto simp: )
      using of_int_eq_iff apply fastforce
      by (metis of_int_add of_int_mult of_int_of_nat_eq)
    also have "... \<longleftrightarrow> int j mod int n = int k mod int n"
      by (auto simp: zmod_eq_dvd_iff dvd_def algebra_simps)
    also have "... \<longleftrightarrow> j mod n = k mod n"
      by (metis of_nat_eq_iff zmod_int)
    finally have "(\<exists>z. \<i> * (of_nat j * (of_real pi * 2)) =
             \<i> * (of_nat k * (of_real pi * 2)) + \<i> * (of_int z * (of_nat n * (of_real pi * 2)))) \<longleftrightarrow> j mod n = k mod n" .
   note * = this
  show ?thesis
    using assms
    by (simp add: exp_eq divide_simps mult_ac of_real_numeral *)
qed

corollary bij_betw_roots_unity:
    "bij_betw (\<lambda>j. exp(2 * of_real pi * \<i> * of_nat j / of_nat n))
              {..<n}  {exp(2 * of_real pi * \<i> * of_nat j / of_nat n) | j. j < n}"
  by (auto simp: bij_betw_def inj_on_def complex_root_unity_eq)

lemma complex_root_unity_eq_1:
  fixes j::nat and k::nat
  assumes "1 \<le> n"
    shows "exp(2 * of_real pi * \<i> * of_nat j / of_nat n) = 1 \<longleftrightarrow> n dvd j"
proof -
  have "1 = exp(2 * of_real pi * \<i> * (of_nat n / of_nat n))"
    using assms by simp
  then have "exp(2 * of_real pi * \<i> * (of_nat j / of_nat n)) = 1 \<longleftrightarrow> j mod n = n mod n"
     using complex_root_unity_eq [of n j n] assms
     by simp
  then show ?thesis
    by auto
qed

lemma finite_complex_roots_unity_explicit:
     "finite {exp(2 * of_real pi * \<i> * of_nat j / of_nat n) | j::nat. j < n}"
by simp

lemma card_complex_roots_unity_explicit:
     "card {exp(2 * of_real pi * \<i> * of_nat j / of_nat n) | j::nat. j < n} = n"
  by (simp add:  Finite_Set.bij_betw_same_card [OF bij_betw_roots_unity, symmetric])

lemma complex_roots_unity:
  assumes "1 \<le> n"
    shows "{z::complex. z^n = 1} = {exp(2 * of_real pi * \<i> * of_nat j / of_nat n) | j::nat. j < n}"
  apply (rule Finite_Set.card_seteq [symmetric])
  using assms
  apply (auto simp: card_complex_roots_unity_explicit finite_roots_unity complex_root_unity card_roots_unity)
  done

lemma card_complex_roots_unity: "1 \<le> n \<Longrightarrow> card {z::complex. z^n = 1} = n"
  by (simp add: card_complex_roots_unity_explicit complex_roots_unity)

lemma complex_not_root_unity:
    "1 \<le> n \<Longrightarrow> \<exists>u::complex. norm u = 1 \<and> u^n \<noteq> 1"
  apply (rule_tac x="exp (of_real pi * \<i> * of_real (1 / n))" in exI)
  apply (auto simp: Re_complex_div_eq_0 exp_of_nat_mult [symmetric] mult_ac exp_Euler)
  done

subsection\<open> Formulation of loop homotopy in terms of maps out of type complex\<close>

lemma homotopic_circlemaps_imp_homotopic_loops:
  assumes "homotopic_with (\<lambda>h. True) (sphere 0 1) S f g"
   shows "homotopic_loops S (f \<circ> exp \<circ> (\<lambda>t. 2 * of_real pi * of_real t * \<i>))
                            (g \<circ> exp \<circ> (\<lambda>t. 2 * of_real pi * of_real t * \<i>))"
proof -
  have "homotopic_with (\<lambda>f. True) {z. cmod z = 1} S f g"
    using assms by (auto simp: sphere_def)
  moreover have "continuous_on {0..1} (exp \<circ> (\<lambda>t. 2 * of_real pi * of_real t * \<i>))"
     by (intro continuous_intros)
  moreover have "(exp \<circ> (\<lambda>t. 2 * of_real pi * of_real t * \<i>)) ` {0..1} \<subseteq> {z. cmod z = 1}"
    by (auto simp: norm_mult)
  ultimately
  show ?thesis
    apply (simp add: homotopic_loops_def comp_assoc)
    apply (rule homotopic_with_compose_continuous_right)
      apply (auto simp: pathstart_def pathfinish_def)
    done
qed

lemma homotopic_loops_imp_homotopic_circlemaps:
  assumes "homotopic_loops S p q"
    shows "homotopic_with (\<lambda>h. True) (sphere 0 1) S
                          (p \<circ> (\<lambda>z. (Arg z / (2 * pi))))
                          (q \<circ> (\<lambda>z. (Arg z / (2 * pi))))"
proof -
  obtain h where conth: "continuous_on ({0..1::real} \<times> {0..1}) h"
             and him: "h ` ({0..1} \<times> {0..1}) \<subseteq> S"
             and h0: "(\<forall>x. h (0, x) = p x)"
             and h1: "(\<forall>x. h (1, x) = q x)"
             and h01: "(\<forall>t\<in>{0..1}. h (t, 1) = h (t, 0)) "
    using assms
    by (auto simp: homotopic_loops_def sphere_def homotopic_with_def pathstart_def pathfinish_def)
  define j where "j \<equiv> \<lambda>z. if 0 \<le> Im (snd z)
                          then h (fst z, Arg (snd z) / (2 * pi))
                          else h (fst z, 1 - Arg (cnj (snd z)) / (2 * pi))"
  have Arg_eq: "1 - Arg (cnj y) / (2 * pi) = Arg y / (2 * pi) \<or> Arg y = 0 \<and> Arg (cnj y) = 0" if "cmod y = 1" for y
    using that Arg_eq_0_pi Arg_eq_pi by (force simp: Arg_cnj divide_simps)
  show ?thesis
  proof (simp add: homotopic_with; intro conjI ballI exI)
    show "continuous_on ({0..1} \<times> sphere 0 1) (\<lambda>w. h (fst w, Arg (snd w) / (2 * pi)))"
    proof (rule continuous_on_eq)
      show j: "j x = h (fst x, Arg (snd x) / (2 * pi))" if "x \<in> {0..1} \<times> sphere 0 1" for x
        using Arg_eq that h01 by (force simp: j_def)
      have eq:  "S = S \<inter> (UNIV \<times> {z. 0 \<le> Im z}) \<union> S \<inter> (UNIV \<times> {z. Im z \<le> 0})" for S :: "(real*complex)set"
        by auto
      have c1: "continuous_on ({0..1} \<times> sphere 0 1 \<inter> UNIV \<times> {z. 0 \<le> Im z}) (\<lambda>x. h (fst x, Arg (snd x) / (2 * pi)))"
        apply (intro continuous_intros continuous_on_compose2 [OF conth]  continuous_on_compose2 [OF continuous_on_upperhalf_Arg])
            apply (auto simp: Arg)
        apply (meson Arg_lt_2pi linear not_le)
        done
      have c2: "continuous_on ({0..1} \<times> sphere 0 1 \<inter> UNIV \<times> {z. Im z \<le> 0}) (\<lambda>x. h (fst x, 1 - Arg (cnj (snd x)) / (2 * pi)))"
        apply (intro continuous_intros continuous_on_compose2 [OF conth]  continuous_on_compose2 [OF continuous_on_upperhalf_Arg])
            apply (auto simp: Arg)
        apply (meson Arg_lt_2pi linear not_le)
        done
      show "continuous_on ({0..1} \<times> sphere 0 1) j"
        apply (simp add: j_def)
        apply (subst eq)
        apply (rule continuous_on_cases_local)
            apply (simp_all add: eq [symmetric] closedin_closed_Int closed_Times closed_halfspace_Im_le closed_halfspace_Im_ge c1 c2)
        using Arg_eq h01
        by force
    qed
    have "(\<lambda>w. h (fst w, Arg (snd w) / (2 * pi))) ` ({0..1} \<times> sphere 0 1) \<subseteq> h ` ({0..1} \<times> {0..1})"
      by (auto simp: Arg_ge_0 Arg_lt_2pi less_imp_le)
    also have "... \<subseteq> S"
      using him by blast
    finally show "(\<lambda>w. h (fst w, Arg (snd w) / (2 * pi))) ` ({0..1} \<times> sphere 0 1) \<subseteq> S" .
  qed (auto simp: h0 h1)
qed

lemma simply_connected_homotopic_loops:
  "simply_connected S \<longleftrightarrow>
       (\<forall>p q. homotopic_loops S p p \<and> homotopic_loops S q q \<longrightarrow> homotopic_loops S p q)"
unfolding simply_connected_def using homotopic_loops_refl by metis


lemma simply_connected_eq_homotopic_circlemaps1:
  fixes f :: "complex \<Rightarrow> 'a::topological_space" and g :: "complex \<Rightarrow> 'a"
  assumes S: "simply_connected S"
      and contf: "continuous_on (sphere 0 1) f" and fim: "f ` (sphere 0 1) \<subseteq> S"
      and contg: "continuous_on (sphere 0 1) g" and gim: "g ` (sphere 0 1) \<subseteq> S"
    shows "homotopic_with (\<lambda>h. True) (sphere 0 1) S f g"
proof -
  have "homotopic_loops S (f \<circ> exp \<circ> (\<lambda>t. of_real(2 * pi * t) * \<i>)) (g \<circ> exp \<circ> (\<lambda>t. of_real(2 * pi *  t) * \<i>))"
    apply (rule S [unfolded simply_connected_homotopic_loops, rule_format])
    apply (simp add: homotopic_circlemaps_imp_homotopic_loops homotopic_with_refl contf fim contg gim)
    done
  then show ?thesis
    apply (rule homotopic_with_eq [OF homotopic_loops_imp_homotopic_circlemaps])
      apply (auto simp: o_def complex_norm_eq_1_exp mult.commute)
    done
qed

lemma simply_connected_eq_homotopic_circlemaps2a:
  fixes h :: "complex \<Rightarrow> 'a::topological_space"
  assumes conth: "continuous_on (sphere 0 1) h" and him: "h ` (sphere 0 1) \<subseteq> S"
      and hom: "\<And>f g::complex \<Rightarrow> 'a.
                \<lbrakk>continuous_on (sphere 0 1) f; f ` (sphere 0 1) \<subseteq> S;
                continuous_on (sphere 0 1) g; g ` (sphere 0 1) \<subseteq> S\<rbrakk>
                \<Longrightarrow> homotopic_with (\<lambda>h. True) (sphere 0 1) S f g"
            shows "\<exists>a. homotopic_with (\<lambda>h. True) (sphere 0 1) S h (\<lambda>x. a)"
    apply (rule_tac x="h 1" in exI)
    apply (rule hom)
    using assms
    by (auto simp: continuous_on_const)

lemma simply_connected_eq_homotopic_circlemaps2b:
  fixes S :: "'a::real_normed_vector set"
  assumes "\<And>f g::complex \<Rightarrow> 'a.
                \<lbrakk>continuous_on (sphere 0 1) f; f ` (sphere 0 1) \<subseteq> S;
                continuous_on (sphere 0 1) g; g ` (sphere 0 1) \<subseteq> S\<rbrakk>
                \<Longrightarrow> homotopic_with (\<lambda>h. True) (sphere 0 1) S f g"
  shows "path_connected S"
proof (clarsimp simp add: path_connected_eq_homotopic_points)
  fix a b
  assume "a \<in> S" "b \<in> S"
  then show "homotopic_loops S (linepath a a) (linepath b b)"
    using homotopic_circlemaps_imp_homotopic_loops [OF assms [of "\<lambda>x. a" "\<lambda>x. b"]]
    by (auto simp: o_def continuous_on_const linepath_def)
qed

lemma simply_connected_eq_homotopic_circlemaps3:
  fixes h :: "complex \<Rightarrow> 'a::real_normed_vector"
  assumes "path_connected S"
      and hom: "\<And>f::complex \<Rightarrow> 'a.
                  \<lbrakk>continuous_on (sphere 0 1) f; f `(sphere 0 1) \<subseteq> S\<rbrakk>
                  \<Longrightarrow> \<exists>a. homotopic_with (\<lambda>h. True) (sphere 0 1) S f (\<lambda>x. a)"
    shows "simply_connected S"
proof (clarsimp simp add: simply_connected_eq_contractible_loop_some assms)
  fix p
  assume p: "path p" "path_image p \<subseteq> S" "pathfinish p = pathstart p"
  then have "homotopic_loops S p p"
    by (simp add: homotopic_loops_refl)
  then obtain a where homp: "homotopic_with (\<lambda>h. True) (sphere 0 1) S (p \<circ> (\<lambda>z. Arg z / (2 * pi))) (\<lambda>x. a)"
    by (metis homotopic_with_imp_subset2 homotopic_loops_imp_homotopic_circlemaps homotopic_with_imp_continuous hom)
  show "\<exists>a. a \<in> S \<and> homotopic_loops S p (linepath a a)"
  proof (intro exI conjI)
    show "a \<in> S"
      using homotopic_with_imp_subset2 [OF homp]
      by (metis dist_0_norm image_subset_iff mem_sphere norm_one)
    have teq: "\<And>t. \<lbrakk>0 \<le> t; t \<le> 1\<rbrakk>
               \<Longrightarrow> t = Arg (exp (2 * of_real pi * of_real t * \<i>)) / (2 * pi) \<or> t=1 \<and> Arg (exp (2 * of_real pi * of_real t * \<i>)) = 0"
      apply (rule disjCI)
      using Arg_of_real [of 1] apply (auto simp: Arg_exp)
      done
    have "homotopic_loops S p (p \<circ> (\<lambda>z. Arg z / (2 * pi)) \<circ> exp \<circ> (\<lambda>t. 2 * complex_of_real pi * complex_of_real t * \<i>))"
      apply (rule homotopic_loops_eq [OF p])
      using p teq apply (fastforce simp: pathfinish_def pathstart_def)
      done
    then
    show "homotopic_loops S p (linepath a a)"
      by (simp add: linepath_refl  homotopic_loops_trans [OF _ homotopic_circlemaps_imp_homotopic_loops [OF homp, simplified K_record_comp]])
  qed
qed


proposition simply_connected_eq_homotopic_circlemaps:
  fixes S :: "'a::real_normed_vector set"
  shows "simply_connected S \<longleftrightarrow>
         (\<forall>f g::complex \<Rightarrow> 'a.
              continuous_on (sphere 0 1) f \<and> f ` (sphere 0 1) \<subseteq> S \<and>
              continuous_on (sphere 0 1) g \<and> g ` (sphere 0 1) \<subseteq> S
              \<longrightarrow> homotopic_with (\<lambda>h. True) (sphere 0 1) S f g)"
  apply (rule iffI)
   apply (blast elim: dest: simply_connected_eq_homotopic_circlemaps1)
  by (simp add: simply_connected_eq_homotopic_circlemaps2a simply_connected_eq_homotopic_circlemaps2b simply_connected_eq_homotopic_circlemaps3)

proposition simply_connected_eq_contractible_circlemap:
  fixes S :: "'a::real_normed_vector set"
  shows "simply_connected S \<longleftrightarrow>
         path_connected S \<and>
         (\<forall>f::complex \<Rightarrow> 'a.
              continuous_on (sphere 0 1) f \<and> f `(sphere 0 1) \<subseteq> S
              \<longrightarrow> (\<exists>a. homotopic_with (\<lambda>h. True) (sphere 0 1) S f (\<lambda>x. a)))"
  apply (rule iffI)
   apply (simp add: simply_connected_eq_homotopic_circlemaps1 simply_connected_eq_homotopic_circlemaps2a simply_connected_eq_homotopic_circlemaps2b)
  using simply_connected_eq_homotopic_circlemaps3 by blast

corollary homotopy_eqv_simple_connectedness:
  fixes S :: "'a::real_normed_vector set" and T :: "'b::real_normed_vector set"
  shows "S homotopy_eqv T \<Longrightarrow> simply_connected S \<longleftrightarrow> simply_connected T"
  by (simp add: simply_connected_eq_homotopic_circlemaps homotopy_eqv_homotopic_triviality)

end
