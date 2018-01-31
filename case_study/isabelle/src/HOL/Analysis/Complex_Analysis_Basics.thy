(*  Author: John Harrison, Marco Maggesi, Graziano Gentili, Gianni Ciolli, Valentina Bruno
    Ported from "hol_light/Multivariate/canal.ml" by L C Paulson (2014)
*)

section \<open>Complex Analysis Basics\<close>

theory Complex_Analysis_Basics
imports Equivalence_Lebesgue_Henstock_Integration "~~/src/HOL/Library/Nonpos_Ints"
begin


subsection\<open>General lemmas\<close>

lemma nonneg_Reals_cmod_eq_Re: "z \<in> \<real>\<^sub>\<ge>\<^sub>0 \<Longrightarrow> norm z = Re z"
  by (simp add: complex_nonneg_Reals_iff cmod_eq_Re)

lemma has_derivative_mult_right:
  fixes c:: "'a :: real_normed_algebra"
  shows "((op * c) has_derivative (op * c)) F"
by (rule has_derivative_mult_right [OF has_derivative_id])

lemma has_derivative_of_real[derivative_intros, simp]:
  "(f has_derivative f') F \<Longrightarrow> ((\<lambda>x. of_real (f x)) has_derivative (\<lambda>x. of_real (f' x))) F"
  using bounded_linear.has_derivative[OF bounded_linear_of_real] .

lemma has_vector_derivative_real_complex:
  "DERIV f (of_real a) :> f' \<Longrightarrow> ((\<lambda>x. f (of_real x)) has_vector_derivative f') (at a within s)"
  using has_derivative_compose[of of_real of_real a _ f "op * f'"]
  by (simp add: scaleR_conv_of_real ac_simps has_vector_derivative_def has_field_derivative_def)

lemma fact_cancel:
  fixes c :: "'a::real_field"
  shows "of_nat (Suc n) * c / (fact (Suc n)) = c / (fact n)"
  by (simp add: of_nat_mult del: of_nat_Suc times_nat.simps)

lemma bilinear_times:
  fixes c::"'a::real_algebra" shows "bilinear (\<lambda>x y::'a. x*y)"
  by (auto simp: bilinear_def distrib_left distrib_right intro!: linearI)

lemma linear_cnj: "linear cnj"
  using bounded_linear.linear[OF bounded_linear_cnj] .

lemma tendsto_Re_upper:
  assumes "~ (trivial_limit F)"
          "(f \<longlongrightarrow> l) F"
          "eventually (\<lambda>x. Re(f x) \<le> b) F"
    shows  "Re(l) \<le> b"
  by (metis assms tendsto_le [OF _ tendsto_const]  tendsto_Re)

lemma tendsto_Re_lower:
  assumes "~ (trivial_limit F)"
          "(f \<longlongrightarrow> l) F"
          "eventually (\<lambda>x. b \<le> Re(f x)) F"
    shows  "b \<le> Re(l)"
  by (metis assms tendsto_le [OF _ _ tendsto_const]  tendsto_Re)

lemma tendsto_Im_upper:
  assumes "~ (trivial_limit F)"
          "(f \<longlongrightarrow> l) F"
          "eventually (\<lambda>x. Im(f x) \<le> b) F"
    shows  "Im(l) \<le> b"
  by (metis assms tendsto_le [OF _ tendsto_const]  tendsto_Im)

lemma tendsto_Im_lower:
  assumes "~ (trivial_limit F)"
          "(f \<longlongrightarrow> l) F"
          "eventually (\<lambda>x. b \<le> Im(f x)) F"
    shows  "b \<le> Im(l)"
  by (metis assms tendsto_le [OF _ _ tendsto_const]  tendsto_Im)

lemma lambda_zero: "(\<lambda>h::'a::mult_zero. 0) = op * 0"
  by auto

lemma lambda_one: "(\<lambda>x::'a::monoid_mult. x) = op * 1"
  by auto

lemma continuous_mult_left:
  fixes c::"'a::real_normed_algebra"
  shows "continuous F f \<Longrightarrow> continuous F (\<lambda>x. c * f x)"
by (rule continuous_mult [OF continuous_const])

lemma continuous_mult_right:
  fixes c::"'a::real_normed_algebra"
  shows "continuous F f \<Longrightarrow> continuous F (\<lambda>x. f x * c)"
by (rule continuous_mult [OF _ continuous_const])

lemma continuous_on_mult_left:
  fixes c::"'a::real_normed_algebra"
  shows "continuous_on s f \<Longrightarrow> continuous_on s (\<lambda>x. c * f x)"
by (rule continuous_on_mult [OF continuous_on_const])

lemma continuous_on_mult_right:
  fixes c::"'a::real_normed_algebra"
  shows "continuous_on s f \<Longrightarrow> continuous_on s (\<lambda>x. f x * c)"
by (rule continuous_on_mult [OF _ continuous_on_const])

lemma uniformly_continuous_on_cmul_right [continuous_intros]:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_algebra"
  shows "uniformly_continuous_on s f \<Longrightarrow> uniformly_continuous_on s (\<lambda>x. f x * c)"
  using bounded_linear.uniformly_continuous_on[OF bounded_linear_mult_left] .

lemma uniformly_continuous_on_cmul_left[continuous_intros]:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_algebra"
  assumes "uniformly_continuous_on s f"
    shows "uniformly_continuous_on s (\<lambda>x. c * f x)"
by (metis assms bounded_linear.uniformly_continuous_on bounded_linear_mult_right)

lemma continuous_within_norm_id [continuous_intros]: "continuous (at x within S) norm"
  by (rule continuous_norm [OF continuous_ident])

lemma continuous_on_norm_id [continuous_intros]: "continuous_on S norm"
  by (intro continuous_on_id continuous_on_norm)

subsection\<open>DERIV stuff\<close>

lemma DERIV_zero_connected_constant:
  fixes f :: "'a::{real_normed_field,euclidean_space} \<Rightarrow> 'a"
  assumes "connected s"
      and "open s"
      and "finite k"
      and "continuous_on s f"
      and "\<forall>x\<in>(s - k). DERIV f x :> 0"
    obtains c where "\<And>x. x \<in> s \<Longrightarrow> f(x) = c"
using has_derivative_zero_connected_constant [OF assms(1-4)] assms
by (metis DERIV_const has_derivative_const Diff_iff at_within_open frechet_derivative_at has_field_derivative_def)

lemma DERIV_zero_constant:
  fixes f :: "'a::{real_normed_field, real_inner} \<Rightarrow> 'a"
  shows    "\<lbrakk>convex s;
             \<And>x. x\<in>s \<Longrightarrow> (f has_field_derivative 0) (at x within s)\<rbrakk>
             \<Longrightarrow> \<exists>c. \<forall>x \<in> s. f(x) = c"
  by (auto simp: has_field_derivative_def lambda_zero intro: has_derivative_zero_constant)

lemma DERIV_zero_unique:
  fixes f :: "'a::{real_normed_field, real_inner} \<Rightarrow> 'a"
  assumes "convex s"
      and d0: "\<And>x. x\<in>s \<Longrightarrow> (f has_field_derivative 0) (at x within s)"
      and "a \<in> s"
      and "x \<in> s"
    shows "f x = f a"
  by (rule has_derivative_zero_unique [OF assms(1) _ assms(4,3)])
     (metis d0 has_field_derivative_imp_has_derivative lambda_zero)

lemma DERIV_zero_connected_unique:
  fixes f :: "'a::{real_normed_field, real_inner} \<Rightarrow> 'a"
  assumes "connected s"
      and "open s"
      and d0: "\<And>x. x\<in>s \<Longrightarrow> DERIV f x :> 0"
      and "a \<in> s"
      and "x \<in> s"
    shows "f x = f a"
    by (rule has_derivative_zero_unique_connected [OF assms(2,1) _ assms(5,4)])
       (metis has_field_derivative_def lambda_zero d0)

lemma DERIV_transform_within:
  assumes "(f has_field_derivative f') (at a within s)"
      and "0 < d" "a \<in> s"
      and "\<And>x. x\<in>s \<Longrightarrow> dist x a < d \<Longrightarrow> f x = g x"
    shows "(g has_field_derivative f') (at a within s)"
  using assms unfolding has_field_derivative_def
  by (blast intro: has_derivative_transform_within)

lemma DERIV_transform_within_open:
  assumes "DERIV f a :> f'"
      and "open s" "a \<in> s"
      and "\<And>x. x\<in>s \<Longrightarrow> f x = g x"
    shows "DERIV g a :> f'"
  using assms unfolding has_field_derivative_def
by (metis has_derivative_transform_within_open)

lemma DERIV_transform_at:
  assumes "DERIV f a :> f'"
      and "0 < d"
      and "\<And>x. dist x a < d \<Longrightarrow> f x = g x"
    shows "DERIV g a :> f'"
  by (blast intro: assms DERIV_transform_within)

(*generalising DERIV_isconst_all, which requires type real (using the ordering)*)
lemma DERIV_zero_UNIV_unique:
  fixes f :: "'a::{real_normed_field, real_inner} \<Rightarrow> 'a"
  shows "(\<And>x. DERIV f x :> 0) \<Longrightarrow> f x = f a"
by (metis DERIV_zero_unique UNIV_I convex_UNIV)

subsection \<open>Some limit theorems about real part of real series etc.\<close>

(*MOVE? But not to Finite_Cartesian_Product*)
lemma sums_vec_nth :
  assumes "f sums a"
  shows "(\<lambda>x. f x $ i) sums a $ i"
using assms unfolding sums_def
by (auto dest: tendsto_vec_nth [where i=i])

lemma summable_vec_nth :
  assumes "summable f"
  shows "summable (\<lambda>x. f x $ i)"
using assms unfolding summable_def
by (blast intro: sums_vec_nth)

subsection \<open>Complex number lemmas\<close>

lemma
  shows open_halfspace_Re_lt: "open {z. Re(z) < b}"
    and open_halfspace_Re_gt: "open {z. Re(z) > b}"
    and closed_halfspace_Re_ge: "closed {z. Re(z) \<ge> b}"
    and closed_halfspace_Re_le: "closed {z. Re(z) \<le> b}"
    and closed_halfspace_Re_eq: "closed {z. Re(z) = b}"
    and open_halfspace_Im_lt: "open {z. Im(z) < b}"
    and open_halfspace_Im_gt: "open {z. Im(z) > b}"
    and closed_halfspace_Im_ge: "closed {z. Im(z) \<ge> b}"
    and closed_halfspace_Im_le: "closed {z. Im(z) \<le> b}"
    and closed_halfspace_Im_eq: "closed {z. Im(z) = b}"
  by (intro open_Collect_less closed_Collect_le closed_Collect_eq continuous_on_Re
            continuous_on_Im continuous_on_id continuous_on_const)+

lemma closed_complex_Reals: "closed (\<real> :: complex set)"
proof -
  have "(\<real> :: complex set) = {z. Im z = 0}"
    by (auto simp: complex_is_Real_iff)
  then show ?thesis
    by (metis closed_halfspace_Im_eq)
qed

lemma closed_Real_halfspace_Re_le: "closed (\<real> \<inter> {w. Re w \<le> x})"
  by (simp add: closed_Int closed_complex_Reals closed_halfspace_Re_le)

corollary closed_nonpos_Reals_complex [simp]: "closed (\<real>\<^sub>\<le>\<^sub>0 :: complex set)"
proof -
  have "\<real>\<^sub>\<le>\<^sub>0 = \<real> \<inter> {z. Re(z) \<le> 0}"
    using complex_nonpos_Reals_iff complex_is_Real_iff by auto
  then show ?thesis
    by (metis closed_Real_halfspace_Re_le)
qed

lemma closed_Real_halfspace_Re_ge: "closed (\<real> \<inter> {w. x \<le> Re(w)})"
  using closed_halfspace_Re_ge
  by (simp add: closed_Int closed_complex_Reals)

corollary closed_nonneg_Reals_complex [simp]: "closed (\<real>\<^sub>\<ge>\<^sub>0 :: complex set)"
proof -
  have "\<real>\<^sub>\<ge>\<^sub>0 = \<real> \<inter> {z. Re(z) \<ge> 0}"
    using complex_nonneg_Reals_iff complex_is_Real_iff by auto
  then show ?thesis
    by (metis closed_Real_halfspace_Re_ge)
qed

lemma closed_real_abs_le: "closed {w \<in> \<real>. \<bar>Re w\<bar> \<le> r}"
proof -
  have "{w \<in> \<real>. \<bar>Re w\<bar> \<le> r} = (\<real> \<inter> {w. Re w \<le> r}) \<inter> (\<real> \<inter> {w. Re w \<ge> -r})"
    by auto
  then show "closed {w \<in> \<real>. \<bar>Re w\<bar> \<le> r}"
    by (simp add: closed_Int closed_Real_halfspace_Re_ge closed_Real_halfspace_Re_le)
qed

lemma real_lim:
  fixes l::complex
  assumes "(f \<longlongrightarrow> l) F" and "~(trivial_limit F)" and "eventually P F" and "\<And>a. P a \<Longrightarrow> f a \<in> \<real>"
  shows  "l \<in> \<real>"
proof (rule Lim_in_closed_set[OF closed_complex_Reals _ assms(2,1)])
  show "eventually (\<lambda>x. f x \<in> \<real>) F"
    using assms(3, 4) by (auto intro: eventually_mono)
qed

lemma real_lim_sequentially:
  fixes l::complex
  shows "(f \<longlongrightarrow> l) sequentially \<Longrightarrow> (\<exists>N. \<forall>n\<ge>N. f n \<in> \<real>) \<Longrightarrow> l \<in> \<real>"
by (rule real_lim [where F=sequentially]) (auto simp: eventually_sequentially)

lemma real_series:
  fixes l::complex
  shows "f sums l \<Longrightarrow> (\<And>n. f n \<in> \<real>) \<Longrightarrow> l \<in> \<real>"
unfolding sums_def
by (metis real_lim_sequentially sum_in_Reals)

lemma Lim_null_comparison_Re:
  assumes "eventually (\<lambda>x. norm(f x) \<le> Re(g x)) F" "(g \<longlongrightarrow> 0) F" shows "(f \<longlongrightarrow> 0) F"
  by (rule Lim_null_comparison[OF assms(1)] tendsto_eq_intros assms(2))+ simp

subsection\<open>Holomorphic functions\<close>

subsection\<open>Holomorphic functions\<close>

definition holomorphic_on :: "[complex \<Rightarrow> complex, complex set] \<Rightarrow> bool"
           (infixl "(holomorphic'_on)" 50)
  where "f holomorphic_on s \<equiv> \<forall>x\<in>s. f field_differentiable (at x within s)"

named_theorems holomorphic_intros "structural introduction rules for holomorphic_on"

lemma holomorphic_onI [intro?]: "(\<And>x. x \<in> s \<Longrightarrow> f field_differentiable (at x within s)) \<Longrightarrow> f holomorphic_on s"
  by (simp add: holomorphic_on_def)

lemma holomorphic_onD [dest?]: "\<lbrakk>f holomorphic_on s; x \<in> s\<rbrakk> \<Longrightarrow> f field_differentiable (at x within s)"
  by (simp add: holomorphic_on_def)

lemma holomorphic_on_imp_differentiable_on:
    "f holomorphic_on s \<Longrightarrow> f differentiable_on s"
  unfolding holomorphic_on_def differentiable_on_def
  by (simp add: field_differentiable_imp_differentiable)

lemma holomorphic_on_imp_differentiable_at:
   "\<lbrakk>f holomorphic_on s; open s; x \<in> s\<rbrakk> \<Longrightarrow> f field_differentiable (at x)"
using at_within_open holomorphic_on_def by fastforce

lemma holomorphic_on_empty [holomorphic_intros]: "f holomorphic_on {}"
  by (simp add: holomorphic_on_def)

lemma holomorphic_on_open:
    "open s \<Longrightarrow> f holomorphic_on s \<longleftrightarrow> (\<forall>x \<in> s. \<exists>f'. DERIV f x :> f')"
  by (auto simp: holomorphic_on_def field_differentiable_def has_field_derivative_def at_within_open [of _ s])

lemma holomorphic_on_imp_continuous_on:
    "f holomorphic_on s \<Longrightarrow> continuous_on s f"
  by (metis field_differentiable_imp_continuous_at continuous_on_eq_continuous_within holomorphic_on_def)

lemma holomorphic_on_subset [elim]:
    "f holomorphic_on s \<Longrightarrow> t \<subseteq> s \<Longrightarrow> f holomorphic_on t"
  unfolding holomorphic_on_def
  by (metis field_differentiable_within_subset subsetD)

lemma holomorphic_transform: "\<lbrakk>f holomorphic_on s; \<And>x. x \<in> s \<Longrightarrow> f x = g x\<rbrakk> \<Longrightarrow> g holomorphic_on s"
  by (metis field_differentiable_transform_within linordered_field_no_ub holomorphic_on_def)

lemma holomorphic_cong: "s = t ==> (\<And>x. x \<in> s \<Longrightarrow> f x = g x) \<Longrightarrow> f holomorphic_on s \<longleftrightarrow> g holomorphic_on t"
  by (metis holomorphic_transform)

lemma holomorphic_on_linear [simp, holomorphic_intros]: "(op * c) holomorphic_on s"
  unfolding holomorphic_on_def by (metis field_differentiable_linear)

lemma holomorphic_on_const [simp, holomorphic_intros]: "(\<lambda>z. c) holomorphic_on s"
  unfolding holomorphic_on_def by (metis field_differentiable_const)

lemma holomorphic_on_ident [simp, holomorphic_intros]: "(\<lambda>x. x) holomorphic_on s"
  unfolding holomorphic_on_def by (metis field_differentiable_ident)

lemma holomorphic_on_id [simp, holomorphic_intros]: "id holomorphic_on s"
  unfolding id_def by (rule holomorphic_on_ident)

lemma holomorphic_on_compose:
  "f holomorphic_on s \<Longrightarrow> g holomorphic_on (f ` s) \<Longrightarrow> (g o f) holomorphic_on s"
  using field_differentiable_compose_within[of f _ s g]
  by (auto simp: holomorphic_on_def)

lemma holomorphic_on_compose_gen:
  "f holomorphic_on s \<Longrightarrow> g holomorphic_on t \<Longrightarrow> f ` s \<subseteq> t \<Longrightarrow> (g o f) holomorphic_on s"
  by (metis holomorphic_on_compose holomorphic_on_subset)

lemma holomorphic_on_minus [holomorphic_intros]: "f holomorphic_on s \<Longrightarrow> (\<lambda>z. -(f z)) holomorphic_on s"
  by (metis field_differentiable_minus holomorphic_on_def)

lemma holomorphic_on_add [holomorphic_intros]:
  "\<lbrakk>f holomorphic_on s; g holomorphic_on s\<rbrakk> \<Longrightarrow> (\<lambda>z. f z + g z) holomorphic_on s"
  unfolding holomorphic_on_def by (metis field_differentiable_add)

lemma holomorphic_on_diff [holomorphic_intros]:
  "\<lbrakk>f holomorphic_on s; g holomorphic_on s\<rbrakk> \<Longrightarrow> (\<lambda>z. f z - g z) holomorphic_on s"
  unfolding holomorphic_on_def by (metis field_differentiable_diff)

lemma holomorphic_on_mult [holomorphic_intros]:
  "\<lbrakk>f holomorphic_on s; g holomorphic_on s\<rbrakk> \<Longrightarrow> (\<lambda>z. f z * g z) holomorphic_on s"
  unfolding holomorphic_on_def by (metis field_differentiable_mult)

lemma holomorphic_on_inverse [holomorphic_intros]:
  "\<lbrakk>f holomorphic_on s; \<And>z. z \<in> s \<Longrightarrow> f z \<noteq> 0\<rbrakk> \<Longrightarrow> (\<lambda>z. inverse (f z)) holomorphic_on s"
  unfolding holomorphic_on_def by (metis field_differentiable_inverse)

lemma holomorphic_on_divide [holomorphic_intros]:
  "\<lbrakk>f holomorphic_on s; g holomorphic_on s; \<And>z. z \<in> s \<Longrightarrow> g z \<noteq> 0\<rbrakk> \<Longrightarrow> (\<lambda>z. f z / g z) holomorphic_on s"
  unfolding holomorphic_on_def by (metis field_differentiable_divide)

lemma holomorphic_on_power [holomorphic_intros]:
  "f holomorphic_on s \<Longrightarrow> (\<lambda>z. (f z)^n) holomorphic_on s"
  unfolding holomorphic_on_def by (metis field_differentiable_power)

lemma holomorphic_on_sum [holomorphic_intros]:
  "(\<And>i. i \<in> I \<Longrightarrow> (f i) holomorphic_on s) \<Longrightarrow> (\<lambda>x. sum (\<lambda>i. f i x) I) holomorphic_on s"
  unfolding holomorphic_on_def by (metis field_differentiable_sum)

lemma DERIV_deriv_iff_field_differentiable:
  "DERIV f x :> deriv f x \<longleftrightarrow> f field_differentiable at x"
  unfolding field_differentiable_def by (metis DERIV_imp_deriv)

lemma holomorphic_derivI:
     "\<lbrakk>f holomorphic_on S; open S; x \<in> S\<rbrakk>
      \<Longrightarrow> (f has_field_derivative deriv f x) (at x within T)"
by (metis DERIV_deriv_iff_field_differentiable at_within_open  holomorphic_on_def has_field_derivative_at_within)

lemma complex_derivative_chain:
  "f field_differentiable at x \<Longrightarrow> g field_differentiable at (f x)
    \<Longrightarrow> deriv (g o f) x = deriv g (f x) * deriv f x"
  by (metis DERIV_deriv_iff_field_differentiable DERIV_chain DERIV_imp_deriv)

lemma deriv_linear [simp]: "deriv (\<lambda>w. c * w) = (\<lambda>z. c)"
  by (metis DERIV_imp_deriv DERIV_cmult_Id)

lemma deriv_ident [simp]: "deriv (\<lambda>w. w) = (\<lambda>z. 1)"
  by (metis DERIV_imp_deriv DERIV_ident)

lemma deriv_id [simp]: "deriv id = (\<lambda>z. 1)"
  by (simp add: id_def)

lemma deriv_const [simp]: "deriv (\<lambda>w. c) = (\<lambda>z. 0)"
  by (metis DERIV_imp_deriv DERIV_const)

lemma deriv_add [simp]:
  "\<lbrakk>f field_differentiable at z; g field_differentiable at z\<rbrakk>
   \<Longrightarrow> deriv (\<lambda>w. f w + g w) z = deriv f z + deriv g z"
  unfolding DERIV_deriv_iff_field_differentiable[symmetric]
  by (auto intro!: DERIV_imp_deriv derivative_intros)

lemma deriv_diff [simp]:
  "\<lbrakk>f field_differentiable at z; g field_differentiable at z\<rbrakk>
   \<Longrightarrow> deriv (\<lambda>w. f w - g w) z = deriv f z - deriv g z"
  unfolding DERIV_deriv_iff_field_differentiable[symmetric]
  by (auto intro!: DERIV_imp_deriv derivative_intros)

lemma deriv_mult [simp]:
  "\<lbrakk>f field_differentiable at z; g field_differentiable at z\<rbrakk>
   \<Longrightarrow> deriv (\<lambda>w. f w * g w) z = f z * deriv g z + deriv f z * g z"
  unfolding DERIV_deriv_iff_field_differentiable[symmetric]
  by (auto intro!: DERIV_imp_deriv derivative_eq_intros)

lemma deriv_cmult [simp]:
  "f field_differentiable at z \<Longrightarrow> deriv (\<lambda>w. c * f w) z = c * deriv f z"
  unfolding DERIV_deriv_iff_field_differentiable[symmetric]
  by (auto intro!: DERIV_imp_deriv derivative_eq_intros)

lemma deriv_cmult_right [simp]:
  "f field_differentiable at z \<Longrightarrow> deriv (\<lambda>w. f w * c) z = deriv f z * c"
  unfolding DERIV_deriv_iff_field_differentiable[symmetric]
  by (auto intro!: DERIV_imp_deriv derivative_eq_intros)

lemma deriv_cdivide_right [simp]:
  "f field_differentiable at z \<Longrightarrow> deriv (\<lambda>w. f w / c) z = deriv f z / c"
  unfolding Fields.field_class.field_divide_inverse
  by (blast intro: deriv_cmult_right)

lemma complex_derivative_transform_within_open:
  "\<lbrakk>f holomorphic_on s; g holomorphic_on s; open s; z \<in> s; \<And>w. w \<in> s \<Longrightarrow> f w = g w\<rbrakk>
   \<Longrightarrow> deriv f z = deriv g z"
  unfolding holomorphic_on_def
  by (rule DERIV_imp_deriv)
     (metis DERIV_deriv_iff_field_differentiable DERIV_transform_within_open at_within_open)

lemma deriv_compose_linear:
  "f field_differentiable at (c * z) \<Longrightarrow> deriv (\<lambda>w. f (c * w)) z = c * deriv f (c * z)"
apply (rule DERIV_imp_deriv)
apply (simp add: DERIV_deriv_iff_field_differentiable [symmetric])
apply (drule DERIV_chain' [of "times c" c z UNIV f "deriv f (c * z)", OF DERIV_cmult_Id])
apply (simp add: algebra_simps)
done

lemma nonzero_deriv_nonconstant:
  assumes df: "DERIV f \<xi> :> df" and S: "open S" "\<xi> \<in> S" and "df \<noteq> 0"
    shows "\<not> f constant_on S"
unfolding constant_on_def
by (metis \<open>df \<noteq> 0\<close> DERIV_transform_within_open [OF df S] DERIV_const DERIV_unique)

lemma holomorphic_nonconstant:
  assumes holf: "f holomorphic_on S" and "open S" "\<xi> \<in> S" "deriv f \<xi> \<noteq> 0"
    shows "\<not> f constant_on S"
    apply (rule nonzero_deriv_nonconstant [of f "deriv f \<xi>" \<xi> S])
    using assms
    apply (auto simp: holomorphic_derivI)
    done

subsection\<open>Caratheodory characterization\<close>

lemma field_differentiable_caratheodory_at:
  "f field_differentiable (at z) \<longleftrightarrow>
         (\<exists>g. (\<forall>w. f(w) - f(z) = g(w) * (w - z)) \<and> continuous (at z) g)"
  using CARAT_DERIV [of f]
  by (simp add: field_differentiable_def has_field_derivative_def)

lemma field_differentiable_caratheodory_within:
  "f field_differentiable (at z within s) \<longleftrightarrow>
         (\<exists>g. (\<forall>w. f(w) - f(z) = g(w) * (w - z)) \<and> continuous (at z within s) g)"
  using DERIV_caratheodory_within [of f]
  by (simp add: field_differentiable_def has_field_derivative_def)

subsection\<open>Analyticity on a set\<close>

definition analytic_on (infixl "(analytic'_on)" 50)
  where
   "f analytic_on s \<equiv> \<forall>x \<in> s. \<exists>e. 0 < e \<and> f holomorphic_on (ball x e)"

lemma analytic_imp_holomorphic: "f analytic_on s \<Longrightarrow> f holomorphic_on s"
  by (simp add: at_within_open [OF _ open_ball] analytic_on_def holomorphic_on_def)
     (metis centre_in_ball field_differentiable_at_within)

lemma analytic_on_open: "open s \<Longrightarrow> f analytic_on s \<longleftrightarrow> f holomorphic_on s"
apply (auto simp: analytic_imp_holomorphic)
apply (auto simp: analytic_on_def holomorphic_on_def)
by (metis holomorphic_on_def holomorphic_on_subset open_contains_ball)

lemma analytic_on_imp_differentiable_at:
  "f analytic_on s \<Longrightarrow> x \<in> s \<Longrightarrow> f field_differentiable (at x)"
 apply (auto simp: analytic_on_def holomorphic_on_def)
by (metis Topology_Euclidean_Space.open_ball centre_in_ball field_differentiable_within_open)

lemma analytic_on_subset: "f analytic_on s \<Longrightarrow> t \<subseteq> s \<Longrightarrow> f analytic_on t"
  by (auto simp: analytic_on_def)

lemma analytic_on_Un: "f analytic_on (s \<union> t) \<longleftrightarrow> f analytic_on s \<and> f analytic_on t"
  by (auto simp: analytic_on_def)

lemma analytic_on_Union: "f analytic_on (\<Union>s) \<longleftrightarrow> (\<forall>t \<in> s. f analytic_on t)"
  by (auto simp: analytic_on_def)

lemma analytic_on_UN: "f analytic_on (\<Union>i\<in>I. s i) \<longleftrightarrow> (\<forall>i\<in>I. f analytic_on (s i))"
  by (auto simp: analytic_on_def)

lemma analytic_on_holomorphic:
  "f analytic_on s \<longleftrightarrow> (\<exists>t. open t \<and> s \<subseteq> t \<and> f holomorphic_on t)"
  (is "?lhs = ?rhs")
proof -
  have "?lhs \<longleftrightarrow> (\<exists>t. open t \<and> s \<subseteq> t \<and> f analytic_on t)"
  proof safe
    assume "f analytic_on s"
    then show "\<exists>t. open t \<and> s \<subseteq> t \<and> f analytic_on t"
      apply (simp add: analytic_on_def)
      apply (rule exI [where x="\<Union>{u. open u \<and> f analytic_on u}"], auto)
      apply (metis Topology_Euclidean_Space.open_ball analytic_on_open centre_in_ball)
      by (metis analytic_on_def)
  next
    fix t
    assume "open t" "s \<subseteq> t" "f analytic_on t"
    then show "f analytic_on s"
        by (metis analytic_on_subset)
  qed
  also have "... \<longleftrightarrow> ?rhs"
    by (auto simp: analytic_on_open)
  finally show ?thesis .
qed

lemma analytic_on_linear: "(op * c) analytic_on s"
  by (auto simp add: analytic_on_holomorphic holomorphic_on_linear)

lemma analytic_on_const: "(\<lambda>z. c) analytic_on s"
  by (metis analytic_on_def holomorphic_on_const zero_less_one)

lemma analytic_on_ident: "(\<lambda>x. x) analytic_on s"
  by (simp add: analytic_on_def holomorphic_on_ident gt_ex)

lemma analytic_on_id: "id analytic_on s"
  unfolding id_def by (rule analytic_on_ident)

lemma analytic_on_compose:
  assumes f: "f analytic_on s"
      and g: "g analytic_on (f ` s)"
    shows "(g o f) analytic_on s"
unfolding analytic_on_def
proof (intro ballI)
  fix x
  assume x: "x \<in> s"
  then obtain e where e: "0 < e" and fh: "f holomorphic_on ball x e" using f
    by (metis analytic_on_def)
  obtain e' where e': "0 < e'" and gh: "g holomorphic_on ball (f x) e'" using g
    by (metis analytic_on_def g image_eqI x)
  have "isCont f x"
    by (metis analytic_on_imp_differentiable_at field_differentiable_imp_continuous_at f x)
  with e' obtain d where d: "0 < d" and fd: "f ` ball x d \<subseteq> ball (f x) e'"
     by (auto simp: continuous_at_ball)
  have "g \<circ> f holomorphic_on ball x (min d e)"
    apply (rule holomorphic_on_compose)
    apply (metis fh holomorphic_on_subset min.bounded_iff order_refl subset_ball)
    by (metis fd gh holomorphic_on_subset image_mono min.cobounded1 subset_ball)
  then show "\<exists>e>0. g \<circ> f holomorphic_on ball x e"
    by (metis d e min_less_iff_conj)
qed

lemma analytic_on_compose_gen:
  "f analytic_on s \<Longrightarrow> g analytic_on t \<Longrightarrow> (\<And>z. z \<in> s \<Longrightarrow> f z \<in> t)
             \<Longrightarrow> g o f analytic_on s"
by (metis analytic_on_compose analytic_on_subset image_subset_iff)

lemma analytic_on_neg:
  "f analytic_on s \<Longrightarrow> (\<lambda>z. -(f z)) analytic_on s"
by (metis analytic_on_holomorphic holomorphic_on_minus)

lemma analytic_on_add:
  assumes f: "f analytic_on s"
      and g: "g analytic_on s"
    shows "(\<lambda>z. f z + g z) analytic_on s"
unfolding analytic_on_def
proof (intro ballI)
  fix z
  assume z: "z \<in> s"
  then obtain e where e: "0 < e" and fh: "f holomorphic_on ball z e" using f
    by (metis analytic_on_def)
  obtain e' where e': "0 < e'" and gh: "g holomorphic_on ball z e'" using g
    by (metis analytic_on_def g z)
  have "(\<lambda>z. f z + g z) holomorphic_on ball z (min e e')"
    apply (rule holomorphic_on_add)
    apply (metis fh holomorphic_on_subset min.bounded_iff order_refl subset_ball)
    by (metis gh holomorphic_on_subset min.bounded_iff order_refl subset_ball)
  then show "\<exists>e>0. (\<lambda>z. f z + g z) holomorphic_on ball z e"
    by (metis e e' min_less_iff_conj)
qed

lemma analytic_on_diff:
  assumes f: "f analytic_on s"
      and g: "g analytic_on s"
    shows "(\<lambda>z. f z - g z) analytic_on s"
unfolding analytic_on_def
proof (intro ballI)
  fix z
  assume z: "z \<in> s"
  then obtain e where e: "0 < e" and fh: "f holomorphic_on ball z e" using f
    by (metis analytic_on_def)
  obtain e' where e': "0 < e'" and gh: "g holomorphic_on ball z e'" using g
    by (metis analytic_on_def g z)
  have "(\<lambda>z. f z - g z) holomorphic_on ball z (min e e')"
    apply (rule holomorphic_on_diff)
    apply (metis fh holomorphic_on_subset min.bounded_iff order_refl subset_ball)
    by (metis gh holomorphic_on_subset min.bounded_iff order_refl subset_ball)
  then show "\<exists>e>0. (\<lambda>z. f z - g z) holomorphic_on ball z e"
    by (metis e e' min_less_iff_conj)
qed

lemma analytic_on_mult:
  assumes f: "f analytic_on s"
      and g: "g analytic_on s"
    shows "(\<lambda>z. f z * g z) analytic_on s"
unfolding analytic_on_def
proof (intro ballI)
  fix z
  assume z: "z \<in> s"
  then obtain e where e: "0 < e" and fh: "f holomorphic_on ball z e" using f
    by (metis analytic_on_def)
  obtain e' where e': "0 < e'" and gh: "g holomorphic_on ball z e'" using g
    by (metis analytic_on_def g z)
  have "(\<lambda>z. f z * g z) holomorphic_on ball z (min e e')"
    apply (rule holomorphic_on_mult)
    apply (metis fh holomorphic_on_subset min.bounded_iff order_refl subset_ball)
    by (metis gh holomorphic_on_subset min.bounded_iff order_refl subset_ball)
  then show "\<exists>e>0. (\<lambda>z. f z * g z) holomorphic_on ball z e"
    by (metis e e' min_less_iff_conj)
qed

lemma analytic_on_inverse:
  assumes f: "f analytic_on s"
      and nz: "(\<And>z. z \<in> s \<Longrightarrow> f z \<noteq> 0)"
    shows "(\<lambda>z. inverse (f z)) analytic_on s"
unfolding analytic_on_def
proof (intro ballI)
  fix z
  assume z: "z \<in> s"
  then obtain e where e: "0 < e" and fh: "f holomorphic_on ball z e" using f
    by (metis analytic_on_def)
  have "continuous_on (ball z e) f"
    by (metis fh holomorphic_on_imp_continuous_on)
  then obtain e' where e': "0 < e'" and nz': "\<And>y. dist z y < e' \<Longrightarrow> f y \<noteq> 0"
    by (metis Topology_Euclidean_Space.open_ball centre_in_ball continuous_on_open_avoid e z nz)
  have "(\<lambda>z. inverse (f z)) holomorphic_on ball z (min e e')"
    apply (rule holomorphic_on_inverse)
    apply (metis fh holomorphic_on_subset min.cobounded2 min.commute subset_ball)
    by (metis nz' mem_ball min_less_iff_conj)
  then show "\<exists>e>0. (\<lambda>z. inverse (f z)) holomorphic_on ball z e"
    by (metis e e' min_less_iff_conj)
qed

lemma analytic_on_divide:
  assumes f: "f analytic_on s"
      and g: "g analytic_on s"
      and nz: "(\<And>z. z \<in> s \<Longrightarrow> g z \<noteq> 0)"
    shows "(\<lambda>z. f z / g z) analytic_on s"
unfolding divide_inverse
by (metis analytic_on_inverse analytic_on_mult f g nz)

lemma analytic_on_power:
  "f analytic_on s \<Longrightarrow> (\<lambda>z. (f z) ^ n) analytic_on s"
by (induct n) (auto simp: analytic_on_const analytic_on_mult)

lemma analytic_on_sum:
  "(\<And>i. i \<in> I \<Longrightarrow> (f i) analytic_on s) \<Longrightarrow> (\<lambda>x. sum (\<lambda>i. f i x) I) analytic_on s"
  by (induct I rule: infinite_finite_induct) (auto simp: analytic_on_const analytic_on_add)

lemma deriv_left_inverse:
  assumes "f holomorphic_on S" and "g holomorphic_on T"
      and "open S" and "open T"
      and "f ` S \<subseteq> T"
      and [simp]: "\<And>z. z \<in> S \<Longrightarrow> g (f z) = z"
      and "w \<in> S"
    shows "deriv f w * deriv g (f w) = 1"
proof -
  have "deriv f w * deriv g (f w) = deriv g (f w) * deriv f w"
    by (simp add: algebra_simps)
  also have "... = deriv (g o f) w"
    using assms
    by (metis analytic_on_imp_differentiable_at analytic_on_open complex_derivative_chain image_subset_iff)
  also have "... = deriv id w"
    apply (rule complex_derivative_transform_within_open [where s=S])
    apply (rule assms holomorphic_on_compose_gen holomorphic_intros)+
    apply simp
    done
  also have "... = 1"
    by simp
  finally show ?thesis .
qed

subsection\<open>analyticity at a point\<close>

lemma analytic_at_ball:
  "f analytic_on {z} \<longleftrightarrow> (\<exists>e. 0<e \<and> f holomorphic_on ball z e)"
by (metis analytic_on_def singleton_iff)

lemma analytic_at:
    "f analytic_on {z} \<longleftrightarrow> (\<exists>s. open s \<and> z \<in> s \<and> f holomorphic_on s)"
by (metis analytic_on_holomorphic empty_subsetI insert_subset)

lemma analytic_on_analytic_at:
    "f analytic_on s \<longleftrightarrow> (\<forall>z \<in> s. f analytic_on {z})"
by (metis analytic_at_ball analytic_on_def)

lemma analytic_at_two:
  "f analytic_on {z} \<and> g analytic_on {z} \<longleftrightarrow>
   (\<exists>s. open s \<and> z \<in> s \<and> f holomorphic_on s \<and> g holomorphic_on s)"
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  then obtain s t
    where st: "open s" "z \<in> s" "f holomorphic_on s"
              "open t" "z \<in> t" "g holomorphic_on t"
    by (auto simp: analytic_at)
  show ?rhs
    apply (rule_tac x="s \<inter> t" in exI)
    using st
    apply (auto simp: Diff_subset holomorphic_on_subset)
    done
next
  assume ?rhs
  then show ?lhs
    by (force simp add: analytic_at)
qed

subsection\<open>Combining theorems for derivative with ``analytic at'' hypotheses\<close>

lemma
  assumes "f analytic_on {z}" "g analytic_on {z}"
  shows complex_derivative_add_at: "deriv (\<lambda>w. f w + g w) z = deriv f z + deriv g z"
    and complex_derivative_diff_at: "deriv (\<lambda>w. f w - g w) z = deriv f z - deriv g z"
    and complex_derivative_mult_at: "deriv (\<lambda>w. f w * g w) z =
           f z * deriv g z + deriv f z * g z"
proof -
  obtain s where s: "open s" "z \<in> s" "f holomorphic_on s" "g holomorphic_on s"
    using assms by (metis analytic_at_two)
  show "deriv (\<lambda>w. f w + g w) z = deriv f z + deriv g z"
    apply (rule DERIV_imp_deriv [OF DERIV_add])
    using s
    apply (auto simp: holomorphic_on_open field_differentiable_def DERIV_deriv_iff_field_differentiable)
    done
  show "deriv (\<lambda>w. f w - g w) z = deriv f z - deriv g z"
    apply (rule DERIV_imp_deriv [OF DERIV_diff])
    using s
    apply (auto simp: holomorphic_on_open field_differentiable_def DERIV_deriv_iff_field_differentiable)
    done
  show "deriv (\<lambda>w. f w * g w) z = f z * deriv g z + deriv f z * g z"
    apply (rule DERIV_imp_deriv [OF DERIV_mult'])
    using s
    apply (auto simp: holomorphic_on_open field_differentiable_def DERIV_deriv_iff_field_differentiable)
    done
qed

lemma deriv_cmult_at:
  "f analytic_on {z} \<Longrightarrow>  deriv (\<lambda>w. c * f w) z = c * deriv f z"
by (auto simp: complex_derivative_mult_at deriv_const analytic_on_const)

lemma deriv_cmult_right_at:
  "f analytic_on {z} \<Longrightarrow>  deriv (\<lambda>w. f w * c) z = deriv f z * c"
by (auto simp: complex_derivative_mult_at deriv_const analytic_on_const)

subsection\<open>Complex differentiation of sequences and series\<close>

(* TODO: Could probably be simplified using Uniform_Limit *)
lemma has_complex_derivative_sequence:
  fixes s :: "complex set"
  assumes cvs: "convex s"
      and df:  "\<And>n x. x \<in> s \<Longrightarrow> (f n has_field_derivative f' n x) (at x within s)"
      and conv: "\<And>e. 0 < e \<Longrightarrow> \<exists>N. \<forall>n x. n \<ge> N \<longrightarrow> x \<in> s \<longrightarrow> norm (f' n x - g' x) \<le> e"
      and "\<exists>x l. x \<in> s \<and> ((\<lambda>n. f n x) \<longlongrightarrow> l) sequentially"
    shows "\<exists>g. \<forall>x \<in> s. ((\<lambda>n. f n x) \<longlongrightarrow> g x) sequentially \<and>
                       (g has_field_derivative (g' x)) (at x within s)"
proof -
  from assms obtain x l where x: "x \<in> s" and tf: "((\<lambda>n. f n x) \<longlongrightarrow> l) sequentially"
    by blast
  { fix e::real assume e: "e > 0"
    then obtain N where N: "\<forall>n\<ge>N. \<forall>x. x \<in> s \<longrightarrow> cmod (f' n x - g' x) \<le> e"
      by (metis conv)
    have "\<exists>N. \<forall>n\<ge>N. \<forall>x\<in>s. \<forall>h. cmod (f' n x * h - g' x * h) \<le> e * cmod h"
    proof (rule exI [of _ N], clarify)
      fix n y h
      assume "N \<le> n" "y \<in> s"
      then have "cmod (f' n y - g' y) \<le> e"
        by (metis N)
      then have "cmod h * cmod (f' n y - g' y) \<le> cmod h * e"
        by (auto simp: antisym_conv2 mult_le_cancel_left norm_triangle_ineq2)
      then show "cmod (f' n y * h - g' y * h) \<le> e * cmod h"
        by (simp add: norm_mult [symmetric] field_simps)
    qed
  } note ** = this
  show ?thesis
  unfolding has_field_derivative_def
  proof (rule has_derivative_sequence [OF cvs _ _ x])
    show "\<forall>n. \<forall>x\<in>s. (f n has_derivative (op * (f' n x))) (at x within s)"
      by (metis has_field_derivative_def df)
  next show "(\<lambda>n. f n x) \<longlonglongrightarrow> l"
    by (rule tf)
  next show "\<forall>e>0. \<exists>N. \<forall>n\<ge>N. \<forall>x\<in>s. \<forall>h. cmod (f' n x * h - g' x * h) \<le> e * cmod h"
    by (blast intro: **)
  qed
qed

lemma has_complex_derivative_series:
  fixes s :: "complex set"
  assumes cvs: "convex s"
      and df:  "\<And>n x. x \<in> s \<Longrightarrow> (f n has_field_derivative f' n x) (at x within s)"
      and conv: "\<And>e. 0 < e \<Longrightarrow> \<exists>N. \<forall>n x. n \<ge> N \<longrightarrow> x \<in> s
                \<longrightarrow> cmod ((\<Sum>i<n. f' i x) - g' x) \<le> e"
      and "\<exists>x l. x \<in> s \<and> ((\<lambda>n. f n x) sums l)"
    shows "\<exists>g. \<forall>x \<in> s. ((\<lambda>n. f n x) sums g x) \<and> ((g has_field_derivative g' x) (at x within s))"
proof -
  from assms obtain x l where x: "x \<in> s" and sf: "((\<lambda>n. f n x) sums l)"
    by blast
  { fix e::real assume e: "e > 0"
    then obtain N where N: "\<forall>n x. n \<ge> N \<longrightarrow> x \<in> s
            \<longrightarrow> cmod ((\<Sum>i<n. f' i x) - g' x) \<le> e"
      by (metis conv)
    have "\<exists>N. \<forall>n\<ge>N. \<forall>x\<in>s. \<forall>h. cmod ((\<Sum>i<n. h * f' i x) - g' x * h) \<le> e * cmod h"
    proof (rule exI [of _ N], clarify)
      fix n y h
      assume "N \<le> n" "y \<in> s"
      then have "cmod ((\<Sum>i<n. f' i y) - g' y) \<le> e"
        by (metis N)
      then have "cmod h * cmod ((\<Sum>i<n. f' i y) - g' y) \<le> cmod h * e"
        by (auto simp: antisym_conv2 mult_le_cancel_left norm_triangle_ineq2)
      then show "cmod ((\<Sum>i<n. h * f' i y) - g' y * h) \<le> e * cmod h"
        by (simp add: norm_mult [symmetric] field_simps sum_distrib_left)
    qed
  } note ** = this
  show ?thesis
  unfolding has_field_derivative_def
  proof (rule has_derivative_series [OF cvs _ _ x])
    fix n x
    assume "x \<in> s"
    then show "((f n) has_derivative (\<lambda>z. z * f' n x)) (at x within s)"
      by (metis df has_field_derivative_def mult_commute_abs)
  next show " ((\<lambda>n. f n x) sums l)"
    by (rule sf)
  next show "\<forall>e>0. \<exists>N. \<forall>n\<ge>N. \<forall>x\<in>s. \<forall>h. cmod ((\<Sum>i<n. h * f' i x) - g' x * h) \<le> e * cmod h"
    by (blast intro: **)
  qed
qed


lemma field_differentiable_series:
  fixes f :: "nat \<Rightarrow> complex \<Rightarrow> complex"
  assumes "convex s" "open s"
  assumes "\<And>n x. x \<in> s \<Longrightarrow> (f n has_field_derivative f' n x) (at x)"
  assumes "uniformly_convergent_on s (\<lambda>n x. \<Sum>i<n. f' i x)"
  assumes "x0 \<in> s" "summable (\<lambda>n. f n x0)" and x: "x \<in> s"
  shows   "summable (\<lambda>n. f n x)" and "(\<lambda>x. \<Sum>n. f n x) field_differentiable (at x)"
proof -
  from assms(4) obtain g' where A: "uniform_limit s (\<lambda>n x. \<Sum>i<n. f' i x) g' sequentially"
    unfolding uniformly_convergent_on_def by blast
  from x and \<open>open s\<close> have s: "at x within s = at x" by (rule at_within_open)
  have "\<exists>g. \<forall>x\<in>s. (\<lambda>n. f n x) sums g x \<and> (g has_field_derivative g' x) (at x within s)"
    by (intro has_field_derivative_series[of s f f' g' x0] assms A has_field_derivative_at_within)
  then obtain g where g: "\<And>x. x \<in> s \<Longrightarrow> (\<lambda>n. f n x) sums g x"
    "\<And>x. x \<in> s \<Longrightarrow> (g has_field_derivative g' x) (at x within s)" by blast
  from g[OF x] show "summable (\<lambda>n. f n x)" by (auto simp: summable_def)
  from g(2)[OF x] have g': "(g has_derivative op * (g' x)) (at x)"
    by (simp add: has_field_derivative_def s)
  have "((\<lambda>x. \<Sum>n. f n x) has_derivative op * (g' x)) (at x)"
    by (rule has_derivative_transform_within_open[OF g' \<open>open s\<close> x])
       (insert g, auto simp: sums_iff)
  thus "(\<lambda>x. \<Sum>n. f n x) field_differentiable (at x)" unfolding differentiable_def
    by (auto simp: summable_def field_differentiable_def has_field_derivative_def)
qed

lemma field_differentiable_series':
  fixes f :: "nat \<Rightarrow> complex \<Rightarrow> complex"
  assumes "convex s" "open s"
  assumes "\<And>n x. x \<in> s \<Longrightarrow> (f n has_field_derivative f' n x) (at x)"
  assumes "uniformly_convergent_on s (\<lambda>n x. \<Sum>i<n. f' i x)"
  assumes "x0 \<in> s" "summable (\<lambda>n. f n x0)"
  shows   "(\<lambda>x. \<Sum>n. f n x) field_differentiable (at x0)"
  using field_differentiable_series[OF assms, of x0] \<open>x0 \<in> s\<close> by blast+

subsection\<open>Bound theorem\<close>

lemma field_differentiable_bound:
  fixes s :: "complex set"
  assumes cvs: "convex s"
      and df:  "\<And>z. z \<in> s \<Longrightarrow> (f has_field_derivative f' z) (at z within s)"
      and dn:  "\<And>z. z \<in> s \<Longrightarrow> norm (f' z) \<le> B"
      and "x \<in> s"  "y \<in> s"
    shows "norm(f x - f y) \<le> B * norm(x - y)"
  apply (rule differentiable_bound [OF cvs])
  apply (rule ballI, erule df [unfolded has_field_derivative_def])
  apply (rule ballI, rule onorm_le, simp add: norm_mult mult_right_mono dn)
  apply fact
  apply fact
  done

subsection\<open>Inverse function theorem for complex derivatives\<close>

lemma has_complex_derivative_inverse_basic:
  fixes f :: "complex \<Rightarrow> complex"
  shows "DERIV f (g y) :> f' \<Longrightarrow>
        f' \<noteq> 0 \<Longrightarrow>
        continuous (at y) g \<Longrightarrow>
        open t \<Longrightarrow>
        y \<in> t \<Longrightarrow>
        (\<And>z. z \<in> t \<Longrightarrow> f (g z) = z)
        \<Longrightarrow> DERIV g y :> inverse (f')"
  unfolding has_field_derivative_def
  apply (rule has_derivative_inverse_basic)
  apply (auto simp:  bounded_linear_mult_right)
  done

(*Used only once, in Multivariate/cauchy.ml. *)
lemma has_complex_derivative_inverse_strong:
  fixes f :: "complex \<Rightarrow> complex"
  shows "DERIV f x :> f' \<Longrightarrow>
         f' \<noteq> 0 \<Longrightarrow>
         open s \<Longrightarrow>
         x \<in> s \<Longrightarrow>
         continuous_on s f \<Longrightarrow>
         (\<And>z. z \<in> s \<Longrightarrow> g (f z) = z)
         \<Longrightarrow> DERIV g (f x) :> inverse (f')"
  unfolding has_field_derivative_def
  apply (rule has_derivative_inverse_strong [of s x f g ])
  by auto

lemma has_complex_derivative_inverse_strong_x:
  fixes f :: "complex \<Rightarrow> complex"
  shows  "DERIV f (g y) :> f' \<Longrightarrow>
          f' \<noteq> 0 \<Longrightarrow>
          open s \<Longrightarrow>
          continuous_on s f \<Longrightarrow>
          g y \<in> s \<Longrightarrow> f(g y) = y \<Longrightarrow>
          (\<And>z. z \<in> s \<Longrightarrow> g (f z) = z)
          \<Longrightarrow> DERIV g y :> inverse (f')"
  unfolding has_field_derivative_def
  apply (rule has_derivative_inverse_strong_x [of s g y f])
  by auto

subsection \<open>Taylor on Complex Numbers\<close>

lemma sum_Suc_reindex:
  fixes f :: "nat \<Rightarrow> 'a::ab_group_add"
    shows  "sum f {0..n} = f 0 - f (Suc n) + sum (\<lambda>i. f (Suc i)) {0..n}"
by (induct n) auto

lemma complex_taylor:
  assumes s: "convex s"
      and f: "\<And>i x. x \<in> s \<Longrightarrow> i \<le> n \<Longrightarrow> (f i has_field_derivative f (Suc i) x) (at x within s)"
      and B: "\<And>x. x \<in> s \<Longrightarrow> cmod (f (Suc n) x) \<le> B"
      and w: "w \<in> s"
      and z: "z \<in> s"
    shows "cmod(f 0 z - (\<Sum>i\<le>n. f i w * (z-w) ^ i / (fact i)))
          \<le> B * cmod(z - w)^(Suc n) / fact n"
proof -
  have wzs: "closed_segment w z \<subseteq> s" using assms
    by (metis convex_contains_segment)
  { fix u
    assume "u \<in> closed_segment w z"
    then have "u \<in> s"
      by (metis wzs subsetD)
    have "(\<Sum>i\<le>n. f i u * (- of_nat i * (z-u)^(i - 1)) / (fact i) +
                      f (Suc i) u * (z-u)^i / (fact i)) =
              f (Suc n) u * (z-u) ^ n / (fact n)"
    proof (induction n)
      case 0 show ?case by simp
    next
      case (Suc n)
      have "(\<Sum>i\<le>Suc n. f i u * (- of_nat i * (z-u) ^ (i - 1)) / (fact i) +
                             f (Suc i) u * (z-u) ^ i / (fact i)) =
           f (Suc n) u * (z-u) ^ n / (fact n) +
           f (Suc (Suc n)) u * ((z-u) * (z-u) ^ n) / (fact (Suc n)) -
           f (Suc n) u * ((1 + of_nat n) * (z-u) ^ n) / (fact (Suc n))"
        using Suc by simp
      also have "... = f (Suc (Suc n)) u * (z-u) ^ Suc n / (fact (Suc n))"
      proof -
        have "(fact(Suc n)) *
             (f(Suc n) u *(z-u) ^ n / (fact n) +
               f(Suc(Suc n)) u *((z-u) *(z-u) ^ n) / (fact(Suc n)) -
               f(Suc n) u *((1 + of_nat n) *(z-u) ^ n) / (fact(Suc n))) =
            ((fact(Suc n)) *(f(Suc n) u *(z-u) ^ n)) / (fact n) +
            ((fact(Suc n)) *(f(Suc(Suc n)) u *((z-u) *(z-u) ^ n)) / (fact(Suc n))) -
            ((fact(Suc n)) *(f(Suc n) u *(of_nat(Suc n) *(z-u) ^ n))) / (fact(Suc n))"
          by (simp add: algebra_simps del: fact_Suc)
        also have "... = ((fact (Suc n)) * (f (Suc n) u * (z-u) ^ n)) / (fact n) +
                         (f (Suc (Suc n)) u * ((z-u) * (z-u) ^ n)) -
                         (f (Suc n) u * ((1 + of_nat n) * (z-u) ^ n))"
          by (simp del: fact_Suc)
        also have "... = (of_nat (Suc n) * (f (Suc n) u * (z-u) ^ n)) +
                         (f (Suc (Suc n)) u * ((z-u) * (z-u) ^ n)) -
                         (f (Suc n) u * ((1 + of_nat n) * (z-u) ^ n))"
          by (simp only: fact_Suc of_nat_mult ac_simps) simp
        also have "... = f (Suc (Suc n)) u * ((z-u) * (z-u) ^ n)"
          by (simp add: algebra_simps)
        finally show ?thesis
        by (simp add: mult_left_cancel [where c = "(fact (Suc n))", THEN iffD1] del: fact_Suc)
      qed
      finally show ?case .
    qed
    then have "((\<lambda>v. (\<Sum>i\<le>n. f i v * (z - v)^i / (fact i)))
                has_field_derivative f (Suc n) u * (z-u) ^ n / (fact n))
               (at u within s)"
      apply (intro derivative_eq_intros)
      apply (blast intro: assms \<open>u \<in> s\<close>)
      apply (rule refl)+
      apply (auto simp: field_simps)
      done
  } note sum_deriv = this
  { fix u
    assume u: "u \<in> closed_segment w z"
    then have us: "u \<in> s"
      by (metis wzs subsetD)
    have "cmod (f (Suc n) u) * cmod (z - u) ^ n \<le> cmod (f (Suc n) u) * cmod (u - z) ^ n"
      by (metis norm_minus_commute order_refl)
    also have "... \<le> cmod (f (Suc n) u) * cmod (z - w) ^ n"
      by (metis mult_left_mono norm_ge_zero power_mono segment_bound [OF u])
    also have "... \<le> B * cmod (z - w) ^ n"
      by (metis norm_ge_zero zero_le_power mult_right_mono  B [OF us])
    finally have "cmod (f (Suc n) u) * cmod (z - u) ^ n \<le> B * cmod (z - w) ^ n" .
  } note cmod_bound = this
  have "(\<Sum>i\<le>n. f i z * (z - z) ^ i / (fact i)) = (\<Sum>i\<le>n. (f i z / (fact i)) * 0 ^ i)"
    by simp
  also have "\<dots> = f 0 z / (fact 0)"
    by (subst sum_zero_power) simp
  finally have "cmod (f 0 z - (\<Sum>i\<le>n. f i w * (z - w) ^ i / (fact i)))
                \<le> cmod ((\<Sum>i\<le>n. f i w * (z - w) ^ i / (fact i)) -
                        (\<Sum>i\<le>n. f i z * (z - z) ^ i / (fact i)))"
    by (simp add: norm_minus_commute)
  also have "... \<le> B * cmod (z - w) ^ n / (fact n) * cmod (w - z)"
    apply (rule field_differentiable_bound
      [where f' = "\<lambda>w. f (Suc n) w * (z - w)^n / (fact n)"
         and s = "closed_segment w z", OF convex_closed_segment])
    apply (auto simp: ends_in_segment DERIV_subset [OF sum_deriv wzs]
                  norm_divide norm_mult norm_power divide_le_cancel cmod_bound)
    done
  also have "...  \<le> B * cmod (z - w) ^ Suc n / (fact n)"
    by (simp add: algebra_simps norm_minus_commute)
  finally show ?thesis .
qed

text\<open>Something more like the traditional MVT for real components\<close>

lemma complex_mvt_line:
  assumes "\<And>u. u \<in> closed_segment w z \<Longrightarrow> (f has_field_derivative f'(u)) (at u)"
    shows "\<exists>u. u \<in> closed_segment w z \<and> Re(f z) - Re(f w) = Re(f'(u) * (z - w))"
proof -
  have twz: "\<And>t. (1 - t) *\<^sub>R w + t *\<^sub>R z = w + t *\<^sub>R (z - w)"
    by (simp add: real_vector.scale_left_diff_distrib real_vector.scale_right_diff_distrib)
  note assms[unfolded has_field_derivative_def, derivative_intros]
  show ?thesis
    apply (cut_tac mvt_simple
                     [of 0 1 "Re o f o (\<lambda>t. (1 - t) *\<^sub>R w +  t *\<^sub>R z)"
                      "\<lambda>u. Re o (\<lambda>h. f'((1 - u) *\<^sub>R w + u *\<^sub>R z) * h) o (\<lambda>t. t *\<^sub>R (z - w))"])
    apply auto
    apply (rule_tac x="(1 - x) *\<^sub>R w + x *\<^sub>R z" in exI)
    apply (auto simp: closed_segment_def twz) []
    apply (intro derivative_eq_intros has_derivative_at_within, simp_all)
    apply (simp add: fun_eq_iff real_vector.scale_right_diff_distrib)
    apply (force simp: twz closed_segment_def)
    done
qed

lemma complex_taylor_mvt:
  assumes "\<And>i x. \<lbrakk>x \<in> closed_segment w z; i \<le> n\<rbrakk> \<Longrightarrow> ((f i) has_field_derivative f (Suc i) x) (at x)"
    shows "\<exists>u. u \<in> closed_segment w z \<and>
            Re (f 0 z) =
            Re ((\<Sum>i = 0..n. f i w * (z - w) ^ i / (fact i)) +
                (f (Suc n) u * (z-u)^n / (fact n)) * (z - w))"
proof -
  { fix u
    assume u: "u \<in> closed_segment w z"
    have "(\<Sum>i = 0..n.
               (f (Suc i) u * (z-u) ^ i - of_nat i * (f i u * (z-u) ^ (i - Suc 0))) /
               (fact i)) =
          f (Suc 0) u -
             (f (Suc (Suc n)) u * ((z-u) ^ Suc n) - (of_nat (Suc n)) * (z-u) ^ n * f (Suc n) u) /
             (fact (Suc n)) +
             (\<Sum>i = 0..n.
                 (f (Suc (Suc i)) u * ((z-u) ^ Suc i) - of_nat (Suc i) * (f (Suc i) u * (z-u) ^ i)) /
                 (fact (Suc i)))"
       by (subst sum_Suc_reindex) simp
    also have "... = f (Suc 0) u -
             (f (Suc (Suc n)) u * ((z-u) ^ Suc n) - (of_nat (Suc n)) * (z-u) ^ n * f (Suc n) u) /
             (fact (Suc n)) +
             (\<Sum>i = 0..n.
                 f (Suc (Suc i)) u * ((z-u) ^ Suc i) / (fact (Suc i))  -
                 f (Suc i) u * (z-u) ^ i / (fact i))"
      by (simp only: diff_divide_distrib fact_cancel ac_simps)
    also have "... = f (Suc 0) u -
             (f (Suc (Suc n)) u * (z-u) ^ Suc n - of_nat (Suc n) * (z-u) ^ n * f (Suc n) u) /
             (fact (Suc n)) +
             f (Suc (Suc n)) u * (z-u) ^ Suc n / (fact (Suc n)) - f (Suc 0) u"
      by (subst sum_Suc_diff) auto
    also have "... = f (Suc n) u * (z-u) ^ n / (fact n)"
      by (simp only: algebra_simps diff_divide_distrib fact_cancel)
    finally have "(\<Sum>i = 0..n. (f (Suc i) u * (z - u) ^ i
                             - of_nat i * (f i u * (z-u) ^ (i - Suc 0))) / (fact i)) =
                  f (Suc n) u * (z - u) ^ n / (fact n)" .
    then have "((\<lambda>u. \<Sum>i = 0..n. f i u * (z - u) ^ i / (fact i)) has_field_derivative
                f (Suc n) u * (z - u) ^ n / (fact n))  (at u)"
      apply (intro derivative_eq_intros)+
      apply (force intro: u assms)
      apply (rule refl)+
      apply (auto simp: ac_simps)
      done
  }
  then show ?thesis
    apply (cut_tac complex_mvt_line [of w z "\<lambda>u. \<Sum>i = 0..n. f i u * (z-u) ^ i / (fact i)"
               "\<lambda>u. (f (Suc n) u * (z-u)^n / (fact n))"])
    apply (auto simp add: intro: open_closed_segment)
    done
qed


subsection \<open>Polynomal function extremal theorem, from HOL Light\<close>

lemma polyfun_extremal_lemma: (*COMPLEX_POLYFUN_EXTREMAL_LEMMA in HOL Light*)
    fixes c :: "nat \<Rightarrow> 'a::real_normed_div_algebra"
  assumes "0 < e"
    shows "\<exists>M. \<forall>z. M \<le> norm(z) \<longrightarrow> norm (\<Sum>i\<le>n. c(i) * z^i) \<le> e * norm(z) ^ (Suc n)"
proof (induct n)
  case 0 with assms
  show ?case
    apply (rule_tac x="norm (c 0) / e" in exI)
    apply (auto simp: field_simps)
    done
next
  case (Suc n)
  obtain M where M: "\<And>z. M \<le> norm z \<Longrightarrow> norm (\<Sum>i\<le>n. c i * z^i) \<le> e * norm z ^ Suc n"
    using Suc assms by blast
  show ?case
  proof (rule exI [where x= "max M (1 + norm(c(Suc n)) / e)"], clarsimp simp del: power_Suc)
    fix z::'a
    assume z1: "M \<le> norm z" and "1 + norm (c (Suc n)) / e \<le> norm z"
    then have z2: "e + norm (c (Suc n)) \<le> e * norm z"
      using assms by (simp add: field_simps)
    have "norm (\<Sum>i\<le>n. c i * z^i) \<le> e * norm z ^ Suc n"
      using M [OF z1] by simp
    then have "norm (\<Sum>i\<le>n. c i * z^i) + norm (c (Suc n) * z ^ Suc n) \<le> e * norm z ^ Suc n + norm (c (Suc n) * z ^ Suc n)"
      by simp
    then have "norm ((\<Sum>i\<le>n. c i * z^i) + c (Suc n) * z ^ Suc n) \<le> e * norm z ^ Suc n + norm (c (Suc n) * z ^ Suc n)"
      by (blast intro: norm_triangle_le elim: )
    also have "... \<le> (e + norm (c (Suc n))) * norm z ^ Suc n"
      by (simp add: norm_power norm_mult algebra_simps)
    also have "... \<le> (e * norm z) * norm z ^ Suc n"
      by (metis z2 mult.commute mult_left_mono norm_ge_zero norm_power)
    finally show "norm ((\<Sum>i\<le>n. c i * z^i) + c (Suc n) * z ^ Suc n) \<le> e * norm z ^ Suc (Suc n)"
      by simp
  qed
qed

lemma polyfun_extremal: (*COMPLEX_POLYFUN_EXTREMAL in HOL Light*)
    fixes c :: "nat \<Rightarrow> 'a::real_normed_div_algebra"
  assumes k: "c k \<noteq> 0" "1\<le>k" and kn: "k\<le>n"
    shows "eventually (\<lambda>z. norm (\<Sum>i\<le>n. c(i) * z^i) \<ge> B) at_infinity"
using kn
proof (induction n)
  case 0
  then show ?case
    using k  by simp
next
  case (Suc m)
  let ?even = ?case
  show ?even
  proof (cases "c (Suc m) = 0")
    case True
    then show ?even using Suc k
      by auto (metis antisym_conv less_eq_Suc_le not_le)
  next
    case False
    then obtain M where M:
          "\<And>z. M \<le> norm z \<Longrightarrow> norm (\<Sum>i\<le>m. c i * z^i) \<le> norm (c (Suc m)) / 2 * norm z ^ Suc m"
      using polyfun_extremal_lemma [of "norm(c (Suc m)) / 2" c m] Suc
      by auto
    have "\<exists>b. \<forall>z. b \<le> norm z \<longrightarrow> B \<le> norm (\<Sum>i\<le>Suc m. c i * z^i)"
    proof (rule exI [where x="max M (max 1 (\<bar>B\<bar> / (norm(c (Suc m)) / 2)))"], clarsimp simp del: power_Suc)
      fix z::'a
      assume z1: "M \<le> norm z" "1 \<le> norm z"
         and "\<bar>B\<bar> * 2 / norm (c (Suc m)) \<le> norm z"
      then have z2: "\<bar>B\<bar> \<le> norm (c (Suc m)) * norm z / 2"
        using False by (simp add: field_simps)
      have nz: "norm z \<le> norm z ^ Suc m"
        by (metis \<open>1 \<le> norm z\<close> One_nat_def less_eq_Suc_le power_increasing power_one_right zero_less_Suc)
      have *: "\<And>y x. norm (c (Suc m)) * norm z / 2 \<le> norm y - norm x \<Longrightarrow> B \<le> norm (x + y)"
        by (metis abs_le_iff add.commute norm_diff_ineq order_trans z2)
      have "norm z * norm (c (Suc m)) + 2 * norm (\<Sum>i\<le>m. c i * z^i)
            \<le> norm (c (Suc m)) * norm z + norm (c (Suc m)) * norm z ^ Suc m"
        using M [of z] Suc z1  by auto
      also have "... \<le> 2 * (norm (c (Suc m)) * norm z ^ Suc m)"
        using nz by (simp add: mult_mono del: power_Suc)
      finally show "B \<le> norm ((\<Sum>i\<le>m. c i * z^i) + c (Suc m) * z ^ Suc m)"
        using Suc.IH
        apply (auto simp: eventually_at_infinity)
        apply (rule *)
        apply (simp add: field_simps norm_mult norm_power)
        done
    qed
    then show ?even
      by (simp add: eventually_at_infinity)
  qed
qed

end
