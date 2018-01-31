(*  Title:      HOL/Analysis/Product_Vector.thy
    Author:     Brian Huffman
*)

section \<open>Cartesian Products as Vector Spaces\<close>

theory Product_Vector
imports
  Inner_Product
  "~~/src/HOL/Library/Product_Plus"
begin

subsection \<open>Product is a real vector space\<close>

instantiation prod :: (real_vector, real_vector) real_vector
begin

definition scaleR_prod_def:
  "scaleR r A = (scaleR r (fst A), scaleR r (snd A))"

lemma fst_scaleR [simp]: "fst (scaleR r A) = scaleR r (fst A)"
  unfolding scaleR_prod_def by simp

lemma snd_scaleR [simp]: "snd (scaleR r A) = scaleR r (snd A)"
  unfolding scaleR_prod_def by simp

lemma scaleR_Pair [simp]: "scaleR r (a, b) = (scaleR r a, scaleR r b)"
  unfolding scaleR_prod_def by simp

instance
proof
  fix a b :: real and x y :: "'a \<times> 'b"
  show "scaleR a (x + y) = scaleR a x + scaleR a y"
    by (simp add: prod_eq_iff scaleR_right_distrib)
  show "scaleR (a + b) x = scaleR a x + scaleR b x"
    by (simp add: prod_eq_iff scaleR_left_distrib)
  show "scaleR a (scaleR b x) = scaleR (a * b) x"
    by (simp add: prod_eq_iff)
  show "scaleR 1 x = x"
    by (simp add: prod_eq_iff)
qed

end

subsection \<open>Product is a metric space\<close>

(* TODO: Product of uniform spaces and compatibility with metric_spaces! *)

instantiation prod :: (metric_space, metric_space) dist
begin

definition dist_prod_def[code del]:
  "dist x y = sqrt ((dist (fst x) (fst y))\<^sup>2 + (dist (snd x) (snd y))\<^sup>2)"

instance ..
end

instantiation prod :: (metric_space, metric_space) uniformity_dist
begin

definition [code del]:
  "(uniformity :: (('a \<times> 'b) \<times> ('a \<times> 'b)) filter) =
    (INF e:{0 <..}. principal {(x, y). dist x y < e})"

instance
  by standard (rule uniformity_prod_def)
end

declare uniformity_Abort[where 'a="'a :: metric_space \<times> 'b :: metric_space", code]

instantiation prod :: (metric_space, metric_space) metric_space
begin

lemma dist_Pair_Pair: "dist (a, b) (c, d) = sqrt ((dist a c)\<^sup>2 + (dist b d)\<^sup>2)"
  unfolding dist_prod_def by simp

lemma dist_fst_le: "dist (fst x) (fst y) \<le> dist x y"
  unfolding dist_prod_def by (rule real_sqrt_sum_squares_ge1)

lemma dist_snd_le: "dist (snd x) (snd y) \<le> dist x y"
  unfolding dist_prod_def by (rule real_sqrt_sum_squares_ge2)

instance
proof
  fix x y :: "'a \<times> 'b"
  show "dist x y = 0 \<longleftrightarrow> x = y"
    unfolding dist_prod_def prod_eq_iff by simp
next
  fix x y z :: "'a \<times> 'b"
  show "dist x y \<le> dist x z + dist y z"
    unfolding dist_prod_def
    by (intro order_trans [OF _ real_sqrt_sum_squares_triangle_ineq]
        real_sqrt_le_mono add_mono power_mono dist_triangle2 zero_le_dist)
next
  fix S :: "('a \<times> 'b) set"
  have *: "open S \<longleftrightarrow> (\<forall>x\<in>S. \<exists>e>0. \<forall>y. dist y x < e \<longrightarrow> y \<in> S)"
  proof
    assume "open S" show "\<forall>x\<in>S. \<exists>e>0. \<forall>y. dist y x < e \<longrightarrow> y \<in> S"
    proof
      fix x assume "x \<in> S"
      obtain A B where "open A" "open B" "x \<in> A \<times> B" "A \<times> B \<subseteq> S"
        using \<open>open S\<close> and \<open>x \<in> S\<close> by (rule open_prod_elim)
      obtain r where r: "0 < r" "\<forall>y. dist y (fst x) < r \<longrightarrow> y \<in> A"
        using \<open>open A\<close> and \<open>x \<in> A \<times> B\<close> unfolding open_dist by auto
      obtain s where s: "0 < s" "\<forall>y. dist y (snd x) < s \<longrightarrow> y \<in> B"
        using \<open>open B\<close> and \<open>x \<in> A \<times> B\<close> unfolding open_dist by auto
      let ?e = "min r s"
      have "0 < ?e \<and> (\<forall>y. dist y x < ?e \<longrightarrow> y \<in> S)"
      proof (intro allI impI conjI)
        show "0 < min r s" by (simp add: r(1) s(1))
      next
        fix y assume "dist y x < min r s"
        hence "dist y x < r" and "dist y x < s"
          by simp_all
        hence "dist (fst y) (fst x) < r" and "dist (snd y) (snd x) < s"
          by (auto intro: le_less_trans dist_fst_le dist_snd_le)
        hence "fst y \<in> A" and "snd y \<in> B"
          by (simp_all add: r(2) s(2))
        hence "y \<in> A \<times> B" by (induct y, simp)
        with \<open>A \<times> B \<subseteq> S\<close> show "y \<in> S" ..
      qed
      thus "\<exists>e>0. \<forall>y. dist y x < e \<longrightarrow> y \<in> S" ..
    qed
  next
    assume *: "\<forall>x\<in>S. \<exists>e>0. \<forall>y. dist y x < e \<longrightarrow> y \<in> S" show "open S"
    proof (rule open_prod_intro)
      fix x assume "x \<in> S"
      then obtain e where "0 < e" and S: "\<forall>y. dist y x < e \<longrightarrow> y \<in> S"
        using * by fast
      define r where "r = e / sqrt 2"
      define s where "s = e / sqrt 2"
      from \<open>0 < e\<close> have "0 < r" and "0 < s"
        unfolding r_def s_def by simp_all
      from \<open>0 < e\<close> have "e = sqrt (r\<^sup>2 + s\<^sup>2)"
        unfolding r_def s_def by (simp add: power_divide)
      define A where "A = {y. dist (fst x) y < r}"
      define B where "B = {y. dist (snd x) y < s}"
      have "open A" and "open B"
        unfolding A_def B_def by (simp_all add: open_ball)
      moreover have "x \<in> A \<times> B"
        unfolding A_def B_def mem_Times_iff
        using \<open>0 < r\<close> and \<open>0 < s\<close> by simp
      moreover have "A \<times> B \<subseteq> S"
      proof (clarify)
        fix a b assume "a \<in> A" and "b \<in> B"
        hence "dist a (fst x) < r" and "dist b (snd x) < s"
          unfolding A_def B_def by (simp_all add: dist_commute)
        hence "dist (a, b) x < e"
          unfolding dist_prod_def \<open>e = sqrt (r\<^sup>2 + s\<^sup>2)\<close>
          by (simp add: add_strict_mono power_strict_mono)
        thus "(a, b) \<in> S"
          by (simp add: S)
      qed
      ultimately show "\<exists>A B. open A \<and> open B \<and> x \<in> A \<times> B \<and> A \<times> B \<subseteq> S" by fast
    qed
  qed
  show "open S = (\<forall>x\<in>S. \<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> S)"
    unfolding * eventually_uniformity_metric
    by (simp del: split_paired_All add: dist_prod_def dist_commute)
qed

end

declare [[code abort: "dist::('a::metric_space*'b::metric_space)\<Rightarrow>('a*'b) \<Rightarrow> real"]]

lemma Cauchy_fst: "Cauchy X \<Longrightarrow> Cauchy (\<lambda>n. fst (X n))"
  unfolding Cauchy_def by (fast elim: le_less_trans [OF dist_fst_le])

lemma Cauchy_snd: "Cauchy X \<Longrightarrow> Cauchy (\<lambda>n. snd (X n))"
  unfolding Cauchy_def by (fast elim: le_less_trans [OF dist_snd_le])

lemma Cauchy_Pair:
  assumes "Cauchy X" and "Cauchy Y"
  shows "Cauchy (\<lambda>n. (X n, Y n))"
proof (rule metric_CauchyI)
  fix r :: real assume "0 < r"
  hence "0 < r / sqrt 2" (is "0 < ?s") by simp
  obtain M where M: "\<forall>m\<ge>M. \<forall>n\<ge>M. dist (X m) (X n) < ?s"
    using metric_CauchyD [OF \<open>Cauchy X\<close> \<open>0 < ?s\<close>] ..
  obtain N where N: "\<forall>m\<ge>N. \<forall>n\<ge>N. dist (Y m) (Y n) < ?s"
    using metric_CauchyD [OF \<open>Cauchy Y\<close> \<open>0 < ?s\<close>] ..
  have "\<forall>m\<ge>max M N. \<forall>n\<ge>max M N. dist (X m, Y m) (X n, Y n) < r"
    using M N by (simp add: real_sqrt_sum_squares_less dist_Pair_Pair)
  then show "\<exists>n0. \<forall>m\<ge>n0. \<forall>n\<ge>n0. dist (X m, Y m) (X n, Y n) < r" ..
qed

subsection \<open>Product is a complete metric space\<close>

instance prod :: (complete_space, complete_space) complete_space
proof
  fix X :: "nat \<Rightarrow> 'a \<times> 'b" assume "Cauchy X"
  have 1: "(\<lambda>n. fst (X n)) \<longlonglongrightarrow> lim (\<lambda>n. fst (X n))"
    using Cauchy_fst [OF \<open>Cauchy X\<close>]
    by (simp add: Cauchy_convergent_iff convergent_LIMSEQ_iff)
  have 2: "(\<lambda>n. snd (X n)) \<longlonglongrightarrow> lim (\<lambda>n. snd (X n))"
    using Cauchy_snd [OF \<open>Cauchy X\<close>]
    by (simp add: Cauchy_convergent_iff convergent_LIMSEQ_iff)
  have "X \<longlonglongrightarrow> (lim (\<lambda>n. fst (X n)), lim (\<lambda>n. snd (X n)))"
    using tendsto_Pair [OF 1 2] by simp
  then show "convergent X"
    by (rule convergentI)
qed

subsection \<open>Product is a normed vector space\<close>

instantiation prod :: (real_normed_vector, real_normed_vector) real_normed_vector
begin

definition norm_prod_def[code del]:
  "norm x = sqrt ((norm (fst x))\<^sup>2 + (norm (snd x))\<^sup>2)"

definition sgn_prod_def:
  "sgn (x::'a \<times> 'b) = scaleR (inverse (norm x)) x"

lemma norm_Pair: "norm (a, b) = sqrt ((norm a)\<^sup>2 + (norm b)\<^sup>2)"
  unfolding norm_prod_def by simp

instance
proof
  fix r :: real and x y :: "'a \<times> 'b"
  show "norm x = 0 \<longleftrightarrow> x = 0"
    unfolding norm_prod_def
    by (simp add: prod_eq_iff)
  show "norm (x + y) \<le> norm x + norm y"
    unfolding norm_prod_def
    apply (rule order_trans [OF _ real_sqrt_sum_squares_triangle_ineq])
    apply (simp add: add_mono power_mono norm_triangle_ineq)
    done
  show "norm (scaleR r x) = \<bar>r\<bar> * norm x"
    unfolding norm_prod_def
    apply (simp add: power_mult_distrib)
    apply (simp add: distrib_left [symmetric])
    apply (simp add: real_sqrt_mult_distrib)
    done
  show "sgn x = scaleR (inverse (norm x)) x"
    by (rule sgn_prod_def)
  show "dist x y = norm (x - y)"
    unfolding dist_prod_def norm_prod_def
    by (simp add: dist_norm)
qed

end

declare [[code abort: "norm::('a::real_normed_vector*'b::real_normed_vector) \<Rightarrow> real"]]

instance prod :: (banach, banach) banach ..

subsubsection \<open>Pair operations are linear\<close>

lemma bounded_linear_fst: "bounded_linear fst"
  using fst_add fst_scaleR
  by (rule bounded_linear_intro [where K=1], simp add: norm_prod_def)

lemma bounded_linear_snd: "bounded_linear snd"
  using snd_add snd_scaleR
  by (rule bounded_linear_intro [where K=1], simp add: norm_prod_def)

lemmas bounded_linear_fst_comp = bounded_linear_fst[THEN bounded_linear_compose]

lemmas bounded_linear_snd_comp = bounded_linear_snd[THEN bounded_linear_compose]

lemma bounded_linear_Pair:
  assumes f: "bounded_linear f"
  assumes g: "bounded_linear g"
  shows "bounded_linear (\<lambda>x. (f x, g x))"
proof
  interpret f: bounded_linear f by fact
  interpret g: bounded_linear g by fact
  fix x y and r :: real
  show "(f (x + y), g (x + y)) = (f x, g x) + (f y, g y)"
    by (simp add: f.add g.add)
  show "(f (r *\<^sub>R x), g (r *\<^sub>R x)) = r *\<^sub>R (f x, g x)"
    by (simp add: f.scaleR g.scaleR)
  obtain Kf where "0 < Kf" and norm_f: "\<And>x. norm (f x) \<le> norm x * Kf"
    using f.pos_bounded by fast
  obtain Kg where "0 < Kg" and norm_g: "\<And>x. norm (g x) \<le> norm x * Kg"
    using g.pos_bounded by fast
  have "\<forall>x. norm (f x, g x) \<le> norm x * (Kf + Kg)"
    apply (rule allI)
    apply (simp add: norm_Pair)
    apply (rule order_trans [OF sqrt_add_le_add_sqrt], simp, simp)
    apply (simp add: distrib_left)
    apply (rule add_mono [OF norm_f norm_g])
    done
  then show "\<exists>K. \<forall>x. norm (f x, g x) \<le> norm x * K" ..
qed

subsubsection \<open>Frechet derivatives involving pairs\<close>

lemma has_derivative_Pair [derivative_intros]:
  assumes f: "(f has_derivative f') (at x within s)" and g: "(g has_derivative g') (at x within s)"
  shows "((\<lambda>x. (f x, g x)) has_derivative (\<lambda>h. (f' h, g' h))) (at x within s)"
proof (rule has_derivativeI_sandwich[of 1])
  show "bounded_linear (\<lambda>h. (f' h, g' h))"
    using f g by (intro bounded_linear_Pair has_derivative_bounded_linear)
  let ?Rf = "\<lambda>y. f y - f x - f' (y - x)"
  let ?Rg = "\<lambda>y. g y - g x - g' (y - x)"
  let ?R = "\<lambda>y. ((f y, g y) - (f x, g x) - (f' (y - x), g' (y - x)))"

  show "((\<lambda>y. norm (?Rf y) / norm (y - x) + norm (?Rg y) / norm (y - x)) \<longlongrightarrow> 0) (at x within s)"
    using f g by (intro tendsto_add_zero) (auto simp: has_derivative_iff_norm)

  fix y :: 'a assume "y \<noteq> x"
  show "norm (?R y) / norm (y - x) \<le> norm (?Rf y) / norm (y - x) + norm (?Rg y) / norm (y - x)"
    unfolding add_divide_distrib [symmetric]
    by (simp add: norm_Pair divide_right_mono order_trans [OF sqrt_add_le_add_sqrt])
qed simp

lemmas has_derivative_fst [derivative_intros] = bounded_linear.has_derivative [OF bounded_linear_fst]
lemmas has_derivative_snd [derivative_intros] = bounded_linear.has_derivative [OF bounded_linear_snd]

lemma has_derivative_split [derivative_intros]:
  "((\<lambda>p. f (fst p) (snd p)) has_derivative f') F \<Longrightarrow> ((\<lambda>(a, b). f a b) has_derivative f') F"
  unfolding split_beta' .

subsection \<open>Product is an inner product space\<close>

instantiation prod :: (real_inner, real_inner) real_inner
begin

definition inner_prod_def:
  "inner x y = inner (fst x) (fst y) + inner (snd x) (snd y)"

lemma inner_Pair [simp]: "inner (a, b) (c, d) = inner a c + inner b d"
  unfolding inner_prod_def by simp

instance
proof
  fix r :: real
  fix x y z :: "'a::real_inner \<times> 'b::real_inner"
  show "inner x y = inner y x"
    unfolding inner_prod_def
    by (simp add: inner_commute)
  show "inner (x + y) z = inner x z + inner y z"
    unfolding inner_prod_def
    by (simp add: inner_add_left)
  show "inner (scaleR r x) y = r * inner x y"
    unfolding inner_prod_def
    by (simp add: distrib_left)
  show "0 \<le> inner x x"
    unfolding inner_prod_def
    by (intro add_nonneg_nonneg inner_ge_zero)
  show "inner x x = 0 \<longleftrightarrow> x = 0"
    unfolding inner_prod_def prod_eq_iff
    by (simp add: add_nonneg_eq_0_iff)
  show "norm x = sqrt (inner x x)"
    unfolding norm_prod_def inner_prod_def
    by (simp add: power2_norm_eq_inner)
qed

end

lemma inner_Pair_0: "inner x (0, b) = inner (snd x) b" "inner x (a, 0) = inner (fst x) a"
    by (cases x, simp)+

lemma
  fixes x :: "'a::real_normed_vector"
  shows norm_Pair1 [simp]: "norm (0,x) = norm x"
    and norm_Pair2 [simp]: "norm (x,0) = norm x"
by (auto simp: norm_Pair)

lemma norm_commute: "norm (x,y) = norm (y,x)"
  by (simp add: norm_Pair)

lemma norm_fst_le: "norm x \<le> norm (x,y)"
  by (metis dist_fst_le fst_conv fst_zero norm_conv_dist)

lemma norm_snd_le: "norm y \<le> norm (x,y)"
  by (metis dist_snd_le snd_conv snd_zero norm_conv_dist)

end
