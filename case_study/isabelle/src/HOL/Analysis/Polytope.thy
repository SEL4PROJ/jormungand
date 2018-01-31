section \<open>Faces, Extreme Points, Polytopes, Polyhedra etc.\<close>

text\<open>Ported from HOL Light by L C Paulson\<close>

theory Polytope
imports Cartesian_Euclidean_Space
begin

subsection \<open>Faces of a (usually convex) set\<close>

definition face_of :: "['a::real_vector set, 'a set] \<Rightarrow> bool" (infixr "(face'_of)" 50)
  where
  "T face_of S \<longleftrightarrow>
        T \<subseteq> S \<and> convex T \<and>
        (\<forall>a \<in> S. \<forall>b \<in> S. \<forall>x \<in> T. x \<in> open_segment a b \<longrightarrow> a \<in> T \<and> b \<in> T)"

lemma face_ofD: "\<lbrakk>T face_of S; x \<in> open_segment a b; a \<in> S; b \<in> S; x \<in> T\<rbrakk> \<Longrightarrow> a \<in> T \<and> b \<in> T"
  unfolding face_of_def by blast

lemma face_of_translation_eq [simp]:
    "(op + a ` T face_of op + a ` S) \<longleftrightarrow> T face_of S"
proof -
  have *: "\<And>a T S. T face_of S \<Longrightarrow> (op + a ` T face_of op + a ` S)"
    apply (simp add: face_of_def Ball_def, clarify)
    apply (drule open_segment_translation_eq [THEN iffD1])
    using inj_image_mem_iff inj_add_left apply metis
    done
  show ?thesis
    apply (rule iffI)
    apply (force simp: image_comp o_def dest: * [where a = "-a"])
    apply (blast intro: *)
    done
qed

lemma face_of_linear_image:
  assumes "linear f" "inj f"
    shows "(f ` c face_of f ` S) \<longleftrightarrow> c face_of S"
by (simp add: face_of_def inj_image_subset_iff inj_image_mem_iff open_segment_linear_image assms)

lemma face_of_refl: "convex S \<Longrightarrow> S face_of S"
  by (auto simp: face_of_def)

lemma face_of_refl_eq: "S face_of S \<longleftrightarrow> convex S"
  by (auto simp: face_of_def)

lemma empty_face_of [iff]: "{} face_of S"
  by (simp add: face_of_def)

lemma face_of_empty [simp]: "S face_of {} \<longleftrightarrow> S = {}"
  by (meson empty_face_of face_of_def subset_empty)

lemma face_of_trans [trans]: "\<lbrakk>S face_of T; T face_of u\<rbrakk> \<Longrightarrow> S face_of u"
  unfolding face_of_def by (safe; blast)

lemma face_of_face: "T face_of S \<Longrightarrow> (f face_of T \<longleftrightarrow> f face_of S \<and> f \<subseteq> T)"
  unfolding face_of_def by (safe; blast)

lemma face_of_subset: "\<lbrakk>F face_of S; F \<subseteq> T; T \<subseteq> S\<rbrakk> \<Longrightarrow> F face_of T"
  unfolding face_of_def by (safe; blast)

lemma face_of_slice: "\<lbrakk>F face_of S; convex T\<rbrakk> \<Longrightarrow> (F \<inter> T) face_of (S \<inter> T)"
  unfolding face_of_def by (blast intro: convex_Int)

lemma face_of_Int: "\<lbrakk>t1 face_of S; t2 face_of S\<rbrakk> \<Longrightarrow> (t1 \<inter> t2) face_of S"
  unfolding face_of_def by (blast intro: convex_Int)

lemma face_of_Inter: "\<lbrakk>A \<noteq> {}; \<And>T. T \<in> A \<Longrightarrow> T face_of S\<rbrakk> \<Longrightarrow> (\<Inter> A) face_of S"
  unfolding face_of_def by (blast intro: convex_Inter)

lemma face_of_Int_Int: "\<lbrakk>F face_of T; F' face_of t'\<rbrakk> \<Longrightarrow> (F \<inter> F') face_of (T \<inter> t')"
  unfolding face_of_def by (blast intro: convex_Int)

lemma face_of_imp_subset: "T face_of S \<Longrightarrow> T \<subseteq> S"
  unfolding face_of_def by blast

lemma face_of_imp_eq_affine_Int:
     fixes S :: "'a::euclidean_space set"
     assumes S: "convex S" "closed S" and T: "T face_of S"
     shows "T = (affine hull T) \<inter> S"
proof -
  have "convex T" using T by (simp add: face_of_def)
  have *: False if x: "x \<in> affine hull T" and "x \<in> S" "x \<notin> T" and y: "y \<in> rel_interior T" for x y
  proof -
    obtain e where "e>0" and e: "cball y e \<inter> affine hull T \<subseteq> T"
      using y by (auto simp: rel_interior_cball)
    have "y \<noteq> x" "y \<in> S" "y \<in> T"
      using face_of_imp_subset rel_interior_subset T that by blast+
    then have zne: "\<And>u. \<lbrakk>u \<in> {0<..<1}; (1 - u) *\<^sub>R y + u *\<^sub>R x \<in> T\<rbrakk> \<Longrightarrow>  False"
      using \<open>x \<in> S\<close> \<open>x \<notin> T\<close> \<open>T face_of S\<close> unfolding face_of_def
      apply clarify
      apply (drule_tac x=x in bspec, assumption)
      apply (drule_tac x=y in bspec, assumption)
      apply (subst (asm) open_segment_commute)
      apply (force simp: open_segment_image_interval image_def)
      done
    have in01: "min (1/2) (e / norm (x - y)) \<in> {0<..<1}"
      using \<open>y \<noteq> x\<close> \<open>e > 0\<close> by simp
    show ?thesis
      apply (rule zne [OF in01])
      apply (rule e [THEN subsetD])
      apply (rule IntI)
        using \<open>y \<noteq> x\<close> \<open>e > 0\<close>
        apply (simp add: cball_def dist_norm algebra_simps)
        apply (simp add: Real_Vector_Spaces.scaleR_diff_right [symmetric] norm_minus_commute min_mult_distrib_right)
      apply (rule mem_affine [OF affine_affine_hull _ x])
      using \<open>y \<in> T\<close>  apply (auto simp: hull_inc)
      done
  qed
  show ?thesis
    apply (rule subset_antisym)
    using assms apply (simp add: hull_subset face_of_imp_subset)
    apply (cases "T={}", simp)
    apply (force simp: rel_interior_eq_empty [symmetric] \<open>convex T\<close> intro: *)
    done
qed

lemma face_of_imp_closed:
     fixes S :: "'a::euclidean_space set"
     assumes "convex S" "closed S" "T face_of S" shows "closed T"
  by (metis affine_affine_hull affine_closed closed_Int face_of_imp_eq_affine_Int assms)

lemma face_of_Int_supporting_hyperplane_le_strong:
    assumes "convex(S \<inter> {x. a \<bullet> x = b})" and aleb: "\<And>x. x \<in> S \<Longrightarrow> a \<bullet> x \<le> b"
      shows "(S \<inter> {x. a \<bullet> x = b}) face_of S"
proof -
  have *: "a \<bullet> u = a \<bullet> x" if "x \<in> open_segment u v" "u \<in> S" "v \<in> S" and b: "b = a \<bullet> x"
          for u v x
  proof (rule antisym)
    show "a \<bullet> u \<le> a \<bullet> x"
      using aleb \<open>u \<in> S\<close> \<open>b = a \<bullet> x\<close> by blast
  next
    obtain \<xi> where "b = a \<bullet> ((1 - \<xi>) *\<^sub>R u + \<xi> *\<^sub>R v)" "0 < \<xi>" "\<xi> < 1"
      using \<open>b = a \<bullet> x\<close> \<open>x \<in> open_segment u v\<close> in_segment
      by (auto simp: open_segment_image_interval split: if_split_asm)
    then have "b + \<xi> * (a \<bullet> u) \<le> a \<bullet> u + \<xi> * b"
      using aleb [OF \<open>v \<in> S\<close>] by (simp add: algebra_simps)
    then have "(1 - \<xi>) * b \<le> (1 - \<xi>) * (a \<bullet> u)"
      by (simp add: algebra_simps)
    then have "b \<le> a \<bullet> u"
      using \<open>\<xi> < 1\<close> by auto
    with b show "a \<bullet> x \<le> a \<bullet> u" by simp
  qed
  show ?thesis
    apply (simp add: face_of_def assms)
    using "*" open_segment_commute by blast
qed

lemma face_of_Int_supporting_hyperplane_ge_strong:
   "\<lbrakk>convex(S \<inter> {x. a \<bullet> x = b}); \<And>x. x \<in> S \<Longrightarrow> a \<bullet> x \<ge> b\<rbrakk>
    \<Longrightarrow> (S \<inter> {x. a \<bullet> x = b}) face_of S"
  using face_of_Int_supporting_hyperplane_le_strong [of S "-a" "-b"] by simp

lemma face_of_Int_supporting_hyperplane_le:
    "\<lbrakk>convex S; \<And>x. x \<in> S \<Longrightarrow> a \<bullet> x \<le> b\<rbrakk> \<Longrightarrow> (S \<inter> {x. a \<bullet> x = b}) face_of S"
  by (simp add: convex_Int convex_hyperplane face_of_Int_supporting_hyperplane_le_strong)

lemma face_of_Int_supporting_hyperplane_ge:
    "\<lbrakk>convex S; \<And>x. x \<in> S \<Longrightarrow> a \<bullet> x \<ge> b\<rbrakk> \<Longrightarrow> (S \<inter> {x. a \<bullet> x = b}) face_of S"
  by (simp add: convex_Int convex_hyperplane face_of_Int_supporting_hyperplane_ge_strong)

lemma face_of_imp_convex: "T face_of S \<Longrightarrow> convex T"
  using face_of_def by blast

lemma face_of_imp_compact:
    fixes S :: "'a::euclidean_space set"
    shows "\<lbrakk>convex S; compact S; T face_of S\<rbrakk> \<Longrightarrow> compact T"
  by (meson bounded_subset compact_eq_bounded_closed face_of_imp_closed face_of_imp_subset)

lemma face_of_Int_subface:
     "\<lbrakk>A \<inter> B face_of A; A \<inter> B face_of B; C face_of A; D face_of B\<rbrakk>
      \<Longrightarrow> (C \<inter> D) face_of C \<and> (C \<inter> D) face_of D"
  by (meson face_of_Int_Int face_of_face inf_le1 inf_le2)

lemma subset_of_face_of:
    fixes S :: "'a::real_normed_vector set"
    assumes "T face_of S" "u \<subseteq> S" "T \<inter> (rel_interior u) \<noteq> {}"
      shows "u \<subseteq> T"
proof
  fix c
  assume "c \<in> u"
  obtain b where "b \<in> T" "b \<in> rel_interior u" using assms by auto
  then obtain e where "e>0" "b \<in> u" and e: "cball b e \<inter> affine hull u \<subseteq> u"
    by (auto simp: rel_interior_cball)
  show "c \<in> T"
  proof (cases "b=c")
    case True with \<open>b \<in> T\<close> show ?thesis by blast
  next
    case False
    define d where "d = b + (e / norm(b - c)) *\<^sub>R (b - c)"
    have "d \<in> cball b e \<inter> affine hull u"
      using \<open>e > 0\<close> \<open>b \<in> u\<close> \<open>c \<in> u\<close>
      by (simp add: d_def dist_norm hull_inc mem_affine_3_minus False)
    with e have "d \<in> u" by blast
    have nbc: "norm (b - c) + e > 0" using \<open>e > 0\<close>
      by (metis add.commute le_less_trans less_add_same_cancel2 norm_ge_zero)
    then have [simp]: "d \<noteq> c" using False scaleR_cancel_left [of "1 + (e / norm (b - c))" b c]
      by (simp add: algebra_simps d_def) (simp add: divide_simps)
    have [simp]: "((e - e * e / (e + norm (b - c))) / norm (b - c)) = (e / (e + norm (b - c)))"
      using False nbc
      apply (simp add: algebra_simps divide_simps)
      by (metis mult_eq_0_iff norm_eq_zero norm_imp_pos_and_ge norm_pths(2) real_scaleR_def scaleR_left.add zero_less_norm_iff)
    have "b \<in> open_segment d c"
      apply (simp add: open_segment_image_interval)
      apply (simp add: d_def algebra_simps image_def)
      apply (rule_tac x="e / (e + norm (b - c))" in bexI)
      using False nbc \<open>0 < e\<close>
      apply (auto simp: algebra_simps)
      done
    then have "d \<in> T \<and> c \<in> T"
      apply (rule face_ofD [OF \<open>T face_of S\<close>])
      using \<open>d \<in> u\<close>  \<open>c \<in> u\<close> \<open>u \<subseteq> S\<close>  \<open>b \<in> T\<close>  apply auto
      done
    then show ?thesis ..
  qed
qed

lemma face_of_eq:
    fixes S :: "'a::real_normed_vector set"
    assumes "T face_of S" "u face_of S" "(rel_interior T) \<inter> (rel_interior u) \<noteq> {}"
      shows "T = u"
  apply (rule subset_antisym)
  apply (metis assms disjoint_iff_not_equal face_of_imp_subset rel_interior_subset subsetCE subset_of_face_of)
  by (metis assms disjoint_iff_not_equal face_of_imp_subset rel_interior_subset subset_iff subset_of_face_of)

lemma face_of_disjoint_rel_interior:
      fixes S :: "'a::real_normed_vector set"
      assumes "T face_of S" "T \<noteq> S"
        shows "T \<inter> rel_interior S = {}"
  by (meson assms subset_of_face_of face_of_imp_subset order_refl subset_antisym)

lemma face_of_disjoint_interior:
      fixes S :: "'a::real_normed_vector set"
      assumes "T face_of S" "T \<noteq> S"
        shows "T \<inter> interior S = {}"
proof -
  have "T \<inter> interior S \<subseteq> rel_interior S"
    by (meson inf_sup_ord(2) interior_subset_rel_interior order.trans)
  thus ?thesis
    by (metis (no_types) Int_greatest assms face_of_disjoint_rel_interior inf_sup_ord(1) subset_empty)
qed

lemma face_of_subset_rel_boundary:
  fixes S :: "'a::real_normed_vector set"
  assumes "T face_of S" "T \<noteq> S"
    shows "T \<subseteq> (S - rel_interior S)"
by (meson DiffI assms disjoint_iff_not_equal face_of_disjoint_rel_interior face_of_imp_subset rev_subsetD subsetI)

lemma face_of_subset_rel_frontier:
    fixes S :: "'a::real_normed_vector set"
    assumes "T face_of S" "T \<noteq> S"
      shows "T \<subseteq> rel_frontier S"
  using assms closure_subset face_of_disjoint_rel_interior face_of_imp_subset rel_frontier_def by fastforce

lemma face_of_aff_dim_lt:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S" "T face_of S" "T \<noteq> S"
    shows "aff_dim T < aff_dim S"
proof -
  have "aff_dim T \<le> aff_dim S"
    by (simp add: face_of_imp_subset aff_dim_subset assms)
  moreover have "aff_dim T \<noteq> aff_dim S"
  proof (cases "T = {}")
    case True then show ?thesis
      by (metis aff_dim_empty \<open>T \<noteq> S\<close>)
  next case False then show ?thesis
    by (metis Set.set_insert assms convex_rel_frontier_aff_dim dual_order.irrefl face_of_imp_convex face_of_subset_rel_frontier insert_not_empty subsetI)
  qed
  ultimately show ?thesis
    by simp
qed


lemma affine_diff_divide:
    assumes "affine S" "k \<noteq> 0" "k \<noteq> 1" and xy: "x \<in> S" "y /\<^sub>R (1 - k) \<in> S"
      shows "(x - y) /\<^sub>R k \<in> S"
proof -
  have "inverse(k) *\<^sub>R (x - y) = (1 - inverse k) *\<^sub>R inverse(1 - k) *\<^sub>R y + inverse(k) *\<^sub>R x"
    using assms
    by (simp add: algebra_simps) (simp add: scaleR_left_distrib [symmetric] divide_simps)
  then show ?thesis
    using \<open>affine S\<close> xy by (auto simp: affine_alt)
qed

lemma face_of_convex_hulls:
      assumes S: "finite S" "T \<subseteq> S" and disj: "affine hull T \<inter> convex hull (S - T) = {}"
      shows  "(convex hull T) face_of (convex hull S)"
proof -
  have fin: "finite T" "finite (S - T)" using assms
    by (auto simp: finite_subset)
  have *: "x \<in> convex hull T"
          if x: "x \<in> convex hull S" and y: "y \<in> convex hull S" and w: "w \<in> convex hull T" "w \<in> open_segment x y"
          for x y w
  proof -
    have waff: "w \<in> affine hull T"
      using convex_hull_subset_affine_hull w by blast
    obtain a b where a: "\<And>i. i \<in> S \<Longrightarrow> 0 \<le> a i" and asum: "sum a S = 1" and aeqx: "(\<Sum>i\<in>S. a i *\<^sub>R i) = x"
                 and b: "\<And>i. i \<in> S \<Longrightarrow> 0 \<le> b i" and bsum: "sum b S = 1" and beqy: "(\<Sum>i\<in>S. b i *\<^sub>R i) = y"
      using x y by (auto simp: assms convex_hull_finite)
    obtain u where "(1 - u) *\<^sub>R x + u *\<^sub>R y \<in> convex hull T" "x \<noteq> y" and weq: "w = (1 - u) *\<^sub>R x + u *\<^sub>R y"
               and u01: "0 < u" "u < 1"
      using w by (auto simp: open_segment_image_interval split: if_split_asm)
    define c where "c i = (1 - u) * a i + u * b i" for i
    have cge0: "\<And>i. i \<in> S \<Longrightarrow> 0 \<le> c i"
      using a b u01 by (simp add: c_def)
    have sumc1: "sum c S = 1"
      by (simp add: c_def sum.distrib sum_distrib_left [symmetric] asum bsum)
    have sumci_xy: "(\<Sum>i\<in>S. c i *\<^sub>R i) = (1 - u) *\<^sub>R x + u *\<^sub>R y"
      apply (simp add: c_def sum.distrib scaleR_left_distrib)
      by (simp only: scaleR_scaleR [symmetric] Real_Vector_Spaces.scaleR_right.sum [symmetric] aeqx beqy)
    show ?thesis
    proof (cases "sum c (S - T) = 0")
      case True
      have ci0: "\<And>i. i \<in> (S - T) \<Longrightarrow> c i = 0"
        using True cge0 by (simp add: \<open>finite S\<close> sum_nonneg_eq_0_iff)
      have a0: "a i = 0" if "i \<in> (S - T)" for i
        using ci0 [OF that] u01 a [of i] b [of i] that
        by (simp add: c_def Groups.ordered_comm_monoid_add_class.add_nonneg_eq_0_iff)
      have [simp]: "sum a T = 1"
        using assms by (metis sum.mono_neutral_cong_right a0 asum)
      show ?thesis
        apply (simp add: convex_hull_finite \<open>finite T\<close>)
        apply (rule_tac x=a in exI)
        using a0 assms
        apply (auto simp: cge0 a aeqx [symmetric] sum.mono_neutral_right)
        done
    next
      case False
      define k where "k = sum c (S - T)"
      have "k > 0" using False
        unfolding k_def by (metis DiffD1 antisym_conv cge0 sum_nonneg not_less)
      have weq_sumsum: "w = sum (\<lambda>x. c x *\<^sub>R x) T + sum (\<lambda>x. c x *\<^sub>R x) (S - T)"
        by (metis (no_types) add.commute S(1) S(2) sum.subset_diff sumci_xy weq)
      show ?thesis
      proof (cases "k = 1")
        case True
        then have "sum c T = 0"
          by (simp add: S k_def sum_diff sumc1)
        then have [simp]: "sum c (S - T) = 1"
          by (simp add: S sum_diff sumc1)
        have ci0: "\<And>i. i \<in> T \<Longrightarrow> c i = 0"
          by (meson \<open>finite T\<close> \<open>sum c T = 0\<close> \<open>T \<subseteq> S\<close> cge0 sum_nonneg_eq_0_iff subsetCE)
        then have [simp]: "(\<Sum>i\<in>S-T. c i *\<^sub>R i) = w"
          by (simp add: weq_sumsum)
        have "w \<in> convex hull (S - T)"
          apply (simp add: convex_hull_finite fin)
          apply (rule_tac x=c in exI)
          apply (auto simp: cge0 weq True k_def)
          done
        then show ?thesis
          using disj waff by blast
      next
        case False
        then have sumcf: "sum c T = 1 - k"
          by (simp add: S k_def sum_diff sumc1)
        have "(\<Sum>i\<in>T. c i *\<^sub>R i) /\<^sub>R (1 - k) \<in> convex hull T"
          apply (simp add: convex_hull_finite fin)
          apply (rule_tac x="\<lambda>i. inverse (1-k) * c i" in exI)
          apply auto
          apply (metis sumcf cge0 inverse_nonnegative_iff_nonnegative mult_nonneg_nonneg S(2) sum_nonneg subsetCE)
          apply (metis False mult.commute right_inverse right_minus_eq sum_distrib_left sumcf)
          by (metis (mono_tags, lifting) scaleR_right.sum scaleR_scaleR sum.cong)
        with \<open>0 < k\<close>  have "inverse(k) *\<^sub>R (w - sum (\<lambda>i. c i *\<^sub>R i) T) \<in> affine hull T"
          by (simp add: affine_diff_divide [OF affine_affine_hull] False waff convex_hull_subset_affine_hull [THEN subsetD])
        moreover have "inverse(k) *\<^sub>R (w - sum (\<lambda>x. c x *\<^sub>R x) T) \<in> convex hull (S - T)"
          apply (simp add: weq_sumsum convex_hull_finite fin)
          apply (rule_tac x="\<lambda>i. inverse k * c i" in exI)
          using \<open>k > 0\<close> cge0
          apply (auto simp: scaleR_right.sum sum_distrib_left [symmetric] k_def [symmetric])
          done
        ultimately show ?thesis
          using disj by blast
      qed
    qed
  qed
  have [simp]: "convex hull T \<subseteq> convex hull S"
    by (simp add: \<open>T \<subseteq> S\<close> hull_mono)
  show ?thesis
    using open_segment_commute by (auto simp: face_of_def intro: *)
qed

proposition face_of_convex_hull_insert:
   "\<lbrakk>finite S; a \<notin> affine hull S; T face_of convex hull S\<rbrakk> \<Longrightarrow> T face_of convex hull insert a S"
  apply (rule face_of_trans, blast)
  apply (rule face_of_convex_hulls; force simp: insert_Diff_if)
  done

proposition face_of_affine_trivial:
    assumes "affine S" "T face_of S"
    shows "T = {} \<or> T = S"
proof (rule ccontr, clarsimp)
  assume "T \<noteq> {}" "T \<noteq> S"
  then obtain a where "a \<in> T" by auto
  then have "a \<in> S"
    using \<open>T face_of S\<close> face_of_imp_subset by blast
  have "S \<subseteq> T"
  proof
    fix b  assume "b \<in> S"
    show "b \<in> T"
    proof (cases "a = b")
      case True with \<open>a \<in> T\<close> show ?thesis by auto
    next
      case False
      then have "a \<in> open_segment (2 *\<^sub>R a - b) b"
        apply (auto simp: open_segment_def closed_segment_def)
        apply (rule_tac x="1/2" in exI)
        apply (simp add: algebra_simps)
        by (simp add: scaleR_2)
      moreover have "2 *\<^sub>R a - b \<in> S"
        by (rule mem_affine [OF \<open>affine S\<close> \<open>a \<in> S\<close> \<open>b \<in> S\<close>, of 2 "-1", simplified])
      moreover note \<open>b \<in> S\<close> \<open>a \<in> T\<close>
      ultimately show ?thesis
        by (rule face_ofD [OF \<open>T face_of S\<close>, THEN conjunct2])
    qed
  qed
  then show False
    using \<open>T \<noteq> S\<close> \<open>T face_of S\<close> face_of_imp_subset by blast
qed


lemma face_of_affine_eq:
   "affine S \<Longrightarrow> (T face_of S \<longleftrightarrow> T = {} \<or> T = S)"
using affine_imp_convex face_of_affine_trivial face_of_refl by auto


lemma Inter_faces_finite_altbound:
    fixes T :: "'a::euclidean_space set set"
    assumes cfaI: "\<And>c. c \<in> T \<Longrightarrow> c face_of S"
    shows "\<exists>F'. finite F' \<and> F' \<subseteq> T \<and> card F' \<le> DIM('a) + 2 \<and> \<Inter>F' = \<Inter>T"
proof (cases "\<forall>F'. finite F' \<and> F' \<subseteq> T \<and> card F' \<le> DIM('a) + 2 \<longrightarrow> (\<exists>c. c \<in> T \<and> c \<inter> (\<Inter>F') \<subset> (\<Inter>F'))")
  case True
  then obtain c where c:
       "\<And>F'. \<lbrakk>finite F'; F' \<subseteq> T; card F' \<le> DIM('a) + 2\<rbrakk> \<Longrightarrow> c F' \<in> T \<and> c F' \<inter> (\<Inter>F') \<subset> (\<Inter>F')"
    by metis
  define d where "d = rec_nat {c{}} (\<lambda>n r. insert (c r) r)"
  have [simp]: "d 0 = {c {}}"
    by (simp add: d_def)
  have dSuc [simp]: "\<And>n. d (Suc n) = insert (c (d n)) (d n)"
    by (simp add: d_def)
  have dn_notempty: "d n \<noteq> {}" for n
    by (induction n) auto
  have dn_le_Suc: "d n \<subseteq> T \<and> finite(d n) \<and> card(d n) \<le> Suc n" if "n \<le> DIM('a) + 2" for n
  using that
  proof (induction n)
    case 0
    then show ?case by (simp add: c)
  next
    case (Suc n)
    then show ?case by (auto simp: c card_insert_if)
  qed
  have aff_dim_le: "aff_dim(\<Inter>(d n)) \<le> DIM('a) - int n" if "n \<le> DIM('a) + 2" for n
  using that
  proof (induction n)
    case 0
    then show ?case
      by (simp add: aff_dim_le_DIM)
  next
    case (Suc n)
    have fs: "\<Inter>d (Suc n) face_of S"
      by (meson Suc.prems cfaI dn_le_Suc dn_notempty face_of_Inter subsetCE)
    have condn: "convex (\<Inter>d n)"
      using Suc.prems nat_le_linear not_less_eq_eq
      by (blast intro: face_of_imp_convex cfaI convex_Inter dest: dn_le_Suc)
    have fdn: "\<Inter>d (Suc n) face_of \<Inter>d n"
      by (metis (no_types, lifting) Inter_anti_mono Suc.prems dSuc cfaI dn_le_Suc dn_notempty face_of_Inter face_of_imp_subset face_of_subset subset_iff subset_insertI)
    have ne: "\<Inter>d (Suc n) \<noteq> \<Inter>d n"
      by (metis (no_types, lifting) Suc.prems Suc_leD c complete_lattice_class.Inf_insert dSuc dn_le_Suc less_irrefl order.trans)
    have *: "\<And>m::int. \<And>d. \<And>d'::int. d < d' \<and> d' \<le> m - n \<Longrightarrow> d \<le> m - of_nat(n+1)"
      by arith
    have "aff_dim (\<Inter>d (Suc n)) < aff_dim (\<Inter>d n)"
      by (rule face_of_aff_dim_lt [OF condn fdn ne])
    moreover have "aff_dim (\<Inter>d n) \<le> int (DIM('a)) - int n"
      using Suc by auto
    ultimately
    have "aff_dim (\<Inter>d (Suc n)) \<le> int (DIM('a)) - (n+1)" by arith
    then show ?case by linarith
  qed
  have "aff_dim (\<Inter>d (DIM('a) + 2)) \<le> -2"
      using aff_dim_le [OF order_refl] by simp
  with aff_dim_geq [of "\<Inter>d (DIM('a) + 2)"] show ?thesis
    using order.trans by fastforce
next
  case False
  then show ?thesis
    apply simp
    apply (erule ex_forward)
    by blast
qed

lemma faces_of_translation:
   "{F. F face_of image (\<lambda>x. a + x) S} = image (image (\<lambda>x. a + x)) {F. F face_of S}"
apply (rule subset_antisym, clarify)
apply (auto simp: image_iff)
apply (metis face_of_imp_subset face_of_translation_eq subset_imageE)
done

proposition face_of_Times:
  assumes "F face_of S" and "F' face_of S'"
    shows "(F \<times> F') face_of (S \<times> S')"
proof -
  have "F \<times> F' \<subseteq> S \<times> S'"
    using assms [unfolded face_of_def] by blast
  moreover
  have "convex (F \<times> F')"
    using assms [unfolded face_of_def] by (blast intro: convex_Times)
  moreover
    have "a \<in> F \<and> a' \<in> F' \<and> b \<in> F \<and> b' \<in> F'"
       if "a \<in> S" "b \<in> S" "a' \<in> S'" "b' \<in> S'" "x \<in> F \<times> F'" "x \<in> open_segment (a,a') (b,b')"
       for a b a' b' x
  proof (cases "b=a \<or> b'=a'")
    case True with that show ?thesis
      using assms
      by (force simp: in_segment dest: face_ofD)
  next
    case False with assms [unfolded face_of_def] that show ?thesis
      by (blast dest!: open_segment_PairD)
  qed
  ultimately show ?thesis
    unfolding face_of_def by blast
qed

corollary face_of_Times_decomp:
    fixes S :: "'a::euclidean_space set" and S' :: "'b::euclidean_space set"
    shows "c face_of (S \<times> S') \<longleftrightarrow> (\<exists>F F'. F face_of S \<and> F' face_of S' \<and> c = F \<times> F')"
     (is "?lhs = ?rhs")
proof
  assume c: ?lhs
  show ?rhs
  proof (cases "c = {}")
    case True then show ?thesis by auto
  next
    case False
    have 1: "fst ` c \<subseteq> S" "snd ` c \<subseteq> S'"
      using c face_of_imp_subset by fastforce+
    have "convex c"
      using c by (metis face_of_imp_convex)
    have conv: "convex (fst ` c)" "convex (snd ` c)"
      by (simp_all add: \<open>convex c\<close> convex_linear_image fst_linear snd_linear)
    have fstab: "a \<in> fst ` c \<and> b \<in> fst ` c"
            if "a \<in> S" "b \<in> S" "x \<in> open_segment a b" "(x,x') \<in> c" for a b x x'
    proof -
      have *: "(x,x') \<in> open_segment (a,x') (b,x')"
        using that by (auto simp: in_segment)
      show ?thesis
        using face_ofD [OF c *] that face_of_imp_subset [OF c] by force
    qed
    have fst: "fst ` c face_of S"
      by (force simp: face_of_def 1 conv fstab)
    have sndab: "a' \<in> snd ` c \<and> b' \<in> snd ` c"
            if "a' \<in> S'" "b' \<in> S'" "x' \<in> open_segment a' b'" "(x,x') \<in> c" for a' b' x x'
    proof -
      have *: "(x,x') \<in> open_segment (x,a') (x,b')"
        using that by (auto simp: in_segment)
      show ?thesis
        using face_ofD [OF c *] that face_of_imp_subset [OF c] by force
    qed
    have snd: "snd ` c face_of S'"
      by (force simp: face_of_def 1 conv sndab)
    have cc: "rel_interior c \<subseteq> rel_interior (fst ` c) \<times> rel_interior (snd ` c)"
      by (force simp: face_of_Times rel_interior_Times conv fst snd \<open>convex c\<close> fst_linear snd_linear rel_interior_convex_linear_image [symmetric])
    have "c = fst ` c \<times> snd ` c"
      apply (rule face_of_eq [OF c])
      apply (simp_all add: face_of_Times rel_interior_Times conv fst snd)
      using False rel_interior_eq_empty \<open>convex c\<close> cc
      apply blast
      done
    with fst snd show ?thesis by metis
  qed
next
  assume ?rhs with face_of_Times show ?lhs by auto
qed

lemma face_of_Times_eq:
    fixes S :: "'a::euclidean_space set" and S' :: "'b::euclidean_space set"
    shows "(F \<times> F') face_of (S \<times> S') \<longleftrightarrow>
           F = {} \<or> F' = {} \<or> F face_of S \<and> F' face_of S'"
by (auto simp: face_of_Times_decomp times_eq_iff)

lemma hyperplane_face_of_halfspace_le: "{x. a \<bullet> x = b} face_of {x. a \<bullet> x \<le> b}"
proof -
  have "{x. a \<bullet> x \<le> b} \<inter> {x. a \<bullet> x = b} = {x. a \<bullet> x = b}"
    by auto
  with face_of_Int_supporting_hyperplane_le [OF convex_halfspace_le [of a b], of a b]
  show ?thesis by auto
qed

lemma hyperplane_face_of_halfspace_ge: "{x. a \<bullet> x = b} face_of {x. a \<bullet> x \<ge> b}"
proof -
  have "{x. a \<bullet> x \<ge> b} \<inter> {x. a \<bullet> x = b} = {x. a \<bullet> x = b}"
    by auto
  with face_of_Int_supporting_hyperplane_ge [OF convex_halfspace_ge [of b a], of b a]
  show ?thesis by auto
qed

lemma face_of_halfspace_le:
  fixes a :: "'n::euclidean_space"
  shows "F face_of {x. a \<bullet> x \<le> b} \<longleftrightarrow>
         F = {} \<or> F = {x. a \<bullet> x = b} \<or> F = {x. a \<bullet> x \<le> b}"
     (is "?lhs = ?rhs")
proof (cases "a = 0")
  case True then show ?thesis
    using face_of_affine_eq affine_UNIV by auto
next
  case False
  then have ine: "interior {x. a \<bullet> x \<le> b} \<noteq> {}"
    using halfspace_eq_empty_lt interior_halfspace_le by blast
  show ?thesis
  proof
    assume L: ?lhs
    have "F \<noteq> {x. a \<bullet> x \<le> b} \<Longrightarrow> F face_of {x. a \<bullet> x = b}"
      using False
      apply (simp add: frontier_halfspace_le [symmetric] rel_frontier_nonempty_interior [OF ine, symmetric])
      apply (rule face_of_subset [OF L])
      apply (simp add: face_of_subset_rel_frontier [OF L])
      apply (force simp: rel_frontier_def closed_halfspace_le)
      done
    with L show ?rhs
      using affine_hyperplane face_of_affine_eq by blast
  next
    assume ?rhs
    then show ?lhs
      by (metis convex_halfspace_le empty_face_of face_of_refl hyperplane_face_of_halfspace_le)
  qed
qed

lemma face_of_halfspace_ge:
  fixes a :: "'n::euclidean_space"
  shows "F face_of {x. a \<bullet> x \<ge> b} \<longleftrightarrow>
         F = {} \<or> F = {x. a \<bullet> x = b} \<or> F = {x. a \<bullet> x \<ge> b}"
using face_of_halfspace_le [of F "-a" "-b"] by simp

subsection\<open>Exposed faces\<close>

text\<open>That is, faces that are intersection with supporting hyperplane\<close>

definition exposed_face_of :: "['a::euclidean_space set, 'a set] \<Rightarrow> bool"
                               (infixr "(exposed'_face'_of)" 50)
  where "T exposed_face_of S \<longleftrightarrow>
         T face_of S \<and> (\<exists>a b. S \<subseteq> {x. a \<bullet> x \<le> b} \<and> T = S \<inter> {x. a \<bullet> x = b})"

lemma empty_exposed_face_of [iff]: "{} exposed_face_of S"
  apply (simp add: exposed_face_of_def)
  apply (rule_tac x=0 in exI)
  apply (rule_tac x=1 in exI, force)
  done

lemma exposed_face_of_refl_eq [simp]: "S exposed_face_of S \<longleftrightarrow> convex S"
  apply (simp add: exposed_face_of_def face_of_refl_eq, auto)
  apply (rule_tac x=0 in exI)+
  apply force
  done

lemma exposed_face_of_refl: "convex S \<Longrightarrow> S exposed_face_of S"
  by simp

lemma exposed_face_of:
    "T exposed_face_of S \<longleftrightarrow>
     T face_of S \<and>
     (T = {} \<or> T = S \<or>
      (\<exists>a b. a \<noteq> 0 \<and> S \<subseteq> {x. a \<bullet> x \<le> b} \<and> T = S \<inter> {x. a \<bullet> x = b}))"
proof (cases "T = {}")
  case True then show ?thesis
    by simp
next
  case False
  show ?thesis
  proof (cases "T = S")
    case True then show ?thesis
      by (simp add: face_of_refl_eq)
  next
    case False
    with \<open>T \<noteq> {}\<close> show ?thesis
      apply (auto simp: exposed_face_of_def)
      apply (metis inner_zero_left)
      done
  qed
qed

lemma exposed_face_of_Int_supporting_hyperplane_le:
   "\<lbrakk>convex S; \<And>x. x \<in> S \<Longrightarrow> a \<bullet> x \<le> b\<rbrakk> \<Longrightarrow> (S \<inter> {x. a \<bullet> x = b}) exposed_face_of S"
by (force simp: exposed_face_of_def face_of_Int_supporting_hyperplane_le)

lemma exposed_face_of_Int_supporting_hyperplane_ge:
   "\<lbrakk>convex S; \<And>x. x \<in> S \<Longrightarrow> a \<bullet> x \<ge> b\<rbrakk> \<Longrightarrow> (S \<inter> {x. a \<bullet> x = b}) exposed_face_of S"
using exposed_face_of_Int_supporting_hyperplane_le [of S "-a" "-b"] by simp

proposition exposed_face_of_Int:
  assumes "T exposed_face_of S"
      and "u exposed_face_of S"
    shows "(T \<inter> u) exposed_face_of S"
proof -
  obtain a b where T: "S \<inter> {x. a \<bullet> x = b} face_of S"
               and S: "S \<subseteq> {x. a \<bullet> x \<le> b}"
               and teq: "T = S \<inter> {x. a \<bullet> x = b}"
    using assms by (auto simp: exposed_face_of_def)
  obtain a' b' where u: "S \<inter> {x. a' \<bullet> x = b'} face_of S"
                 and s': "S \<subseteq> {x. a' \<bullet> x \<le> b'}"
                 and ueq: "u = S \<inter> {x. a' \<bullet> x = b'}"
    using assms by (auto simp: exposed_face_of_def)
  have tu: "T \<inter> u face_of S"
    using T teq u ueq by (simp add: face_of_Int)
  have ss: "S \<subseteq> {x. (a + a') \<bullet> x \<le> b + b'}"
    using S s' by (force simp: inner_left_distrib)
  show ?thesis
    apply (simp add: exposed_face_of_def tu)
    apply (rule_tac x="a+a'" in exI)
    apply (rule_tac x="b+b'" in exI)
    using S s'
    apply (fastforce simp: ss inner_left_distrib teq ueq)
    done
qed

proposition exposed_face_of_Inter:
    fixes P :: "'a::euclidean_space set set"
  assumes "P \<noteq> {}"
      and "\<And>T. T \<in> P \<Longrightarrow> T exposed_face_of S"
    shows "\<Inter>P exposed_face_of S"
proof -
  obtain Q where "finite Q" and QsubP: "Q \<subseteq> P" "card Q \<le> DIM('a) + 2" and IntQ: "\<Inter>Q = \<Inter>P"
    using Inter_faces_finite_altbound [of P S] assms [unfolded exposed_face_of]
    by force
  show ?thesis
  proof (cases "Q = {}")
    case True then show ?thesis
      by (metis Inf_empty Inf_lower IntQ assms ex_in_conv subset_antisym top_greatest)
  next
    case False
    have "Q \<subseteq> {T. T exposed_face_of S}"
      using QsubP assms by blast
    moreover have "Q \<subseteq> {T. T exposed_face_of S} \<Longrightarrow> \<Inter>Q exposed_face_of S"
      using \<open>finite Q\<close> False
      apply (induction Q rule: finite_induct)
      using exposed_face_of_Int apply fastforce+
      done
    ultimately show ?thesis
      by (simp add: IntQ)
  qed
qed

proposition exposed_face_of_sums:
  assumes "convex S" and "convex T"
      and "F exposed_face_of {x + y | x y. x \<in> S \<and> y \<in> T}"
          (is "F exposed_face_of ?ST")
  obtains k l
    where "k exposed_face_of S" "l exposed_face_of T"
          "F = {x + y | x y. x \<in> k \<and> y \<in> l}"
proof (cases "F = {}")
  case True then show ?thesis
    using that by blast
next
  case False
  show ?thesis
  proof (cases "F = ?ST")
    case True then show ?thesis
      using assms exposed_face_of_refl_eq that by blast
  next
    case False
    obtain p where "p \<in> F" using \<open>F \<noteq> {}\<close> by blast
    moreover
    obtain u z where T: "?ST \<inter> {x. u \<bullet> x = z} face_of ?ST"
                 and S: "?ST \<subseteq> {x. u \<bullet> x \<le> z}"
                 and feq: "F = ?ST \<inter> {x. u \<bullet> x = z}"
      using assms by (auto simp: exposed_face_of_def)
    ultimately obtain a0 b0
            where p: "p = a0 + b0" and "a0 \<in> S" "b0 \<in> T" and z: "u \<bullet> p = z"
      by auto
    have lez: "u \<bullet> (x + y) \<le> z" if "x \<in> S" "y \<in> T" for x y
      using S that by auto
    have sef: "S \<inter> {x. u \<bullet> x = u \<bullet> a0} exposed_face_of S"
      apply (rule exposed_face_of_Int_supporting_hyperplane_le [OF \<open>convex S\<close>])
      apply (metis p z add_le_cancel_right inner_right_distrib lez [OF _ \<open>b0 \<in> T\<close>])
      done
    have tef: "T \<inter> {x. u \<bullet> x = u \<bullet> b0} exposed_face_of T"
      apply (rule exposed_face_of_Int_supporting_hyperplane_le [OF \<open>convex T\<close>])
      apply (metis p z add.commute add_le_cancel_right inner_right_distrib lez [OF \<open>a0 \<in> S\<close>])
      done
    have "{x + y |x y. x \<in> S \<and> u \<bullet> x = u \<bullet> a0 \<and> y \<in> T \<and> u \<bullet> y = u \<bullet> b0} \<subseteq> F"
      by (auto simp: feq) (metis inner_right_distrib p z)
    moreover have "F \<subseteq> {x + y |x y. x \<in> S \<and> u \<bullet> x = u \<bullet> a0 \<and> y \<in> T \<and> u \<bullet> y = u \<bullet> b0}"
      apply (auto simp: feq)
      apply (rename_tac x y)
      apply (rule_tac x=x in exI)
      apply (rule_tac x=y in exI, simp)
      using z p \<open>a0 \<in> S\<close> \<open>b0 \<in> T\<close>
      apply clarify
      apply (simp add: inner_right_distrib)
      apply (metis add_le_cancel_right antisym lez [unfolded inner_right_distrib] add.commute)
      done
    ultimately have "F = {x + y |x y. x \<in> S \<inter> {x. u \<bullet> x = u \<bullet> a0} \<and> y \<in> T \<inter> {x. u \<bullet> x = u \<bullet> b0}}"
      by blast
    then show ?thesis
      by (rule that [OF sef tef])
  qed
qed

subsection\<open>Extreme points of a set: its singleton faces\<close>

definition extreme_point_of :: "['a::real_vector, 'a set] \<Rightarrow> bool"
                               (infixr "(extreme'_point'_of)" 50)
  where "x extreme_point_of S \<longleftrightarrow>
         x \<in> S \<and> (\<forall>a \<in> S. \<forall>b \<in> S. x \<notin> open_segment a b)"

lemma extreme_point_of_stillconvex:
   "convex S \<Longrightarrow> (x extreme_point_of S \<longleftrightarrow> x \<in> S \<and> convex(S - {x}))"
  by (fastforce simp add: convex_contains_segment extreme_point_of_def open_segment_def)

lemma face_of_singleton:
   "{x} face_of S \<longleftrightarrow> x extreme_point_of S"
by (fastforce simp add: extreme_point_of_def face_of_def)

lemma extreme_point_not_in_REL_INTERIOR:
    fixes S :: "'a::real_normed_vector set"
    shows "\<lbrakk>x extreme_point_of S; S \<noteq> {x}\<rbrakk> \<Longrightarrow> x \<notin> rel_interior S"
apply (simp add: face_of_singleton [symmetric])
apply (blast dest: face_of_disjoint_rel_interior)
done

lemma extreme_point_not_in_interior:
    fixes S :: "'a::{real_normed_vector, perfect_space} set"
    shows "x extreme_point_of S \<Longrightarrow> x \<notin> interior S"
apply (case_tac "S = {x}")
apply (simp add: empty_interior_finite)
by (meson contra_subsetD extreme_point_not_in_REL_INTERIOR interior_subset_rel_interior)

lemma extreme_point_of_face:
     "F face_of S \<Longrightarrow> v extreme_point_of F \<longleftrightarrow> v extreme_point_of S \<and> v \<in> F"
  by (meson empty_subsetI face_of_face face_of_singleton insert_subset)

lemma extreme_point_of_convex_hull:
   "x extreme_point_of (convex hull S) \<Longrightarrow> x \<in> S"
apply (simp add: extreme_point_of_stillconvex)
using hull_minimal [of S "(convex hull S) - {x}" convex]
using hull_subset [of S convex]
apply blast
done

lemma extreme_points_of_convex_hull:
   "{x. x extreme_point_of (convex hull S)} \<subseteq> S"
using extreme_point_of_convex_hull by auto

lemma extreme_point_of_empty [simp]: "~ (x extreme_point_of {})"
  by (simp add: extreme_point_of_def)

lemma extreme_point_of_singleton [iff]: "x extreme_point_of {a} \<longleftrightarrow> x = a"
  using extreme_point_of_stillconvex by auto

lemma extreme_point_of_translation_eq:
   "(a + x) extreme_point_of (image (\<lambda>x. a + x) S) \<longleftrightarrow> x extreme_point_of S"
by (auto simp: extreme_point_of_def)

lemma extreme_points_of_translation:
   "{x. x extreme_point_of (image (\<lambda>x. a + x) S)} =
    (\<lambda>x. a + x) ` {x. x extreme_point_of S}"
using extreme_point_of_translation_eq
by auto (metis (no_types, lifting) image_iff mem_Collect_eq minus_add_cancel)

lemma extreme_point_of_Int:
   "\<lbrakk>x extreme_point_of S; x extreme_point_of T\<rbrakk> \<Longrightarrow> x extreme_point_of (S \<inter> T)"
by (simp add: extreme_point_of_def)

lemma extreme_point_of_Int_supporting_hyperplane_le:
   "\<lbrakk>S \<inter> {x. a \<bullet> x = b} = {c}; \<And>x. x \<in> S \<Longrightarrow> a \<bullet> x \<le> b\<rbrakk> \<Longrightarrow> c extreme_point_of S"
apply (simp add: face_of_singleton [symmetric])
by (metis face_of_Int_supporting_hyperplane_le_strong convex_singleton)

lemma extreme_point_of_Int_supporting_hyperplane_ge:
   "\<lbrakk>S \<inter> {x. a \<bullet> x = b} = {c}; \<And>x. x \<in> S \<Longrightarrow> a \<bullet> x \<ge> b\<rbrakk> \<Longrightarrow> c extreme_point_of S"
apply (simp add: face_of_singleton [symmetric])
by (metis face_of_Int_supporting_hyperplane_ge_strong convex_singleton)

lemma exposed_point_of_Int_supporting_hyperplane_le:
   "\<lbrakk>S \<inter> {x. a \<bullet> x = b} = {c}; \<And>x. x \<in> S \<Longrightarrow> a \<bullet> x \<le> b\<rbrakk> \<Longrightarrow> {c} exposed_face_of S"
apply (simp add: exposed_face_of_def face_of_singleton)
apply (force simp: extreme_point_of_Int_supporting_hyperplane_le)
done

lemma exposed_point_of_Int_supporting_hyperplane_ge:
    "\<lbrakk>S \<inter> {x. a \<bullet> x = b} = {c}; \<And>x. x \<in> S \<Longrightarrow> a \<bullet> x \<ge> b\<rbrakk> \<Longrightarrow> {c} exposed_face_of S"
using exposed_point_of_Int_supporting_hyperplane_le [of S "-a" "-b" c]
by simp

lemma extreme_point_of_convex_hull_insert:
   "\<lbrakk>finite S; a \<notin> convex hull S\<rbrakk> \<Longrightarrow> a extreme_point_of (convex hull (insert a S))"
apply (case_tac "a \<in> S")
apply (simp add: hull_inc)
using face_of_convex_hulls [of "insert a S" "{a}"]
apply (auto simp: face_of_singleton hull_same)
done

subsection\<open>Facets\<close>

definition facet_of :: "['a::euclidean_space set, 'a set] \<Rightarrow> bool"
                    (infixr "(facet'_of)" 50)
  where "F facet_of S \<longleftrightarrow> F face_of S \<and> F \<noteq> {} \<and> aff_dim F = aff_dim S - 1"

lemma facet_of_empty [simp]: "~ S facet_of {}"
  by (simp add: facet_of_def)

lemma facet_of_irrefl [simp]: "~ S facet_of S "
  by (simp add: facet_of_def)

lemma facet_of_imp_face_of: "F facet_of S \<Longrightarrow> F face_of S"
  by (simp add: facet_of_def)

lemma facet_of_imp_subset: "F facet_of S \<Longrightarrow> F \<subseteq> S"
  by (simp add: face_of_imp_subset facet_of_def)

lemma hyperplane_facet_of_halfspace_le:
   "a \<noteq> 0 \<Longrightarrow> {x. a \<bullet> x = b} facet_of {x. a \<bullet> x \<le> b}"
unfolding facet_of_def hyperplane_eq_empty
by (auto simp: hyperplane_face_of_halfspace_ge hyperplane_face_of_halfspace_le
           DIM_positive Suc_leI of_nat_diff aff_dim_halfspace_le)

lemma hyperplane_facet_of_halfspace_ge:
    "a \<noteq> 0 \<Longrightarrow> {x. a \<bullet> x = b} facet_of {x. a \<bullet> x \<ge> b}"
unfolding facet_of_def hyperplane_eq_empty
by (auto simp: hyperplane_face_of_halfspace_le hyperplane_face_of_halfspace_ge
           DIM_positive Suc_leI of_nat_diff aff_dim_halfspace_ge)

lemma facet_of_halfspace_le:
    "F facet_of {x. a \<bullet> x \<le> b} \<longleftrightarrow> a \<noteq> 0 \<and> F = {x. a \<bullet> x = b}"
    (is "?lhs = ?rhs")
proof
  assume c: ?lhs
  with c facet_of_irrefl show ?rhs
    by (force simp: aff_dim_halfspace_le facet_of_def face_of_halfspace_le cong: conj_cong split: if_split_asm)
next
  assume ?rhs then show ?lhs
    by (simp add: hyperplane_facet_of_halfspace_le)
qed

lemma facet_of_halfspace_ge:
    "F facet_of {x. a \<bullet> x \<ge> b} \<longleftrightarrow> a \<noteq> 0 \<and> F = {x. a \<bullet> x = b}"
using facet_of_halfspace_le [of F "-a" "-b"] by simp

subsection \<open>Edges: faces of affine dimension 1\<close>

definition edge_of :: "['a::euclidean_space set, 'a set] \<Rightarrow> bool"  (infixr "(edge'_of)" 50)
  where "e edge_of S \<longleftrightarrow> e face_of S \<and> aff_dim e = 1"

lemma edge_of_imp_subset:
   "S edge_of T \<Longrightarrow> S \<subseteq> T"
by (simp add: edge_of_def face_of_imp_subset)

subsection\<open>Existence of extreme points\<close>

lemma different_norm_3_collinear_points:
  fixes a :: "'a::euclidean_space"
  assumes "x \<in> open_segment a b" "norm(a) = norm(b)" "norm(x) = norm(b)"
  shows False
proof -
  obtain u where "norm ((1 - u) *\<^sub>R a + u *\<^sub>R b) = norm b"
             and "a \<noteq> b"
             and u01: "0 < u" "u < 1"
    using assms by (auto simp: open_segment_image_interval if_splits)
  then have "(1 - u) *\<^sub>R a \<bullet> (1 - u) *\<^sub>R a + ((1 - u) * 2) *\<^sub>R a \<bullet> u *\<^sub>R b =
             (1 - u * u) *\<^sub>R (a \<bullet> a)"
    using assms by (simp add: norm_eq algebra_simps inner_commute)
  then have "(1 - u) *\<^sub>R ((1 - u) *\<^sub>R a \<bullet> a + (2 * u) *\<^sub>R  a \<bullet> b) =
             (1 - u) *\<^sub>R ((1 + u) *\<^sub>R (a \<bullet> a))"
    by (simp add: algebra_simps)
  then have "(1 - u) *\<^sub>R (a \<bullet> a) + (2 * u) *\<^sub>R (a \<bullet> b) = (1 + u) *\<^sub>R (a \<bullet> a)"
    using u01 by auto
  then have "a \<bullet> b = a \<bullet> a"
    using u01 by (simp add: algebra_simps)
  then have "a = b"
    using \<open>norm(a) = norm(b)\<close> norm_eq vector_eq by fastforce
  then show ?thesis
    using \<open>a \<noteq> b\<close> by force
qed

proposition extreme_point_exists_convex:
  fixes S :: "'a::euclidean_space set"
  assumes "compact S" "convex S" "S \<noteq> {}"
  obtains x where "x extreme_point_of S"
proof -
  obtain x where "x \<in> S" and xsup: "\<And>y. y \<in> S \<Longrightarrow> norm y \<le> norm x"
    using distance_attains_sup [of S 0] assms by auto
  have False if "a \<in> S" "b \<in> S" and x: "x \<in> open_segment a b" for a b
  proof -
    have noax: "norm a \<le> norm x" and nobx: "norm b \<le> norm x" using xsup that by auto
    have "a \<noteq> b"
      using empty_iff open_segment_idem x by auto
    have *: "(1 - u) * na + u * nb < norm x" if "na < norm x"  "nb \<le> norm x" "0 < u" "u < 1" for na nb u
    proof -
      have "(1 - u) * na + u * nb < (1 - u) * norm x + u * nb"
        by (simp add: that)
      also have "... \<le> (1 - u) * norm x + u * norm x"
        by (simp add: that)
      finally have "(1 - u) * na + u * nb < (1 - u) * norm x + u * norm x" .
      then show ?thesis
      using scaleR_collapse [symmetric, of "norm x" u] by auto
    qed
    have "norm x < norm x" if "norm a < norm x"
      using x
      apply (clarsimp simp only: open_segment_image_interval \<open>a \<noteq> b\<close> if_False)
      apply (rule norm_triangle_lt)
      apply (simp add: norm_mult)
      using * [of "norm a" "norm b"] nobx that
        apply blast
      done
    moreover have "norm x < norm x" if "norm b < norm x"
      using x
      apply (clarsimp simp only: open_segment_image_interval \<open>a \<noteq> b\<close> if_False)
      apply (rule norm_triangle_lt)
      apply (simp add: norm_mult)
      using * [of "norm b" "norm a" "1-u" for u] noax that
        apply (simp add: add.commute)
      done
    ultimately have "~ (norm a < norm x) \<and> ~ (norm b < norm x)"
      by auto
    then show ?thesis
      using different_norm_3_collinear_points noax nobx that(3) by fastforce
  qed
  then show ?thesis
    apply (rule_tac x=x in that)
    apply (force simp: extreme_point_of_def \<open>x \<in> S\<close>)
    done
qed

subsection\<open>Krein-Milman, the weaker form\<close>

proposition Krein_Milman:
  fixes S :: "'a::euclidean_space set"
  assumes "compact S" "convex S"
    shows "S = closure(convex hull {x. x extreme_point_of S})"
proof (cases "S = {}")
  case True then show ?thesis   by simp
next
  case False
  have "closed S"
    by (simp add: \<open>compact S\<close> compact_imp_closed)
  have "closure (convex hull {x. x extreme_point_of S}) \<subseteq> S"
    apply (rule closure_minimal [OF hull_minimal \<open>closed S\<close>])
    using assms
    apply (auto simp: extreme_point_of_def)
    done
  moreover have "u \<in> closure (convex hull {x. x extreme_point_of S})"
                if "u \<in> S" for u
  proof (rule ccontr)
    assume unot: "u \<notin> closure(convex hull {x. x extreme_point_of S})"
    then obtain a b where "a \<bullet> u < b"
          and ab: "\<And>x. x \<in> closure(convex hull {x. x extreme_point_of S}) \<Longrightarrow> b < a \<bullet> x"
      using separating_hyperplane_closed_point [of "closure(convex hull {x. x extreme_point_of S})"]
      by blast
    have "continuous_on S (op \<bullet> a)"
      by (rule continuous_intros)+
    then obtain m where "m \<in> S" and m: "\<And>y. y \<in> S \<Longrightarrow> a \<bullet> m \<le> a \<bullet> y"
      using continuous_attains_inf [of S "\<lambda>x. a \<bullet> x"] \<open>compact S\<close> \<open>u \<in> S\<close>
      by auto
    define T where "T = S \<inter> {x. a \<bullet> x = a \<bullet> m}"
    have "m \<in> T"
      by (simp add: T_def \<open>m \<in> S\<close>)
    moreover have "compact T"
      by (simp add: T_def compact_Int_closed [OF \<open>compact S\<close> closed_hyperplane])
    moreover have "convex T"
      by (simp add: T_def convex_Int [OF \<open>convex S\<close> convex_hyperplane])
    ultimately obtain v where v: "v extreme_point_of T"
      using extreme_point_exists_convex [of T] by auto
    then have "{v} face_of T"
      by (simp add: face_of_singleton)
    also have "T face_of S"
      by (simp add: T_def m face_of_Int_supporting_hyperplane_ge [OF \<open>convex S\<close>])
    finally have "v extreme_point_of S"
      by (simp add: face_of_singleton)
    then have "b < a \<bullet> v"
      using closure_subset by (simp add: closure_hull hull_inc ab)
    then show False
      using \<open>a \<bullet> u < b\<close> \<open>{v} face_of T\<close> face_of_imp_subset m T_def that by fastforce
  qed
  ultimately show ?thesis
    by blast
qed

text\<open>Now the sharper form.\<close>

lemma Krein_Milman_Minkowski_aux:
  fixes S :: "'a::euclidean_space set"
  assumes n: "dim S = n" and S: "compact S" "convex S" "0 \<in> S"
    shows "0 \<in> convex hull {x. x extreme_point_of S}"
using n S
proof (induction n arbitrary: S rule: less_induct)
  case (less n S) show ?case
  proof (cases "0 \<in> rel_interior S")
    case True with Krein_Milman show ?thesis
      by (metis subsetD convex_convex_hull convex_rel_interior_closure less.prems(2) less.prems(3) rel_interior_subset)
  next
    case False
    have "rel_interior S \<noteq> {}"
      by (simp add: rel_interior_convex_nonempty_aux less)
    then obtain c where c: "c \<in> rel_interior S" by blast
    obtain a where "a \<noteq> 0"
              and le_ay: "\<And>y. y \<in> S \<Longrightarrow> a \<bullet> 0 \<le> a \<bullet> y"
              and less_ay: "\<And>y. y \<in> rel_interior S \<Longrightarrow> a \<bullet> 0 < a \<bullet> y"
      by (blast intro: supporting_hyperplane_rel_boundary intro!: less False)
    have face: "S \<inter> {x. a \<bullet> x = 0} face_of S"
      apply (rule face_of_Int_supporting_hyperplane_ge [OF \<open>convex S\<close>])
      using le_ay by auto
    then have co: "compact (S \<inter> {x. a \<bullet> x = 0})" "convex (S \<inter> {x. a \<bullet> x = 0})"
      using less.prems by (blast intro: face_of_imp_compact face_of_imp_convex)+
    have "a \<bullet> y = 0" if "y \<in> span (S \<inter> {x. a \<bullet> x = 0})" for y
    proof -
      have "y \<in> span {x. a \<bullet> x = 0}"
        by (metis inf.cobounded2 span_mono subsetCE that)
      then show ?thesis
        by (blast intro: span_induct [OF _ subspace_hyperplane])
    qed
    then have "dim (S \<inter> {x. a \<bullet> x = 0}) < n"
      by (metis (no_types) less_ay c subsetD dim_eq_span inf.strict_order_iff
           inf_le1 \<open>dim S = n\<close> not_le rel_interior_subset span_0 span_clauses(1))
    then have "0 \<in> convex hull {x. x extreme_point_of (S \<inter> {x. a \<bullet> x = 0})}"
      by (rule less.IH) (auto simp: co less.prems)
    then show ?thesis
      by (metis (mono_tags, lifting) Collect_mono_iff \<open>S \<inter> {x. a \<bullet> x = 0} face_of S\<close> extreme_point_of_face hull_mono subset_iff)
  qed
qed


theorem Krein_Milman_Minkowski:
  fixes S :: "'a::euclidean_space set"
  assumes "compact S" "convex S"
    shows "S = convex hull {x. x extreme_point_of S}"
proof
  show "S \<subseteq> convex hull {x. x extreme_point_of S}"
  proof
    fix a assume [simp]: "a \<in> S"
    have 1: "compact (op + (- a) ` S)"
      by (simp add: \<open>compact S\<close> compact_translation)
    have 2: "convex (op + (- a) ` S)"
      by (simp add: \<open>convex S\<close> convex_translation)
    show a_invex: "a \<in> convex hull {x. x extreme_point_of S}"
      using Krein_Milman_Minkowski_aux [OF refl 1 2]
            convex_hull_translation [of "-a"]
      by (auto simp: extreme_points_of_translation translation_assoc)
    qed
next
  show "convex hull {x. x extreme_point_of S} \<subseteq> S"
  proof -
    have "{a. a extreme_point_of S} \<subseteq> S"
      using extreme_point_of_def by blast
    then show ?thesis
      by (simp add: \<open>convex S\<close> hull_minimal)
  qed
qed


subsection\<open>Applying it to convex hulls of explicitly indicated finite sets\<close>

lemma Krein_Milman_polytope:
  fixes S :: "'a::euclidean_space set"
  shows
   "finite S
       \<Longrightarrow> convex hull S =
           convex hull {x. x extreme_point_of (convex hull S)}"
by (simp add: Krein_Milman_Minkowski finite_imp_compact_convex_hull)

lemma extreme_points_of_convex_hull_eq:
  fixes S :: "'a::euclidean_space set"
  shows
   "\<lbrakk>compact S; \<And>T. T \<subset> S \<Longrightarrow> convex hull T \<noteq> convex hull S\<rbrakk>
        \<Longrightarrow> {x. x extreme_point_of (convex hull S)} = S"
by (metis (full_types) Krein_Milman_Minkowski compact_convex_hull convex_convex_hull extreme_points_of_convex_hull psubsetI)


lemma extreme_point_of_convex_hull_eq:
  fixes S :: "'a::euclidean_space set"
  shows
   "\<lbrakk>compact S; \<And>T. T \<subset> S \<Longrightarrow> convex hull T \<noteq> convex hull S\<rbrakk>
    \<Longrightarrow> (x extreme_point_of (convex hull S) \<longleftrightarrow> x \<in> S)"
using extreme_points_of_convex_hull_eq by auto

lemma extreme_point_of_convex_hull_convex_independent:
  fixes S :: "'a::euclidean_space set"
  assumes "compact S" and S: "\<And>a. a \<in> S \<Longrightarrow> a \<notin> convex hull (S - {a})"
  shows "(x extreme_point_of (convex hull S) \<longleftrightarrow> x \<in> S)"
proof -
  have "convex hull T \<noteq> convex hull S" if "T \<subset> S" for T
  proof -
    obtain a where  "T \<subseteq> S" "a \<in> S" "a \<notin> T" using \<open>T \<subset> S\<close> by blast
    then show ?thesis
      by (metis (full_types) Diff_eq_empty_iff Diff_insert0 S hull_mono hull_subset insert_Diff_single subsetCE)
  qed
  then show ?thesis
    by (rule extreme_point_of_convex_hull_eq [OF \<open>compact S\<close>])
qed

lemma extreme_point_of_convex_hull_affine_independent:
  fixes S :: "'a::euclidean_space set"
  shows
   "~ affine_dependent S
         \<Longrightarrow> (x extreme_point_of (convex hull S) \<longleftrightarrow> x \<in> S)"
by (metis aff_independent_finite affine_dependent_def affine_hull_convex_hull extreme_point_of_convex_hull_convex_independent finite_imp_compact hull_inc)

text\<open>Elementary proofs exist, not requiring Euclidean spaces and all this development\<close>
lemma extreme_point_of_convex_hull_2:
  fixes x :: "'a::euclidean_space"
  shows "x extreme_point_of (convex hull {a,b}) \<longleftrightarrow> x = a \<or> x = b"
proof -
  have "x extreme_point_of (convex hull {a,b}) \<longleftrightarrow> x \<in> {a,b}"
    by (intro extreme_point_of_convex_hull_affine_independent affine_independent_2)
  then show ?thesis
    by simp
qed

lemma extreme_point_of_segment:
  fixes x :: "'a::euclidean_space"
  shows
   "x extreme_point_of closed_segment a b \<longleftrightarrow> x = a \<or> x = b"
by (simp add: extreme_point_of_convex_hull_2 segment_convex_hull)

lemma face_of_convex_hull_subset:
  fixes S :: "'a::euclidean_space set"
  assumes "compact S" and T: "T face_of (convex hull S)"
  obtains s' where "s' \<subseteq> S" "T = convex hull s'"
apply (rule_tac s' = "{x. x extreme_point_of T}" in that)
using T extreme_point_of_convex_hull extreme_point_of_face apply blast
by (metis (no_types) Krein_Milman_Minkowski assms compact_convex_hull convex_convex_hull face_of_imp_compact face_of_imp_convex)


proposition face_of_convex_hull_affine_independent:
  fixes S :: "'a::euclidean_space set"
  assumes "~ affine_dependent S"
    shows "(T face_of (convex hull S) \<longleftrightarrow> (\<exists>c. c \<subseteq> S \<and> T = convex hull c))"
          (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    by (meson \<open>T face_of convex hull S\<close> aff_independent_finite assms face_of_convex_hull_subset finite_imp_compact)
next
  assume ?rhs
  then obtain c where "c \<subseteq> S" and T: "T = convex hull c"
    by blast
  have "affine hull c \<inter> affine hull (S - c) = {}"
    apply (rule disjoint_affine_hull [OF assms \<open>c \<subseteq> S\<close>], auto)
    done
  then have "affine hull c \<inter> convex hull (S - c) = {}"
    using convex_hull_subset_affine_hull by fastforce
  then show ?lhs
    by (metis face_of_convex_hulls \<open>c \<subseteq> S\<close> aff_independent_finite assms T)
qed

lemma facet_of_convex_hull_affine_independent:
  fixes S :: "'a::euclidean_space set"
  assumes "~ affine_dependent S"
    shows "T facet_of (convex hull S) \<longleftrightarrow>
           T \<noteq> {} \<and> (\<exists>u. u \<in> S \<and> T = convex hull (S - {u}))"
          (is "?lhs = ?rhs")
proof
  assume ?lhs
  then have "T face_of (convex hull S)" "T \<noteq> {}"
        and afft: "aff_dim T = aff_dim (convex hull S) - 1"
    by (auto simp: facet_of_def)
  then obtain c where "c \<subseteq> S" and c: "T = convex hull c"
    by (auto simp: face_of_convex_hull_affine_independent [OF assms])
  then have affs: "aff_dim S = aff_dim c + 1"
    by (metis aff_dim_convex_hull afft eq_diff_eq)
  have "~ affine_dependent c"
    using \<open>c \<subseteq> S\<close> affine_dependent_subset assms by blast
  with affs have "card (S - c) = 1"
    apply (simp add: aff_dim_affine_independent [symmetric] aff_dim_convex_hull)
    by (metis aff_dim_affine_independent aff_independent_finite One_nat_def \<open>c \<subseteq> S\<close> add.commute
                add_diff_cancel_right' assms card_Diff_subset card_mono of_nat_1 of_nat_diff of_nat_eq_iff)
  then obtain u where u: "u \<in> S - c"
    by (metis DiffI \<open>c \<subseteq> S\<close> aff_independent_finite assms cancel_comm_monoid_add_class.diff_cancel
                card_Diff_subset subsetI subset_antisym zero_neq_one)
  then have u: "S = insert u c"
    by (metis Diff_subset \<open>c \<subseteq> S\<close> \<open>card (S - c) = 1\<close> card_1_singletonE double_diff insert_Diff insert_subset singletonD)
  have "T = convex hull (c - {u})"
    by (metis Diff_empty Diff_insert0 \<open>T facet_of convex hull S\<close> c facet_of_irrefl insert_absorb u)
  with \<open>T \<noteq> {}\<close> show ?rhs
    using c u by auto
next
  assume ?rhs
  then obtain u where "T \<noteq> {}" "u \<in> S" and u: "T = convex hull (S - {u})"
    by (force simp: facet_of_def)
  then have "\<not> S \<subseteq> {u}"
    using \<open>T \<noteq> {}\<close> u by auto
  have [simp]: "aff_dim (convex hull (S - {u})) = aff_dim (convex hull S) - 1"
    using assms \<open>u \<in> S\<close>
    apply (simp add: aff_dim_convex_hull affine_dependent_def)
    apply (drule bspec, assumption)
    by (metis add_diff_cancel_right' aff_dim_insert insert_Diff [of u S])
  show ?lhs
    apply (subst u)
    apply (simp add: \<open>\<not> S \<subseteq> {u}\<close> facet_of_def face_of_convex_hull_affine_independent [OF assms], blast)
    done
qed

lemma facet_of_convex_hull_affine_independent_alt:
  fixes S :: "'a::euclidean_space set"
  shows
   "~affine_dependent S
        \<Longrightarrow> (T facet_of (convex hull S) \<longleftrightarrow>
             2 \<le> card S \<and> (\<exists>u. u \<in> S \<and> T = convex hull (S - {u})))"
apply (simp add: facet_of_convex_hull_affine_independent)
apply (auto simp: Set.subset_singleton_iff)
apply (metis Diff_cancel Int_empty_right Int_insert_right_if1  aff_independent_finite card_eq_0_iff card_insert_if card_mono card_subset_eq convex_hull_eq_empty eq_iff equals0D finite_insert finite_subset inf.absorb_iff2 insert_absorb insert_not_empty  not_less_eq_eq numeral_2_eq_2)
done

lemma segment_face_of:
  assumes "(closed_segment a b) face_of S"
  shows "a extreme_point_of S" "b extreme_point_of S"
proof -
  have as: "{a} face_of S"
    by (metis (no_types) assms convex_hull_singleton empty_iff extreme_point_of_convex_hull_insert face_of_face face_of_singleton finite.emptyI finite.insertI insert_absorb insert_iff segment_convex_hull)
  moreover have "{b} face_of S"
  proof -
    have "b \<in> convex hull {a} \<or> b extreme_point_of convex hull {b, a}"
      by (meson extreme_point_of_convex_hull_insert finite.emptyI finite.insertI)
    moreover have "closed_segment a b = convex hull {b, a}"
      using closed_segment_commute segment_convex_hull by blast
    ultimately show ?thesis
      by (metis as assms face_of_face convex_hull_singleton empty_iff face_of_singleton insertE)
    qed
  ultimately show "a extreme_point_of S" "b extreme_point_of S"
    using face_of_singleton by blast+
qed


lemma Krein_Milman_frontier:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S" "compact S"
    shows "S = convex hull (frontier S)"
          (is "?lhs = ?rhs")
proof
  have "?lhs \<subseteq> convex hull {x. x extreme_point_of S}"
    using Krein_Milman_Minkowski assms by blast
  also have "... \<subseteq> ?rhs"
    apply (rule hull_mono)
    apply (auto simp: frontier_def extreme_point_not_in_interior)
    using closure_subset apply (force simp: extreme_point_of_def)
    done
  finally show "?lhs \<subseteq> ?rhs" .
next
  have "?rhs \<subseteq> convex hull S"
    by (metis Diff_subset \<open>compact S\<close> closure_closed compact_eq_bounded_closed frontier_def hull_mono)
  also have "... \<subseteq> ?lhs"
    by (simp add: \<open>convex S\<close> hull_same)
  finally show "?rhs \<subseteq> ?lhs" .
qed

subsection\<open>Polytopes\<close>

definition polytope where
 "polytope S \<equiv> \<exists>v. finite v \<and> S = convex hull v"

lemma polytope_translation_eq: "polytope (image (\<lambda>x. a + x) S) \<longleftrightarrow> polytope S"
apply (simp add: polytope_def, safe)
apply (metis convex_hull_translation finite_imageI translation_galois)
by (metis convex_hull_translation finite_imageI)

lemma polytope_linear_image: "\<lbrakk>linear f; polytope p\<rbrakk> \<Longrightarrow> polytope(image f p)"
  unfolding polytope_def using convex_hull_linear_image by blast

lemma polytope_empty: "polytope {}"
  using convex_hull_empty polytope_def by blast

lemma polytope_convex_hull: "finite S \<Longrightarrow> polytope(convex hull S)"
  using polytope_def by auto

lemma polytope_Times: "\<lbrakk>polytope S; polytope T\<rbrakk> \<Longrightarrow> polytope(S \<times> T)"
  unfolding polytope_def
  by (metis finite_cartesian_product convex_hull_Times)

lemma face_of_polytope_polytope:
  fixes S :: "'a::euclidean_space set"
  shows "\<lbrakk>polytope S; F face_of S\<rbrakk> \<Longrightarrow> polytope F"
unfolding polytope_def
by (meson face_of_convex_hull_subset finite_imp_compact finite_subset)

lemma finite_polytope_faces:
  fixes S :: "'a::euclidean_space set"
  assumes "polytope S"
  shows "finite {F. F face_of S}"
proof -
  obtain v where "finite v" "S = convex hull v"
    using assms polytope_def by auto
  have "finite (op hull convex ` {T. T \<subseteq> v})"
    by (simp add: \<open>finite v\<close>)
  moreover have "{F. F face_of S} \<subseteq> (op hull convex ` {T. T \<subseteq> v})"
    by (metis (no_types, lifting) \<open>finite v\<close> \<open>S = convex hull v\<close> face_of_convex_hull_subset finite_imp_compact image_eqI mem_Collect_eq subsetI)
  ultimately show ?thesis
    by (blast intro: finite_subset)
qed

lemma finite_polytope_facets:
  assumes "polytope S"
  shows "finite {T. T facet_of S}"
by (simp add: assms facet_of_def finite_polytope_faces)

lemma polytope_scaling:
  assumes "polytope S"  shows "polytope (image (\<lambda>x. c *\<^sub>R x) S)"
by (simp add: assms polytope_linear_image)

lemma polytope_imp_compact:
  fixes S :: "'a::real_normed_vector set"
  shows "polytope S \<Longrightarrow> compact S"
by (metis finite_imp_compact_convex_hull polytope_def)

lemma polytope_imp_convex: "polytope S \<Longrightarrow> convex S"
  by (metis convex_convex_hull polytope_def)

lemma polytope_imp_closed:
  fixes S :: "'a::real_normed_vector set"
  shows "polytope S \<Longrightarrow> closed S"
by (simp add: compact_imp_closed polytope_imp_compact)

lemma polytope_imp_bounded:
  fixes S :: "'a::real_normed_vector set"
  shows "polytope S \<Longrightarrow> bounded S"
by (simp add: compact_imp_bounded polytope_imp_compact)

lemma polytope_interval: "polytope(cbox a b)"
  unfolding polytope_def by (meson closed_interval_as_convex_hull)

lemma polytope_sing: "polytope {a}"
  using polytope_def by force


subsection\<open>Polyhedra\<close>

definition polyhedron where
 "polyhedron S \<equiv>
        \<exists>F. finite F \<and>
            S = \<Inter> F \<and>
            (\<forall>h \<in> F. \<exists>a b. a \<noteq> 0 \<and> h = {x. a \<bullet> x \<le> b})"

lemma polyhedron_Int [intro,simp]:
   "\<lbrakk>polyhedron S; polyhedron T\<rbrakk> \<Longrightarrow> polyhedron (S \<inter> T)"
  apply (simp add: polyhedron_def, clarify)
  apply (rename_tac F G)
  apply (rule_tac x="F \<union> G" in exI, auto)
  done

lemma polyhedron_UNIV [iff]: "polyhedron UNIV"
  unfolding polyhedron_def
  by (rule_tac x="{}" in exI) auto

lemma polyhedron_Inter [intro,simp]:
   "\<lbrakk>finite F; \<And>S. S \<in> F \<Longrightarrow> polyhedron S\<rbrakk> \<Longrightarrow> polyhedron(\<Inter>F)"
by (induction F rule: finite_induct) auto


lemma polyhedron_empty [iff]: "polyhedron ({} :: 'a :: euclidean_space set)"
proof -
  have "\<exists>a. a \<noteq> 0 \<and>
             (\<exists>b. {x. (SOME i. i \<in> Basis) \<bullet> x \<le> - 1} = {x. a \<bullet> x \<le> b})"
    by (rule_tac x="(SOME i. i \<in> Basis)" in exI) (force simp: SOME_Basis nonzero_Basis)
  moreover have "\<exists>a b. a \<noteq> 0 \<and>
                       {x. - (SOME i. i \<in> Basis) \<bullet> x \<le> - 1} = {x. a \<bullet> x \<le> b}"
      apply (rule_tac x="-(SOME i. i \<in> Basis)" in exI)
      apply (rule_tac x="-1" in exI)
      apply (simp add: SOME_Basis nonzero_Basis)
      done
  ultimately show ?thesis
    unfolding polyhedron_def
    apply (rule_tac x="{{x. (SOME i. i \<in> Basis) \<bullet> x \<le> -1},
                        {x. -(SOME i. i \<in> Basis) \<bullet> x \<le> -1}}" in exI)
    apply force
    done
qed

lemma polyhedron_halfspace_le:
  fixes a :: "'a :: euclidean_space"
  shows "polyhedron {x. a \<bullet> x \<le> b}"
proof (cases "a = 0")
  case True then show ?thesis by auto
next
  case False
  then show ?thesis
    unfolding polyhedron_def
    by (rule_tac x="{{x. a \<bullet> x \<le> b}}" in exI) auto
qed

lemma polyhedron_halfspace_ge:
  fixes a :: "'a :: euclidean_space"
  shows "polyhedron {x. a \<bullet> x \<ge> b}"
using polyhedron_halfspace_le [of "-a" "-b"] by simp

lemma polyhedron_hyperplane:
  fixes a :: "'a :: euclidean_space"
  shows "polyhedron {x. a \<bullet> x = b}"
proof -
  have "{x. a \<bullet> x = b} = {x. a \<bullet> x \<le> b} \<inter> {x. a \<bullet> x \<ge> b}"
    by force
  then show ?thesis
    by (simp add: polyhedron_halfspace_ge polyhedron_halfspace_le)
qed

lemma affine_imp_polyhedron:
  fixes S :: "'a :: euclidean_space set"
  shows "affine S \<Longrightarrow> polyhedron S"
by (metis affine_hull_eq polyhedron_Inter polyhedron_hyperplane affine_hull_finite_intersection_hyperplanes [of S])

lemma polyhedron_imp_closed:
  fixes S :: "'a :: euclidean_space set"
  shows "polyhedron S \<Longrightarrow> closed S"
apply (simp add: polyhedron_def)
using closed_halfspace_le by fastforce

lemma polyhedron_imp_convex:
  fixes S :: "'a :: euclidean_space set"
  shows "polyhedron S \<Longrightarrow> convex S"
apply (simp add: polyhedron_def)
using convex_Inter convex_halfspace_le by fastforce

lemma polyhedron_affine_hull:
  fixes S :: "'a :: euclidean_space set"
  shows "polyhedron(affine hull S)"
by (simp add: affine_imp_polyhedron)


subsection\<open>Canonical polyhedron representation making facial structure explicit\<close>

lemma polyhedron_Int_affine:
  fixes S :: "'a :: euclidean_space set"
  shows "polyhedron S \<longleftrightarrow>
           (\<exists>F. finite F \<and> S = (affine hull S) \<inter> \<Inter>F \<and>
                (\<forall>h \<in> F. \<exists>a b. a \<noteq> 0 \<and> h = {x. a \<bullet> x \<le> b}))"
        (is "?lhs = ?rhs")
proof
  assume ?lhs then show ?rhs
    apply (simp add: polyhedron_def)
    apply (erule ex_forward)
    using hull_subset apply force
    done
next
  assume ?rhs then show ?lhs
    apply clarify
    apply (erule ssubst)
    apply (force intro: polyhedron_affine_hull polyhedron_halfspace_le)
    done
qed

proposition rel_interior_polyhedron_explicit:
  assumes "finite F"
      and seq: "S = affine hull S \<inter> \<Inter>F"
      and faceq: "\<And>h. h \<in> F \<Longrightarrow> a h \<noteq> 0 \<and> h = {x. a h \<bullet> x \<le> b h}"
      and psub: "\<And>F'. F' \<subset> F \<Longrightarrow> S \<subset> affine hull S \<inter> \<Inter>F'"
    shows "rel_interior S = {x \<in> S. \<forall>h \<in> F. a h \<bullet> x < b h}"
proof -
  have rels: "\<And>x. x \<in> rel_interior S \<Longrightarrow> x \<in> S"
    by (meson IntE mem_rel_interior)
  moreover have "a i \<bullet> x < b i" if x: "x \<in> rel_interior S" and "i \<in> F" for x i
  proof -
    have fif: "F - {i} \<subset> F"
      using \<open>i \<in> F\<close> Diff_insert_absorb Diff_subset set_insert psubsetI by blast
    then have "S \<subset> affine hull S \<inter> \<Inter>(F - {i})"
      by (rule psub)
    then obtain z where ssub: "S \<subseteq> \<Inter>(F - {i})" and zint: "z \<in> \<Inter>(F - {i})"
                    and "z \<notin> S" and zaff: "z \<in> affine hull S"
      by auto
    have "z \<noteq> x"
      using \<open>z \<notin> S\<close> rels x by blast
    have "z \<notin> affine hull S \<inter> \<Inter>F"
      using \<open>z \<notin> S\<close> seq by auto
    then have aiz: "a i \<bullet> z > b i"
      using faceq zint zaff by fastforce
    obtain e where "e > 0" "x \<in> S" and e: "ball x e \<inter> affine hull S \<subseteq> S"
      using x by (auto simp: mem_rel_interior_ball)
    then have ins: "\<And>y. \<lbrakk>norm (x - y) < e; y \<in> affine hull S\<rbrakk> \<Longrightarrow> y \<in> S"
      by (metis IntI subsetD dist_norm mem_ball)
    define \<xi> where "\<xi> = min (1/2) (e / 2 / norm(z - x))"
    have "norm (\<xi> *\<^sub>R x - \<xi> *\<^sub>R z) = norm (\<xi> *\<^sub>R (x - z))"
      by (simp add: \<xi>_def algebra_simps norm_mult)
    also have "... = \<xi> * norm (x - z)"
      using \<open>e > 0\<close> by (simp add: \<xi>_def)
    also have "... < e"
      using \<open>z \<noteq> x\<close> \<open>e > 0\<close> by (simp add: \<xi>_def min_def divide_simps norm_minus_commute)
    finally have lte: "norm (\<xi> *\<^sub>R x - \<xi> *\<^sub>R z) < e" .
    have \<xi>_aff: "\<xi> *\<^sub>R z + (1 - \<xi>) *\<^sub>R x \<in> affine hull S"
      by (metis \<open>x \<in> S\<close> add.commute affine_affine_hull diff_add_cancel hull_inc mem_affine zaff)
    have "\<xi> *\<^sub>R z + (1 - \<xi>) *\<^sub>R x \<in> S"
      apply (rule ins [OF _ \<xi>_aff])
      apply (simp add: algebra_simps lte)
      done
    then obtain l where l: "0 < l" "l < 1" and ls: "(l *\<^sub>R z + (1 - l) *\<^sub>R x) \<in> S"
      apply (rule_tac l = \<xi> in that)
      using \<open>e > 0\<close> \<open>z \<noteq> x\<close>  apply (auto simp: \<xi>_def)
      done
    then have i: "l *\<^sub>R z + (1 - l) *\<^sub>R x \<in> i"
      using seq \<open>i \<in> F\<close> by auto
    have "b i * l + (a i \<bullet> x) * (1 - l) < a i \<bullet> (l *\<^sub>R z + (1 - l) *\<^sub>R x)"
      using l by (simp add: algebra_simps aiz)
    also have "\<dots> \<le> b i" using i l
      using faceq mem_Collect_eq \<open>i \<in> F\<close> by blast
    finally have "(a i \<bullet> x) * (1 - l) < b i * (1 - l)"
      by (simp add: algebra_simps)
    with l show ?thesis
      by simp
  qed
  moreover have "x \<in> rel_interior S"
           if "x \<in> S" and less: "\<And>h. h \<in> F \<Longrightarrow> a h \<bullet> x < b h" for x
  proof -
    have 1: "\<And>h. h \<in> F \<Longrightarrow> x \<in> interior h"
      by (metis interior_halfspace_le mem_Collect_eq less faceq)
    have 2: "\<And>y. \<lbrakk>\<forall>h\<in>F. y \<in> interior h; y \<in> affine hull S\<rbrakk> \<Longrightarrow> y \<in> S"
      by (metis IntI Inter_iff contra_subsetD interior_subset seq)
    show ?thesis
      apply (simp add: rel_interior \<open>x \<in> S\<close>)
      apply (rule_tac x="\<Inter>h\<in>F. interior h" in exI)
      apply (auto simp: \<open>finite F\<close> open_INT 1 2)
      done
  qed
  ultimately show ?thesis by blast
qed


lemma polyhedron_Int_affine_parallel:
  fixes S :: "'a :: euclidean_space set"
  shows "polyhedron S \<longleftrightarrow>
         (\<exists>F. finite F \<and>
              S = (affine hull S) \<inter> (\<Inter>F) \<and>
              (\<forall>h \<in> F. \<exists>a b. a \<noteq> 0 \<and> h = {x. a \<bullet> x \<le> b} \<and>
                             (\<forall>x \<in> affine hull S. (x + a) \<in> affine hull S)))"
    (is "?lhs = ?rhs")
proof
  assume ?lhs
  then obtain F where "finite F" and seq: "S = (affine hull S) \<inter> \<Inter>F"
                  and faces: "\<And>h. h \<in> F \<Longrightarrow> \<exists>a b. a \<noteq> 0 \<and> h = {x. a \<bullet> x \<le> b}"
    by (fastforce simp add: polyhedron_Int_affine)
  then obtain a b where ab: "\<And>h. h \<in> F \<Longrightarrow> a h \<noteq> 0 \<and> h = {x. a h \<bullet> x \<le> b h}"
    by metis
  show ?rhs
  proof -
    have "\<exists>a' b'. a' \<noteq> 0 \<and>
                  affine hull S \<inter> {x. a' \<bullet> x \<le> b'} = affine hull S \<inter> h \<and>
                  (\<forall>w \<in> affine hull S. (w + a') \<in> affine hull S)"
        if "h \<in> F" "~(affine hull S \<subseteq> h)" for h
    proof -
      have "a h \<noteq> 0" and "h = {x. a h \<bullet> x \<le> b h}" "h \<inter> \<Inter>F = \<Inter>F"
        using \<open>h \<in> F\<close> ab by auto
      then have "(affine hull S) \<inter> {x. a h \<bullet> x \<le> b h} \<noteq> {}"
        by (metis (no_types) affine_hull_eq_empty inf.absorb_iff2 inf_assoc inf_bot_right inf_commute seq that(2))
      moreover have "~ (affine hull S \<subseteq> {x. a h \<bullet> x \<le> b h})"
        using \<open>h = {x. a h \<bullet> x \<le> b h}\<close> that(2) by blast
      ultimately show ?thesis
        using affine_parallel_slice [of "affine hull S"]
        by (metis \<open>h = {x. a h \<bullet> x \<le> b h}\<close> affine_affine_hull)
    qed
    then obtain a b
         where ab: "\<And>h. \<lbrakk>h \<in> F; ~ (affine hull S \<subseteq> h)\<rbrakk>
             \<Longrightarrow> a h \<noteq> 0 \<and>
                  affine hull S \<inter> {x. a h \<bullet> x \<le> b h} = affine hull S \<inter> h \<and>
                  (\<forall>w \<in> affine hull S. (w + a h) \<in> affine hull S)"
      by metis
    have seq2: "S = affine hull S \<inter> (\<Inter>h\<in>{h \<in> F. \<not> affine hull S \<subseteq> h}. {x. a h \<bullet> x \<le> b h})"
      by (subst seq) (auto simp: ab INT_extend_simps)
    show ?thesis
      apply (rule_tac x="(\<lambda>h. {x. a h \<bullet> x \<le> b h}) ` {h. h \<in> F \<and> ~(affine hull S \<subseteq> h)}" in exI)
      apply (intro conjI seq2)
        using \<open>finite F\<close> apply force
       using ab apply blast
       done
  qed
next
  assume ?rhs then show ?lhs
    apply (simp add: polyhedron_Int_affine)
    by metis
qed


proposition polyhedron_Int_affine_parallel_minimal:
  fixes S :: "'a :: euclidean_space set"
  shows "polyhedron S \<longleftrightarrow>
         (\<exists>F. finite F \<and>
              S = (affine hull S) \<inter> (\<Inter>F) \<and>
              (\<forall>h \<in> F. \<exists>a b. a \<noteq> 0 \<and> h = {x. a \<bullet> x \<le> b} \<and>
                             (\<forall>x \<in> affine hull S. (x + a) \<in> affine hull S)) \<and>
              (\<forall>F'. F' \<subset> F \<longrightarrow> S \<subset> (affine hull S) \<inter> (\<Inter>F')))"
    (is "?lhs = ?rhs")
proof
  assume ?lhs
  then obtain f0
           where f0: "finite f0"
                 "S = (affine hull S) \<inter> (\<Inter>f0)"
                   (is "?P f0")
                 "\<forall>h \<in> f0. \<exists>a b. a \<noteq> 0 \<and> h = {x. a \<bullet> x \<le> b} \<and>
                             (\<forall>x \<in> affine hull S. (x + a) \<in> affine hull S)"
                   (is "?Q f0")
    by (force simp: polyhedron_Int_affine_parallel)
  define n where "n = (LEAST n. \<exists>F. card F = n \<and> finite F \<and> ?P F \<and> ?Q F)"
  have nf: "\<exists>F. card F = n \<and> finite F \<and> ?P F \<and> ?Q F"
    apply (simp add: n_def)
    apply (rule LeastI [where k = "card f0"])
    using f0 apply auto
    done
  then obtain F where F: "card F = n" "finite F" and seq: "?P F" and aff: "?Q F"
    by blast
  then have "~ (finite g \<and> ?P g \<and> ?Q g)" if "card g < n" for g
    using that by (auto simp: n_def dest!: not_less_Least)
  then have *: "~ (?P g \<and> ?Q g)" if "g \<subset> F" for g
    using that \<open>finite F\<close> psubset_card_mono \<open>card F = n\<close>
    by (metis finite_Int inf.strict_order_iff)
  have 1: "\<And>F'. F' \<subset> F \<Longrightarrow> S \<subseteq> affine hull S \<inter> \<Inter>F'"
    by (subst seq) blast
  have 2: "\<And>F'. F' \<subset> F \<Longrightarrow> S \<noteq> affine hull S \<inter> \<Inter>F'"
    apply (frule *)
    by (metis aff subsetCE subset_iff_psubset_eq)
  show ?rhs
    by (metis \<open>finite F\<close> seq aff psubsetI 1 2)
next
  assume ?rhs then show ?lhs
    by (auto simp: polyhedron_Int_affine_parallel)
qed


lemma polyhedron_Int_affine_minimal:
  fixes S :: "'a :: euclidean_space set"
  shows "polyhedron S \<longleftrightarrow>
         (\<exists>F. finite F \<and> S = (affine hull S) \<inter> \<Inter>F \<and>
              (\<forall>h \<in> F. \<exists>a b. a \<noteq> 0 \<and> h = {x. a \<bullet> x \<le> b}) \<and>
              (\<forall>F'. F' \<subset> F \<longrightarrow> S \<subset> (affine hull S) \<inter> \<Inter>F'))"
apply (rule iffI)
 apply (force simp: polyhedron_Int_affine_parallel_minimal elim!: ex_forward)
apply (auto simp: polyhedron_Int_affine elim!: ex_forward)
done

proposition facet_of_polyhedron_explicit:
  assumes "finite F"
      and seq: "S = affine hull S \<inter> \<Inter>F"
      and faceq: "\<And>h. h \<in> F \<Longrightarrow> a h \<noteq> 0 \<and> h = {x. a h \<bullet> x \<le> b h}"
      and psub: "\<And>F'. F' \<subset> F \<Longrightarrow> S \<subset> affine hull S \<inter> \<Inter>F'"
    shows "c facet_of S \<longleftrightarrow> (\<exists>h. h \<in> F \<and> c = S \<inter> {x. a h \<bullet> x = b h})"
proof (cases "S = {}")
  case True with psub show ?thesis by force
next
  case False
  have "polyhedron S"
    apply (simp add: polyhedron_Int_affine)
    apply (rule_tac x=F in exI)
    using assms  apply force
    done
  then have "convex S"
    by (rule polyhedron_imp_convex)
  with False rel_interior_eq_empty have "rel_interior S \<noteq> {}" by blast
  then obtain x where "x \<in> rel_interior S" by auto
  then obtain T where "open T" "x \<in> T" "x \<in> S" "T \<inter> affine hull S \<subseteq> S"
    by (force simp: mem_rel_interior)
  then have xaff: "x \<in> affine hull S" and xint: "x \<in> \<Inter>F"
    using seq hull_inc by auto
  have "rel_interior S = {x \<in> S. \<forall>h\<in>F. a h \<bullet> x < b h}"
    by (rule rel_interior_polyhedron_explicit [OF \<open>finite F\<close> seq faceq psub])
  with \<open>x \<in> rel_interior S\<close>
  have [simp]: "\<And>h. h\<in>F \<Longrightarrow> a h \<bullet> x < b h" by blast
  have *: "(S \<inter> {x. a h \<bullet> x = b h}) facet_of S" if "h \<in> F" for h
  proof -
    have "S \<subset> affine hull S \<inter> \<Inter>(F - {h})"
      using psub that by (metis Diff_disjoint Diff_subset insert_disjoint(2) psubsetI)
    then obtain z where zaff: "z \<in> affine hull S" and zint: "z \<in> \<Inter>(F - {h})" and "z \<notin> S"
      by force
    then have "z \<noteq> x" "z \<notin> h" using seq \<open>x \<in> S\<close> by auto
    have "x \<in> h" using that xint by auto
    then have able: "a h \<bullet> x \<le> b h"
      using faceq that by blast
    also have "... < a h \<bullet> z" using \<open>z \<notin> h\<close> faceq [OF that] xint by auto
    finally have xltz: "a h \<bullet> x < a h \<bullet> z" .
    define l where "l = (b h - a h \<bullet> x) / (a h \<bullet> z - a h \<bullet> x)"
    define w where "w = (1 - l) *\<^sub>R x + l *\<^sub>R z"
    have "0 < l" "l < 1"
      using able xltz \<open>b h < a h \<bullet> z\<close> \<open>h \<in> F\<close>
      by (auto simp: l_def divide_simps)
    have awlt: "a i \<bullet> w < b i" if "i \<in> F" "i \<noteq> h" for i
    proof -
      have "(1 - l) * (a i \<bullet> x) < (1 - l) * b i"
        by (simp add: \<open>l < 1\<close> \<open>i \<in> F\<close>)
      moreover have "l * (a i \<bullet> z) \<le> l * b i"
        apply (rule mult_left_mono)
        apply (metis Diff_insert_absorb Inter_iff Set.set_insert \<open>h \<in> F\<close> faceq insertE mem_Collect_eq that zint)
        using \<open>0 < l\<close>
        apply simp
        done
      ultimately show ?thesis by (simp add: w_def algebra_simps)
    qed
    have weq: "a h \<bullet> w = b h"
      using xltz unfolding w_def l_def
      by (simp add: algebra_simps) (simp add: field_simps)
    have "w \<in> affine hull S"
      by (simp add: w_def mem_affine xaff zaff)
    moreover have "w \<in> \<Inter>F"
      using \<open>a h \<bullet> w = b h\<close> awlt faceq less_eq_real_def by blast
    ultimately have "w \<in> S"
      using seq by blast
    with weq have "S \<inter> {x. a h \<bullet> x = b h} \<noteq> {}" by blast
    moreover have "S \<inter> {x. a h \<bullet> x = b h} face_of S"
      apply (rule face_of_Int_supporting_hyperplane_le)
      apply (rule \<open>convex S\<close>)
      apply (subst (asm) seq)
      using faceq that apply fastforce
      done
    moreover have "affine hull (S \<inter> {x. a h \<bullet> x = b h}) =
                   (affine hull S) \<inter> {x. a h \<bullet> x = b h}"
    proof
      show "affine hull (S \<inter> {x. a h \<bullet> x = b h}) \<subseteq> affine hull S \<inter> {x. a h \<bullet> x = b h}"
        apply (intro Int_greatest hull_mono Int_lower1)
        apply (metis affine_hull_eq affine_hyperplane hull_mono inf_le2)
        done
    next
      show "affine hull S \<inter> {x. a h \<bullet> x = b h} \<subseteq> affine hull (S \<inter> {x. a h \<bullet> x = b h})"
      proof
        fix y
        assume yaff: "y \<in> affine hull S \<inter> {y. a h \<bullet> y = b h}"
        obtain T where "0 < T"
                 and T: "\<And>j. \<lbrakk>j \<in> F; j \<noteq> h\<rbrakk> \<Longrightarrow> T * (a j \<bullet> y - a j \<bullet> w) \<le> b j - a j \<bullet> w"
        proof (cases "F - {h} = {}")
          case True then show ?thesis
            by (rule_tac T=1 in that) auto
        next
          case False
          then obtain h' where h': "h' \<in> F - {h}" by auto
          define inff where "inff =
            (INF j:F - {h}.
              if 0 < a j \<bullet> y - a j \<bullet> w
              then (b j - a j \<bullet> w) / (a j \<bullet> y - a j \<bullet> w)
              else 1)"
          have "0 < inff"
            apply (simp add: inff_def)
            apply (rule finite_imp_less_Inf)
              using \<open>finite F\<close> apply blast
             using h' apply blast
            apply simp
            using awlt apply (force simp: divide_simps)
            done
          moreover have "inff * (a j \<bullet> y - a j \<bullet> w) \<le> b j - a j \<bullet> w"
                        if "j \<in> F" "j \<noteq> h" for j
          proof (cases "a j \<bullet> w < a j \<bullet> y")
            case True
            then have "inff \<le> (b j - a j \<bullet> w) / (a j \<bullet> y - a j \<bullet> w)"
              apply (simp add: inff_def)
              apply (rule cInf_le_finite)
              using \<open>finite F\<close> apply blast
              apply (simp add: that split: if_split_asm)
              done
            then show ?thesis
              using \<open>0 < inff\<close> awlt [OF that] mult_strict_left_mono
              by (fastforce simp add: algebra_simps divide_simps split: if_split_asm)
          next
            case False
            with \<open>0 < inff\<close> have "inff * (a j \<bullet> y - a j \<bullet> w) \<le> 0"
              by (simp add: mult_le_0_iff)
            also have "... < b j - a j \<bullet> w"
              by (simp add: awlt that)
            finally show ?thesis by simp
          qed
          ultimately show ?thesis
            by (blast intro: that)
        qed
        define c where "c = (1 - T) *\<^sub>R w + T *\<^sub>R y"
        have "(1 - T) *\<^sub>R w + T *\<^sub>R y \<in> j" if "j \<in> F" for j
        proof (cases "j = h")
          case True
          have "(1 - T) *\<^sub>R w + T *\<^sub>R y \<in> {x. a h \<bullet> x \<le> b h}"
            using weq yaff by (auto simp: algebra_simps)
          with True faceq [OF that] show ?thesis by metis
        next
          case False
          with T that have "(1 - T) *\<^sub>R w + T *\<^sub>R y \<in> {x. a j \<bullet> x \<le> b j}"
            by (simp add: algebra_simps)
          with faceq [OF that] show ?thesis by simp
        qed
        moreover have "(1 - T) *\<^sub>R w + T *\<^sub>R y \<in> affine hull S"
          apply (rule affine_affine_hull [simplified affine_alt, rule_format])
          apply (simp add: \<open>w \<in> affine hull S\<close>)
          using yaff apply blast
          done
        ultimately have "c \<in> S"
          using seq by (force simp: c_def)
        moreover have "a h \<bullet> c = b h"
          using yaff by (force simp: c_def algebra_simps weq)
        ultimately have caff: "c \<in> affine hull (S \<inter> {y. a h \<bullet> y = b h})"
          by (simp add: hull_inc)
        have waff: "w \<in> affine hull (S \<inter> {y. a h \<bullet> y = b h})"
          using \<open>w \<in> S\<close> weq by (blast intro: hull_inc)
        have yeq: "y = (1 - inverse T) *\<^sub>R w + c /\<^sub>R T"
          using \<open>0 < T\<close> by (simp add: c_def algebra_simps)
        show "y \<in> affine hull (S \<inter> {y. a h \<bullet> y = b h})"
          by (metis yeq affine_affine_hull [simplified affine_alt, rule_format, OF waff caff])
      qed
    qed
    ultimately show ?thesis
      apply (simp add: facet_of_def)
      apply (subst aff_dim_affine_hull [symmetric])
      using  \<open>b h < a h \<bullet> z\<close> zaff
      apply (force simp: aff_dim_affine_Int_hyperplane)
      done
  qed
  show ?thesis
  proof
    show "\<exists>h. h \<in> F \<and> c = S \<inter> {x. a h \<bullet> x = b h} \<Longrightarrow> c facet_of S"
      using * by blast
  next
    assume "c facet_of S"
    then have "c face_of S" "convex c" "c \<noteq> {}" and affc: "aff_dim c = aff_dim S - 1"
      by (auto simp: facet_of_def face_of_imp_convex)
    then obtain x where x: "x \<in> rel_interior c"
      by (force simp: rel_interior_eq_empty)
    then have "x \<in> c"
      by (meson subsetD rel_interior_subset)
    then have "x \<in> S"
      using \<open>c facet_of S\<close> facet_of_imp_subset by blast
    have rels: "rel_interior S = {x \<in> S. \<forall>h\<in>F. a h \<bullet> x < b h}"
      by (rule rel_interior_polyhedron_explicit [OF assms])
    have "c \<noteq> S"
      using \<open>c facet_of S\<close> facet_of_irrefl by blast
    then have "x \<notin> rel_interior S"
      by (metis IntI empty_iff \<open>x \<in> c\<close> \<open>c \<noteq> S\<close> \<open>c face_of S\<close> face_of_disjoint_rel_interior)
    with rels \<open>x \<in> S\<close> obtain i where "i \<in> F" and i: "a i \<bullet> x \<ge> b i"
      by force
    have "x \<in> {u. a i \<bullet> u \<le> b i}"
      by (metis IntD2 InterE \<open>i \<in> F\<close> \<open>x \<in> S\<close> faceq seq)
    then have "a i \<bullet> x \<le> b i" by simp
    then have "a i \<bullet> x = b i" using i by auto
    have "c \<subseteq> S \<inter> {x. a i \<bullet> x = b i}"
      apply (rule subset_of_face_of [of _ S])
        apply (simp add: "*" \<open>i \<in> F\<close> facet_of_imp_face_of)
       apply (simp add: \<open>c face_of S\<close> face_of_imp_subset)
      using \<open>a i \<bullet> x = b i\<close> \<open>x \<in> S\<close> x by blast
    then have cface: "c face_of (S \<inter> {x. a i \<bullet> x = b i})"
      by (meson \<open>c face_of S\<close> face_of_subset inf_le1)
    have con: "convex (S \<inter> {x. a i \<bullet> x = b i})"
      by (simp add: \<open>convex S\<close> convex_Int convex_hyperplane)
    show "\<exists>h. h \<in> F \<and> c = S \<inter> {x. a h \<bullet> x = b h}"
      apply (rule_tac x=i in exI)
      apply (simp add: \<open>i \<in> F\<close>)
      by (metis (no_types) * \<open>i \<in> F\<close> affc facet_of_def less_irrefl face_of_aff_dim_lt [OF con cface])
  qed
qed


lemma face_of_polyhedron_subset_explicit:
  fixes S :: "'a :: euclidean_space set"
  assumes "finite F"
      and seq: "S = affine hull S \<inter> \<Inter>F"
      and faceq: "\<And>h. h \<in> F \<Longrightarrow> a h \<noteq> 0 \<and> h = {x. a h \<bullet> x \<le> b h}"
      and psub: "\<And>F'. F' \<subset> F \<Longrightarrow> S \<subset> affine hull S \<inter> \<Inter>F'"
      and c: "c face_of S" and "c \<noteq> {}" "c \<noteq> S"
   obtains h where "h \<in> F" "c \<subseteq> S \<inter> {x. a h \<bullet> x = b h}"
proof -
  have "c \<subseteq> S" using \<open>c face_of S\<close>
    by (simp add: face_of_imp_subset)
  have "polyhedron S"
    apply (simp add: polyhedron_Int_affine)
    by (metis \<open>finite F\<close> faceq seq)
  then have "convex S"
    by (simp add: polyhedron_imp_convex)
  then have *: "(S \<inter> {x. a h \<bullet> x = b h}) face_of S" if "h \<in> F" for h
    apply (rule face_of_Int_supporting_hyperplane_le)
    using faceq seq that by fastforce
  have "rel_interior c \<noteq> {}"
    using c \<open>c \<noteq> {}\<close> face_of_imp_convex rel_interior_eq_empty by blast
  then obtain x where "x \<in> rel_interior c" by auto
  have rels: "rel_interior S = {x \<in> S. \<forall>h\<in>F. a h \<bullet> x < b h}"
    by (rule rel_interior_polyhedron_explicit [OF \<open>finite F\<close> seq faceq psub])
  then have xnot: "x \<notin> rel_interior S"
    by (metis IntI \<open>x \<in> rel_interior c\<close> c \<open>c \<noteq> S\<close> contra_subsetD empty_iff face_of_disjoint_rel_interior rel_interior_subset)
  then have "x \<in> S"
    using \<open>c \<subseteq> S\<close> \<open>x \<in> rel_interior c\<close> rel_interior_subset by auto
  then have xint: "x \<in> \<Inter>F"
    using seq by blast
  have "F \<noteq> {}" using assms
    by (metis affine_Int affine_Inter affine_affine_hull ex_in_conv face_of_affine_trivial)
  then obtain i where "i \<in> F" "~ (a i \<bullet> x < b i)"
    using \<open>x \<in> S\<close> rels xnot by auto
  with xint have "a i \<bullet> x = b i"
    by (metis eq_iff mem_Collect_eq not_le Inter_iff faceq)
  have face: "S \<inter> {x. a i \<bullet> x = b i} face_of S"
    by (simp add: "*" \<open>i \<in> F\<close>)
  show ?thesis
    apply (rule_tac h = i in that)
     apply (rule \<open>i \<in> F\<close>)
    apply (rule subset_of_face_of [OF face \<open>c \<subseteq> S\<close>])
    using \<open>a i \<bullet> x = b i\<close> \<open>x \<in> rel_interior c\<close> \<open>x \<in> S\<close> apply blast
    done
qed

text\<open>Initial part of proof duplicates that above\<close>
proposition face_of_polyhedron_explicit:
  fixes S :: "'a :: euclidean_space set"
  assumes "finite F"
      and seq: "S = affine hull S \<inter> \<Inter>F"
      and faceq: "\<And>h. h \<in> F \<Longrightarrow> a h \<noteq> 0 \<and> h = {x. a h \<bullet> x \<le> b h}"
      and psub: "\<And>F'. F' \<subset> F \<Longrightarrow> S \<subset> affine hull S \<inter> \<Inter>F'"
      and c: "c face_of S" and "c \<noteq> {}" "c \<noteq> S"
    shows "c = \<Inter>{S \<inter> {x. a h \<bullet> x = b h} | h. h \<in> F \<and> c \<subseteq> S \<inter> {x. a h \<bullet> x = b h}}"
proof -
  let ?ab = "\<lambda>h. {x. a h \<bullet> x = b h}"
  have "c \<subseteq> S" using \<open>c face_of S\<close>
    by (simp add: face_of_imp_subset)
  have "polyhedron S"
    apply (simp add: polyhedron_Int_affine)
    by (metis \<open>finite F\<close> faceq seq)
  then have "convex S"
    by (simp add: polyhedron_imp_convex)
  then have *: "(S \<inter> ?ab h) face_of S" if "h \<in> F" for h
    apply (rule face_of_Int_supporting_hyperplane_le)
    using faceq seq that by fastforce
  have "rel_interior c \<noteq> {}"
    using c \<open>c \<noteq> {}\<close> face_of_imp_convex rel_interior_eq_empty by blast
  then obtain z where z: "z \<in> rel_interior c" by auto
  have rels: "rel_interior S = {z \<in> S. \<forall>h\<in>F. a h \<bullet> z < b h}"
    by (rule rel_interior_polyhedron_explicit [OF \<open>finite F\<close> seq faceq psub])
  then have xnot: "z \<notin> rel_interior S"
    by (metis IntI \<open>z \<in> rel_interior c\<close> c \<open>c \<noteq> S\<close> contra_subsetD empty_iff face_of_disjoint_rel_interior rel_interior_subset)
  then have "z \<in> S"
    using \<open>c \<subseteq> S\<close> \<open>z \<in> rel_interior c\<close> rel_interior_subset by auto
  with seq have xint: "z \<in> \<Inter>F" by blast
  have "open (\<Inter>h\<in>{h \<in> F. a h \<bullet> z < b h}. {w. a h \<bullet> w < b h})"
    by (auto simp: \<open>finite F\<close> open_halfspace_lt open_INT)
  then obtain e where "0 < e"
                 "ball z e \<subseteq> (\<Inter>h\<in>{h \<in> F. a h \<bullet> z < b h}. {w. a h \<bullet> w < b h})"
    by (auto intro: openE [of _ z])
  then have e: "\<And>h. \<lbrakk>h \<in> F; a h \<bullet> z < b h\<rbrakk> \<Longrightarrow> ball z e \<subseteq> {w. a h \<bullet> w < b h}"
    by blast
  have "c \<subseteq> (S \<inter> ?ab h) \<longleftrightarrow> z \<in> S \<inter> ?ab h" if "h \<in> F" for h
  proof
    show "z \<in> S \<inter> ?ab h \<Longrightarrow> c \<subseteq> S \<inter> ?ab h"
      apply (rule subset_of_face_of [of _ S])
      using that \<open>c \<subseteq> S\<close> \<open>z \<in> rel_interior c\<close>
      using facet_of_polyhedron_explicit [OF \<open>finite F\<close> seq faceq psub]
            unfolding facet_of_def
      apply auto
      done
  next
    show "c \<subseteq> S \<inter> ?ab h \<Longrightarrow> z \<in> S \<inter> ?ab h"
      using \<open>z \<in> rel_interior c\<close> rel_interior_subset by force
  qed
  then have **: "{S \<inter> ?ab h | h. h \<in> F \<and> c \<subseteq> S \<and> c \<subseteq> ?ab h} =
                 {S \<inter> ?ab h |h. h \<in> F \<and> z \<in> S \<inter> ?ab h}"
    by blast
  have bsub: "ball z e \<inter> affine hull \<Inter>{S \<inter> ?ab h |h. h \<in> F \<and> a h \<bullet> z = b h}
             \<subseteq> affine hull S \<inter> \<Inter>F \<inter> \<Inter>{?ab h |h. h \<in> F \<and> a h \<bullet> z = b h}"
            if "i \<in> F" and i: "a i \<bullet> z = b i" for i
  proof -
    have sub: "ball z e \<inter> \<Inter>{?ab h |h. h \<in> F \<and> a h \<bullet> z = b h} \<subseteq> j"
             if "j \<in> F" for j
    proof -
      have "a j \<bullet> z \<le> b j" using faceq that xint by auto
      then consider "a j \<bullet> z < b j" | "a j \<bullet> z = b j" by linarith
      then have "\<exists>G. G \<in> {?ab h |h. h \<in> F \<and> a h \<bullet> z = b h} \<and> ball z e \<inter> G \<subseteq> j"
      proof cases
        assume "a j \<bullet> z < b j"
        then have "ball z e \<inter> {x. a i \<bullet> x = b i} \<subseteq> j"
          using e [OF \<open>j \<in> F\<close>] faceq that
          by (fastforce simp: ball_def)
        then show ?thesis
          by (rule_tac x="{x. a i \<bullet> x = b i}" in exI) (force simp: \<open>i \<in> F\<close> i)
      next
        assume eq: "a j \<bullet> z = b j"
        with faceq that show ?thesis
          by (rule_tac x="{x. a j \<bullet> x = b j}" in exI) (fastforce simp add: \<open>j \<in> F\<close>)
      qed
      then show ?thesis  by blast
    qed
    have 1: "affine hull \<Inter>{S \<inter> ?ab h |h. h \<in> F \<and> a h \<bullet> z = b h} \<subseteq> affine hull S"
      apply (rule hull_mono)
      using that \<open>z \<in> S\<close> by auto
    have 2: "affine hull \<Inter>{S \<inter> ?ab h |h. h \<in> F \<and> a h \<bullet> z = b h}
          \<subseteq> \<Inter>{?ab h |h. h \<in> F \<and> a h \<bullet> z = b h}"
      by (rule hull_minimal) (auto intro: affine_hyperplane)
    have 3: "ball z e \<inter> \<Inter>{?ab h |h. h \<in> F \<and> a h \<bullet> z = b h} \<subseteq> \<Inter>F"
      by (iprover intro: sub Inter_greatest)
    have *: "\<lbrakk>A \<subseteq> (B :: 'a set); A \<subseteq> C; E \<inter> C \<subseteq> D\<rbrakk> \<Longrightarrow> E \<inter> A \<subseteq> (B \<inter> D) \<inter> C"
             for A B C D E  by blast
    show ?thesis by (intro * 1 2 3)
  qed
  have "\<exists>h. h \<in> F \<and> c \<subseteq> ?ab h"
    apply (rule face_of_polyhedron_subset_explicit [OF \<open>finite F\<close> seq faceq psub])
    using assms by auto
  then have fac: "\<Inter>{S \<inter> ?ab h |h. h \<in> F \<and> c \<subseteq> S \<inter> ?ab h} face_of S"
    using * by (force simp: \<open>c \<subseteq> S\<close> intro: face_of_Inter)
  have red:
     "(\<And>a. P a \<Longrightarrow> T \<subseteq> S \<inter> \<Inter>{F x |x. P x}) \<Longrightarrow> T \<subseteq> \<Inter>{S \<inter> F x |x. P x}"
     for P T F   by blast
  have "ball z e \<inter> affine hull \<Inter>{S \<inter> ?ab h |h. h \<in> F \<and> a h \<bullet> z = b h}
        \<subseteq> \<Inter>{S \<inter> ?ab h |h. h \<in> F \<and> a h \<bullet> z = b h}"
    apply (rule red)
    apply (metis seq bsub)
    done
  with \<open>0 < e\<close> have zinrel: "z \<in> rel_interior
                    (\<Inter>{S \<inter> ?ab h |h. h \<in> F \<and> z \<in> S \<and> a h \<bullet> z = b h})"
    by (auto simp: mem_rel_interior_ball \<open>z \<in> S\<close>)
  show ?thesis
    apply (rule face_of_eq [OF c fac])
    using z zinrel apply (force simp: **)
    done
qed


subsection\<open>More general corollaries from the explicit representation\<close>

corollary facet_of_polyhedron:
  assumes "polyhedron S" and "c facet_of S"
  obtains a b where "a \<noteq> 0" "S \<subseteq> {x. a \<bullet> x \<le> b}" "c = S \<inter> {x. a \<bullet> x = b}"
proof -
  obtain F where "finite F" and seq: "S = affine hull S \<inter> \<Inter>F"
             and faces: "\<And>h. h \<in> F \<Longrightarrow> \<exists>a b. a \<noteq> 0 \<and> h = {x. a \<bullet> x \<le> b}"
             and min: "\<And>F'. F' \<subset> F \<Longrightarrow> S \<subset> (affine hull S) \<inter> \<Inter>F'"
    using assms by (simp add: polyhedron_Int_affine_minimal) meson
  then obtain a b where ab: "\<And>h. h \<in> F \<Longrightarrow> a h \<noteq> 0 \<and> h = {x. a h \<bullet> x \<le> b h}"
    by metis
  obtain i where "i \<in> F" and c: "c = S \<inter> {x. a i \<bullet> x = b i}"
    using facet_of_polyhedron_explicit [OF \<open>finite F\<close> seq ab min] assms
    by force
  moreover have ssub: "S \<subseteq> {x. a i \<bullet> x \<le> b i}"
     apply (subst seq)
     using \<open>i \<in> F\<close> ab by auto
  ultimately show ?thesis
    by (rule_tac a = "a i" and b = "b i" in that) (simp_all add: ab)
qed

corollary face_of_polyhedron:
  assumes "polyhedron S" and "c face_of S" and "c \<noteq> {}" and "c \<noteq> S"
    shows "c = \<Inter>{F. F facet_of S \<and> c \<subseteq> F}"
proof -
  obtain F where "finite F" and seq: "S = affine hull S \<inter> \<Inter>F"
             and faces: "\<And>h. h \<in> F \<Longrightarrow> \<exists>a b. a \<noteq> 0 \<and> h = {x. a \<bullet> x \<le> b}"
             and min: "\<And>F'. F' \<subset> F \<Longrightarrow> S \<subset> (affine hull S) \<inter> \<Inter>F'"
    using assms by (simp add: polyhedron_Int_affine_minimal) meson
  then obtain a b where ab: "\<And>h. h \<in> F \<Longrightarrow> a h \<noteq> 0 \<and> h = {x. a h \<bullet> x \<le> b h}"
    by metis
  show ?thesis
    apply (subst face_of_polyhedron_explicit [OF \<open>finite F\<close> seq ab min])
    apply (auto simp: assms facet_of_polyhedron_explicit [OF \<open>finite F\<close> seq ab min] cong: Collect_cong)
    done
qed

lemma face_of_polyhedron_subset_facet:
  assumes "polyhedron S" and "c face_of S" and "c \<noteq> {}" and "c \<noteq> S"
  obtains F where "F facet_of S" "c \<subseteq> F"
using face_of_polyhedron assms
by (metis (no_types, lifting) Inf_greatest antisym_conv face_of_imp_subset mem_Collect_eq)


lemma exposed_face_of_polyhedron:
  assumes "polyhedron S"
    shows "F exposed_face_of S \<longleftrightarrow> F face_of S"
proof
  show "F exposed_face_of S \<Longrightarrow> F face_of S"
    by (simp add: exposed_face_of_def)
next
  assume "F face_of S"
  show "F exposed_face_of S"
  proof (cases "F = {} \<or> F = S")
    case True then show ?thesis
      using \<open>F face_of S\<close> exposed_face_of by blast
  next
    case False
    then have "{g. g facet_of S \<and> F \<subseteq> g} \<noteq> {}"
      by (metis Collect_empty_eq_bot \<open>F face_of S\<close> assms empty_def face_of_polyhedron_subset_facet)
    moreover have "\<And>T. \<lbrakk>T facet_of S; F \<subseteq> T\<rbrakk> \<Longrightarrow> T exposed_face_of S"
      by (metis assms exposed_face_of facet_of_imp_face_of facet_of_polyhedron)
    ultimately have "\<Inter>{fa.
       fa facet_of S \<and> F \<subseteq> fa} exposed_face_of S"
      by (metis (no_types, lifting) mem_Collect_eq exposed_face_of_Inter)
    then show ?thesis
      using False
      apply (subst face_of_polyhedron [OF assms \<open>F face_of S\<close>], auto)
      done
  qed
qed

lemma face_of_polyhedron_polyhedron:
  fixes S :: "'a :: euclidean_space set"
  assumes "polyhedron S" "c face_of S"
    shows "polyhedron c"
by (metis assms face_of_imp_eq_affine_Int polyhedron_Int polyhedron_affine_hull polyhedron_imp_closed polyhedron_imp_convex)

lemma finite_polyhedron_faces:
  fixes S :: "'a :: euclidean_space set"
  assumes "polyhedron S"
    shows "finite {F. F face_of S}"
proof -
  obtain F where "finite F" and seq: "S = affine hull S \<inter> \<Inter>F"
             and faces: "\<And>h. h \<in> F \<Longrightarrow> \<exists>a b. a \<noteq> 0 \<and> h = {x. a \<bullet> x \<le> b}"
             and min:   "\<And>F'. F' \<subset> F \<Longrightarrow> S \<subset> (affine hull S) \<inter> \<Inter>F'"
    using assms by (simp add: polyhedron_Int_affine_minimal) meson
  then obtain a b where ab: "\<And>h. h \<in> F \<Longrightarrow> a h \<noteq> 0 \<and> h = {x. a h \<bullet> x \<le> b h}"
    by metis
  have "finite {\<Inter>{S \<inter> {x. a h \<bullet> x = b h} |h. h \<in> F'}| F'. F' \<in> Pow F}"
    by (simp add: \<open>finite F\<close>)
  moreover have "{F. F face_of S} - {{}, S} \<subseteq> {\<Inter>{S \<inter> {x. a h \<bullet> x = b h} |h. h \<in> F'}| F'. F' \<in> Pow F}"
    apply clarify
    apply (rename_tac c)
    apply (drule face_of_polyhedron_explicit [OF \<open>finite F\<close> seq ab min, simplified], simp_all)
    apply (erule ssubst)
    apply (rule_tac x="{h \<in> F. c \<subseteq> S \<inter> {x. a h \<bullet> x = b h}}" in exI, auto)
    done
  ultimately show ?thesis
    by (meson finite.emptyI finite.insertI finite_Diff2 finite_subset)
qed

lemma finite_polyhedron_exposed_faces:
   "polyhedron S \<Longrightarrow> finite {F. F exposed_face_of S}"
using exposed_face_of_polyhedron finite_polyhedron_faces by fastforce

lemma finite_polyhedron_extreme_points:
  fixes S :: "'a :: euclidean_space set"
  shows "polyhedron S \<Longrightarrow> finite {v. v extreme_point_of S}"
apply (simp add: face_of_singleton [symmetric])
apply (rule finite_subset [OF _ finite_vimageI [OF finite_polyhedron_faces]], auto)
done

lemma finite_polyhedron_facets:
  fixes S :: "'a :: euclidean_space set"
  shows "polyhedron S \<Longrightarrow> finite {F. F facet_of S}"
unfolding facet_of_def
by (blast intro: finite_subset [OF _ finite_polyhedron_faces])


proposition rel_interior_of_polyhedron:
  fixes S :: "'a :: euclidean_space set"
  assumes "polyhedron S"
    shows "rel_interior S = S - \<Union>{F. F facet_of S}"
proof -
  obtain F where "finite F" and seq: "S = affine hull S \<inter> \<Inter>F"
             and faces: "\<And>h. h \<in> F \<Longrightarrow> \<exists>a b. a \<noteq> 0 \<and> h = {x. a \<bullet> x \<le> b}"
             and min: "\<And>F'. F' \<subset> F \<Longrightarrow> S \<subset> (affine hull S) \<inter> \<Inter>F'"
    using assms by (simp add: polyhedron_Int_affine_minimal) meson
  then obtain a b where ab: "\<And>h. h \<in> F \<Longrightarrow> a h \<noteq> 0 \<and> h = {x. a h \<bullet> x \<le> b h}"
    by metis
  have facet: "(c facet_of S) \<longleftrightarrow> (\<exists>h. h \<in> F \<and> c = S \<inter> {x. a h \<bullet> x = b h})" for c
    by (rule facet_of_polyhedron_explicit [OF \<open>finite F\<close> seq ab min])
  have rel: "rel_interior S = {x \<in> S. \<forall>h\<in>F. a h \<bullet> x < b h}"
    by (rule rel_interior_polyhedron_explicit [OF \<open>finite F\<close> seq ab min])
  have "a h \<bullet> x < b h" if "x \<in> S" "h \<in> F" and xnot: "x \<notin> \<Union>{F. F facet_of S}" for x h
  proof -
    have "x \<in> \<Inter>F" using seq that by force
    with \<open>h \<in> F\<close> ab have "a h \<bullet> x \<le> b h" by auto
    then consider "a h \<bullet> x < b h" | "a h \<bullet> x = b h" by linarith
    then show ?thesis
    proof cases
      case 1 then show ?thesis .
    next
      case 2
      have "Collect (op \<in> x) \<notin> Collect (op \<in> (\<Union>{A. A facet_of S}))"
        using xnot by fastforce
      then have "F \<notin> Collect (op \<in> h)"
        using 2 \<open>x \<in> S\<close> facet by blast
      with \<open>h \<in> F\<close> have "\<Inter>F \<subseteq> S \<inter> {x. a h \<bullet> x = b h}" by blast
      with 2 that \<open>x \<in> \<Inter>F\<close> show ?thesis
        apply simp
        apply (drule_tac x="\<Inter>F" in spec)
        apply (simp add: facet)
        apply (drule_tac x=h in spec)
        using seq by auto
      qed
  qed
  moreover have "\<exists>h\<in>F. a h \<bullet> x \<ge> b h" if "x \<in> \<Union>{F. F facet_of S}" for x
    using that by (force simp: facet)
  ultimately show ?thesis
    by (force simp: rel)
qed

lemma rel_boundary_of_polyhedron:
  fixes S :: "'a :: euclidean_space set"
  assumes "polyhedron S"
    shows "S - rel_interior S = \<Union> {F. F facet_of S}"
using facet_of_imp_subset by (fastforce simp add: rel_interior_of_polyhedron assms)

lemma rel_frontier_of_polyhedron:
  fixes S :: "'a :: euclidean_space set"
  assumes "polyhedron S"
    shows "rel_frontier S = \<Union> {F. F facet_of S}"
by (simp add: assms rel_frontier_def polyhedron_imp_closed rel_boundary_of_polyhedron)

lemma rel_frontier_of_polyhedron_alt:
  fixes S :: "'a :: euclidean_space set"
  assumes "polyhedron S"
    shows "rel_frontier S = \<Union> {F. F face_of S \<and> (F \<noteq> S)}"
apply (rule subset_antisym)
  apply (force simp: rel_frontier_of_polyhedron facet_of_def assms)
using face_of_subset_rel_frontier by fastforce


text\<open>A characterization of polyhedra as having finitely many faces\<close>

proposition polyhedron_eq_finite_exposed_faces:
  fixes S :: "'a :: euclidean_space set"
  shows "polyhedron S \<longleftrightarrow> closed S \<and> convex S \<and> finite {F. F exposed_face_of S}"
         (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    by (auto simp: polyhedron_imp_closed polyhedron_imp_convex finite_polyhedron_exposed_faces)
next
  assume ?rhs
  then have "closed S" "convex S" and fin: "finite {F. F exposed_face_of S}" by auto
  show ?lhs
  proof (cases "S = {}")
    case True then show ?thesis by auto
  next
    case False
    define F where "F = {h. h exposed_face_of S \<and> h \<noteq> {} \<and> h \<noteq> S}"
    have "finite F" by (simp add: fin F_def)
    have hface: "h face_of S"
      and "\<exists>a b. a \<noteq> 0 \<and> S \<subseteq> {x. a \<bullet> x \<le> b} \<and> h = S \<inter> {x. a \<bullet> x = b}"
      if "h \<in> F" for h
      using exposed_face_of F_def that by simp_all auto
    then obtain a b where ab:
      "\<And>h. h \<in> F \<Longrightarrow> a h \<noteq> 0 \<and> S \<subseteq> {x. a h \<bullet> x \<le> b h} \<and> h = S \<inter> {x. a h \<bullet> x = b h}"
      by metis
    have *: "False"
      if paff: "p \<in> affine hull S" and "p \<notin> S"
      and pint: "p \<in> \<Inter>{{x. a h \<bullet> x \<le> b h} |h. h \<in> F}" for p
    proof -
      have "rel_interior S \<noteq> {}"
        by (simp add: \<open>S \<noteq> {}\<close> \<open>convex S\<close> rel_interior_eq_empty)
      then obtain c where c: "c \<in> rel_interior S" by auto
      with rel_interior_subset have "c \<in> S"  by blast
      have ccp: "closed_segment c p \<subseteq> affine hull S"
        by (meson affine_affine_hull affine_imp_convex c closed_segment_subset hull_subset paff rel_interior_subset subsetCE)
      obtain x where xcl: "x \<in> closed_segment c p" and "x \<in> S" and xnot: "x \<notin> rel_interior S"
        using connected_openin [of "closed_segment c p"]
        apply simp
        apply (drule_tac x="closed_segment c p \<inter> rel_interior S" in spec)
        apply (erule impE)
         apply (force simp: openin_rel_interior openin_Int intro: openin_subtopology_Int_subset [OF _ ccp])
        apply (drule_tac x="closed_segment c p \<inter> (- S)" in spec)
        using rel_interior_subset \<open>closed S\<close> c \<open>p \<notin> S\<close> apply blast
        done
      then obtain \<mu> where "0 \<le> \<mu>" "\<mu> \<le> 1" and xeq: "x = (1 - \<mu>) *\<^sub>R c + \<mu> *\<^sub>R p"
        by (auto simp: in_segment)
      show False
      proof (cases "\<mu>=0 \<or> \<mu>=1")
        case True with xeq c xnot \<open>x \<in> S\<close> \<open>p \<notin> S\<close>
        show False by auto
      next
        case False
        then have xos: "x \<in> open_segment c p"
          using \<open>x \<in> S\<close> c open_segment_def that(2) xcl xnot by auto
        have xclo: "x \<in> closure S"
          using \<open>x \<in> S\<close> closure_subset by blast
        obtain d where "d \<noteq> 0"
              and dle: "\<And>y. y \<in> closure S \<Longrightarrow> d \<bullet> x \<le> d \<bullet> y"
              and dless: "\<And>y. y \<in> rel_interior S \<Longrightarrow> d \<bullet> x < d \<bullet> y"
          by (metis supporting_hyperplane_relative_frontier [OF \<open>convex S\<close> xclo xnot])
        have sex: "S \<inter> {y. d \<bullet> y = d \<bullet> x} exposed_face_of S"
          by (simp add: \<open>closed S\<close> dle exposed_face_of_Int_supporting_hyperplane_ge [OF \<open>convex S\<close>])
        have sne: "S \<inter> {y. d \<bullet> y = d \<bullet> x} \<noteq> {}"
          using \<open>x \<in> S\<close> by blast
        have sns: "S \<inter> {y. d \<bullet> y = d \<bullet> x} \<noteq> S"
          by (metis (mono_tags) Int_Collect c subsetD dless not_le order_refl rel_interior_subset)
        obtain h where "h \<in> F" "x \<in> h"
          apply (rule_tac h="S \<inter> {y. d \<bullet> y = d \<bullet> x}" in that)
          apply (simp_all add: F_def sex sne sns \<open>x \<in> S\<close>)
          done
        have abface: "{y. a h \<bullet> y = b h} face_of {y. a h \<bullet> y \<le> b h}"
          using hyperplane_face_of_halfspace_le by blast
        then have "c \<in> h"
          using face_ofD [OF abface xos] \<open>c \<in> S\<close> \<open>h \<in> F\<close> ab pint \<open>x \<in> h\<close> by blast
        with c have "h \<inter> rel_interior S \<noteq> {}" by blast
        then show False
          using \<open>h \<in> F\<close> F_def face_of_disjoint_rel_interior hface by auto
      qed
    qed
    have "S \<subseteq> affine hull S \<inter> \<Inter>{{x. a h \<bullet> x \<le> b h} |h. h \<in> F}"
      using ab by (auto simp: hull_subset)
    moreover have "affine hull S \<inter> \<Inter>{{x. a h \<bullet> x \<le> b h} |h. h \<in> F} \<subseteq> S"
      using * by blast
    ultimately have "S = affine hull S \<inter> \<Inter> {{x. a h \<bullet> x \<le> b h} |h. h \<in> F}" ..
    then show ?thesis
      apply (rule ssubst)
      apply (force intro: polyhedron_affine_hull polyhedron_halfspace_le simp: \<open>finite F\<close>)
      done
  qed
qed

corollary polyhedron_eq_finite_faces:
  fixes S :: "'a :: euclidean_space set"
  shows "polyhedron S \<longleftrightarrow> closed S \<and> convex S \<and> finite {F. F face_of S}"
         (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    by (simp add: finite_polyhedron_faces polyhedron_imp_closed polyhedron_imp_convex)
next
  assume ?rhs
  then show ?lhs
    by (force simp: polyhedron_eq_finite_exposed_faces exposed_face_of intro: finite_subset)
qed

lemma polyhedron_linear_image_eq:
  fixes h :: "'a :: euclidean_space \<Rightarrow> 'b :: euclidean_space"
  assumes "linear h" "bij h"
    shows "polyhedron (h ` S) \<longleftrightarrow> polyhedron S"
proof -
  have *: "{f. P f} = (image h) ` {f. P (h ` f)}" for P
    apply safe
    apply (rule_tac x="inv h ` x" in image_eqI)
    apply (auto simp: \<open>bij h\<close> bij_is_surj image_f_inv_f)
    done
  have "inj h" using bij_is_inj assms by blast
  then have injim: "inj_on (op ` h) A" for A
    by (simp add: inj_on_def inj_image_eq_iff)
  show ?thesis
    using \<open>linear h\<close> \<open>inj h\<close>
    apply (simp add: polyhedron_eq_finite_faces closed_injective_linear_image_eq)
    apply (simp add: * face_of_linear_image [of h _ S, symmetric] finite_image_iff injim)
    done
qed

lemma polyhedron_negations:
  fixes S :: "'a :: euclidean_space set"
  shows   "polyhedron S \<Longrightarrow> polyhedron(image uminus S)"
by (auto simp: polyhedron_linear_image_eq linear_uminus bij_uminus)

subsection\<open>Relation between polytopes and polyhedra\<close>

lemma polytope_eq_bounded_polyhedron:
  fixes S :: "'a :: euclidean_space set"
  shows "polytope S \<longleftrightarrow> polyhedron S \<and> bounded S"
         (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    by (simp add: finite_polytope_faces polyhedron_eq_finite_faces
                  polytope_imp_closed polytope_imp_convex polytope_imp_bounded)
next
  assume ?rhs then show ?lhs
    unfolding polytope_def
    apply (rule_tac x="{v. v extreme_point_of S}" in exI)
    apply (simp add: finite_polyhedron_extreme_points Krein_Milman_Minkowski compact_eq_bounded_closed polyhedron_imp_closed polyhedron_imp_convex)
    done
qed

lemma polytope_Int:
  fixes S :: "'a :: euclidean_space set"
  shows "\<lbrakk>polytope S; polytope T\<rbrakk> \<Longrightarrow> polytope(S \<inter> T)"
by (simp add: polytope_eq_bounded_polyhedron bounded_Int)


lemma polytope_Int_polyhedron:
  fixes S :: "'a :: euclidean_space set"
  shows "\<lbrakk>polytope S; polyhedron T\<rbrakk> \<Longrightarrow> polytope(S \<inter> T)"
by (simp add: bounded_Int polytope_eq_bounded_polyhedron)

lemma polyhedron_Int_polytope:
  fixes S :: "'a :: euclidean_space set"
  shows "\<lbrakk>polyhedron S; polytope T\<rbrakk> \<Longrightarrow> polytope(S \<inter> T)"
by (simp add: bounded_Int polytope_eq_bounded_polyhedron)

lemma polytope_imp_polyhedron:
  fixes S :: "'a :: euclidean_space set"
  shows "polytope S \<Longrightarrow> polyhedron S"
by (simp add: polytope_eq_bounded_polyhedron)

lemma polytope_facet_exists:
  fixes p :: "'a :: euclidean_space set"
  assumes "polytope p" "0 < aff_dim p"
  obtains F where "F facet_of p"
proof (cases "p = {}")
  case True with assms show ?thesis by auto
next
  case False
  then obtain v where "v extreme_point_of p"
    using extreme_point_exists_convex
    by (blast intro: \<open>polytope p\<close> polytope_imp_compact polytope_imp_convex)
  then
  show ?thesis
    by (metis face_of_polyhedron_subset_facet polytope_imp_polyhedron aff_dim_sing
       all_not_in_conv assms face_of_singleton less_irrefl singletonI that)
qed

lemma polyhedron_interval [iff]: "polyhedron(cbox a b)"
by (metis polytope_imp_polyhedron polytope_interval)

lemma polyhedron_convex_hull:
  fixes S :: "'a :: euclidean_space set"
  shows "finite S \<Longrightarrow> polyhedron(convex hull S)"
by (simp add: polytope_convex_hull polytope_imp_polyhedron)


subsection\<open>Relative and absolute frontier of a polytope\<close>

lemma rel_boundary_of_convex_hull:
    fixes S :: "'a::euclidean_space set"
    assumes "~ affine_dependent S"
      shows "(convex hull S) - rel_interior(convex hull S) = (\<Union>a\<in>S. convex hull (S - {a}))"
proof -
  have "finite S" by (metis assms aff_independent_finite)
  then consider "card S = 0" | "card S = 1" | "2 \<le> card S" by arith
  then show ?thesis
  proof cases
    case 1 then have "S = {}" by (simp add: \<open>finite S\<close>)
    then show ?thesis by simp
  next
    case 2 show ?thesis
      by (auto intro: card_1_singletonE [OF \<open>card S = 1\<close>])
  next
    case 3
    with assms show ?thesis
      by (auto simp: polyhedron_convex_hull rel_boundary_of_polyhedron facet_of_convex_hull_affine_independent_alt \<open>finite S\<close>)
  qed
qed

proposition frontier_of_convex_hull:
    fixes S :: "'a::euclidean_space set"
    assumes "card S = Suc (DIM('a))"
      shows "frontier(convex hull S) = \<Union> {convex hull (S - {a}) | a. a \<in> S}"
proof (cases "affine_dependent S")
  case True
    have [iff]: "finite S"
      using assms using card_infinite by force
    then have ccs: "closed (convex hull S)"
      by (simp add: compact_imp_closed finite_imp_compact_convex_hull)
    { fix x T
      assume "finite T" "T \<subseteq> S" "int (card T) \<le> aff_dim S + 1" "x \<in> convex hull T"
      then have "S \<noteq> T"
        using True \<open>finite S\<close> aff_dim_le_card affine_independent_iff_card by fastforce
      then obtain a where "a \<in> S" "a \<notin> T"
        using \<open>T \<subseteq> S\<close> by blast
      then have "x \<in> (\<Union>a\<in>S. convex hull (S - {a}))"
        using True affine_independent_iff_card [of S]
        apply simp
        apply (metis (no_types, hide_lams) Diff_eq_empty_iff Diff_insert0 \<open>a \<notin> T\<close> \<open>T \<subseteq> S\<close> \<open>x \<in> convex hull T\<close>  hull_mono insert_Diff_single   subsetCE)
        done
    } note * = this
    have 1: "convex hull S \<subseteq> (\<Union> a\<in>S. convex hull (S - {a}))"
      apply (subst caratheodory_aff_dim)
      apply (blast intro: *)
      done
    have 2: "\<Union>((\<lambda>a. convex hull (S - {a})) ` S) \<subseteq> convex hull S"
      by (rule Union_least) (metis (no_types, lifting)  Diff_subset hull_mono imageE)
    show ?thesis using True
      apply (simp add: segment_convex_hull frontier_def)
      using interior_convex_hull_eq_empty [OF assms]
      apply (simp add: closure_closed [OF ccs])
      apply (rule subset_antisym)
      using 1 apply blast
      using 2 apply blast
      done
next
  case False
  then have "frontier (convex hull S) = (convex hull S) - rel_interior(convex hull S)"
    apply (simp add: rel_boundary_of_convex_hull [symmetric] frontier_def)
    by (metis aff_independent_finite assms closure_convex_hull finite_imp_compact_convex_hull hull_hull interior_convex_hull_eq_empty rel_interior_nonempty_interior)
  also have "... = \<Union>{convex hull (S - {a}) |a. a \<in> S}"
  proof -
    have "convex hull S - rel_interior (convex hull S) = rel_frontier (convex hull S)"
      by (simp add: False aff_independent_finite polyhedron_convex_hull rel_boundary_of_polyhedron rel_frontier_of_polyhedron)
    then show ?thesis
      by (simp add: False rel_frontier_convex_hull_cases)
  qed
  finally show ?thesis .
qed

subsection\<open>Special case of a triangle\<close>

proposition frontier_of_triangle:
    fixes a :: "'a::euclidean_space"
    assumes "DIM('a) = 2"
    shows "frontier(convex hull {a,b,c}) = closed_segment a b \<union> closed_segment b c \<union> closed_segment c a"
          (is "?lhs = ?rhs")
proof (cases "b = a \<or> c = a \<or> c = b")
  case True then show ?thesis
    by (auto simp: assms segment_convex_hull frontier_def empty_interior_convex_hull insert_commute card_insert_le_m1 hull_inc insert_absorb)
next
  case False then have [simp]: "card {a, b, c} = Suc (DIM('a))"
    by (simp add: card_insert Set.insert_Diff_if assms)
  show ?thesis
  proof
    show "?lhs \<subseteq> ?rhs"
      using False
      by (force simp: segment_convex_hull frontier_of_convex_hull insert_Diff_if insert_commute split: if_split_asm)
    show "?rhs \<subseteq> ?lhs"
      using False
      apply (simp add: frontier_of_convex_hull segment_convex_hull)
      apply (intro conjI subsetI)
        apply (rule_tac X="convex hull {a,b}" in UnionI; force simp: Set.insert_Diff_if)
       apply (rule_tac X="convex hull {b,c}" in UnionI; force)
      apply (rule_tac X="convex hull {a,c}" in UnionI; force simp: insert_commute Set.insert_Diff_if)
      done
  qed
qed

corollary inside_of_triangle:
    fixes a :: "'a::euclidean_space"
    assumes "DIM('a) = 2"
    shows "inside (closed_segment a b \<union> closed_segment b c \<union> closed_segment c a) = interior(convex hull {a,b,c})"
by (metis assms frontier_of_triangle bounded_empty bounded_insert convex_convex_hull inside_frontier_eq_interior bounded_convex_hull)

corollary interior_of_triangle:
    fixes a :: "'a::euclidean_space"
    assumes "DIM('a) = 2"
    shows "interior(convex hull {a,b,c}) =
           convex hull {a,b,c} - (closed_segment a b \<union> closed_segment b c \<union> closed_segment c a)"
  using interior_subset
  by (force simp: frontier_of_triangle [OF assms, symmetric] frontier_def Diff_Diff_Int)

subsection\<open>Subdividing a cell complex\<close>

lemma subdivide_interval:
  fixes x::real
  assumes "a < \<bar>x - y\<bar>" "0 < a"
  obtains n where "n \<in> \<int>" "x < n * a \<and> n * a < y \<or> y <  n * a \<and> n * a < x"
proof -
  consider "a + x < y" | "a + y < x"
    using assms by linarith
  then show ?thesis
  proof cases
    case 1
    let ?n = "of_int (floor (x/a)) + 1"
    have x: "x < ?n * a"
      by (meson \<open>0 < a\<close> divide_less_eq floor_unique_iff)
    have "?n * a \<le> a + x"
      apply (simp add: algebra_simps)
      by (metis \<open>0 < a\<close> floor_correct less_irrefl nonzero_mult_div_cancel_left real_mult_le_cancel_iff2 times_divide_eq_right)
    also have "... < y"
      by (rule 1)
    finally have "?n * a < y" .
    with x show ?thesis
      using Ints_1 Ints_add Ints_of_int that by blast
  next
    case 2
    let ?n = "of_int (floor (y/a)) + 1"
    have y: "y < ?n * a"
      by (meson \<open>0 < a\<close> divide_less_eq floor_unique_iff)
    have "?n * a \<le> a + y"
      apply (simp add: algebra_simps)
      by (metis \<open>0 < a\<close> floor_correct less_irrefl nonzero_mult_div_cancel_left real_mult_le_cancel_iff2 times_divide_eq_right)
    also have "... < x"
      by (rule 2)
    finally have "?n * a < x" .
    then show ?thesis
      using Ints_1 Ints_add Ints_of_int that y by blast
  qed
qed


lemma cell_subdivision_lemma:
  assumes "finite \<F>"
      and "\<And>X. X \<in> \<F> \<Longrightarrow> polytope X"
      and "\<And>X. X \<in> \<F> \<Longrightarrow> aff_dim X \<le> d"
      and "\<And>X Y. \<lbrakk>X \<in> \<F>; Y \<in> \<F>\<rbrakk> \<Longrightarrow> (X \<inter> Y) face_of X \<and> (X \<inter> Y) face_of Y"
      and "finite I"
    shows "\<exists>\<F>'. \<Union>\<F>' = \<Union>\<F> \<and>
                 finite \<F>' \<and>
                 (\<forall>X \<in> \<F>'. polytope X) \<and>
                 (\<forall>X \<in> \<F>'. aff_dim X \<le> d) \<and>
                 (\<forall>X \<in> \<F>'. \<forall>Y \<in> \<F>'. X \<inter> Y face_of X \<and> X \<inter> Y face_of Y) \<and>
                 (\<forall>X \<in> \<F>'. \<forall>x \<in> X. \<forall>y \<in> X. \<forall>a b.
                          (a,b) \<in> I \<longrightarrow> a \<bullet> x \<le> b \<and> a \<bullet> y \<le> b \<or>
                                        a \<bullet> x \<ge> b \<and> a \<bullet> y \<ge> b)"
  using \<open>finite I\<close>
proof induction
  case empty
  then show ?case
    by (rule_tac x="\<F>" in exI) (simp add: assms)
next
  case (insert ab I)
  then obtain \<F>' where eq: "\<Union>\<F>' = \<Union>\<F>" and "finite \<F>'"
                   and poly: "\<And>X. X \<in> \<F>' \<Longrightarrow> polytope X"
                   and aff: "\<And>X. X \<in> \<F>' \<Longrightarrow> aff_dim X \<le> d"
                   and face: "\<And>X Y. \<lbrakk>X \<in> \<F>'; Y \<in> \<F>'\<rbrakk> \<Longrightarrow> X \<inter> Y face_of X \<and> X \<inter> Y face_of Y"
                   and I: "\<And>X x y a b.  \<lbrakk>X \<in> \<F>'; x \<in> X; y \<in> X; (a,b) \<in> I\<rbrakk> \<Longrightarrow>
                                    a \<bullet> x \<le> b \<and> a \<bullet> y \<le> b \<or> a \<bullet> x \<ge> b \<and> a \<bullet> y \<ge> b"
    by (auto simp: that)
  obtain a b where "ab = (a,b)"
    by fastforce
  let ?\<G> = "(\<lambda>X. X \<inter> {x. a \<bullet> x \<le> b}) ` \<F>' \<union> (\<lambda>X. X \<inter> {x. a \<bullet> x \<ge> b}) ` \<F>'"
  have eqInt: "(S \<inter> Collect P) \<inter> (T \<inter> Collect Q) = (S \<inter> T) \<inter> (Collect P \<inter> Collect Q)" for S T::"'a set" and P Q
    by blast
  show ?case
  proof (intro conjI exI)
    show "\<Union>?\<G> = \<Union>\<F>"
      by (force simp: eq [symmetric])
    show "finite ?\<G>"
      using \<open>finite \<F>'\<close> by force
    show "\<forall>X \<in> ?\<G>. polytope X"
      by (force simp: poly polytope_Int_polyhedron polyhedron_halfspace_le polyhedron_halfspace_ge)
    show "\<forall>X \<in> ?\<G>. aff_dim X \<le> d"
      by (auto; metis order_trans aff aff_dim_subset inf_le1)
    show "\<forall>X \<in> ?\<G>. \<forall>x \<in> X. \<forall>y \<in> X. \<forall>a b.
                          (a,b) \<in> insert ab I \<longrightarrow> a \<bullet> x \<le> b \<and> a \<bullet> y \<le> b \<or>
                                                  a \<bullet> x \<ge> b \<and> a \<bullet> y \<ge> b"
      using \<open>ab = (a, b)\<close> I by fastforce
    show "\<forall>X \<in> ?\<G>. \<forall>Y \<in> ?\<G>. X \<inter> Y face_of X \<and> X \<inter> Y face_of Y"
      by (auto simp: eqInt halfspace_Int_eq face_of_Int_Int face face_of_halfspace_le face_of_halfspace_ge)
  qed
qed


proposition cell_complex_subdivision_exists:
  fixes \<F> :: "'a::euclidean_space set set"
  assumes "0 < e" "finite \<F>"
      and poly: "\<And>X. X \<in> \<F> \<Longrightarrow> polytope X"
      and aff: "\<And>X. X \<in> \<F> \<Longrightarrow> aff_dim X \<le> d"
      and face: "\<And>X Y. \<lbrakk>X \<in> \<F>; Y \<in> \<F>\<rbrakk> \<Longrightarrow> X \<inter> Y face_of X \<and> X \<inter> Y face_of Y"
  obtains "\<F>'" where "finite \<F>'" "\<Union>\<F>' = \<Union>\<F>" "\<And>X. X \<in> \<F>' \<Longrightarrow> diameter X < e"
                "\<And>X. X \<in> \<F>' \<Longrightarrow> polytope X" "\<And>X. X \<in> \<F>' \<Longrightarrow> aff_dim X \<le> d"
                "\<And>X Y. \<lbrakk>X \<in> \<F>'; Y \<in> \<F>'\<rbrakk> \<Longrightarrow> X \<inter> Y face_of X \<and> X \<inter> Y face_of Y"
proof -
  have "bounded(\<Union>\<F>)"
    by (simp add: \<open>finite \<F>\<close> poly bounded_Union polytope_imp_bounded)
  then obtain B where "B > 0" and B: "\<And>x. x \<in> \<Union>\<F> \<Longrightarrow> norm x < B"
    by (meson bounded_pos_less)
  define C where "C \<equiv> {z \<in> \<int>. \<bar>z * e / 2 / real DIM('a)\<bar> \<le> B}"
  define I where "I \<equiv> \<Union>i \<in> Basis. \<Union>j \<in> C. { (i::'a, j * e / 2 / DIM('a)) }"
  have "finite C"
    using finite_int_segment [of "-B / (e / 2 / DIM('a))" "B / (e / 2 / DIM('a))"]
    apply (simp add: C_def)
    apply (erule rev_finite_subset)
    using \<open>0 < e\<close>
    apply (auto simp: divide_simps)
    done
  then have "finite I"
    by (simp add: I_def)
  obtain \<F>' where eq: "\<Union>\<F>' = \<Union>\<F>" and "finite \<F>'"
              and poly: "\<And>X. X \<in> \<F>' \<Longrightarrow> polytope X"
              and aff: "\<And>X. X \<in> \<F>' \<Longrightarrow> aff_dim X \<le> d"
              and face: "\<And>X Y. \<lbrakk>X \<in> \<F>'; Y \<in> \<F>'\<rbrakk> \<Longrightarrow> X \<inter> Y face_of X \<and> X \<inter> Y face_of Y"
              and I: "\<And>X x y a b.  \<lbrakk>X \<in> \<F>'; x \<in> X; y \<in> X; (a,b) \<in> I\<rbrakk> \<Longrightarrow>
                                     a \<bullet> x \<le> b \<and> a \<bullet> y \<le> b \<or> a \<bullet> x \<ge> b \<and> a \<bullet> y \<ge> b"
    apply (rule exE [OF cell_subdivision_lemma])
         apply (rule assms \<open>finite I\<close> | assumption)+
    apply (auto intro: that)
    done
  show ?thesis
  proof (rule_tac \<F>'="\<F>'" in that)
    show "diameter X < e" if "X \<in> \<F>'" for X
    proof -
      have "diameter X \<le> e/2"
      proof (rule diameter_le)
        show "norm (x - y) \<le> e / 2" if "x \<in> X" "y \<in> X" for x y
        proof -
          have "norm x < B" "norm y < B"
            using B \<open>X \<in> \<F>'\<close> eq that by fastforce+
          have "norm (x - y) \<le> (\<Sum>b\<in>Basis. \<bar>(x-y) \<bullet> b\<bar>)"
            by (rule norm_le_l1)
          also have "... \<le> of_nat (DIM('a)) * (e / 2 / DIM('a))"
          proof (rule sum_bounded_above)
            fix i::'a
            assume "i \<in> Basis"
            then have I': "\<And>z b. \<lbrakk>z \<in> C; b = z * e / (2 * real DIM('a))\<rbrakk> \<Longrightarrow> i \<bullet> x \<le> b \<and> i \<bullet> y \<le> b \<or> i \<bullet> x \<ge> b \<and> i \<bullet> y \<ge> b"
              using I \<open>X \<in> \<F>'\<close> that
              by (fastforce simp: I_def)
            show "\<bar>(x - y) \<bullet> i\<bar> \<le> e / 2 / real DIM('a)"
            proof (rule ccontr)
              assume "\<not> \<bar>(x - y) \<bullet> i\<bar> \<le> e / 2 / real DIM('a)"
              then have xyi: "\<bar>i \<bullet> x - i \<bullet> y\<bar> > e / 2 / real DIM('a)"
                by (simp add: inner_commute inner_diff_right)
              obtain n where "n \<in> \<int>" and n: "i \<bullet> x < n * (e / 2 / real DIM('a)) \<and> n * (e / 2 / real DIM('a)) < i \<bullet> y \<or> i \<bullet> y < n * (e / 2 / real DIM('a)) \<and> n * (e / 2 / real DIM('a)) < i \<bullet> x"
                using subdivide_interval [OF xyi] DIM_positive \<open>0 < e\<close>
                by (auto simp: zero_less_divide_iff)
              have "\<bar>i \<bullet> x\<bar> < B"
                by (metis \<open>i \<in> Basis\<close> \<open>norm x < B\<close> inner_commute norm_bound_Basis_lt)
              have "\<bar>i \<bullet> y\<bar> < B"
                by (metis \<open>i \<in> Basis\<close> \<open>norm y < B\<close> inner_commute norm_bound_Basis_lt)
              have *: "\<bar>n * e\<bar> \<le> B * (2 * real DIM('a))"
                      if "\<bar>ix\<bar> < B" "\<bar>iy\<bar> < B"
                         and ix: "ix * (2 * real DIM('a)) < n * e"
                         and iy: "n * e < iy * (2 * real DIM('a))" for ix iy
              proof (rule abs_leI)
                have "iy * (2 * real DIM('a)) \<le> B * (2 * real DIM('a))"
                  by (rule mult_right_mono) (use \<open>\<bar>iy\<bar> < B\<close> in linarith)+
                then show "n * e \<le> B * (2 * real DIM('a))"
                  using iy by linarith
              next
                have "- ix * (2 * real DIM('a)) \<le> B * (2 * real DIM('a))"
                  by (rule mult_right_mono) (use \<open>\<bar>ix\<bar> < B\<close> in linarith)+
                then show "- (n * e) \<le> B * (2 * real DIM('a))"
                  using ix by linarith
              qed
              have "n \<in> C"
                using \<open>n \<in> \<int>\<close> n  by (auto simp: C_def divide_simps intro: * \<open>\<bar>i \<bullet> x\<bar> < B\<close> \<open>\<bar>i \<bullet> y\<bar> < B\<close>)
              show False
                using  I' [OF \<open>n \<in> C\<close> refl] n  by auto
            qed
          qed
          also have "... = e / 2"
            by simp
          finally show ?thesis .
        qed
      qed (use \<open>0 < e\<close> in force)
      also have "... < e"
        by (simp add: \<open>0 < e\<close>)
      finally show ?thesis .
    qed
  qed (auto simp: eq poly aff face  \<open>finite \<F>'\<close>)
qed

end
