(*  Title:      HOL/Finite_Set.thy
    Author:     Tobias Nipkow
    Author:     Lawrence C Paulson
    Author:     Markus Wenzel
    Author:     Jeremy Avigad
    Author:     Andrei Popescu
*)

section \<open>Finite sets\<close>

theory Finite_Set
  imports Product_Type Sum_Type Fields
begin

subsection \<open>Predicate for finite sets\<close>

context notes [[inductive_internals]]
begin

inductive finite :: "'a set \<Rightarrow> bool"
  where
    emptyI [simp, intro!]: "finite {}"
  | insertI [simp, intro!]: "finite A \<Longrightarrow> finite (insert a A)"

end

simproc_setup finite_Collect ("finite (Collect P)") = \<open>K Set_Comprehension_Pointfree.simproc\<close>

declare [[simproc del: finite_Collect]]

lemma finite_induct [case_names empty insert, induct set: finite]:
  \<comment> \<open>Discharging \<open>x \<notin> F\<close> entails extra work.\<close>
  assumes "finite F"
  assumes "P {}"
    and insert: "\<And>x F. finite F \<Longrightarrow> x \<notin> F \<Longrightarrow> P F \<Longrightarrow> P (insert x F)"
  shows "P F"
  using \<open>finite F\<close>
proof induct
  show "P {}" by fact
next
  fix x F
  assume F: "finite F" and P: "P F"
  show "P (insert x F)"
  proof cases
    assume "x \<in> F"
    then have "insert x F = F" by (rule insert_absorb)
    with P show ?thesis by (simp only:)
  next
    assume "x \<notin> F"
    from F this P show ?thesis by (rule insert)
  qed
qed

lemma infinite_finite_induct [case_names infinite empty insert]:
  assumes infinite: "\<And>A. \<not> finite A \<Longrightarrow> P A"
    and empty: "P {}"
    and insert: "\<And>x F. finite F \<Longrightarrow> x \<notin> F \<Longrightarrow> P F \<Longrightarrow> P (insert x F)"
  shows "P A"
proof (cases "finite A")
  case False
  with infinite show ?thesis .
next
  case True
  then show ?thesis by (induct A) (fact empty insert)+
qed


subsubsection \<open>Choice principles\<close>

lemma ex_new_if_finite: \<comment> "does not depend on def of finite at all"
  assumes "\<not> finite (UNIV :: 'a set)" and "finite A"
  shows "\<exists>a::'a. a \<notin> A"
proof -
  from assms have "A \<noteq> UNIV" by blast
  then show ?thesis by blast
qed

text \<open>A finite choice principle. Does not need the SOME choice operator.\<close>

lemma finite_set_choice: "finite A \<Longrightarrow> \<forall>x\<in>A. \<exists>y. P x y \<Longrightarrow> \<exists>f. \<forall>x\<in>A. P x (f x)"
proof (induct rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert a A)
  then obtain f b where f: "\<forall>x\<in>A. P x (f x)" and ab: "P a b"
    by auto
  show ?case (is "\<exists>f. ?P f")
  proof
    show "?P (\<lambda>x. if x = a then b else f x)"
      using f ab by auto
  qed
qed


subsubsection \<open>Finite sets are the images of initial segments of natural numbers\<close>

lemma finite_imp_nat_seg_image_inj_on:
  assumes "finite A"
  shows "\<exists>(n::nat) f. A = f ` {i. i < n} \<and> inj_on f {i. i < n}"
  using assms
proof induct
  case empty
  show ?case
  proof
    show "\<exists>f. {} = f ` {i::nat. i < 0} \<and> inj_on f {i. i < 0}"
      by simp
  qed
next
  case (insert a A)
  have notinA: "a \<notin> A" by fact
  from insert.hyps obtain n f where "A = f ` {i::nat. i < n}" "inj_on f {i. i < n}"
    by blast
  then have "insert a A = f(n:=a) ` {i. i < Suc n}" and "inj_on (f(n:=a)) {i. i < Suc n}"
    using notinA by (auto simp add: image_def Ball_def inj_on_def less_Suc_eq)
  then show ?case by blast
qed

lemma nat_seg_image_imp_finite: "A = f ` {i::nat. i < n} \<Longrightarrow> finite A"
proof (induct n arbitrary: A)
  case 0
  then show ?case by simp
next
  case (Suc n)
  let ?B = "f ` {i. i < n}"
  have finB: "finite ?B" by (rule Suc.hyps[OF refl])
  show ?case
  proof (cases "\<exists>k<n. f n = f k")
    case True
    then have "A = ?B"
      using Suc.prems by (auto simp:less_Suc_eq)
    then show ?thesis
      using finB by simp
  next
    case False
    then have "A = insert (f n) ?B"
      using Suc.prems by (auto simp:less_Suc_eq)
    then show ?thesis using finB by simp
  qed
qed

lemma finite_conv_nat_seg_image: "finite A \<longleftrightarrow> (\<exists>n f. A = f ` {i::nat. i < n})"
  by (blast intro: nat_seg_image_imp_finite dest: finite_imp_nat_seg_image_inj_on)

lemma finite_imp_inj_to_nat_seg:
  assumes "finite A"
  shows "\<exists>f n. f ` A = {i::nat. i < n} \<and> inj_on f A"
proof -
  from finite_imp_nat_seg_image_inj_on [OF \<open>finite A\<close>]
  obtain f and n :: nat where bij: "bij_betw f {i. i<n} A"
    by (auto simp: bij_betw_def)
  let ?f = "the_inv_into {i. i<n} f"
  have "inj_on ?f A \<and> ?f ` A = {i. i<n}"
    by (fold bij_betw_def) (rule bij_betw_the_inv_into[OF bij])
  then show ?thesis by blast
qed

lemma finite_Collect_less_nat [iff]: "finite {n::nat. n < k}"
  by (fastforce simp: finite_conv_nat_seg_image)

lemma finite_Collect_le_nat [iff]: "finite {n::nat. n \<le> k}"
  by (simp add: le_eq_less_or_eq Collect_disj_eq)


subsubsection \<open>Finiteness and common set operations\<close>

lemma rev_finite_subset: "finite B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> finite A"
proof (induct arbitrary: A rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert x F A)
  have A: "A \<subseteq> insert x F" and r: "A - {x} \<subseteq> F \<Longrightarrow> finite (A - {x})"
    by fact+
  show "finite A"
  proof cases
    assume x: "x \<in> A"
    with A have "A - {x} \<subseteq> F" by (simp add: subset_insert_iff)
    with r have "finite (A - {x})" .
    then have "finite (insert x (A - {x}))" ..
    also have "insert x (A - {x}) = A"
      using x by (rule insert_Diff)
    finally show ?thesis .
  next
    show ?thesis when "A \<subseteq> F"
      using that by fact
    assume "x \<notin> A"
    with A show "A \<subseteq> F"
      by (simp add: subset_insert_iff)
  qed
qed

lemma finite_subset: "A \<subseteq> B \<Longrightarrow> finite B \<Longrightarrow> finite A"
  by (rule rev_finite_subset)

lemma finite_UnI:
  assumes "finite F" and "finite G"
  shows "finite (F \<union> G)"
  using assms by induct simp_all

lemma finite_Un [iff]: "finite (F \<union> G) \<longleftrightarrow> finite F \<and> finite G"
  by (blast intro: finite_UnI finite_subset [of _ "F \<union> G"])

lemma finite_insert [simp]: "finite (insert a A) \<longleftrightarrow> finite A"
proof -
  have "finite {a} \<and> finite A \<longleftrightarrow> finite A" by simp
  then have "finite ({a} \<union> A) \<longleftrightarrow> finite A" by (simp only: finite_Un)
  then show ?thesis by simp
qed

lemma finite_Int [simp, intro]: "finite F \<or> finite G \<Longrightarrow> finite (F \<inter> G)"
  by (blast intro: finite_subset)

lemma finite_Collect_conjI [simp, intro]:
  "finite {x. P x} \<or> finite {x. Q x} \<Longrightarrow> finite {x. P x \<and> Q x}"
  by (simp add: Collect_conj_eq)

lemma finite_Collect_disjI [simp]:
  "finite {x. P x \<or> Q x} \<longleftrightarrow> finite {x. P x} \<and> finite {x. Q x}"
  by (simp add: Collect_disj_eq)

lemma finite_Diff [simp, intro]: "finite A \<Longrightarrow> finite (A - B)"
  by (rule finite_subset, rule Diff_subset)

lemma finite_Diff2 [simp]:
  assumes "finite B"
  shows "finite (A - B) \<longleftrightarrow> finite A"
proof -
  have "finite A \<longleftrightarrow> finite ((A - B) \<union> (A \<inter> B))"
    by (simp add: Un_Diff_Int)
  also have "\<dots> \<longleftrightarrow> finite (A - B)"
    using \<open>finite B\<close> by simp
  finally show ?thesis ..
qed

lemma finite_Diff_insert [iff]: "finite (A - insert a B) \<longleftrightarrow> finite (A - B)"
proof -
  have "finite (A - B) \<longleftrightarrow> finite (A - B - {a})" by simp
  moreover have "A - insert a B = A - B - {a}" by auto
  ultimately show ?thesis by simp
qed

lemma finite_compl [simp]:
  "finite (A :: 'a set) \<Longrightarrow> finite (- A) \<longleftrightarrow> finite (UNIV :: 'a set)"
  by (simp add: Compl_eq_Diff_UNIV)

lemma finite_Collect_not [simp]:
  "finite {x :: 'a. P x} \<Longrightarrow> finite {x. \<not> P x} \<longleftrightarrow> finite (UNIV :: 'a set)"
  by (simp add: Collect_neg_eq)

lemma finite_Union [simp, intro]:
  "finite A \<Longrightarrow> (\<And>M. M \<in> A \<Longrightarrow> finite M) \<Longrightarrow> finite (\<Union>A)"
  by (induct rule: finite_induct) simp_all

lemma finite_UN_I [intro]:
  "finite A \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> finite (B a)) \<Longrightarrow> finite (\<Union>a\<in>A. B a)"
  by (induct rule: finite_induct) simp_all

lemma finite_UN [simp]: "finite A \<Longrightarrow> finite (UNION A B) \<longleftrightarrow> (\<forall>x\<in>A. finite (B x))"
  by (blast intro: finite_subset)

lemma finite_Inter [intro]: "\<exists>A\<in>M. finite A \<Longrightarrow> finite (\<Inter>M)"
  by (blast intro: Inter_lower finite_subset)

lemma finite_INT [intro]: "\<exists>x\<in>I. finite (A x) \<Longrightarrow> finite (\<Inter>x\<in>I. A x)"
  by (blast intro: INT_lower finite_subset)

lemma finite_imageI [simp, intro]: "finite F \<Longrightarrow> finite (h ` F)"
  by (induct rule: finite_induct) simp_all

lemma finite_image_set [simp]: "finite {x. P x} \<Longrightarrow> finite {f x |x. P x}"
  by (simp add: image_Collect [symmetric])

lemma finite_image_set2:
  "finite {x. P x} \<Longrightarrow> finite {y. Q y} \<Longrightarrow> finite {f x y |x y. P x \<and> Q y}"
  by (rule finite_subset [where B = "\<Union>x \<in> {x. P x}. \<Union>y \<in> {y. Q y}. {f x y}"]) auto

lemma finite_imageD:
  assumes "finite (f ` A)" and "inj_on f A"
  shows "finite A"
  using assms
proof (induct "f ` A" arbitrary: A)
  case empty
  then show ?case by simp
next
  case (insert x B)
  then have B_A: "insert x B = f ` A"
    by simp
  then obtain y where "x = f y" and "y \<in> A"
    by blast
  from B_A \<open>x \<notin> B\<close> have "B = f ` A - {x}"
    by blast
  with B_A \<open>x \<notin> B\<close> \<open>x = f y\<close> \<open>inj_on f A\<close> \<open>y \<in> A\<close> have "B = f ` (A - {y})"
    by (simp add: inj_on_image_set_diff Set.Diff_subset)
  moreover from \<open>inj_on f A\<close> have "inj_on f (A - {y})"
    by (rule inj_on_diff)
  ultimately have "finite (A - {y})"
    by (rule insert.hyps)
  then show "finite A"
    by simp
qed

lemma finite_image_iff: "inj_on f A \<Longrightarrow> finite (f ` A) \<longleftrightarrow> finite A"
  using finite_imageD by blast

lemma finite_surj: "finite A \<Longrightarrow> B \<subseteq> f ` A \<Longrightarrow> finite B"
  by (erule finite_subset) (rule finite_imageI)

lemma finite_range_imageI: "finite (range g) \<Longrightarrow> finite (range (\<lambda>x. f (g x)))"
  by (drule finite_imageI) (simp add: range_composition)

lemma finite_subset_image:
  assumes "finite B"
  shows "B \<subseteq> f ` A \<Longrightarrow> \<exists>C\<subseteq>A. finite C \<and> B = f ` C"
  using assms
proof induct
  case empty
  then show ?case by simp
next
  case insert
  then show ?case
    by (clarsimp simp del: image_insert simp add: image_insert [symmetric]) blast  (* slow *)
qed

lemma finite_vimage_IntI: "finite F \<Longrightarrow> inj_on h A \<Longrightarrow> finite (h -` F \<inter> A)"
  apply (induct rule: finite_induct)
   apply simp_all
  apply (subst vimage_insert)
  apply (simp add: finite_subset [OF inj_on_vimage_singleton] Int_Un_distrib2)
  done

lemma finite_finite_vimage_IntI:
  assumes "finite F"
    and "\<And>y. y \<in> F \<Longrightarrow> finite ((h -` {y}) \<inter> A)"
  shows "finite (h -` F \<inter> A)"
proof -
  have *: "h -` F \<inter> A = (\<Union> y\<in>F. (h -` {y}) \<inter> A)"
    by blast
  show ?thesis
    by (simp only: * assms finite_UN_I)
qed

lemma finite_vimageI: "finite F \<Longrightarrow> inj h \<Longrightarrow> finite (h -` F)"
  using finite_vimage_IntI[of F h UNIV] by auto

lemma finite_vimageD': "finite (f -` A) \<Longrightarrow> A \<subseteq> range f \<Longrightarrow> finite A"
  by (auto simp add: subset_image_iff intro: finite_subset[rotated])

lemma finite_vimageD: "finite (h -` F) \<Longrightarrow> surj h \<Longrightarrow> finite F"
  by (auto dest: finite_vimageD')

lemma finite_vimage_iff: "bij h \<Longrightarrow> finite (h -` F) \<longleftrightarrow> finite F"
  unfolding bij_def by (auto elim: finite_vimageD finite_vimageI)

lemma finite_Collect_bex [simp]:
  assumes "finite A"
  shows "finite {x. \<exists>y\<in>A. Q x y} \<longleftrightarrow> (\<forall>y\<in>A. finite {x. Q x y})"
proof -
  have "{x. \<exists>y\<in>A. Q x y} = (\<Union>y\<in>A. {x. Q x y})" by auto
  with assms show ?thesis by simp
qed

lemma finite_Collect_bounded_ex [simp]:
  assumes "finite {y. P y}"
  shows "finite {x. \<exists>y. P y \<and> Q x y} \<longleftrightarrow> (\<forall>y. P y \<longrightarrow> finite {x. Q x y})"
proof -
  have "{x. \<exists>y. P y \<and> Q x y} = (\<Union>y\<in>{y. P y}. {x. Q x y})"
    by auto
  with assms show ?thesis
    by simp
qed

lemma finite_Plus: "finite A \<Longrightarrow> finite B \<Longrightarrow> finite (A <+> B)"
  by (simp add: Plus_def)

lemma finite_PlusD:
  fixes A :: "'a set" and B :: "'b set"
  assumes fin: "finite (A <+> B)"
  shows "finite A" "finite B"
proof -
  have "Inl ` A \<subseteq> A <+> B"
    by auto
  then have "finite (Inl ` A :: ('a + 'b) set)"
    using fin by (rule finite_subset)
  then show "finite A"
    by (rule finite_imageD) (auto intro: inj_onI)
next
  have "Inr ` B \<subseteq> A <+> B"
    by auto
  then have "finite (Inr ` B :: ('a + 'b) set)"
    using fin by (rule finite_subset)
  then show "finite B"
    by (rule finite_imageD) (auto intro: inj_onI)
qed

lemma finite_Plus_iff [simp]: "finite (A <+> B) \<longleftrightarrow> finite A \<and> finite B"
  by (auto intro: finite_PlusD finite_Plus)

lemma finite_Plus_UNIV_iff [simp]:
  "finite (UNIV :: ('a + 'b) set) \<longleftrightarrow> finite (UNIV :: 'a set) \<and> finite (UNIV :: 'b set)"
  by (subst UNIV_Plus_UNIV [symmetric]) (rule finite_Plus_iff)

lemma finite_SigmaI [simp, intro]:
  "finite A \<Longrightarrow> (\<And>a. a\<in>A \<Longrightarrow> finite (B a)) \<Longrightarrow> finite (SIGMA a:A. B a)"
  unfolding Sigma_def by blast

lemma finite_SigmaI2:
  assumes "finite {x\<in>A. B x \<noteq> {}}"
  and "\<And>a. a \<in> A \<Longrightarrow> finite (B a)"
  shows "finite (Sigma A B)"
proof -
  from assms have "finite (Sigma {x\<in>A. B x \<noteq> {}} B)"
    by auto
  also have "Sigma {x:A. B x \<noteq> {}} B = Sigma A B"
    by auto
  finally show ?thesis .
qed

lemma finite_cartesian_product: "finite A \<Longrightarrow> finite B \<Longrightarrow> finite (A \<times> B)"
  by (rule finite_SigmaI)

lemma finite_Prod_UNIV:
  "finite (UNIV :: 'a set) \<Longrightarrow> finite (UNIV :: 'b set) \<Longrightarrow> finite (UNIV :: ('a \<times> 'b) set)"
  by (simp only: UNIV_Times_UNIV [symmetric] finite_cartesian_product)

lemma finite_cartesian_productD1:
  assumes "finite (A \<times> B)" and "B \<noteq> {}"
  shows "finite A"
proof -
  from assms obtain n f where "A \<times> B = f ` {i::nat. i < n}"
    by (auto simp add: finite_conv_nat_seg_image)
  then have "fst ` (A \<times> B) = fst ` f ` {i::nat. i < n}"
    by simp
  with \<open>B \<noteq> {}\<close> have "A = (fst \<circ> f) ` {i::nat. i < n}"
    by (simp add: image_comp)
  then have "\<exists>n f. A = f ` {i::nat. i < n}"
    by blast
  then show ?thesis
    by (auto simp add: finite_conv_nat_seg_image)
qed

lemma finite_cartesian_productD2:
  assumes "finite (A \<times> B)" and "A \<noteq> {}"
  shows "finite B"
proof -
  from assms obtain n f where "A \<times> B = f ` {i::nat. i < n}"
    by (auto simp add: finite_conv_nat_seg_image)
  then have "snd ` (A \<times> B) = snd ` f ` {i::nat. i < n}"
    by simp
  with \<open>A \<noteq> {}\<close> have "B = (snd \<circ> f) ` {i::nat. i < n}"
    by (simp add: image_comp)
  then have "\<exists>n f. B = f ` {i::nat. i < n}"
    by blast
  then show ?thesis
    by (auto simp add: finite_conv_nat_seg_image)
qed

lemma finite_cartesian_product_iff:
  "finite (A \<times> B) \<longleftrightarrow> (A = {} \<or> B = {} \<or> (finite A \<and> finite B))"
  by (auto dest: finite_cartesian_productD1 finite_cartesian_productD2 finite_cartesian_product)

lemma finite_prod:
  "finite (UNIV :: ('a \<times> 'b) set) \<longleftrightarrow> finite (UNIV :: 'a set) \<and> finite (UNIV :: 'b set)"
  using finite_cartesian_product_iff[of UNIV UNIV] by simp

lemma finite_Pow_iff [iff]: "finite (Pow A) \<longleftrightarrow> finite A"
proof
  assume "finite (Pow A)"
  then have "finite ((\<lambda>x. {x}) ` A)"
    by (blast intro: finite_subset)  (* somewhat slow *)
  then show "finite A"
    by (rule finite_imageD [unfolded inj_on_def]) simp
next
  assume "finite A"
  then show "finite (Pow A)"
    by induct (simp_all add: Pow_insert)
qed

corollary finite_Collect_subsets [simp, intro]: "finite A \<Longrightarrow> finite {B. B \<subseteq> A}"
  by (simp add: Pow_def [symmetric])

lemma finite_set: "finite (UNIV :: 'a set set) \<longleftrightarrow> finite (UNIV :: 'a set)"
  by (simp only: finite_Pow_iff Pow_UNIV[symmetric])

lemma finite_UnionD: "finite (\<Union>A) \<Longrightarrow> finite A"
  by (blast intro: finite_subset [OF subset_Pow_Union])

lemma finite_set_of_finite_funs:
  assumes "finite A" "finite B"
  shows "finite {f. \<forall>x. (x \<in> A \<longrightarrow> f x \<in> B) \<and> (x \<notin> A \<longrightarrow> f x = d)}" (is "finite ?S")
proof -
  let ?F = "\<lambda>f. {(a,b). a \<in> A \<and> b = f a}"
  have "?F ` ?S \<subseteq> Pow(A \<times> B)"
    by auto
  from finite_subset[OF this] assms have 1: "finite (?F ` ?S)"
    by simp
  have 2: "inj_on ?F ?S"
    by (fastforce simp add: inj_on_def set_eq_iff fun_eq_iff)  (* somewhat slow *)
  show ?thesis
    by (rule finite_imageD [OF 1 2])
qed

lemma not_finite_existsD:
  assumes "\<not> finite {a. P a}"
  shows "\<exists>a. P a"
proof (rule classical)
  assume "\<not> ?thesis"
  with assms show ?thesis by auto
qed


subsubsection \<open>Further induction rules on finite sets\<close>

lemma finite_ne_induct [case_names singleton insert, consumes 2]:
  assumes "finite F" and "F \<noteq> {}"
  assumes "\<And>x. P {x}"
    and "\<And>x F. finite F \<Longrightarrow> F \<noteq> {} \<Longrightarrow> x \<notin> F \<Longrightarrow> P F  \<Longrightarrow> P (insert x F)"
  shows "P F"
  using assms
proof induct
  case empty
  then show ?case by simp
next
  case (insert x F)
  then show ?case by cases auto
qed

lemma finite_subset_induct [consumes 2, case_names empty insert]:
  assumes "finite F" and "F \<subseteq> A"
    and empty: "P {}"
    and insert: "\<And>a F. finite F \<Longrightarrow> a \<in> A \<Longrightarrow> a \<notin> F \<Longrightarrow> P F \<Longrightarrow> P (insert a F)"
  shows "P F"
  using \<open>finite F\<close> \<open>F \<subseteq> A\<close>
proof induct
  show "P {}" by fact
next
  fix x F
  assume "finite F" and "x \<notin> F" and P: "F \<subseteq> A \<Longrightarrow> P F" and i: "insert x F \<subseteq> A"
  show "P (insert x F)"
  proof (rule insert)
    from i show "x \<in> A" by blast
    from i have "F \<subseteq> A" by blast
    with P show "P F" .
    show "finite F" by fact
    show "x \<notin> F" by fact
  qed
qed

lemma finite_empty_induct:
  assumes "finite A"
    and "P A"
    and remove: "\<And>a A. finite A \<Longrightarrow> a \<in> A \<Longrightarrow> P A \<Longrightarrow> P (A - {a})"
  shows "P {}"
proof -
  have "P (A - B)" if "B \<subseteq> A" for B :: "'a set"
  proof -
    from \<open>finite A\<close> that have "finite B"
      by (rule rev_finite_subset)
    from this \<open>B \<subseteq> A\<close> show "P (A - B)"
    proof induct
      case empty
      from \<open>P A\<close> show ?case by simp
    next
      case (insert b B)
      have "P (A - B - {b})"
      proof (rule remove)
        from \<open>finite A\<close> show "finite (A - B)"
          by induct auto
        from insert show "b \<in> A - B"
          by simp
        from insert show "P (A - B)"
          by simp
      qed
      also have "A - B - {b} = A - insert b B"
        by (rule Diff_insert [symmetric])
      finally show ?case .
    qed
  qed
  then have "P (A - A)" by blast
  then show ?thesis by simp
qed

lemma finite_update_induct [consumes 1, case_names const update]:
  assumes finite: "finite {a. f a \<noteq> c}"
    and const: "P (\<lambda>a. c)"
    and update: "\<And>a b f. finite {a. f a \<noteq> c} \<Longrightarrow> f a = c \<Longrightarrow> b \<noteq> c \<Longrightarrow> P f \<Longrightarrow> P (f(a := b))"
  shows "P f"
  using finite
proof (induct "{a. f a \<noteq> c}" arbitrary: f)
  case empty
  with const show ?case by simp
next
  case (insert a A)
  then have "A = {a'. (f(a := c)) a' \<noteq> c}" and "f a \<noteq> c"
    by auto
  with \<open>finite A\<close> have "finite {a'. (f(a := c)) a' \<noteq> c}"
    by simp
  have "(f(a := c)) a = c"
    by simp
  from insert \<open>A = {a'. (f(a := c)) a' \<noteq> c}\<close> have "P (f(a := c))"
    by simp
  with \<open>finite {a'. (f(a := c)) a' \<noteq> c}\<close> \<open>(f(a := c)) a = c\<close> \<open>f a \<noteq> c\<close>
  have "P ((f(a := c))(a := f a))"
    by (rule update)
  then show ?case by simp
qed

lemma finite_subset_induct' [consumes 2, case_names empty insert]:
  assumes "finite F" and "F \<subseteq> A"
    and empty: "P {}"
    and insert: "\<And>a F. \<lbrakk>finite F; a \<in> A; F \<subseteq> A; a \<notin> F; P F \<rbrakk> \<Longrightarrow> P (insert a F)"
  shows "P F"
  using assms(1,2)
proof induct
  show "P {}" by fact
next
  fix x F
  assume "finite F" and "x \<notin> F" and
    P: "F \<subseteq> A \<Longrightarrow> P F" and i: "insert x F \<subseteq> A"
  show "P (insert x F)"
  proof (rule insert)
    from i show "x \<in> A" by blast
    from i have "F \<subseteq> A" by blast
    with P show "P F" .
    show "finite F" by fact
    show "x \<notin> F" by fact
    show "F \<subseteq> A" by fact
  qed
qed


subsection \<open>Class \<open>finite\<close>\<close>

class finite =
  assumes finite_UNIV: "finite (UNIV :: 'a set)"
begin

lemma finite [simp]: "finite (A :: 'a set)"
  by (rule subset_UNIV finite_UNIV finite_subset)+

lemma finite_code [code]: "finite (A :: 'a set) \<longleftrightarrow> True"
  by simp

end

instance prod :: (finite, finite) finite
  by standard (simp only: UNIV_Times_UNIV [symmetric] finite_cartesian_product finite)

lemma inj_graph: "inj (\<lambda>f. {(x, y). y = f x})"
  by (rule inj_onI) (auto simp add: set_eq_iff fun_eq_iff)

instance "fun" :: (finite, finite) finite
proof
  show "finite (UNIV :: ('a \<Rightarrow> 'b) set)"
  proof (rule finite_imageD)
    let ?graph = "\<lambda>f::'a \<Rightarrow> 'b. {(x, y). y = f x}"
    have "range ?graph \<subseteq> Pow UNIV"
      by simp
    moreover have "finite (Pow (UNIV :: ('a * 'b) set))"
      by (simp only: finite_Pow_iff finite)
    ultimately show "finite (range ?graph)"
      by (rule finite_subset)
    show "inj ?graph"
      by (rule inj_graph)
  qed
qed

instance bool :: finite
  by standard (simp add: UNIV_bool)

instance set :: (finite) finite
  by standard (simp only: Pow_UNIV [symmetric] finite_Pow_iff finite)

instance unit :: finite
  by standard (simp add: UNIV_unit)

instance sum :: (finite, finite) finite
  by standard (simp only: UNIV_Plus_UNIV [symmetric] finite_Plus finite)


subsection \<open>A basic fold functional for finite sets\<close>

text \<open>The intended behaviour is
  \<open>fold f z {x\<^sub>1, \<dots>, x\<^sub>n} = f x\<^sub>1 (\<dots> (f x\<^sub>n z)\<dots>)\<close>
  if \<open>f\<close> is ``left-commutative'':
\<close>

locale comp_fun_commute =
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'b"
  assumes comp_fun_commute: "f y \<circ> f x = f x \<circ> f y"
begin

lemma fun_left_comm: "f y (f x z) = f x (f y z)"
  using comp_fun_commute by (simp add: fun_eq_iff)

lemma commute_left_comp: "f y \<circ> (f x \<circ> g) = f x \<circ> (f y \<circ> g)"
  by (simp add: o_assoc comp_fun_commute)

end

inductive fold_graph :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> bool"
  for f :: "'a \<Rightarrow> 'b \<Rightarrow> 'b" and z :: 'b
  where
    emptyI [intro]: "fold_graph f z {} z"
  | insertI [intro]: "x \<notin> A \<Longrightarrow> fold_graph f z A y \<Longrightarrow> fold_graph f z (insert x A) (f x y)"

inductive_cases empty_fold_graphE [elim!]: "fold_graph f z {} x"

definition fold :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a set \<Rightarrow> 'b"
  where "fold f z A = (if finite A then (THE y. fold_graph f z A y) else z)"

text \<open>
  A tempting alternative for the definiens is
  @{term "if finite A then THE y. fold_graph f z A y else e"}.
  It allows the removal of finiteness assumptions from the theorems
  \<open>fold_comm\<close>, \<open>fold_reindex\<close> and \<open>fold_distrib\<close>.
  The proofs become ugly. It is not worth the effort. (???)
\<close>

lemma finite_imp_fold_graph: "finite A \<Longrightarrow> \<exists>x. fold_graph f z A x"
  by (induct rule: finite_induct) auto


subsubsection \<open>From @{const fold_graph} to @{term fold}\<close>

context comp_fun_commute
begin

lemma fold_graph_finite:
  assumes "fold_graph f z A y"
  shows "finite A"
  using assms by induct simp_all

lemma fold_graph_insertE_aux:
  "fold_graph f z A y \<Longrightarrow> a \<in> A \<Longrightarrow> \<exists>y'. y = f a y' \<and> fold_graph f z (A - {a}) y'"
proof (induct set: fold_graph)
  case emptyI
  then show ?case by simp
next
  case (insertI x A y)
  show ?case
  proof (cases "x = a")
    case True
    with insertI show ?thesis by auto
  next
    case False
    then obtain y' where y: "y = f a y'" and y': "fold_graph f z (A - {a}) y'"
      using insertI by auto
    have "f x y = f a (f x y')"
      unfolding y by (rule fun_left_comm)
    moreover have "fold_graph f z (insert x A - {a}) (f x y')"
      using y' and \<open>x \<noteq> a\<close> and \<open>x \<notin> A\<close>
      by (simp add: insert_Diff_if fold_graph.insertI)
    ultimately show ?thesis
      by fast
  qed
qed

lemma fold_graph_insertE:
  assumes "fold_graph f z (insert x A) v" and "x \<notin> A"
  obtains y where "v = f x y" and "fold_graph f z A y"
  using assms by (auto dest: fold_graph_insertE_aux [OF _ insertI1])

lemma fold_graph_determ: "fold_graph f z A x \<Longrightarrow> fold_graph f z A y \<Longrightarrow> y = x"
proof (induct arbitrary: y set: fold_graph)
  case emptyI
  then show ?case by fast
next
  case (insertI x A y v)
  from \<open>fold_graph f z (insert x A) v\<close> and \<open>x \<notin> A\<close>
  obtain y' where "v = f x y'" and "fold_graph f z A y'"
    by (rule fold_graph_insertE)
  from \<open>fold_graph f z A y'\<close> have "y' = y"
    by (rule insertI)
  with \<open>v = f x y'\<close> show "v = f x y"
    by simp
qed

lemma fold_equality: "fold_graph f z A y \<Longrightarrow> fold f z A = y"
  by (cases "finite A") (auto simp add: fold_def intro: fold_graph_determ dest: fold_graph_finite)

lemma fold_graph_fold:
  assumes "finite A"
  shows "fold_graph f z A (fold f z A)"
proof -
  from assms have "\<exists>x. fold_graph f z A x"
    by (rule finite_imp_fold_graph)
  moreover note fold_graph_determ
  ultimately have "\<exists>!x. fold_graph f z A x"
    by (rule ex_ex1I)
  then have "fold_graph f z A (The (fold_graph f z A))"
    by (rule theI')
  with assms show ?thesis
    by (simp add: fold_def)
qed

text \<open>The base case for \<open>fold\<close>:\<close>

lemma (in -) fold_infinite [simp]: "\<not> finite A \<Longrightarrow> fold f z A = z"
  by (auto simp: fold_def)

lemma (in -) fold_empty [simp]: "fold f z {} = z"
  by (auto simp: fold_def)

text \<open>The various recursion equations for @{const fold}:\<close>

lemma fold_insert [simp]:
  assumes "finite A" and "x \<notin> A"
  shows "fold f z (insert x A) = f x (fold f z A)"
proof (rule fold_equality)
  fix z
  from \<open>finite A\<close> have "fold_graph f z A (fold f z A)"
    by (rule fold_graph_fold)
  with \<open>x \<notin> A\<close> have "fold_graph f z (insert x A) (f x (fold f z A))"
    by (rule fold_graph.insertI)
  then show "fold_graph f z (insert x A) (f x (fold f z A))"
    by simp
qed

declare (in -) empty_fold_graphE [rule del] fold_graph.intros [rule del]
  \<comment> \<open>No more proofs involve these.\<close>

lemma fold_fun_left_comm: "finite A \<Longrightarrow> f x (fold f z A) = fold f (f x z) A"
proof (induct rule: finite_induct)
  case empty
  then show ?case by simp
next
  case insert
  then show ?case
    by (simp add: fun_left_comm [of x])
qed

lemma fold_insert2: "finite A \<Longrightarrow> x \<notin> A \<Longrightarrow> fold f z (insert x A)  = fold f (f x z) A"
  by (simp add: fold_fun_left_comm)

lemma fold_rec:
  assumes "finite A" and "x \<in> A"
  shows "fold f z A = f x (fold f z (A - {x}))"
proof -
  have A: "A = insert x (A - {x})"
    using \<open>x \<in> A\<close> by blast
  then have "fold f z A = fold f z (insert x (A - {x}))"
    by simp
  also have "\<dots> = f x (fold f z (A - {x}))"
    by (rule fold_insert) (simp add: \<open>finite A\<close>)+
  finally show ?thesis .
qed

lemma fold_insert_remove:
  assumes "finite A"
  shows "fold f z (insert x A) = f x (fold f z (A - {x}))"
proof -
  from \<open>finite A\<close> have "finite (insert x A)"
    by auto
  moreover have "x \<in> insert x A"
    by auto
  ultimately have "fold f z (insert x A) = f x (fold f z (insert x A - {x}))"
    by (rule fold_rec)
  then show ?thesis
    by simp
qed

lemma fold_set_union_disj:
  assumes "finite A" "finite B" "A \<inter> B = {}"
  shows "Finite_Set.fold f z (A \<union> B) = Finite_Set.fold f (Finite_Set.fold f z A) B"
  using assms(2,1,3) by induct simp_all

end

text \<open>Other properties of @{const fold}:\<close>

lemma fold_image:
  assumes "inj_on g A"
  shows "fold f z (g ` A) = fold (f \<circ> g) z A"
proof (cases "finite A")
  case False
  with assms show ?thesis
    by (auto dest: finite_imageD simp add: fold_def)
next
  case True
  have "fold_graph f z (g ` A) = fold_graph (f \<circ> g) z A"
  proof
    fix w
    show "fold_graph f z (g ` A) w \<longleftrightarrow> fold_graph (f \<circ> g) z A w" (is "?P \<longleftrightarrow> ?Q")
    proof
      assume ?P
      then show ?Q
        using assms
      proof (induct "g ` A" w arbitrary: A)
        case emptyI
        then show ?case by (auto intro: fold_graph.emptyI)
      next
        case (insertI x A r B)
        from \<open>inj_on g B\<close> \<open>x \<notin> A\<close> \<open>insert x A = image g B\<close> obtain x' A'
          where "x' \<notin> A'" and [simp]: "B = insert x' A'" "x = g x'" "A = g ` A'"
          by (rule inj_img_insertE)
        from insertI.prems have "fold_graph (f \<circ> g) z A' r"
          by (auto intro: insertI.hyps)
        with \<open>x' \<notin> A'\<close> have "fold_graph (f \<circ> g) z (insert x' A') ((f \<circ> g) x' r)"
          by (rule fold_graph.insertI)
        then show ?case
          by simp
      qed
    next
      assume ?Q
      then show ?P
        using assms
      proof induct
        case emptyI
        then show ?case
          by (auto intro: fold_graph.emptyI)
      next
        case (insertI x A r)
        from \<open>x \<notin> A\<close> insertI.prems have "g x \<notin> g ` A"
          by auto
        moreover from insertI have "fold_graph f z (g ` A) r"
          by simp
        ultimately have "fold_graph f z (insert (g x) (g ` A)) (f (g x) r)"
          by (rule fold_graph.insertI)
        then show ?case
          by simp
      qed
    qed
  qed
  with True assms show ?thesis
    by (auto simp add: fold_def)
qed

lemma fold_cong:
  assumes "comp_fun_commute f" "comp_fun_commute g"
    and "finite A"
    and cong: "\<And>x. x \<in> A \<Longrightarrow> f x = g x"
    and "s = t" and "A = B"
  shows "fold f s A = fold g t B"
proof -
  have "fold f s A = fold g s A"
    using \<open>finite A\<close> cong
  proof (induct A)
    case empty
    then show ?case by simp
  next
    case insert
    interpret f: comp_fun_commute f by (fact \<open>comp_fun_commute f\<close>)
    interpret g: comp_fun_commute g by (fact \<open>comp_fun_commute g\<close>)
    from insert show ?case by simp
  qed
  with assms show ?thesis by simp
qed


text \<open>A simplified version for idempotent functions:\<close>

locale comp_fun_idem = comp_fun_commute +
  assumes comp_fun_idem: "f x \<circ> f x = f x"
begin

lemma fun_left_idem: "f x (f x z) = f x z"
  using comp_fun_idem by (simp add: fun_eq_iff)

lemma fold_insert_idem:
  assumes fin: "finite A"
  shows "fold f z (insert x A)  = f x (fold f z A)"
proof cases
  assume "x \<in> A"
  then obtain B where "A = insert x B" and "x \<notin> B"
    by (rule set_insert)
  then show ?thesis
    using assms by (simp add: comp_fun_idem fun_left_idem)
next
  assume "x \<notin> A"
  then show ?thesis
    using assms by simp
qed

declare fold_insert [simp del] fold_insert_idem [simp]

lemma fold_insert_idem2: "finite A \<Longrightarrow> fold f z (insert x A) = fold f (f x z) A"
  by (simp add: fold_fun_left_comm)

end


subsubsection \<open>Liftings to \<open>comp_fun_commute\<close> etc.\<close>

lemma (in comp_fun_commute) comp_comp_fun_commute: "comp_fun_commute (f \<circ> g)"
  by standard (simp_all add: comp_fun_commute)

lemma (in comp_fun_idem) comp_comp_fun_idem: "comp_fun_idem (f \<circ> g)"
  by (rule comp_fun_idem.intro, rule comp_comp_fun_commute, unfold_locales)
    (simp_all add: comp_fun_idem)

lemma (in comp_fun_commute) comp_fun_commute_funpow: "comp_fun_commute (\<lambda>x. f x ^^ g x)"
proof
  show "f y ^^ g y \<circ> f x ^^ g x = f x ^^ g x \<circ> f y ^^ g y" for x y
  proof (cases "x = y")
    case True
    then show ?thesis by simp
  next
    case False
    show ?thesis
    proof (induct "g x" arbitrary: g)
      case 0
      then show ?case by simp
    next
      case (Suc n g)
      have hyp1: "f y ^^ g y \<circ> f x = f x \<circ> f y ^^ g y"
      proof (induct "g y" arbitrary: g)
        case 0
        then show ?case by simp
      next
        case (Suc n g)
        define h where "h z = g z - 1" for z
        with Suc have "n = h y"
          by simp
        with Suc have hyp: "f y ^^ h y \<circ> f x = f x \<circ> f y ^^ h y"
          by auto
        from Suc h_def have "g y = Suc (h y)"
          by simp
        then show ?case
          by (simp add: comp_assoc hyp) (simp add: o_assoc comp_fun_commute)
      qed
      define h where "h z = (if z = x then g x - 1 else g z)" for z
      with Suc have "n = h x"
        by simp
      with Suc have "f y ^^ h y \<circ> f x ^^ h x = f x ^^ h x \<circ> f y ^^ h y"
        by auto
      with False h_def have hyp2: "f y ^^ g y \<circ> f x ^^ h x = f x ^^ h x \<circ> f y ^^ g y"
        by simp
      from Suc h_def have "g x = Suc (h x)"
        by simp
      then show ?case
        by (simp del: funpow.simps add: funpow_Suc_right o_assoc hyp2) (simp add: comp_assoc hyp1)
    qed
  qed
qed


subsubsection \<open>Expressing set operations via @{const fold}\<close>

lemma comp_fun_commute_const: "comp_fun_commute (\<lambda>_. f)"
  by standard rule

lemma comp_fun_idem_insert: "comp_fun_idem insert"
  by standard auto

lemma comp_fun_idem_remove: "comp_fun_idem Set.remove"
  by standard auto

lemma (in semilattice_inf) comp_fun_idem_inf: "comp_fun_idem inf"
  by standard (auto simp add: inf_left_commute)

lemma (in semilattice_sup) comp_fun_idem_sup: "comp_fun_idem sup"
  by standard (auto simp add: sup_left_commute)

lemma union_fold_insert:
  assumes "finite A"
  shows "A \<union> B = fold insert B A"
proof -
  interpret comp_fun_idem insert
    by (fact comp_fun_idem_insert)
  from \<open>finite A\<close> show ?thesis
    by (induct A arbitrary: B) simp_all
qed

lemma minus_fold_remove:
  assumes "finite A"
  shows "B - A = fold Set.remove B A"
proof -
  interpret comp_fun_idem Set.remove
    by (fact comp_fun_idem_remove)
  from \<open>finite A\<close> have "fold Set.remove B A = B - A"
    by (induct A arbitrary: B) auto  (* slow *)
  then show ?thesis ..
qed

lemma comp_fun_commute_filter_fold:
  "comp_fun_commute (\<lambda>x A'. if P x then Set.insert x A' else A')"
proof -
  interpret comp_fun_idem Set.insert by (fact comp_fun_idem_insert)
  show ?thesis by standard (auto simp: fun_eq_iff)
qed

lemma Set_filter_fold:
  assumes "finite A"
  shows "Set.filter P A = fold (\<lambda>x A'. if P x then Set.insert x A' else A') {} A"
  using assms
  by induct
    (auto simp add: Set.filter_def comp_fun_commute.fold_insert[OF comp_fun_commute_filter_fold])

lemma inter_Set_filter:
  assumes "finite B"
  shows "A \<inter> B = Set.filter (\<lambda>x. x \<in> A) B"
  using assms
  by induct (auto simp: Set.filter_def)

lemma image_fold_insert:
  assumes "finite A"
  shows "image f A = fold (\<lambda>k A. Set.insert (f k) A) {} A"
proof -
  interpret comp_fun_commute "\<lambda>k A. Set.insert (f k) A"
    by standard auto
  show ?thesis
    using assms by (induct A) auto
qed

lemma Ball_fold:
  assumes "finite A"
  shows "Ball A P = fold (\<lambda>k s. s \<and> P k) True A"
proof -
  interpret comp_fun_commute "\<lambda>k s. s \<and> P k"
    by standard auto
  show ?thesis
    using assms by (induct A) auto
qed

lemma Bex_fold:
  assumes "finite A"
  shows "Bex A P = fold (\<lambda>k s. s \<or> P k) False A"
proof -
  interpret comp_fun_commute "\<lambda>k s. s \<or> P k"
    by standard auto
  show ?thesis
    using assms by (induct A) auto
qed

lemma comp_fun_commute_Pow_fold: "comp_fun_commute (\<lambda>x A. A \<union> Set.insert x ` A)"
  by (clarsimp simp: fun_eq_iff comp_fun_commute_def) blast  (* somewhat slow *)

lemma Pow_fold:
  assumes "finite A"
  shows "Pow A = fold (\<lambda>x A. A \<union> Set.insert x ` A) {{}} A"
proof -
  interpret comp_fun_commute "\<lambda>x A. A \<union> Set.insert x ` A"
    by (rule comp_fun_commute_Pow_fold)
  show ?thesis
    using assms by (induct A) (auto simp: Pow_insert)
qed

lemma fold_union_pair:
  assumes "finite B"
  shows "(\<Union>y\<in>B. {(x, y)}) \<union> A = fold (\<lambda>y. Set.insert (x, y)) A B"
proof -
  interpret comp_fun_commute "\<lambda>y. Set.insert (x, y)"
    by standard auto
  show ?thesis
    using assms by (induct arbitrary: A) simp_all
qed

lemma comp_fun_commute_product_fold:
  "finite B \<Longrightarrow> comp_fun_commute (\<lambda>x z. fold (\<lambda>y. Set.insert (x, y)) z B)"
  by standard (auto simp: fold_union_pair [symmetric])

lemma product_fold:
  assumes "finite A" "finite B"
  shows "A \<times> B = fold (\<lambda>x z. fold (\<lambda>y. Set.insert (x, y)) z B) {} A"
  using assms unfolding Sigma_def
  by (induct A)
    (simp_all add: comp_fun_commute.fold_insert[OF comp_fun_commute_product_fold] fold_union_pair)

context complete_lattice
begin

lemma inf_Inf_fold_inf:
  assumes "finite A"
  shows "inf (Inf A) B = fold inf B A"
proof -
  interpret comp_fun_idem inf
    by (fact comp_fun_idem_inf)
  from \<open>finite A\<close> fold_fun_left_comm show ?thesis
    by (induct A arbitrary: B) (simp_all add: inf_commute fun_eq_iff)
qed

lemma sup_Sup_fold_sup:
  assumes "finite A"
  shows "sup (Sup A) B = fold sup B A"
proof -
  interpret comp_fun_idem sup
    by (fact comp_fun_idem_sup)
  from \<open>finite A\<close> fold_fun_left_comm show ?thesis
    by (induct A arbitrary: B) (simp_all add: sup_commute fun_eq_iff)
qed

lemma Inf_fold_inf: "finite A \<Longrightarrow> Inf A = fold inf top A"
  using inf_Inf_fold_inf [of A top] by (simp add: inf_absorb2)

lemma Sup_fold_sup: "finite A \<Longrightarrow> Sup A = fold sup bot A"
  using sup_Sup_fold_sup [of A bot] by (simp add: sup_absorb2)

lemma inf_INF_fold_inf:
  assumes "finite A"
  shows "inf B (INFIMUM A f) = fold (inf \<circ> f) B A" (is "?inf = ?fold")
proof -
  interpret comp_fun_idem inf by (fact comp_fun_idem_inf)
  interpret comp_fun_idem "inf \<circ> f" by (fact comp_comp_fun_idem)
  from \<open>finite A\<close> have "?fold = ?inf"
    by (induct A arbitrary: B) (simp_all add: inf_left_commute)
  then show ?thesis ..
qed

lemma sup_SUP_fold_sup:
  assumes "finite A"
  shows "sup B (SUPREMUM A f) = fold (sup \<circ> f) B A" (is "?sup = ?fold")
proof -
  interpret comp_fun_idem sup by (fact comp_fun_idem_sup)
  interpret comp_fun_idem "sup \<circ> f" by (fact comp_comp_fun_idem)
  from \<open>finite A\<close> have "?fold = ?sup"
    by (induct A arbitrary: B) (simp_all add: sup_left_commute)
  then show ?thesis ..
qed

lemma INF_fold_inf: "finite A \<Longrightarrow> INFIMUM A f = fold (inf \<circ> f) top A"
  using inf_INF_fold_inf [of A top] by simp

lemma SUP_fold_sup: "finite A \<Longrightarrow> SUPREMUM A f = fold (sup \<circ> f) bot A"
  using sup_SUP_fold_sup [of A bot] by simp

end


subsection \<open>Locales as mini-packages for fold operations\<close>

subsubsection \<open>The natural case\<close>

locale folding =
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'b" and z :: "'b"
  assumes comp_fun_commute: "f y \<circ> f x = f x \<circ> f y"
begin

interpretation fold?: comp_fun_commute f
  by standard (use comp_fun_commute in \<open>simp add: fun_eq_iff\<close>)

definition F :: "'a set \<Rightarrow> 'b"
  where eq_fold: "F A = fold f z A"

lemma empty [simp]:"F {} = z"
  by (simp add: eq_fold)

lemma infinite [simp]: "\<not> finite A \<Longrightarrow> F A = z"
  by (simp add: eq_fold)

lemma insert [simp]:
  assumes "finite A" and "x \<notin> A"
  shows "F (insert x A) = f x (F A)"
proof -
  from fold_insert assms
  have "fold f z (insert x A) = f x (fold f z A)" by simp
  with \<open>finite A\<close> show ?thesis by (simp add: eq_fold fun_eq_iff)
qed

lemma remove:
  assumes "finite A" and "x \<in> A"
  shows "F A = f x (F (A - {x}))"
proof -
  from \<open>x \<in> A\<close> obtain B where A: "A = insert x B" and "x \<notin> B"
    by (auto dest: mk_disjoint_insert)
  moreover from \<open>finite A\<close> A have "finite B" by simp
  ultimately show ?thesis by simp
qed

lemma insert_remove: "finite A \<Longrightarrow> F (insert x A) = f x (F (A - {x}))"
  by (cases "x \<in> A") (simp_all add: remove insert_absorb)

end


subsubsection \<open>With idempotency\<close>

locale folding_idem = folding +
  assumes comp_fun_idem: "f x \<circ> f x = f x"
begin

declare insert [simp del]

interpretation fold?: comp_fun_idem f
  by standard (insert comp_fun_commute comp_fun_idem, simp add: fun_eq_iff)

lemma insert_idem [simp]:
  assumes "finite A"
  shows "F (insert x A) = f x (F A)"
proof -
  from fold_insert_idem assms
  have "fold f z (insert x A) = f x (fold f z A)" by simp
  with \<open>finite A\<close> show ?thesis by (simp add: eq_fold fun_eq_iff)
qed

end


subsection \<open>Finite cardinality\<close>

text \<open>
  The traditional definition
  @{prop "card A \<equiv> LEAST n. \<exists>f. A = {f i |i. i < n}"}
  is ugly to work with.
  But now that we have @{const fold} things are easy:
\<close>

global_interpretation card: folding "\<lambda>_. Suc" 0
  defines card = "folding.F (\<lambda>_. Suc) 0"
  by standard rule

lemma card_infinite: "\<not> finite A \<Longrightarrow> card A = 0"
  by (fact card.infinite)

lemma card_empty: "card {} = 0"
  by (fact card.empty)

lemma card_insert_disjoint: "finite A \<Longrightarrow> x \<notin> A \<Longrightarrow> card (insert x A) = Suc (card A)"
  by (fact card.insert)

lemma card_insert_if: "finite A \<Longrightarrow> card (insert x A) = (if x \<in> A then card A else Suc (card A))"
  by auto (simp add: card.insert_remove card.remove)

lemma card_ge_0_finite: "card A > 0 \<Longrightarrow> finite A"
  by (rule ccontr) simp

lemma card_0_eq [simp]: "finite A \<Longrightarrow> card A = 0 \<longleftrightarrow> A = {}"
  by (auto dest: mk_disjoint_insert)

lemma finite_UNIV_card_ge_0: "finite (UNIV :: 'a set) \<Longrightarrow> card (UNIV :: 'a set) > 0"
  by (rule ccontr) simp

lemma card_eq_0_iff: "card A = 0 \<longleftrightarrow> A = {} \<or> \<not> finite A"
  by auto

lemma card_range_greater_zero: "finite (range f) \<Longrightarrow> card (range f) > 0"
  by (rule ccontr) (simp add: card_eq_0_iff)

lemma card_gt_0_iff: "0 < card A \<longleftrightarrow> A \<noteq> {} \<and> finite A"
  by (simp add: neq0_conv [symmetric] card_eq_0_iff)

lemma card_Suc_Diff1: "finite A \<Longrightarrow> x \<in> A \<Longrightarrow> Suc (card (A - {x})) = card A"
  apply (rule insert_Diff [THEN subst, where t = A])
   apply assumption
  apply (simp del: insert_Diff_single)
  done

lemma card_insert_le_m1: "n > 0 \<Longrightarrow> card y \<le> n - 1 \<Longrightarrow> card (insert x y) \<le> n"
  apply (cases "finite y")
   apply (cases "x \<in> y")
    apply (auto simp: insert_absorb)
  done

lemma card_Diff_singleton: "finite A \<Longrightarrow> x \<in> A \<Longrightarrow> card (A - {x}) = card A - 1"
  by (simp add: card_Suc_Diff1 [symmetric])

lemma card_Diff_singleton_if:
  "finite A \<Longrightarrow> card (A - {x}) = (if x \<in> A then card A - 1 else card A)"
  by (simp add: card_Diff_singleton)

lemma card_Diff_insert[simp]:
  assumes "finite A" and "a \<in> A" and "a \<notin> B"
  shows "card (A - insert a B) = card (A - B) - 1"
proof -
  have "A - insert a B = (A - B) - {a}"
    using assms by blast
  then show ?thesis
    using assms by (simp add: card_Diff_singleton)
qed

lemma card_insert: "finite A \<Longrightarrow> card (insert x A) = Suc (card (A - {x}))"
  by (fact card.insert_remove)

lemma card_insert_le: "finite A \<Longrightarrow> card A \<le> card (insert x A)"
  by (simp add: card_insert_if)

lemma card_Collect_less_nat[simp]: "card {i::nat. i < n} = n"
  by (induct n) (simp_all add:less_Suc_eq Collect_disj_eq)

lemma card_Collect_le_nat[simp]: "card {i::nat. i \<le> n} = Suc n"
  using card_Collect_less_nat[of "Suc n"] by (simp add: less_Suc_eq_le)

lemma card_mono:
  assumes "finite B" and "A \<subseteq> B"
  shows "card A \<le> card B"
proof -
  from assms have "finite A"
    by (auto intro: finite_subset)
  then show ?thesis
    using assms
  proof (induct A arbitrary: B)
    case empty
    then show ?case by simp
  next
    case (insert x A)
    then have "x \<in> B"
      by simp
    from insert have "A \<subseteq> B - {x}" and "finite (B - {x})"
      by auto
    with insert.hyps have "card A \<le> card (B - {x})"
      by auto
    with \<open>finite A\<close> \<open>x \<notin> A\<close> \<open>finite B\<close> \<open>x \<in> B\<close> show ?case
      by simp (simp only: card.remove)
  qed
qed

lemma card_seteq: "finite B \<Longrightarrow> (\<And>A. A \<subseteq> B \<Longrightarrow> card B \<le> card A \<Longrightarrow> A = B)"
  apply (induct rule: finite_induct)
   apply simp
  apply clarify
  apply (subgoal_tac "finite A \<and> A - {x} \<subseteq> F")
   prefer 2 apply (blast intro: finite_subset, atomize)
  apply (drule_tac x = "A - {x}" in spec)
  apply (simp add: card_Diff_singleton_if split: if_split_asm)
  apply (case_tac "card A", auto)
  done

lemma psubset_card_mono: "finite B \<Longrightarrow> A < B \<Longrightarrow> card A < card B"
  apply (simp add: psubset_eq linorder_not_le [symmetric])
  apply (blast dest: card_seteq)
  done

lemma card_Un_Int:
  assumes "finite A" "finite B"
  shows "card A + card B = card (A \<union> B) + card (A \<inter> B)"
  using assms
proof (induct A)
  case empty
  then show ?case by simp
next
  case insert
  then show ?case
    by (auto simp add: insert_absorb Int_insert_left)
qed

lemma card_Un_disjoint: "finite A \<Longrightarrow> finite B \<Longrightarrow> A \<inter> B = {} \<Longrightarrow> card (A \<union> B) = card A + card B"
  using card_Un_Int [of A B] by simp

lemma card_Un_le: "card (A \<union> B) \<le> card A + card B"
  apply (cases "finite A")
   apply (cases "finite B")
    apply (use le_iff_add card_Un_Int in blast)
   apply simp
  apply simp
  done

lemma card_Diff_subset:
  assumes "finite B"
    and "B \<subseteq> A"
  shows "card (A - B) = card A - card B"
  using assms
proof (cases "finite A")
  case False
  with assms show ?thesis
    by simp
next
  case True
  with assms show ?thesis
    by (induct B arbitrary: A) simp_all
qed

lemma card_Diff_subset_Int:
  assumes "finite (A \<inter> B)"
  shows "card (A - B) = card A - card (A \<inter> B)"
proof -
  have "A - B = A - A \<inter> B" by auto
  with assms show ?thesis
    by (simp add: card_Diff_subset)
qed

lemma diff_card_le_card_Diff:
  assumes "finite B"
  shows "card A - card B \<le> card (A - B)"
proof -
  have "card A - card B \<le> card A - card (A \<inter> B)"
    using card_mono[OF assms Int_lower2, of A] by arith
  also have "\<dots> = card (A - B)"
    using assms by (simp add: card_Diff_subset_Int)
  finally show ?thesis .
qed

lemma card_Diff1_less: "finite A \<Longrightarrow> x \<in> A \<Longrightarrow> card (A - {x}) < card A"
  by (rule Suc_less_SucD) (simp add: card_Suc_Diff1 del: card_Diff_insert)

lemma card_Diff2_less: "finite A \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> card (A - {x} - {y}) < card A"
  apply (cases "x = y")
   apply (simp add: card_Diff1_less del:card_Diff_insert)
  apply (rule less_trans)
   prefer 2 apply (auto intro!: card_Diff1_less simp del: card_Diff_insert)
  done

lemma card_Diff1_le: "finite A \<Longrightarrow> card (A - {x}) \<le> card A"
  by (cases "x \<in> A") (simp_all add: card_Diff1_less less_imp_le)

lemma card_psubset: "finite B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> card A < card B \<Longrightarrow> A < B"
  by (erule psubsetI) blast

lemma card_le_inj:
  assumes fA: "finite A"
    and fB: "finite B"
    and c: "card A \<le> card B"
  shows "\<exists>f. f ` A \<subseteq> B \<and> inj_on f A"
  using fA fB c
proof (induct arbitrary: B rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert x s t)
  then show ?case
  proof (induct rule: finite_induct [OF insert.prems(1)])
    case 1
    then show ?case by simp
  next
    case (2 y t)
    from "2.prems"(1,2,5) "2.hyps"(1,2) have cst: "card s \<le> card t"
      by simp
    from "2.prems"(3) [OF "2.hyps"(1) cst]
    obtain f where "f ` s \<subseteq> t" "inj_on f s"
      by blast
    with "2.prems"(2) "2.hyps"(2) show ?case
      apply -
      apply (rule exI[where x = "\<lambda>z. if z = x then y else f z"])
      apply (auto simp add: inj_on_def)
      done
  qed
qed

lemma card_subset_eq:
  assumes fB: "finite B"
    and AB: "A \<subseteq> B"
    and c: "card A = card B"
  shows "A = B"
proof -
  from fB AB have fA: "finite A"
    by (auto intro: finite_subset)
  from fA fB have fBA: "finite (B - A)"
    by auto
  have e: "A \<inter> (B - A) = {}"
    by blast
  have eq: "A \<union> (B - A) = B"
    using AB by blast
  from card_Un_disjoint[OF fA fBA e, unfolded eq c] have "card (B - A) = 0"
    by arith
  then have "B - A = {}"
    unfolding card_eq_0_iff using fA fB by simp
  with AB show "A = B"
    by blast
qed

lemma insert_partition:
  "x \<notin> F \<Longrightarrow> \<forall>c1 \<in> insert x F. \<forall>c2 \<in> insert x F. c1 \<noteq> c2 \<longrightarrow> c1 \<inter> c2 = {} \<Longrightarrow> x \<inter> \<Union>F = {}"
  by auto  (* somewhat slow *)

lemma finite_psubset_induct [consumes 1, case_names psubset]:
  assumes finite: "finite A"
    and major: "\<And>A. finite A \<Longrightarrow> (\<And>B. B \<subset> A \<Longrightarrow> P B) \<Longrightarrow> P A"
  shows "P A"
  using finite
proof (induct A taking: card rule: measure_induct_rule)
  case (less A)
  have fin: "finite A" by fact
  have ih: "card B < card A \<Longrightarrow> finite B \<Longrightarrow> P B" for B by fact
  have "P B" if "B \<subset> A" for B
  proof -
    from that have "card B < card A"
      using psubset_card_mono fin by blast
    moreover
    from that have "B \<subseteq> A"
      by auto
    then have "finite B"
      using fin finite_subset by blast
    ultimately show ?thesis using ih by simp
  qed
  with fin show "P A" using major by blast
qed

lemma finite_induct_select [consumes 1, case_names empty select]:
  assumes "finite S"
    and "P {}"
    and select: "\<And>T. T \<subset> S \<Longrightarrow> P T \<Longrightarrow> \<exists>s\<in>S - T. P (insert s T)"
  shows "P S"
proof -
  have "0 \<le> card S" by simp
  then have "\<exists>T \<subseteq> S. card T = card S \<and> P T"
  proof (induct rule: dec_induct)
    case base with \<open>P {}\<close>
    show ?case
      by (intro exI[of _ "{}"]) auto
  next
    case (step n)
    then obtain T where T: "T \<subseteq> S" "card T = n" "P T"
      by auto
    with \<open>n < card S\<close> have "T \<subset> S" "P T"
      by auto
    with select[of T] obtain s where "s \<in> S" "s \<notin> T" "P (insert s T)"
      by auto
    with step(2) T \<open>finite S\<close> show ?case
      by (intro exI[of _ "insert s T"]) (auto dest: finite_subset)
  qed
  with \<open>finite S\<close> show "P S"
    by (auto dest: card_subset_eq)
qed

lemma remove_induct [case_names empty infinite remove]:
  assumes empty: "P ({} :: 'a set)"
    and infinite: "\<not> finite B \<Longrightarrow> P B"
    and remove: "\<And>A. finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> A \<subseteq> B \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> P (A - {x})) \<Longrightarrow> P A"
  shows "P B"
proof (cases "finite B")
  case False
  then show ?thesis by (rule infinite)
next
  case True
  define A where "A = B"
  with True have "finite A" "A \<subseteq> B"
    by simp_all
  then show "P A"
  proof (induct "card A" arbitrary: A)
    case 0
    then have "A = {}" by auto
    with empty show ?case by simp
  next
    case (Suc n A)
    from \<open>A \<subseteq> B\<close> and \<open>finite B\<close> have "finite A"
      by (rule finite_subset)
    moreover from Suc.hyps have "A \<noteq> {}" by auto
    moreover note \<open>A \<subseteq> B\<close>
    moreover have "P (A - {x})" if x: "x \<in> A" for x
      using x Suc.prems \<open>Suc n = card A\<close> by (intro Suc) auto
    ultimately show ?case by (rule remove)
  qed
qed

lemma finite_remove_induct [consumes 1, case_names empty remove]:
  fixes P :: "'a set \<Rightarrow> bool"
  assumes "finite B"
    and "P {}"
    and "\<And>A. finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> A \<subseteq> B \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> P (A - {x})) \<Longrightarrow> P A"
  defines "B' \<equiv> B"
  shows "P B'"
  by (induct B' rule: remove_induct) (simp_all add: assms)


text \<open>Main cardinality theorem.\<close>
lemma card_partition [rule_format]:
  "finite C \<Longrightarrow> finite (\<Union>C) \<Longrightarrow> (\<forall>c\<in>C. card c = k) \<Longrightarrow>
    (\<forall>c1 \<in> C. \<forall>c2 \<in> C. c1 \<noteq> c2 \<longrightarrow> c1 \<inter> c2 = {}) \<Longrightarrow>
    k * card C = card (\<Union>C)"
proof (induct rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert x F)
  then show ?case
    by (simp add: card_Un_disjoint insert_partition finite_subset [of _ "\<Union>(insert _ _)"])
qed

lemma card_eq_UNIV_imp_eq_UNIV:
  assumes fin: "finite (UNIV :: 'a set)"
    and card: "card A = card (UNIV :: 'a set)"
  shows "A = (UNIV :: 'a set)"
proof
  show "A \<subseteq> UNIV" by simp
  show "UNIV \<subseteq> A"
  proof
    show "x \<in> A" for x
    proof (rule ccontr)
      assume "x \<notin> A"
      then have "A \<subset> UNIV" by auto
      with fin have "card A < card (UNIV :: 'a set)"
        by (fact psubset_card_mono)
      with card show False by simp
    qed
  qed
qed

text \<open>The form of a finite set of given cardinality\<close>

lemma card_eq_SucD:
  assumes "card A = Suc k"
  shows "\<exists>b B. A = insert b B \<and> b \<notin> B \<and> card B = k \<and> (k = 0 \<longrightarrow> B = {})"
proof -
  have fin: "finite A"
    using assms by (auto intro: ccontr)
  moreover have "card A \<noteq> 0"
    using assms by auto
  ultimately obtain b where b: "b \<in> A"
    by auto
  show ?thesis
  proof (intro exI conjI)
    show "A = insert b (A - {b})"
      using b by blast
    show "b \<notin> A - {b}"
      by blast
    show "card (A - {b}) = k" and "k = 0 \<longrightarrow> A - {b} = {}"
      using assms b fin by (fastforce dest: mk_disjoint_insert)+
  qed
qed

lemma card_Suc_eq:
  "card A = Suc k \<longleftrightarrow>
    (\<exists>b B. A = insert b B \<and> b \<notin> B \<and> card B = k \<and> (k = 0 \<longrightarrow> B = {}))"
  apply (auto elim!: card_eq_SucD)
  apply (subst card.insert)
    apply (auto simp add: intro:ccontr)
  done

lemma card_1_singletonE:
  assumes "card A = 1"
  obtains x where "A = {x}"
  using assms by (auto simp: card_Suc_eq)

lemma is_singleton_altdef: "is_singleton A \<longleftrightarrow> card A = 1"
  unfolding is_singleton_def
  by (auto elim!: card_1_singletonE is_singletonE simp del: One_nat_def)

lemma card_le_Suc_iff:
  "finite A \<Longrightarrow> Suc n \<le> card A = (\<exists>a B. A = insert a B \<and> a \<notin> B \<and> n \<le> card B \<and> finite B)"
  by (fastforce simp: card_Suc_eq less_eq_nat.simps(2) insert_eq_iff
    dest: subset_singletonD split: nat.splits if_splits)

lemma finite_fun_UNIVD2:
  assumes fin: "finite (UNIV :: ('a \<Rightarrow> 'b) set)"
  shows "finite (UNIV :: 'b set)"
proof -
  from fin have "finite (range (\<lambda>f :: 'a \<Rightarrow> 'b. f arbitrary))" for arbitrary
    by (rule finite_imageI)
  moreover have "UNIV = range (\<lambda>f :: 'a \<Rightarrow> 'b. f arbitrary)" for arbitrary
    by (rule UNIV_eq_I) auto
  ultimately show "finite (UNIV :: 'b set)"
    by simp
qed

lemma card_UNIV_unit [simp]: "card (UNIV :: unit set) = 1"
  unfolding UNIV_unit by simp

lemma infinite_arbitrarily_large:
  assumes "\<not> finite A"
  shows "\<exists>B. finite B \<and> card B = n \<and> B \<subseteq> A"
proof (induction n)
  case 0
  show ?case by (intro exI[of _ "{}"]) auto
next
  case (Suc n)
  then obtain B where B: "finite B \<and> card B = n \<and> B \<subseteq> A" ..
  with \<open>\<not> finite A\<close> have "A \<noteq> B" by auto
  with B have "B \<subset> A" by auto
  then have "\<exists>x. x \<in> A - B"
    by (elim psubset_imp_ex_mem)
  then obtain x where x: "x \<in> A - B" ..
  with B have "finite (insert x B) \<and> card (insert x B) = Suc n \<and> insert x B \<subseteq> A"
    by auto
  then show "\<exists>B. finite B \<and> card B = Suc n \<and> B \<subseteq> A" ..
qed


subsubsection \<open>Cardinality of image\<close>

lemma card_image_le: "finite A \<Longrightarrow> card (f ` A) \<le> card A"
  by (induct rule: finite_induct) (simp_all add: le_SucI card_insert_if)

lemma card_image: "inj_on f A \<Longrightarrow> card (f ` A) = card A"
proof (induct A rule: infinite_finite_induct)
  case (infinite A)
  then have "\<not> finite (f ` A)" by (auto dest: finite_imageD)
  with infinite show ?case by simp
qed simp_all

lemma bij_betw_same_card: "bij_betw f A B \<Longrightarrow> card A = card B"
  by (auto simp: card_image bij_betw_def)

lemma endo_inj_surj: "finite A \<Longrightarrow> f ` A \<subseteq> A \<Longrightarrow> inj_on f A \<Longrightarrow> f ` A = A"
  by (simp add: card_seteq card_image)

lemma eq_card_imp_inj_on:
  assumes "finite A" "card(f ` A) = card A"
  shows "inj_on f A"
  using assms
proof (induct rule:finite_induct)
  case empty
  show ?case by simp
next
  case (insert x A)
  then show ?case
    using card_image_le [of A f] by (simp add: card_insert_if split: if_splits)
qed

lemma inj_on_iff_eq_card: "finite A \<Longrightarrow> inj_on f A \<longleftrightarrow> card (f ` A) = card A"
  by (blast intro: card_image eq_card_imp_inj_on)

lemma card_inj_on_le:
  assumes "inj_on f A" "f ` A \<subseteq> B" "finite B"
  shows "card A \<le> card B"
proof -
  have "finite A"
    using assms by (blast intro: finite_imageD dest: finite_subset)
  then show ?thesis
    using assms by (force intro: card_mono simp: card_image [symmetric])
qed

lemma surj_card_le: "finite A \<Longrightarrow> B \<subseteq> f ` A \<Longrightarrow> card B \<le> card A"
  by (blast intro: card_image_le card_mono le_trans)

lemma card_bij_eq:
  "inj_on f A \<Longrightarrow> f ` A \<subseteq> B \<Longrightarrow> inj_on g B \<Longrightarrow> g ` B \<subseteq> A \<Longrightarrow> finite A \<Longrightarrow> finite B
    \<Longrightarrow> card A = card B"
  by (auto intro: le_antisym card_inj_on_le)

lemma bij_betw_finite: "bij_betw f A B \<Longrightarrow> finite A \<longleftrightarrow> finite B"
  unfolding bij_betw_def using finite_imageD [of f A] by auto

lemma inj_on_finite: "inj_on f A \<Longrightarrow> f ` A \<le> B \<Longrightarrow> finite B \<Longrightarrow> finite A"
  using finite_imageD finite_subset by blast

lemma card_vimage_inj: "inj f \<Longrightarrow> A \<subseteq> range f \<Longrightarrow> card (f -` A) = card A"
  by (auto 4 3 simp: subset_image_iff inj_vimage_image_eq
      intro: card_image[symmetric, OF subset_inj_on])


subsubsection \<open>Pigeonhole Principles\<close>

lemma pigeonhole: "card A > card (f ` A) \<Longrightarrow> \<not> inj_on f A "
  by (auto dest: card_image less_irrefl_nat)

lemma pigeonhole_infinite:
  assumes "\<not> finite A" and "finite (f`A)"
  shows "\<exists>a0\<in>A. \<not> finite {a\<in>A. f a = f a0}"
  using assms(2,1)
proof (induct "f`A" arbitrary: A rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert b F)
  show ?case
  proof (cases "finite {a\<in>A. f a = b}")
    case True
    with \<open>\<not> finite A\<close> have "\<not> finite (A - {a\<in>A. f a = b})"
      by simp
    also have "A - {a\<in>A. f a = b} = {a\<in>A. f a \<noteq> b}"
      by blast
    finally have "\<not> finite {a\<in>A. f a \<noteq> b}" .
    from insert(3)[OF _ this] insert(2,4) show ?thesis
      by simp (blast intro: rev_finite_subset)
  next
    case False
    then have "{a \<in> A. f a = b} \<noteq> {}" by force
    with False show ?thesis by blast
  qed
qed

lemma pigeonhole_infinite_rel:
  assumes "\<not> finite A"
    and "finite B"
    and "\<forall>a\<in>A. \<exists>b\<in>B. R a b"
  shows "\<exists>b\<in>B. \<not> finite {a:A. R a b}"
proof -
  let ?F = "\<lambda>a. {b\<in>B. R a b}"
  from finite_Pow_iff[THEN iffD2, OF \<open>finite B\<close>] have "finite (?F ` A)"
    by (blast intro: rev_finite_subset)
  from pigeonhole_infinite [where f = ?F, OF assms(1) this]
  obtain a0 where "a0 \<in> A" and infinite: "\<not> finite {a\<in>A. ?F a = ?F a0}" ..
  obtain b0 where "b0 \<in> B" and "R a0 b0"
    using \<open>a0 \<in> A\<close> assms(3) by blast
  have "finite {a\<in>A. ?F a = ?F a0}" if "finite {a\<in>A. R a b0}"
    using \<open>b0 \<in> B\<close> \<open>R a0 b0\<close> that by (blast intro: rev_finite_subset)
  with infinite \<open>b0 \<in> B\<close> show ?thesis
    by blast
qed


subsubsection \<open>Cardinality of sums\<close>

lemma card_Plus:
  assumes "finite A" "finite B"
  shows "card (A <+> B) = card A + card B"
proof -
  have "Inl`A \<inter> Inr`B = {}" by fast
  with assms show ?thesis
    by (simp add: Plus_def card_Un_disjoint card_image)
qed

lemma card_Plus_conv_if:
  "card (A <+> B) = (if finite A \<and> finite B then card A + card B else 0)"
  by (auto simp add: card_Plus)

text \<open>Relates to equivalence classes.  Based on a theorem of F. Kammüller.\<close>

lemma dvd_partition:
  assumes f: "finite (\<Union>C)"
    and "\<forall>c\<in>C. k dvd card c" "\<forall>c1\<in>C. \<forall>c2\<in>C. c1 \<noteq> c2 \<longrightarrow> c1 \<inter> c2 = {}"
  shows "k dvd card (\<Union>C)"
proof -
  have "finite C"
    by (rule finite_UnionD [OF f])
  then show ?thesis
    using assms
  proof (induct rule: finite_induct)
    case empty
    show ?case by simp
  next
    case insert
    then show ?case
      apply simp
      apply (subst card_Un_disjoint)
         apply (auto simp add: disjoint_eq_subset_Compl)
      done
  qed
qed


subsubsection \<open>Relating injectivity and surjectivity\<close>

lemma finite_surj_inj:
  assumes "finite A" "A \<subseteq> f ` A"
  shows "inj_on f A"
proof -
  have "f ` A = A"
    by (rule card_seteq [THEN sym]) (auto simp add: assms card_image_le)
  then show ?thesis using assms
    by (simp add: eq_card_imp_inj_on)
qed

lemma finite_UNIV_surj_inj: "finite(UNIV:: 'a set) \<Longrightarrow> surj f \<Longrightarrow> inj f"
  for f :: "'a \<Rightarrow> 'a"
  by (blast intro: finite_surj_inj subset_UNIV)

lemma finite_UNIV_inj_surj: "finite(UNIV:: 'a set) \<Longrightarrow> inj f \<Longrightarrow> surj f"
  for f :: "'a \<Rightarrow> 'a"
  by (fastforce simp:surj_def dest!: endo_inj_surj)

corollary infinite_UNIV_nat [iff]: "\<not> finite (UNIV :: nat set)"
proof
  assume "finite (UNIV :: nat set)"
  with finite_UNIV_inj_surj [of Suc] show False
    by simp (blast dest: Suc_neq_Zero surjD)
qed

lemma infinite_UNIV_char_0: "\<not> finite (UNIV :: 'a::semiring_char_0 set)"
proof
  assume "finite (UNIV :: 'a set)"
  with subset_UNIV have "finite (range of_nat :: 'a set)"
    by (rule finite_subset)
  moreover have "inj (of_nat :: nat \<Rightarrow> 'a)"
    by (simp add: inj_on_def)
  ultimately have "finite (UNIV :: nat set)"
    by (rule finite_imageD)
  then show False
    by simp
qed

hide_const (open) Finite_Set.fold


subsection \<open>Infinite Sets\<close>

text \<open>
  Some elementary facts about infinite sets, mostly by Stephan Merz.
  Beware! Because "infinite" merely abbreviates a negation, these
  lemmas may not work well with \<open>blast\<close>.
\<close>

abbreviation infinite :: "'a set \<Rightarrow> bool"
  where "infinite S \<equiv> \<not> finite S"

text \<open>
  Infinite sets are non-empty, and if we remove some elements from an
  infinite set, the result is still infinite.
\<close>

lemma infinite_imp_nonempty: "infinite S \<Longrightarrow> S \<noteq> {}"
  by auto

lemma infinite_remove: "infinite S \<Longrightarrow> infinite (S - {a})"
  by simp

lemma Diff_infinite_finite:
  assumes "finite T" "infinite S"
  shows "infinite (S - T)"
  using \<open>finite T\<close>
proof induct
  from \<open>infinite S\<close> show "infinite (S - {})"
    by auto
next
  fix T x
  assume ih: "infinite (S - T)"
  have "S - (insert x T) = (S - T) - {x}"
    by (rule Diff_insert)
  with ih show "infinite (S - (insert x T))"
    by (simp add: infinite_remove)
qed

lemma Un_infinite: "infinite S \<Longrightarrow> infinite (S \<union> T)"
  by simp

lemma infinite_Un: "infinite (S \<union> T) \<longleftrightarrow> infinite S \<or> infinite T"
  by simp

lemma infinite_super:
  assumes "S \<subseteq> T"
    and "infinite S"
  shows "infinite T"
proof
  assume "finite T"
  with \<open>S \<subseteq> T\<close> have "finite S" by (simp add: finite_subset)
  with \<open>infinite S\<close> show False by simp
qed

proposition infinite_coinduct [consumes 1, case_names infinite]:
  assumes "X A"
    and step: "\<And>A. X A \<Longrightarrow> \<exists>x\<in>A. X (A - {x}) \<or> infinite (A - {x})"
  shows "infinite A"
proof
  assume "finite A"
  then show False
    using \<open>X A\<close>
  proof (induction rule: finite_psubset_induct)
    case (psubset A)
    then obtain x where "x \<in> A" "X (A - {x}) \<or> infinite (A - {x})"
      using local.step psubset.prems by blast
    then have "X (A - {x})"
      using psubset.hyps by blast
    show False
      apply (rule psubset.IH [where B = "A - {x}"])
       apply (use \<open>x \<in> A\<close> in blast)
      apply (simp add: \<open>X (A - {x})\<close>)
      done
  qed
qed

text \<open>
  For any function with infinite domain and finite range there is some
  element that is the image of infinitely many domain elements.  In
  particular, any infinite sequence of elements from a finite set
  contains some element that occurs infinitely often.
\<close>

lemma inf_img_fin_dom':
  assumes img: "finite (f ` A)"
    and dom: "infinite A"
  shows "\<exists>y \<in> f ` A. infinite (f -` {y} \<inter> A)"
proof (rule ccontr)
  have "A \<subseteq> (\<Union>y\<in>f ` A. f -` {y} \<inter> A)" by auto
  moreover assume "\<not> ?thesis"
  with img have "finite (\<Union>y\<in>f ` A. f -` {y} \<inter> A)" by blast
  ultimately have "finite A" by (rule finite_subset)
  with dom show False by contradiction
qed

lemma inf_img_fin_domE':
  assumes "finite (f ` A)" and "infinite A"
  obtains y where "y \<in> f`A" and "infinite (f -` {y} \<inter> A)"
  using assms by (blast dest: inf_img_fin_dom')

lemma inf_img_fin_dom:
  assumes img: "finite (f`A)" and dom: "infinite A"
  shows "\<exists>y \<in> f`A. infinite (f -` {y})"
  using inf_img_fin_dom'[OF assms] by auto

lemma inf_img_fin_domE:
  assumes "finite (f`A)" and "infinite A"
  obtains y where "y \<in> f`A" and "infinite (f -` {y})"
  using assms by (blast dest: inf_img_fin_dom)

proposition finite_image_absD: "finite (abs ` S) \<Longrightarrow> finite S"
  for S :: "'a::linordered_ring set"
  by (rule ccontr) (auto simp: abs_eq_iff vimage_def dest: inf_img_fin_dom)

end
