(*  Title:      HOL/Lattices_Big.thy
    Author:     Tobias Nipkow, Lawrence C Paulson and Markus Wenzel
                with contributions by Jeremy Avigad
*)

section \<open>Big infimum (minimum) and supremum (maximum) over finite (non-empty) sets\<close>

theory Lattices_Big
imports Finite_Set Option
begin

subsection \<open>Generic lattice operations over a set\<close>

subsubsection \<open>Without neutral element\<close>

locale semilattice_set = semilattice
begin

interpretation comp_fun_idem f
  by standard (simp_all add: fun_eq_iff left_commute)

definition F :: "'a set \<Rightarrow> 'a"
where
  eq_fold': "F A = the (Finite_Set.fold (\<lambda>x y. Some (case y of None \<Rightarrow> x | Some z \<Rightarrow> f x z)) None A)"

lemma eq_fold:
  assumes "finite A"
  shows "F (insert x A) = Finite_Set.fold f x A"
proof (rule sym)
  let ?f = "\<lambda>x y. Some (case y of None \<Rightarrow> x | Some z \<Rightarrow> f x z)"
  interpret comp_fun_idem "?f"
    by standard (simp_all add: fun_eq_iff commute left_commute split: option.split)
  from assms show "Finite_Set.fold f x A = F (insert x A)"
  proof induct
    case empty then show ?case by (simp add: eq_fold')
  next
    case (insert y B) then show ?case by (simp add: insert_commute [of x] eq_fold')
  qed
qed

lemma singleton [simp]:
  "F {x} = x"
  by (simp add: eq_fold)

lemma insert_not_elem:
  assumes "finite A" and "x \<notin> A" and "A \<noteq> {}"
  shows "F (insert x A) = x \<^bold>* F A"
proof -
  from \<open>A \<noteq> {}\<close> obtain b where "b \<in> A" by blast
  then obtain B where *: "A = insert b B" "b \<notin> B" by (blast dest: mk_disjoint_insert)
  with \<open>finite A\<close> and \<open>x \<notin> A\<close>
    have "finite (insert x B)" and "b \<notin> insert x B" by auto
  then have "F (insert b (insert x B)) = x \<^bold>* F (insert b B)"
    by (simp add: eq_fold)
  then show ?thesis by (simp add: * insert_commute)
qed

lemma in_idem:
  assumes "finite A" and "x \<in> A"
  shows "x \<^bold>* F A = F A"
proof -
  from assms have "A \<noteq> {}" by auto
  with \<open>finite A\<close> show ?thesis using \<open>x \<in> A\<close>
    by (induct A rule: finite_ne_induct) (auto simp add: ac_simps insert_not_elem)
qed

lemma insert [simp]:
  assumes "finite A" and "A \<noteq> {}"
  shows "F (insert x A) = x \<^bold>* F A"
  using assms by (cases "x \<in> A") (simp_all add: insert_absorb in_idem insert_not_elem)

lemma union:
  assumes "finite A" "A \<noteq> {}" and "finite B" "B \<noteq> {}"
  shows "F (A \<union> B) = F A \<^bold>* F B"
  using assms by (induct A rule: finite_ne_induct) (simp_all add: ac_simps)

lemma remove:
  assumes "finite A" and "x \<in> A"
  shows "F A = (if A - {x} = {} then x else x \<^bold>* F (A - {x}))"
proof -
  from assms obtain B where "A = insert x B" and "x \<notin> B" by (blast dest: mk_disjoint_insert)
  with assms show ?thesis by simp
qed

lemma insert_remove:
  assumes "finite A"
  shows "F (insert x A) = (if A - {x} = {} then x else x \<^bold>* F (A - {x}))"
  using assms by (cases "x \<in> A") (simp_all add: insert_absorb remove)

lemma subset:
  assumes "finite A" "B \<noteq> {}" and "B \<subseteq> A"
  shows "F B \<^bold>* F A = F A"
proof -
  from assms have "A \<noteq> {}" and "finite B" by (auto dest: finite_subset)
  with assms show ?thesis by (simp add: union [symmetric] Un_absorb1)
qed

lemma closed:
  assumes "finite A" "A \<noteq> {}" and elem: "\<And>x y. x \<^bold>* y \<in> {x, y}"
  shows "F A \<in> A"
using \<open>finite A\<close> \<open>A \<noteq> {}\<close> proof (induct rule: finite_ne_induct)
  case singleton then show ?case by simp
next
  case insert with elem show ?case by force
qed

lemma hom_commute:
  assumes hom: "\<And>x y. h (x \<^bold>* y) = h x \<^bold>* h y"
  and N: "finite N" "N \<noteq> {}"
  shows "h (F N) = F (h ` N)"
using N proof (induct rule: finite_ne_induct)
  case singleton thus ?case by simp
next
  case (insert n N)
  then have "h (F (insert n N)) = h (n \<^bold>* F N)" by simp
  also have "\<dots> = h n \<^bold>* h (F N)" by (rule hom)
  also have "h (F N) = F (h ` N)" by (rule insert)
  also have "h n \<^bold>* \<dots> = F (insert (h n) (h ` N))"
    using insert by simp
  also have "insert (h n) (h ` N) = h ` insert n N" by simp
  finally show ?case .
qed

lemma infinite: "\<not> finite A \<Longrightarrow> F A = the None"
  unfolding eq_fold' by (cases "finite (UNIV::'a set)") (auto intro: finite_subset fold_infinite)

end

locale semilattice_order_set = binary?: semilattice_order + semilattice_set
begin

lemma bounded_iff:
  assumes "finite A" and "A \<noteq> {}"
  shows "x \<^bold>\<le> F A \<longleftrightarrow> (\<forall>a\<in>A. x \<^bold>\<le> a)"
  using assms by (induct rule: finite_ne_induct) (simp_all add: bounded_iff)

lemma boundedI:
  assumes "finite A"
  assumes "A \<noteq> {}"
  assumes "\<And>a. a \<in> A \<Longrightarrow> x \<^bold>\<le> a"
  shows "x \<^bold>\<le> F A"
  using assms by (simp add: bounded_iff)

lemma boundedE:
  assumes "finite A" and "A \<noteq> {}" and "x \<^bold>\<le> F A"
  obtains "\<And>a. a \<in> A \<Longrightarrow> x \<^bold>\<le> a"
  using assms by (simp add: bounded_iff)

lemma coboundedI:
  assumes "finite A"
    and "a \<in> A"
  shows "F A \<^bold>\<le> a"
proof -
  from assms have "A \<noteq> {}" by auto
  from \<open>finite A\<close> \<open>A \<noteq> {}\<close> \<open>a \<in> A\<close> show ?thesis
  proof (induct rule: finite_ne_induct)
    case singleton thus ?case by (simp add: refl)
  next
    case (insert x B)
    from insert have "a = x \<or> a \<in> B" by simp
    then show ?case using insert by (auto intro: coboundedI2)
  qed
qed

lemma antimono:
  assumes "A \<subseteq> B" and "A \<noteq> {}" and "finite B"
  shows "F B \<^bold>\<le> F A"
proof (cases "A = B")
  case True then show ?thesis by (simp add: refl)
next
  case False
  have B: "B = A \<union> (B - A)" using \<open>A \<subseteq> B\<close> by blast
  then have "F B = F (A \<union> (B - A))" by simp
  also have "\<dots> = F A \<^bold>* F (B - A)" using False assms by (subst union) (auto intro: finite_subset)
  also have "\<dots> \<^bold>\<le> F A" by simp
  finally show ?thesis .
qed

end


subsubsection \<open>With neutral element\<close>

locale semilattice_neutr_set = semilattice_neutr
begin

interpretation comp_fun_idem f
  by standard (simp_all add: fun_eq_iff left_commute)

definition F :: "'a set \<Rightarrow> 'a"
where
  eq_fold: "F A = Finite_Set.fold f \<^bold>1 A"

lemma infinite [simp]:
  "\<not> finite A \<Longrightarrow> F A = \<^bold>1"
  by (simp add: eq_fold)

lemma empty [simp]:
  "F {} = \<^bold>1"
  by (simp add: eq_fold)

lemma insert [simp]:
  assumes "finite A"
  shows "F (insert x A) = x \<^bold>* F A"
  using assms by (simp add: eq_fold)

lemma in_idem:
  assumes "finite A" and "x \<in> A"
  shows "x \<^bold>* F A = F A"
proof -
  from assms have "A \<noteq> {}" by auto
  with \<open>finite A\<close> show ?thesis using \<open>x \<in> A\<close>
    by (induct A rule: finite_ne_induct) (auto simp add: ac_simps)
qed

lemma union:
  assumes "finite A" and "finite B"
  shows "F (A \<union> B) = F A \<^bold>* F B"
  using assms by (induct A) (simp_all add: ac_simps)

lemma remove:
  assumes "finite A" and "x \<in> A"
  shows "F A = x \<^bold>* F (A - {x})"
proof -
  from assms obtain B where "A = insert x B" and "x \<notin> B" by (blast dest: mk_disjoint_insert)
  with assms show ?thesis by simp
qed

lemma insert_remove:
  assumes "finite A"
  shows "F (insert x A) = x \<^bold>* F (A - {x})"
  using assms by (cases "x \<in> A") (simp_all add: insert_absorb remove)

lemma subset:
  assumes "finite A" and "B \<subseteq> A"
  shows "F B \<^bold>* F A = F A"
proof -
  from assms have "finite B" by (auto dest: finite_subset)
  with assms show ?thesis by (simp add: union [symmetric] Un_absorb1)
qed

lemma closed:
  assumes "finite A" "A \<noteq> {}" and elem: "\<And>x y. x \<^bold>* y \<in> {x, y}"
  shows "F A \<in> A"
using \<open>finite A\<close> \<open>A \<noteq> {}\<close> proof (induct rule: finite_ne_induct)
  case singleton then show ?case by simp
next
  case insert with elem show ?case by force
qed

end

locale semilattice_order_neutr_set = binary?: semilattice_neutr_order + semilattice_neutr_set
begin

lemma bounded_iff:
  assumes "finite A"
  shows "x \<^bold>\<le> F A \<longleftrightarrow> (\<forall>a\<in>A. x \<^bold>\<le> a)"
  using assms by (induct A) (simp_all add: bounded_iff)

lemma boundedI:
  assumes "finite A"
  assumes "\<And>a. a \<in> A \<Longrightarrow> x \<^bold>\<le> a"
  shows "x \<^bold>\<le> F A"
  using assms by (simp add: bounded_iff)

lemma boundedE:
  assumes "finite A" and "x \<^bold>\<le> F A"
  obtains "\<And>a. a \<in> A \<Longrightarrow> x \<^bold>\<le> a"
  using assms by (simp add: bounded_iff)

lemma coboundedI:
  assumes "finite A"
    and "a \<in> A"
  shows "F A \<^bold>\<le> a"
proof -
  from assms have "A \<noteq> {}" by auto
  from \<open>finite A\<close> \<open>A \<noteq> {}\<close> \<open>a \<in> A\<close> show ?thesis
  proof (induct rule: finite_ne_induct)
    case singleton thus ?case by (simp add: refl)
  next
    case (insert x B)
    from insert have "a = x \<or> a \<in> B" by simp
    then show ?case using insert by (auto intro: coboundedI2)
  qed
qed

lemma antimono:
  assumes "A \<subseteq> B" and "finite B"
  shows "F B \<^bold>\<le> F A"
proof (cases "A = B")
  case True then show ?thesis by (simp add: refl)
next
  case False
  have B: "B = A \<union> (B - A)" using \<open>A \<subseteq> B\<close> by blast
  then have "F B = F (A \<union> (B - A))" by simp
  also have "\<dots> = F A \<^bold>* F (B - A)" using False assms by (subst union) (auto intro: finite_subset)
  also have "\<dots> \<^bold>\<le> F A" by simp
  finally show ?thesis .
qed

end


subsection \<open>Lattice operations on finite sets\<close>

context semilattice_inf
begin

sublocale Inf_fin: semilattice_order_set inf less_eq less
defines
  Inf_fin ("\<Sqinter>\<^sub>f\<^sub>i\<^sub>n_" [900] 900) = Inf_fin.F ..

end

context semilattice_sup
begin

sublocale Sup_fin: semilattice_order_set sup greater_eq greater
defines
  Sup_fin ("\<Squnion>\<^sub>f\<^sub>i\<^sub>n_" [900] 900) = Sup_fin.F ..

end


subsection \<open>Infimum and Supremum over non-empty sets\<close>

context lattice
begin

lemma Inf_fin_le_Sup_fin [simp]: 
  assumes "finite A" and "A \<noteq> {}"
  shows "\<Sqinter>\<^sub>f\<^sub>i\<^sub>nA \<le> \<Squnion>\<^sub>f\<^sub>i\<^sub>nA"
proof -
  from \<open>A \<noteq> {}\<close> obtain a where "a \<in> A" by blast
  with \<open>finite A\<close> have "\<Sqinter>\<^sub>f\<^sub>i\<^sub>nA \<le> a" by (rule Inf_fin.coboundedI)
  moreover from \<open>finite A\<close> \<open>a \<in> A\<close> have "a \<le> \<Squnion>\<^sub>f\<^sub>i\<^sub>nA" by (rule Sup_fin.coboundedI)
  ultimately show ?thesis by (rule order_trans)
qed

lemma sup_Inf_absorb [simp]:
  "finite A \<Longrightarrow> a \<in> A \<Longrightarrow> \<Sqinter>\<^sub>f\<^sub>i\<^sub>nA \<squnion> a = a"
  by (rule sup_absorb2) (rule Inf_fin.coboundedI)

lemma inf_Sup_absorb [simp]:
  "finite A \<Longrightarrow> a \<in> A \<Longrightarrow> a \<sqinter> \<Squnion>\<^sub>f\<^sub>i\<^sub>nA = a"
  by (rule inf_absorb1) (rule Sup_fin.coboundedI)

end

context distrib_lattice
begin

lemma sup_Inf1_distrib:
  assumes "finite A"
    and "A \<noteq> {}"
  shows "sup x (\<Sqinter>\<^sub>f\<^sub>i\<^sub>nA) = \<Sqinter>\<^sub>f\<^sub>i\<^sub>n{sup x a|a. a \<in> A}"
using assms by (simp add: image_def Inf_fin.hom_commute [where h="sup x", OF sup_inf_distrib1])
  (rule arg_cong [where f="Inf_fin"], blast)

lemma sup_Inf2_distrib:
  assumes A: "finite A" "A \<noteq> {}" and B: "finite B" "B \<noteq> {}"
  shows "sup (\<Sqinter>\<^sub>f\<^sub>i\<^sub>nA) (\<Sqinter>\<^sub>f\<^sub>i\<^sub>nB) = \<Sqinter>\<^sub>f\<^sub>i\<^sub>n{sup a b|a b. a \<in> A \<and> b \<in> B}"
using A proof (induct rule: finite_ne_induct)
  case singleton then show ?case
    by (simp add: sup_Inf1_distrib [OF B])
next
  case (insert x A)
  have finB: "finite {sup x b |b. b \<in> B}"
    by (rule finite_surj [where f = "sup x", OF B(1)], auto)
  have finAB: "finite {sup a b |a b. a \<in> A \<and> b \<in> B}"
  proof -
    have "{sup a b |a b. a \<in> A \<and> b \<in> B} = (UN a:A. UN b:B. {sup a b})"
      by blast
    thus ?thesis by(simp add: insert(1) B(1))
  qed
  have ne: "{sup a b |a b. a \<in> A \<and> b \<in> B} \<noteq> {}" using insert B by blast
  have "sup (\<Sqinter>\<^sub>f\<^sub>i\<^sub>n(insert x A)) (\<Sqinter>\<^sub>f\<^sub>i\<^sub>nB) = sup (inf x (\<Sqinter>\<^sub>f\<^sub>i\<^sub>nA)) (\<Sqinter>\<^sub>f\<^sub>i\<^sub>nB)"
    using insert by simp
  also have "\<dots> = inf (sup x (\<Sqinter>\<^sub>f\<^sub>i\<^sub>nB)) (sup (\<Sqinter>\<^sub>f\<^sub>i\<^sub>nA) (\<Sqinter>\<^sub>f\<^sub>i\<^sub>nB))" by(rule sup_inf_distrib2)
  also have "\<dots> = inf (\<Sqinter>\<^sub>f\<^sub>i\<^sub>n{sup x b|b. b \<in> B}) (\<Sqinter>\<^sub>f\<^sub>i\<^sub>n{sup a b|a b. a \<in> A \<and> b \<in> B})"
    using insert by(simp add:sup_Inf1_distrib[OF B])
  also have "\<dots> = \<Sqinter>\<^sub>f\<^sub>i\<^sub>n({sup x b |b. b \<in> B} \<union> {sup a b |a b. a \<in> A \<and> b \<in> B})"
    (is "_ = \<Sqinter>\<^sub>f\<^sub>i\<^sub>n?M")
    using B insert
    by (simp add: Inf_fin.union [OF finB _ finAB ne])
  also have "?M = {sup a b |a b. a \<in> insert x A \<and> b \<in> B}"
    by blast
  finally show ?case .
qed

lemma inf_Sup1_distrib:
  assumes "finite A" and "A \<noteq> {}"
  shows "inf x (\<Squnion>\<^sub>f\<^sub>i\<^sub>nA) = \<Squnion>\<^sub>f\<^sub>i\<^sub>n{inf x a|a. a \<in> A}"
using assms by (simp add: image_def Sup_fin.hom_commute [where h="inf x", OF inf_sup_distrib1])
  (rule arg_cong [where f="Sup_fin"], blast)

lemma inf_Sup2_distrib:
  assumes A: "finite A" "A \<noteq> {}" and B: "finite B" "B \<noteq> {}"
  shows "inf (\<Squnion>\<^sub>f\<^sub>i\<^sub>nA) (\<Squnion>\<^sub>f\<^sub>i\<^sub>nB) = \<Squnion>\<^sub>f\<^sub>i\<^sub>n{inf a b|a b. a \<in> A \<and> b \<in> B}"
using A proof (induct rule: finite_ne_induct)
  case singleton thus ?case
    by(simp add: inf_Sup1_distrib [OF B])
next
  case (insert x A)
  have finB: "finite {inf x b |b. b \<in> B}"
    by(rule finite_surj[where f = "%b. inf x b", OF B(1)], auto)
  have finAB: "finite {inf a b |a b. a \<in> A \<and> b \<in> B}"
  proof -
    have "{inf a b |a b. a \<in> A \<and> b \<in> B} = (UN a:A. UN b:B. {inf a b})"
      by blast
    thus ?thesis by(simp add: insert(1) B(1))
  qed
  have ne: "{inf a b |a b. a \<in> A \<and> b \<in> B} \<noteq> {}" using insert B by blast
  have "inf (\<Squnion>\<^sub>f\<^sub>i\<^sub>n(insert x A)) (\<Squnion>\<^sub>f\<^sub>i\<^sub>nB) = inf (sup x (\<Squnion>\<^sub>f\<^sub>i\<^sub>nA)) (\<Squnion>\<^sub>f\<^sub>i\<^sub>nB)"
    using insert by simp
  also have "\<dots> = sup (inf x (\<Squnion>\<^sub>f\<^sub>i\<^sub>nB)) (inf (\<Squnion>\<^sub>f\<^sub>i\<^sub>nA) (\<Squnion>\<^sub>f\<^sub>i\<^sub>nB))" by(rule inf_sup_distrib2)
  also have "\<dots> = sup (\<Squnion>\<^sub>f\<^sub>i\<^sub>n{inf x b|b. b \<in> B}) (\<Squnion>\<^sub>f\<^sub>i\<^sub>n{inf a b|a b. a \<in> A \<and> b \<in> B})"
    using insert by(simp add:inf_Sup1_distrib[OF B])
  also have "\<dots> = \<Squnion>\<^sub>f\<^sub>i\<^sub>n({inf x b |b. b \<in> B} \<union> {inf a b |a b. a \<in> A \<and> b \<in> B})"
    (is "_ = \<Squnion>\<^sub>f\<^sub>i\<^sub>n?M")
    using B insert
    by (simp add: Sup_fin.union [OF finB _ finAB ne])
  also have "?M = {inf a b |a b. a \<in> insert x A \<and> b \<in> B}"
    by blast
  finally show ?case .
qed

end

context complete_lattice
begin

lemma Inf_fin_Inf:
  assumes "finite A" and "A \<noteq> {}"
  shows "\<Sqinter>\<^sub>f\<^sub>i\<^sub>nA = \<Sqinter>A"
proof -
  from assms obtain b B where "A = insert b B" and "finite B" by auto
  then show ?thesis
    by (simp add: Inf_fin.eq_fold inf_Inf_fold_inf inf.commute [of b])
qed

lemma Sup_fin_Sup:
  assumes "finite A" and "A \<noteq> {}"
  shows "\<Squnion>\<^sub>f\<^sub>i\<^sub>nA = \<Squnion>A"
proof -
  from assms obtain b B where "A = insert b B" and "finite B" by auto
  then show ?thesis
    by (simp add: Sup_fin.eq_fold sup_Sup_fold_sup sup.commute [of b])
qed

end


subsection \<open>Minimum and Maximum over non-empty sets\<close>

context linorder
begin

sublocale Min: semilattice_order_set min less_eq less
  + Max: semilattice_order_set max greater_eq greater
defines
  Min = Min.F and Max = Max.F ..

end

text \<open>An aside: @{const Min}/@{const Max} on linear orders as special case of @{const Inf_fin}/@{const Sup_fin}\<close>

lemma Inf_fin_Min:
  "Inf_fin = (Min :: 'a::{semilattice_inf, linorder} set \<Rightarrow> 'a)"
  by (simp add: Inf_fin_def Min_def inf_min)

lemma Sup_fin_Max:
  "Sup_fin = (Max :: 'a::{semilattice_sup, linorder} set \<Rightarrow> 'a)"
  by (simp add: Sup_fin_def Max_def sup_max)

context linorder
begin

lemma dual_min:
  "ord.min greater_eq = max"
  by (auto simp add: ord.min_def max_def fun_eq_iff)

lemma dual_max:
  "ord.max greater_eq = min"
  by (auto simp add: ord.max_def min_def fun_eq_iff)

lemma dual_Min:
  "linorder.Min greater_eq = Max"
proof -
  interpret dual: linorder greater_eq greater by (fact dual_linorder)
  show ?thesis by (simp add: dual.Min_def dual_min Max_def)
qed

lemma dual_Max:
  "linorder.Max greater_eq = Min"
proof -
  interpret dual: linorder greater_eq greater by (fact dual_linorder)
  show ?thesis by (simp add: dual.Max_def dual_max Min_def)
qed

lemmas Min_singleton = Min.singleton
lemmas Max_singleton = Max.singleton
lemmas Min_insert = Min.insert
lemmas Max_insert = Max.insert
lemmas Min_Un = Min.union
lemmas Max_Un = Max.union
lemmas hom_Min_commute = Min.hom_commute
lemmas hom_Max_commute = Max.hom_commute

lemma Min_in [simp]:
  assumes "finite A" and "A \<noteq> {}"
  shows "Min A \<in> A"
  using assms by (auto simp add: min_def Min.closed)

lemma Max_in [simp]:
  assumes "finite A" and "A \<noteq> {}"
  shows "Max A \<in> A"
  using assms by (auto simp add: max_def Max.closed)

lemma Min_insert2:
  assumes "finite A" and min: "\<And>b. b \<in> A \<Longrightarrow> a \<le> b"
  shows "Min (insert a A) = a"
proof (cases "A = {}")
  case True
  then show ?thesis by simp
next
  case False
  with \<open>finite A\<close> have "Min (insert a A) = min a (Min A)"
    by simp
  moreover from \<open>finite A\<close> \<open>A \<noteq> {}\<close> min have "a \<le> Min A" by simp
  ultimately show ?thesis by (simp add: min.absorb1)
qed

lemma Max_insert2:
  assumes "finite A" and max: "\<And>b. b \<in> A \<Longrightarrow> b \<le> a"
  shows "Max (insert a A) = a"
proof (cases "A = {}")
  case True
  then show ?thesis by simp
next
  case False
  with \<open>finite A\<close> have "Max (insert a A) = max a (Max A)"
    by simp
  moreover from \<open>finite A\<close> \<open>A \<noteq> {}\<close> max have "Max A \<le> a" by simp
  ultimately show ?thesis by (simp add: max.absorb1)
qed

lemma Min_le [simp]:
  assumes "finite A" and "x \<in> A"
  shows "Min A \<le> x"
  using assms by (fact Min.coboundedI)

lemma Max_ge [simp]:
  assumes "finite A" and "x \<in> A"
  shows "x \<le> Max A"
  using assms by (fact Max.coboundedI)

lemma Min_eqI:
  assumes "finite A"
  assumes "\<And>y. y \<in> A \<Longrightarrow> y \<ge> x"
    and "x \<in> A"
  shows "Min A = x"
proof (rule antisym)
  from \<open>x \<in> A\<close> have "A \<noteq> {}" by auto
  with assms show "Min A \<ge> x" by simp
next
  from assms show "x \<ge> Min A" by simp
qed

lemma Max_eqI:
  assumes "finite A"
  assumes "\<And>y. y \<in> A \<Longrightarrow> y \<le> x"
    and "x \<in> A"
  shows "Max A = x"
proof (rule antisym)
  from \<open>x \<in> A\<close> have "A \<noteq> {}" by auto
  with assms show "Max A \<le> x" by simp
next
  from assms show "x \<le> Max A" by simp
qed

context
  fixes A :: "'a set"
  assumes fin_nonempty: "finite A" "A \<noteq> {}"
begin

lemma Min_ge_iff [simp]:
  "x \<le> Min A \<longleftrightarrow> (\<forall>a\<in>A. x \<le> a)"
  using fin_nonempty by (fact Min.bounded_iff)

lemma Max_le_iff [simp]:
  "Max A \<le> x \<longleftrightarrow> (\<forall>a\<in>A. a \<le> x)"
  using fin_nonempty by (fact Max.bounded_iff)

lemma Min_gr_iff [simp]:
  "x < Min A \<longleftrightarrow> (\<forall>a\<in>A. x < a)"
  using fin_nonempty  by (induct rule: finite_ne_induct) simp_all

lemma Max_less_iff [simp]:
  "Max A < x \<longleftrightarrow> (\<forall>a\<in>A. a < x)"
  using fin_nonempty by (induct rule: finite_ne_induct) simp_all

lemma Min_le_iff:
  "Min A \<le> x \<longleftrightarrow> (\<exists>a\<in>A. a \<le> x)"
  using fin_nonempty by (induct rule: finite_ne_induct) (simp_all add: min_le_iff_disj)

lemma Max_ge_iff:
  "x \<le> Max A \<longleftrightarrow> (\<exists>a\<in>A. x \<le> a)"
  using fin_nonempty by (induct rule: finite_ne_induct) (simp_all add: le_max_iff_disj)

lemma Min_less_iff:
  "Min A < x \<longleftrightarrow> (\<exists>a\<in>A. a < x)"
  using fin_nonempty by (induct rule: finite_ne_induct) (simp_all add: min_less_iff_disj)

lemma Max_gr_iff:
  "x < Max A \<longleftrightarrow> (\<exists>a\<in>A. x < a)"
  using fin_nonempty by (induct rule: finite_ne_induct) (simp_all add: less_max_iff_disj)

end

lemma Max_eq_if:
  assumes "finite A"  "finite B"  "\<forall>a\<in>A. \<exists>b\<in>B. a \<le> b"  "\<forall>b\<in>B. \<exists>a\<in>A. b \<le> a"
  shows "Max A = Max B"
proof cases
  assume "A = {}" thus ?thesis using assms by simp
next
  assume "A \<noteq> {}" thus ?thesis using assms
    by(blast intro: antisym Max_in Max_ge_iff[THEN iffD2])
qed

lemma Min_antimono:
  assumes "M \<subseteq> N" and "M \<noteq> {}" and "finite N"
  shows "Min N \<le> Min M"
  using assms by (fact Min.antimono)

lemma Max_mono:
  assumes "M \<subseteq> N" and "M \<noteq> {}" and "finite N"
  shows "Max M \<le> Max N"
  using assms by (fact Max.antimono)

end

context linorder  (* FIXME *)
begin

lemma mono_Min_commute:
  assumes "mono f"
  assumes "finite A" and "A \<noteq> {}"
  shows "f (Min A) = Min (f ` A)"
proof (rule linorder_class.Min_eqI [symmetric])
  from \<open>finite A\<close> show "finite (f ` A)" by simp
  from assms show "f (Min A) \<in> f ` A" by simp
  fix x
  assume "x \<in> f ` A"
  then obtain y where "y \<in> A" and "x = f y" ..
  with assms have "Min A \<le> y" by auto
  with \<open>mono f\<close> have "f (Min A) \<le> f y" by (rule monoE)
  with \<open>x = f y\<close> show "f (Min A) \<le> x" by simp
qed

lemma mono_Max_commute:
  assumes "mono f"
  assumes "finite A" and "A \<noteq> {}"
  shows "f (Max A) = Max (f ` A)"
proof (rule linorder_class.Max_eqI [symmetric])
  from \<open>finite A\<close> show "finite (f ` A)" by simp
  from assms show "f (Max A) \<in> f ` A" by simp
  fix x
  assume "x \<in> f ` A"
  then obtain y where "y \<in> A" and "x = f y" ..
  with assms have "y \<le> Max A" by auto
  with \<open>mono f\<close> have "f y \<le> f (Max A)" by (rule monoE)
  with \<open>x = f y\<close> show "x \<le> f (Max A)" by simp
qed

lemma finite_linorder_max_induct [consumes 1, case_names empty insert]:
  assumes fin: "finite A"
  and empty: "P {}" 
  and insert: "\<And>b A. finite A \<Longrightarrow> \<forall>a\<in>A. a < b \<Longrightarrow> P A \<Longrightarrow> P (insert b A)"
  shows "P A"
using fin empty insert
proof (induct rule: finite_psubset_induct)
  case (psubset A)
  have IH: "\<And>B. \<lbrakk>B < A; P {}; (\<And>A b. \<lbrakk>finite A; \<forall>a\<in>A. a<b; P A\<rbrakk> \<Longrightarrow> P (insert b A))\<rbrakk> \<Longrightarrow> P B" by fact 
  have fin: "finite A" by fact 
  have empty: "P {}" by fact
  have step: "\<And>b A. \<lbrakk>finite A; \<forall>a\<in>A. a < b; P A\<rbrakk> \<Longrightarrow> P (insert b A)" by fact
  show "P A"
  proof (cases "A = {}")
    assume "A = {}" 
    then show "P A" using \<open>P {}\<close> by simp
  next
    let ?B = "A - {Max A}" 
    let ?A = "insert (Max A) ?B"
    have "finite ?B" using \<open>finite A\<close> by simp
    assume "A \<noteq> {}"
    with \<open>finite A\<close> have "Max A : A" by auto
    then have A: "?A = A" using insert_Diff_single insert_absorb by auto
    then have "P ?B" using \<open>P {}\<close> step IH [of ?B] by blast
    moreover 
    have "\<forall>a\<in>?B. a < Max A" using Max_ge [OF \<open>finite A\<close>] by fastforce
    ultimately show "P A" using A insert_Diff_single step [OF \<open>finite ?B\<close>] by fastforce
  qed
qed

lemma finite_linorder_min_induct [consumes 1, case_names empty insert]:
  "\<lbrakk>finite A; P {}; \<And>b A. \<lbrakk>finite A; \<forall>a\<in>A. b < a; P A\<rbrakk> \<Longrightarrow> P (insert b A)\<rbrakk> \<Longrightarrow> P A"
  by (rule linorder.finite_linorder_max_induct [OF dual_linorder])

lemma Least_Min:
  assumes "finite {a. P a}" and "\<exists>a. P a"
  shows "(LEAST a. P a) = Min {a. P a}"
proof -
  { fix A :: "'a set"
    assume A: "finite A" "A \<noteq> {}"
    have "(LEAST a. a \<in> A) = Min A"
    using A proof (induct A rule: finite_ne_induct)
      case singleton show ?case by (rule Least_equality) simp_all
    next
      case (insert a A)
      have "(LEAST b. b = a \<or> b \<in> A) = min a (LEAST a. a \<in> A)"
        by (auto intro!: Least_equality simp add: min_def not_le Min_le_iff insert.hyps dest!: less_imp_le)
      with insert show ?case by simp
    qed
  } from this [of "{a. P a}"] assms show ?thesis by simp
qed

lemma infinite_growing:
  assumes "X \<noteq> {}"
  assumes *: "\<And>x. x \<in> X \<Longrightarrow> \<exists>y\<in>X. y > x"
  shows "\<not> finite X"
proof
  assume "finite X"
  with \<open>X \<noteq> {}\<close> have "Max X \<in> X" "\<forall>x\<in>X. x \<le> Max X"
    by auto
  with *[of "Max X"] show False
    by auto
qed

end

context linordered_ab_semigroup_add
begin

lemma add_Min_commute:
  fixes k
  assumes "finite N" and "N \<noteq> {}"
  shows "k + Min N = Min {k + m | m. m \<in> N}"
proof -
  have "\<And>x y. k + min x y = min (k + x) (k + y)"
    by (simp add: min_def not_le)
      (blast intro: antisym less_imp_le add_left_mono)
  with assms show ?thesis
    using hom_Min_commute [of "plus k" N]
    by simp (blast intro: arg_cong [where f = Min])
qed

lemma add_Max_commute:
  fixes k
  assumes "finite N" and "N \<noteq> {}"
  shows "k + Max N = Max {k + m | m. m \<in> N}"
proof -
  have "\<And>x y. k + max x y = max (k + x) (k + y)"
    by (simp add: max_def not_le)
      (blast intro: antisym less_imp_le add_left_mono)
  with assms show ?thesis
    using hom_Max_commute [of "plus k" N]
    by simp (blast intro: arg_cong [where f = Max])
qed

end

context linordered_ab_group_add
begin

lemma minus_Max_eq_Min [simp]:
  "finite S \<Longrightarrow> S \<noteq> {} \<Longrightarrow> - Max S = Min (uminus ` S)"
  by (induct S rule: finite_ne_induct) (simp_all add: minus_max_eq_min)

lemma minus_Min_eq_Max [simp]:
  "finite S \<Longrightarrow> S \<noteq> {} \<Longrightarrow> - Min S = Max (uminus ` S)"
  by (induct S rule: finite_ne_induct) (simp_all add: minus_min_eq_max)

end

context complete_linorder
begin

lemma Min_Inf:
  assumes "finite A" and "A \<noteq> {}"
  shows "Min A = Inf A"
proof -
  from assms obtain b B where "A = insert b B" and "finite B" by auto
  then show ?thesis
    by (simp add: Min.eq_fold complete_linorder_inf_min [symmetric] inf_Inf_fold_inf inf.commute [of b])
qed

lemma Max_Sup:
  assumes "finite A" and "A \<noteq> {}"
  shows "Max A = Sup A"
proof -
  from assms obtain b B where "A = insert b B" and "finite B" by auto
  then show ?thesis
    by (simp add: Max.eq_fold complete_linorder_sup_max [symmetric] sup_Sup_fold_sup sup.commute [of b])
qed

end

end
