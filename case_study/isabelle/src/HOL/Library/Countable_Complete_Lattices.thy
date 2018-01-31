(*  Title:      HOL/Library/Countable_Complete_Lattices.thy
    Author:     Johannes Hölzl
*)

section \<open>Countable Complete Lattices\<close>

theory Countable_Complete_Lattices
  imports Main Countable_Set
begin

lemma UNIV_nat_eq: "UNIV = insert 0 (range Suc)"
  by (metis UNIV_eq_I nat.nchotomy insertCI rangeI)

class countable_complete_lattice = lattice + Inf + Sup + bot + top +
  assumes ccInf_lower: "countable A \<Longrightarrow> x \<in> A \<Longrightarrow> Inf A \<le> x"
  assumes ccInf_greatest: "countable A \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> z \<le> x) \<Longrightarrow> z \<le> Inf A"
  assumes ccSup_upper: "countable A \<Longrightarrow> x \<in> A \<Longrightarrow> x \<le> Sup A"
  assumes ccSup_least: "countable A \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> x \<le> z) \<Longrightarrow> Sup A \<le> z"
  assumes ccInf_empty [simp]: "Inf {} = top"
  assumes ccSup_empty [simp]: "Sup {} = bot"
begin

subclass bounded_lattice
proof
  fix a
  show "bot \<le> a" by (auto intro: ccSup_least simp only: ccSup_empty [symmetric])
  show "a \<le> top" by (auto intro: ccInf_greatest simp only: ccInf_empty [symmetric])
qed

lemma ccINF_lower: "countable A \<Longrightarrow> i \<in> A \<Longrightarrow> (INF i :A. f i) \<le> f i"
  using ccInf_lower [of "f ` A"] by simp

lemma ccINF_greatest: "countable A \<Longrightarrow> (\<And>i. i \<in> A \<Longrightarrow> u \<le> f i) \<Longrightarrow> u \<le> (INF i :A. f i)"
  using ccInf_greatest [of "f ` A"] by auto

lemma ccSUP_upper: "countable A \<Longrightarrow> i \<in> A \<Longrightarrow> f i \<le> (SUP i :A. f i)"
  using ccSup_upper [of "f ` A"] by simp

lemma ccSUP_least: "countable A \<Longrightarrow> (\<And>i. i \<in> A \<Longrightarrow> f i \<le> u) \<Longrightarrow> (SUP i :A. f i) \<le> u"
  using ccSup_least [of "f ` A"] by auto

lemma ccInf_lower2: "countable A \<Longrightarrow> u \<in> A \<Longrightarrow> u \<le> v \<Longrightarrow> Inf A \<le> v"
  using ccInf_lower [of A u] by auto

lemma ccINF_lower2: "countable A \<Longrightarrow> i \<in> A \<Longrightarrow> f i \<le> u \<Longrightarrow> (INF i :A. f i) \<le> u"
  using ccINF_lower [of A i f] by auto

lemma ccSup_upper2: "countable A \<Longrightarrow> u \<in> A \<Longrightarrow> v \<le> u \<Longrightarrow> v \<le> Sup A"
  using ccSup_upper [of A u] by auto

lemma ccSUP_upper2: "countable A \<Longrightarrow> i \<in> A \<Longrightarrow> u \<le> f i \<Longrightarrow> u \<le> (SUP i :A. f i)"
  using ccSUP_upper [of A i f] by auto

lemma le_ccInf_iff: "countable A \<Longrightarrow> b \<le> Inf A \<longleftrightarrow> (\<forall>a\<in>A. b \<le> a)"
  by (auto intro: ccInf_greatest dest: ccInf_lower)

lemma le_ccINF_iff: "countable A \<Longrightarrow> u \<le> (INF i :A. f i) \<longleftrightarrow> (\<forall>i\<in>A. u \<le> f i)"
  using le_ccInf_iff [of "f ` A"] by simp

lemma ccSup_le_iff: "countable A \<Longrightarrow> Sup A \<le> b \<longleftrightarrow> (\<forall>a\<in>A. a \<le> b)"
  by (auto intro: ccSup_least dest: ccSup_upper)

lemma ccSUP_le_iff: "countable A \<Longrightarrow> (SUP i :A. f i) \<le> u \<longleftrightarrow> (\<forall>i\<in>A. f i \<le> u)"
  using ccSup_le_iff [of "f ` A"] by simp

lemma ccInf_insert [simp]: "countable A \<Longrightarrow> Inf (insert a A) = inf a (Inf A)"
  by (force intro: le_infI le_infI1 le_infI2 antisym ccInf_greatest ccInf_lower)

lemma ccINF_insert [simp]: "countable A \<Longrightarrow> (INF x:insert a A. f x) = inf (f a) (INFIMUM A f)"
  unfolding image_insert by simp

lemma ccSup_insert [simp]: "countable A \<Longrightarrow> Sup (insert a A) = sup a (Sup A)"
  by (force intro: le_supI le_supI1 le_supI2 antisym ccSup_least ccSup_upper)

lemma ccSUP_insert [simp]: "countable A \<Longrightarrow> (SUP x:insert a A. f x) = sup (f a) (SUPREMUM A f)"
  unfolding image_insert by simp

lemma ccINF_empty [simp]: "(INF x:{}. f x) = top"
  unfolding image_empty by simp

lemma ccSUP_empty [simp]: "(SUP x:{}. f x) = bot"
  unfolding image_empty by simp

lemma ccInf_superset_mono: "countable A \<Longrightarrow> B \<subseteq> A \<Longrightarrow> Inf A \<le> Inf B"
  by (auto intro: ccInf_greatest ccInf_lower countable_subset)

lemma ccSup_subset_mono: "countable B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> Sup A \<le> Sup B"
  by (auto intro: ccSup_least ccSup_upper countable_subset)

lemma ccInf_mono:
  assumes [intro]: "countable B" "countable A"
  assumes "\<And>b. b \<in> B \<Longrightarrow> \<exists>a\<in>A. a \<le> b"
  shows "Inf A \<le> Inf B"
proof (rule ccInf_greatest)
  fix b assume "b \<in> B"
  with assms obtain a where "a \<in> A" and "a \<le> b" by blast
  from \<open>a \<in> A\<close> have "Inf A \<le> a" by (rule ccInf_lower[rotated]) auto
  with \<open>a \<le> b\<close> show "Inf A \<le> b" by auto
qed auto

lemma ccINF_mono:
  "countable A \<Longrightarrow> countable B \<Longrightarrow> (\<And>m. m \<in> B \<Longrightarrow> \<exists>n\<in>A. f n \<le> g m) \<Longrightarrow> (INF n:A. f n) \<le> (INF n:B. g n)"
  using ccInf_mono [of "g ` B" "f ` A"] by auto

lemma ccSup_mono:
  assumes [intro]: "countable B" "countable A"
  assumes "\<And>a. a \<in> A \<Longrightarrow> \<exists>b\<in>B. a \<le> b"
  shows "Sup A \<le> Sup B"
proof (rule ccSup_least)
  fix a assume "a \<in> A"
  with assms obtain b where "b \<in> B" and "a \<le> b" by blast
  from \<open>b \<in> B\<close> have "b \<le> Sup B" by (rule ccSup_upper[rotated]) auto
  with \<open>a \<le> b\<close> show "a \<le> Sup B" by auto
qed auto

lemma ccSUP_mono:
  "countable A \<Longrightarrow> countable B \<Longrightarrow> (\<And>n. n \<in> A \<Longrightarrow> \<exists>m\<in>B. f n \<le> g m) \<Longrightarrow> (SUP n:A. f n) \<le> (SUP n:B. g n)"
  using ccSup_mono [of "g ` B" "f ` A"] by auto

lemma ccINF_superset_mono:
  "countable A \<Longrightarrow> B \<subseteq> A \<Longrightarrow> (\<And>x. x \<in> B \<Longrightarrow> f x \<le> g x) \<Longrightarrow> (INF x:A. f x) \<le> (INF x:B. g x)"
  by (blast intro: ccINF_mono countable_subset dest: subsetD)

lemma ccSUP_subset_mono:
  "countable B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> f x \<le> g x) \<Longrightarrow> (SUP x:A. f x) \<le> (SUP x:B. g x)"
  by (blast intro: ccSUP_mono countable_subset dest: subsetD)


lemma less_eq_ccInf_inter: "countable A \<Longrightarrow> countable B \<Longrightarrow> sup (Inf A) (Inf B) \<le> Inf (A \<inter> B)"
  by (auto intro: ccInf_greatest ccInf_lower)

lemma ccSup_inter_less_eq: "countable A \<Longrightarrow> countable B \<Longrightarrow> Sup (A \<inter> B) \<le> inf (Sup A) (Sup B)"
  by (auto intro: ccSup_least ccSup_upper)

lemma ccInf_union_distrib: "countable A \<Longrightarrow> countable B \<Longrightarrow> Inf (A \<union> B) = inf (Inf A) (Inf B)"
  by (rule antisym) (auto intro: ccInf_greatest ccInf_lower le_infI1 le_infI2)

lemma ccINF_union:
  "countable A \<Longrightarrow> countable B \<Longrightarrow> (INF i:A \<union> B. M i) = inf (INF i:A. M i) (INF i:B. M i)"
  by (auto intro!: antisym ccINF_mono intro: le_infI1 le_infI2 ccINF_greatest ccINF_lower)

lemma ccSup_union_distrib: "countable A \<Longrightarrow> countable B \<Longrightarrow> Sup (A \<union> B) = sup (Sup A) (Sup B)"
  by (rule antisym) (auto intro: ccSup_least ccSup_upper le_supI1 le_supI2)

lemma ccSUP_union:
  "countable A \<Longrightarrow> countable B \<Longrightarrow> (SUP i:A \<union> B. M i) = sup (SUP i:A. M i) (SUP i:B. M i)"
  by (auto intro!: antisym ccSUP_mono intro: le_supI1 le_supI2 ccSUP_least ccSUP_upper)

lemma ccINF_inf_distrib: "countable A \<Longrightarrow> inf (INF a:A. f a) (INF a:A. g a) = (INF a:A. inf (f a) (g a))"
  by (rule antisym) (rule ccINF_greatest, auto intro: le_infI1 le_infI2 ccINF_lower ccINF_mono)

lemma ccSUP_sup_distrib: "countable A \<Longrightarrow> sup (SUP a:A. f a) (SUP a:A. g a) = (SUP a:A. sup (f a) (g a))"
  by (rule antisym[rotated]) (rule ccSUP_least, auto intro: le_supI1 le_supI2 ccSUP_upper ccSUP_mono)

lemma ccINF_const [simp]: "A \<noteq> {} \<Longrightarrow> (INF i :A. f) = f"
  unfolding image_constant_conv by auto

lemma ccSUP_const [simp]: "A \<noteq> {} \<Longrightarrow> (SUP i :A. f) = f"
  unfolding image_constant_conv by auto

lemma ccINF_top [simp]: "(INF x:A. top) = top"
  by (cases "A = {}") simp_all

lemma ccSUP_bot [simp]: "(SUP x:A. bot) = bot"
  by (cases "A = {}") simp_all

lemma ccINF_commute: "countable A \<Longrightarrow> countable B \<Longrightarrow> (INF i:A. INF j:B. f i j) = (INF j:B. INF i:A. f i j)"
  by (iprover intro: ccINF_lower ccINF_greatest order_trans antisym)

lemma ccSUP_commute: "countable A \<Longrightarrow> countable B \<Longrightarrow> (SUP i:A. SUP j:B. f i j) = (SUP j:B. SUP i:A. f i j)"
  by (iprover intro: ccSUP_upper ccSUP_least order_trans antisym)

end

context
  fixes a :: "'a::{countable_complete_lattice, linorder}"
begin

lemma less_ccSup_iff: "countable S \<Longrightarrow> a < Sup S \<longleftrightarrow> (\<exists>x\<in>S. a < x)"
  unfolding not_le [symmetric] by (subst ccSup_le_iff) auto

lemma less_ccSUP_iff: "countable A \<Longrightarrow> a < (SUP i:A. f i) \<longleftrightarrow> (\<exists>x\<in>A. a < f x)"
  using less_ccSup_iff [of "f ` A"] by simp

lemma ccInf_less_iff: "countable S \<Longrightarrow> Inf S < a \<longleftrightarrow> (\<exists>x\<in>S. x < a)"
  unfolding not_le [symmetric] by (subst le_ccInf_iff) auto

lemma ccINF_less_iff: "countable A \<Longrightarrow> (INF i:A. f i) < a \<longleftrightarrow> (\<exists>x\<in>A. f x < a)"
  using ccInf_less_iff [of "f ` A"] by simp

end

class countable_complete_distrib_lattice = countable_complete_lattice +
  assumes sup_ccInf: "countable B \<Longrightarrow> sup a (Inf B) = (INF b:B. sup a b)"
  assumes inf_ccSup: "countable B \<Longrightarrow> inf a (Sup B) = (SUP b:B. inf a b)"
begin

lemma sup_ccINF:
  "countable B \<Longrightarrow> sup a (INF b:B. f b) = (INF b:B. sup a (f b))"
  by (simp only: sup_ccInf image_image countable_image)

lemma inf_ccSUP:
  "countable B \<Longrightarrow> inf a (SUP b:B. f b) = (SUP b:B. inf a (f b))"
  by (simp only: inf_ccSup image_image countable_image)

subclass distrib_lattice
proof
  fix a b c
  from sup_ccInf[of "{b, c}" a] have "sup a (Inf {b, c}) = (INF d:{b, c}. sup a d)"
    by simp
  then show "sup a (inf b c) = inf (sup a b) (sup a c)"
    by simp
qed

lemma ccInf_sup:
  "countable B \<Longrightarrow> sup (Inf B) a = (INF b:B. sup b a)"
  by (simp add: sup_ccInf sup_commute)

lemma ccSup_inf:
  "countable B \<Longrightarrow> inf (Sup B) a = (SUP b:B. inf b a)"
  by (simp add: inf_ccSup inf_commute)

lemma ccINF_sup:
  "countable B \<Longrightarrow> sup (INF b:B. f b) a = (INF b:B. sup (f b) a)"
  by (simp add: sup_ccINF sup_commute)

lemma ccSUP_inf:
  "countable B \<Longrightarrow> inf (SUP b:B. f b) a = (SUP b:B. inf (f b) a)"
  by (simp add: inf_ccSUP inf_commute)

lemma ccINF_sup_distrib2:
  "countable A \<Longrightarrow> countable B \<Longrightarrow> sup (INF a:A. f a) (INF b:B. g b) = (INF a:A. INF b:B. sup (f a) (g b))"
  by (subst ccINF_commute) (simp_all add: sup_ccINF ccINF_sup)

lemma ccSUP_inf_distrib2:
  "countable A \<Longrightarrow> countable B \<Longrightarrow> inf (SUP a:A. f a) (SUP b:B. g b) = (SUP a:A. SUP b:B. inf (f a) (g b))"
  by (subst ccSUP_commute) (simp_all add: inf_ccSUP ccSUP_inf)

context
  fixes f :: "'a \<Rightarrow> 'b::countable_complete_lattice"
  assumes "mono f"
begin

lemma mono_ccInf:
  "countable A \<Longrightarrow> f (Inf A) \<le> (INF x:A. f x)"
  using \<open>mono f\<close>
  by (auto intro!: countable_complete_lattice_class.ccINF_greatest intro: ccInf_lower dest: monoD)

lemma mono_ccSup:
  "countable A \<Longrightarrow> (SUP x:A. f x) \<le> f (Sup A)"
  using \<open>mono f\<close> by (auto intro: countable_complete_lattice_class.ccSUP_least ccSup_upper dest: monoD)

lemma mono_ccINF:
  "countable I \<Longrightarrow> f (INF i : I. A i) \<le> (INF x : I. f (A x))"
  by (intro countable_complete_lattice_class.ccINF_greatest monoD[OF \<open>mono f\<close>] ccINF_lower)

lemma mono_ccSUP:
  "countable I \<Longrightarrow> (SUP x : I. f (A x)) \<le> f (SUP i : I. A i)"
  by (intro countable_complete_lattice_class.ccSUP_least monoD[OF \<open>mono f\<close>] ccSUP_upper)

end

end

subsubsection \<open>Instances of countable complete lattices\<close>

instance "fun" :: (type, countable_complete_lattice) countable_complete_lattice
  by standard
     (auto simp: le_fun_def intro!: ccSUP_upper ccSUP_least ccINF_lower ccINF_greatest)

subclass (in complete_lattice) countable_complete_lattice
  by standard (auto intro: Sup_upper Sup_least Inf_lower Inf_greatest)

subclass (in complete_distrib_lattice) countable_complete_distrib_lattice
  by standard (auto intro: sup_Inf inf_Sup)

end
