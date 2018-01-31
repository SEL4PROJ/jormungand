(*  Title:      HOL/Library/Finite_Map.thy
    Author:     Lars Hupel, TU München
*)

section \<open>Type of finite maps defined as a subtype of maps\<close>

theory Finite_Map
  imports FSet AList
begin

subsection \<open>Auxiliary constants and lemmas over @{type map}\<close>

context includes lifting_syntax begin

abbreviation rel_map :: "('b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'c) \<Rightarrow> bool" where
"rel_map f \<equiv> op = ===> rel_option f"

lemma map_empty_transfer[transfer_rule]: "rel_map A Map.empty Map.empty"
by transfer_prover

lemma ran_transfer[transfer_rule]: "(rel_map A ===> rel_set A) ran ran"
proof
  fix m n
  assume "rel_map A m n"
  show "rel_set A (ran m) (ran n)"
    proof (rule rel_setI)
      fix x
      assume "x \<in> ran m"
      then obtain a where "m a = Some x"
        unfolding ran_def by auto

      have "rel_option A (m a) (n a)"
        using \<open>rel_map A m n\<close>
        by (auto dest: rel_funD)
      then obtain y where "n a = Some y" "A x y"
        unfolding \<open>m a = _\<close>
        by cases auto
      then show "\<exists>y \<in> ran n. A x y"
        unfolding ran_def by blast
    next
      fix y
      assume "y \<in> ran n"
      then obtain a where "n a = Some y"
        unfolding ran_def by auto

      have "rel_option A (m a) (n a)"
        using \<open>rel_map A m n\<close>
        by (auto dest: rel_funD)
      then obtain x where "m a = Some x" "A x y"
        unfolding \<open>n a = _\<close>
        by cases auto
      then show "\<exists>x \<in> ran m. A x y"
        unfolding ran_def by blast
    qed
qed

lemma ran_alt_def: "ran m = (the \<circ> m) ` dom m"
unfolding ran_def dom_def by force

lemma dom_transfer[transfer_rule]: "(rel_map A ===> op =) dom dom"
proof
  fix m n
  assume "rel_map A m n"
  have "m a \<noteq> None \<longleftrightarrow> n a \<noteq> None" for a
    proof -
      from \<open>rel_map A m n\<close> have "rel_option A (m a) (n a)"
        unfolding rel_fun_def by auto
      then show ?thesis
        by cases auto
    qed
  then show "dom m = dom n"
    by auto
qed

definition map_upd :: "'a \<Rightarrow> 'b \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b)" where
"map_upd k v m = m(k \<mapsto> v)"

lemma map_upd_transfer[transfer_rule]:
  "(op = ===> A ===> rel_map A ===> rel_map A) map_upd map_upd"
unfolding map_upd_def[abs_def]
by transfer_prover

definition map_filter :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b)" where
"map_filter P m = (\<lambda>x. if P x then m x else None)"

lemma map_filter_map_of[simp]: "map_filter P (map_of m) = map_of [(k, _) \<leftarrow> m. P k]"
proof
  fix x
  show "map_filter P (map_of m) x = map_of [(k, _) \<leftarrow> m. P k] x"
    by (induct m) (auto simp: map_filter_def)
qed

lemma map_filter_transfer[transfer_rule]:
  "(op = ===> rel_map A ===> rel_map A) map_filter map_filter"
unfolding map_filter_def[abs_def]
by transfer_prover

lemma map_filter_finite[intro]:
  assumes "finite (dom m)"
  shows "finite (dom (map_filter P m))"
proof -
  have "dom (map_filter P m) = Set.filter P (dom m)"
    unfolding map_filter_def Set.filter_def dom_def
    by auto
  then show ?thesis
    using assms
    by (simp add: Set.filter_def)
qed

definition map_drop :: "'a \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b)" where
"map_drop a = map_filter (\<lambda>a'. a' \<noteq> a)"

lemma map_drop_transfer[transfer_rule]:
  "(op = ===> rel_map A ===> rel_map A) map_drop map_drop"
unfolding map_drop_def[abs_def]
by transfer_prover

definition map_drop_set :: "'a set \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b)" where
"map_drop_set A = map_filter (\<lambda>a. a \<notin> A)"

lemma map_drop_set_transfer[transfer_rule]:
  "(op = ===> rel_map A ===> rel_map A) map_drop_set map_drop_set"
unfolding map_drop_set_def[abs_def]
by transfer_prover

definition map_restrict_set :: "'a set \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b)" where
"map_restrict_set A = map_filter (\<lambda>a. a \<in> A)"

lemma map_restrict_set_transfer[transfer_rule]:
  "(op = ===> rel_map A ===> rel_map A) map_restrict_set map_restrict_set"
unfolding map_restrict_set_def[abs_def]
by transfer_prover

lemma map_add_transfer[transfer_rule]:
  "(rel_map A ===> rel_map A ===> rel_map A) op ++ op ++"
unfolding map_add_def[abs_def]
by transfer_prover

definition map_pred :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> bool" where
"map_pred P m \<longleftrightarrow> (\<forall>x. case m x of None \<Rightarrow> True | Some y \<Rightarrow> P x y)"

lemma map_pred_transfer[transfer_rule]:
  "((op = ===> A ===> op =) ===> rel_map A ===> op =) map_pred map_pred"
unfolding map_pred_def[abs_def]
by transfer_prover

definition rel_map_on_set :: "'a set \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'c) \<Rightarrow> bool" where
"rel_map_on_set S P = eq_onp (\<lambda>x. x \<in> S) ===> rel_option P"
  
lemma map_of_transfer[transfer_rule]:
  includes lifting_syntax
  shows "(list_all2 (rel_prod op = A) ===> rel_map A) map_of map_of"
unfolding map_of_def by transfer_prover
  
end


subsection \<open>Abstract characterisation\<close>

typedef ('a, 'b) fmap = "{m. finite (dom m)} :: ('a \<rightharpoonup> 'b) set"
  morphisms fmlookup Abs_fmap
proof
  show "Map.empty \<in> {m. finite (dom m)}"
    by auto
qed

setup_lifting type_definition_fmap

lemma fmlookup_finite[intro, simp]: "finite (dom (fmlookup m))"
using fmap.fmlookup by auto

lemma fmap_ext:
  assumes "\<And>x. fmlookup m x = fmlookup n x"
  shows "m = n"
using assms
by transfer' auto


subsection \<open>Operations\<close>

context
  includes fset.lifting
begin

lift_definition fmran :: "('a, 'b) fmap \<Rightarrow> 'b fset"
  is ran
  parametric ran_transfer
unfolding ran_alt_def by auto

lemma fmranI: "fmlookup m x = Some y \<Longrightarrow> y |\<in>| fmran m" by transfer' (auto simp: ran_def)

lift_definition fmdom :: "('a, 'b) fmap \<Rightarrow> 'a fset"
  is dom
  parametric dom_transfer
.

lemma fmdom_notI: "fmlookup m x = None \<Longrightarrow> x |\<notin>| fmdom m" by transfer' auto
lemma fmdomI: "fmlookup m x = Some y \<Longrightarrow> x |\<in>| fmdom m" by transfer' auto
lemma fmdom_notD: "x |\<notin>| fmdom m \<Longrightarrow> fmlookup m x = None" by transfer' auto

lift_definition fmdom' :: "('a, 'b) fmap \<Rightarrow> 'a set"
  is dom
  parametric dom_transfer
.

lemma fmdom'_notI: "fmlookup m x = None \<Longrightarrow> x \<notin> fmdom' m" by transfer' auto
lemma fmdom'I: "fmlookup m x = Some y \<Longrightarrow> x \<in> fmdom' m" by transfer' auto
lemma fmdom'_notD: "x \<notin> fmdom' m \<Longrightarrow> fmlookup m x = None" by transfer' auto

lemma fmdom'_alt_def: "fmdom' = fset \<circ> fmdom"
by transfer' force

lemma fmlookup_dom_iff: "x |\<in>| fmdom m \<longleftrightarrow> (\<exists>a. fmlookup m x = Some a)"
by transfer' auto

lift_definition fmempty :: "('a, 'b) fmap"
  is Map.empty
  parametric map_empty_transfer
by simp

lemma fmempty_lookup[simp]: "fmlookup fmempty x = None"
by transfer' simp

lemma fmdom_empty[simp]: "fmdom fmempty = {||}" by transfer' simp
lemma fmdom'_empty[simp]: "fmdom' fmempty = {}" by transfer' simp

lift_definition fmupd :: "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap"
  is map_upd
  parametric map_upd_transfer
unfolding map_upd_def[abs_def]
by simp

lemma fmupd_lookup[simp]: "fmlookup (fmupd a b m) a' = (if a = a' then Some b else fmlookup m a')"
by transfer' (auto simp: map_upd_def)

lemma fmdom_fmupd[simp]: "fmdom (fmupd a b m) = finsert a (fmdom m)" by transfer (simp add: map_upd_def)
lemma fmdom'_fmupd[simp]: "fmdom' (fmupd a b m) = insert a (fmdom' m)" by transfer (simp add: map_upd_def)

lift_definition fmfilter :: "('a \<Rightarrow> bool) \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap"
  is map_filter
  parametric map_filter_transfer
by auto

lemma fmdom_filter[simp]: "fmdom (fmfilter P m) = ffilter P (fmdom m)"
by transfer' (auto simp: map_filter_def Set.filter_def split: if_splits)

lemma fmdom'_filter[simp]: "fmdom' (fmfilter P m) = Set.filter P (fmdom' m)"
by transfer' (auto simp: map_filter_def Set.filter_def split: if_splits)

lemma fmlookup_filter[simp]: "fmlookup (fmfilter P m) x = (if P x then fmlookup m x else None)"
by transfer' (auto simp: map_filter_def)

lemma fmfilter_empty[simp]: "fmfilter P fmempty = fmempty"
by transfer' (auto simp: map_filter_def)

lemma fmfilter_true[simp]:
  assumes "\<And>x. x |\<in>| fmdom m \<Longrightarrow> P x"
  shows "fmfilter P m = m"
proof (rule fmap_ext)
  fix x
  have "fmlookup m x = None" if "\<not> P x"
    using that assms
    unfolding fmlookup_dom_iff by fastforce
  then show "fmlookup (fmfilter P m) x = fmlookup m x"
    by simp
qed

lemma fmfilter_false[simp]: "(\<And>x. x |\<in>| fmdom m \<Longrightarrow> \<not> P x) \<Longrightarrow> fmfilter P m = fmempty"
by transfer' (auto simp: map_filter_def fun_eq_iff)

lemma fmfilter_comp[simp]: "fmfilter P (fmfilter Q m) = fmfilter (\<lambda>x. P x \<and> Q x) m"
by transfer' (auto simp: map_filter_def)

lemma fmfilter_comm: "fmfilter P (fmfilter Q m) = fmfilter Q (fmfilter P m)"
unfolding fmfilter_comp by meson

lemma fmfilter_cong[cong]:
  assumes "\<And>x. x |\<in>| fmdom m \<Longrightarrow> P x = Q x"
  shows "fmfilter P m = fmfilter Q m"
proof (rule fmap_ext)
  fix x
  have "fmlookup m x = None" if "P x \<noteq> Q x"
    using that assms
    unfolding fmlookup_dom_iff by fastforce
  then show "fmlookup (fmfilter P m) x = fmlookup (fmfilter Q m) x"
    by auto
qed

lemma fmfilter_cong'[fundef_cong]:
  assumes "\<And>x. x \<in> fmdom' m \<Longrightarrow> P x = Q x"
  shows "fmfilter P m = fmfilter Q m"
proof (rule fmfilter_cong)
  fix x
  assume "x |\<in>| fmdom m"
  then show "P x = Q x"
    using assms
    unfolding fmdom'_alt_def fmember.rep_eq
    by auto
qed

lemma fmfilter_upd[simp]:
  "fmfilter P (fmupd x y m) = (if P x then fmupd x y (fmfilter P m) else fmfilter P m)"
by transfer' (auto simp: map_upd_def map_filter_def)

lift_definition fmdrop :: "'a \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap"
  is map_drop
  parametric map_drop_transfer
unfolding map_drop_def by auto

lemma fmdrop_lookup[simp]: "fmlookup (fmdrop a m) a = None"
by transfer' (auto simp: map_drop_def map_filter_def)

lift_definition fmdrop_set :: "'a set \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap"
  is map_drop_set
  parametric map_drop_set_transfer
unfolding map_drop_set_def by auto

lift_definition fmdrop_fset :: "'a fset \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap"
  is map_drop_set
  parametric map_drop_set_transfer
unfolding map_drop_set_def by auto

lift_definition fmrestrict_set :: "'a set \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap"
  is map_restrict_set
  parametric map_restrict_set_transfer
unfolding map_restrict_set_def by auto

lift_definition fmrestrict_fset :: "'a fset \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap"
  is map_restrict_set
  parametric map_restrict_set_transfer
unfolding map_restrict_set_def by auto

lemma fmfilter_alt_defs:
  "fmdrop a = fmfilter (\<lambda>a'. a' \<noteq> a)"
  "fmdrop_set A = fmfilter (\<lambda>a. a \<notin> A)"
  "fmdrop_fset B = fmfilter (\<lambda>a. a |\<notin>| B)"
  "fmrestrict_set A = fmfilter (\<lambda>a. a \<in> A)"
  "fmrestrict_fset B = fmfilter (\<lambda>a. a |\<in>| B)"
by (transfer'; simp add: map_drop_def map_drop_set_def map_restrict_set_def)+

lemma fmdom_drop[simp]: "fmdom (fmdrop a m) = fmdom m - {|a|}" unfolding fmfilter_alt_defs by auto
lemma fmdom'_drop[simp]: "fmdom' (fmdrop a m) = fmdom' m - {a}" unfolding fmfilter_alt_defs by auto
lemma fmdom'_drop_set[simp]: "fmdom' (fmdrop_set A m) = fmdom' m - A" unfolding fmfilter_alt_defs by auto
lemma fmdom_drop_fset[simp]: "fmdom (fmdrop_fset A m) = fmdom m - A" unfolding fmfilter_alt_defs by auto
lemma fmdom'_restrict_set: "fmdom' (fmrestrict_set A m) \<subseteq> A" unfolding fmfilter_alt_defs by auto
lemma fmdom_restrict_fset: "fmdom (fmrestrict_fset A m) |\<subseteq>| A" unfolding fmfilter_alt_defs by auto

lemma fmdom'_drop_fset[simp]: "fmdom' (fmdrop_fset A m) = fmdom' m - fset A"
unfolding fmfilter_alt_defs by transfer' (auto simp: map_filter_def split: if_splits)

lemma fmdom'_restrict_fset: "fmdom' (fmrestrict_fset A m) \<subseteq> fset A"
unfolding fmfilter_alt_defs by transfer' (auto simp: map_filter_def)

lemma fmlookup_drop[simp]:
  "fmlookup (fmdrop a m) x = (if x \<noteq> a then fmlookup m x else None)"
unfolding fmfilter_alt_defs by simp

lemma fmlookup_drop_set[simp]:
  "fmlookup (fmdrop_set A m) x = (if x \<notin> A then fmlookup m x else None)"
unfolding fmfilter_alt_defs by simp

lemma fmlookup_drop_fset[simp]:
  "fmlookup (fmdrop_fset A m) x = (if x |\<notin>| A then fmlookup m x else None)"
unfolding fmfilter_alt_defs by simp

lemma fmlookup_restrict_set[simp]:
  "fmlookup (fmrestrict_set A m) x = (if x \<in> A then fmlookup m x else None)"
unfolding fmfilter_alt_defs by simp

lemma fmlookup_restrict_fset[simp]:
  "fmlookup (fmrestrict_fset A m) x = (if x |\<in>| A then fmlookup m x else None)"
unfolding fmfilter_alt_defs by simp

lemma fmrestrict_set_dom[simp]: "fmrestrict_set (fmdom' m) m = m"
  by (rule fmap_ext) (auto dest: fmdom'_notD)

lemma fmrestrict_fset_dom[simp]: "fmrestrict_fset (fmdom m) m = m"
  by (rule fmap_ext) (auto dest: fmdom_notD)

lemma fmdrop_empty[simp]: "fmdrop a fmempty = fmempty"
  unfolding fmfilter_alt_defs by simp

lemma fmdrop_set_empty[simp]: "fmdrop_set A fmempty = fmempty"
  unfolding fmfilter_alt_defs by simp

lemma fmdrop_fset_empty[simp]: "fmdrop_fset A fmempty = fmempty"
  unfolding fmfilter_alt_defs by simp

lemma fmrestrict_set_empty[simp]: "fmrestrict_set A fmempty = fmempty"
  unfolding fmfilter_alt_defs by simp

lemma fmrestrict_fset_empty[simp]: "fmrestrict_fset A fmempty = fmempty"
  unfolding fmfilter_alt_defs by simp

lemma fmdrop_set_single[simp]: "fmdrop_set {a} m = fmdrop a m"
  unfolding fmfilter_alt_defs by simp

lemma fmdrop_fset_single[simp]: "fmdrop_fset {|a|} m = fmdrop a m"
  unfolding fmfilter_alt_defs by simp

lemma fmrestrict_set_null[simp]: "fmrestrict_set {} m = fmempty"
  unfolding fmfilter_alt_defs by simp

lemma fmrestrict_fset_null[simp]: "fmrestrict_fset {||} m = fmempty"
  unfolding fmfilter_alt_defs by simp

lemma fmdrop_comm: "fmdrop a (fmdrop b m) = fmdrop b (fmdrop a m)"
unfolding fmfilter_alt_defs by (rule fmfilter_comm)

lift_definition fmadd :: "('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap" (infixl "++\<^sub>f" 100)
  is map_add
  parametric map_add_transfer
by simp

lemma fmlookup_add[simp]:
  "fmlookup (m ++\<^sub>f n) x = (if x |\<in>| fmdom n then fmlookup n x else fmlookup m x)"
  by transfer' (auto simp: map_add_def split: option.splits)

lemma fmdom_add[simp]: "fmdom (m ++\<^sub>f n) = fmdom m |\<union>| fmdom n" by transfer' auto
lemma fmdom'_add[simp]: "fmdom' (m ++\<^sub>f n) = fmdom' m \<union> fmdom' n" by transfer' auto

lemma fmadd_drop_left_dom: "fmdrop_fset (fmdom n) m ++\<^sub>f n = m ++\<^sub>f n"
  by (rule fmap_ext) auto

lemma fmadd_restrict_right_dom: "fmrestrict_fset (fmdom n) (m ++\<^sub>f n) = n"
  by (rule fmap_ext) (auto dest: fmdom_notD)

lemma fmfilter_add_distrib[simp]: "fmfilter P (m ++\<^sub>f n) = fmfilter P m ++\<^sub>f fmfilter P n"
by transfer' (auto simp: map_filter_def map_add_def)

lemma fmdrop_add_distrib[simp]: "fmdrop a (m ++\<^sub>f n) = fmdrop a m ++\<^sub>f fmdrop a n"
  unfolding fmfilter_alt_defs by simp

lemma fmdrop_set_add_distrib[simp]: "fmdrop_set A (m ++\<^sub>f n) = fmdrop_set A m ++\<^sub>f fmdrop_set A n"
  unfolding fmfilter_alt_defs by simp

lemma fmdrop_fset_add_distrib[simp]: "fmdrop_fset A (m ++\<^sub>f n) = fmdrop_fset A m ++\<^sub>f fmdrop_fset A n"
  unfolding fmfilter_alt_defs by simp

lemma fmrestrict_set_add_distrib[simp]:
  "fmrestrict_set A (m ++\<^sub>f n) = fmrestrict_set A m ++\<^sub>f fmrestrict_set A n"
  unfolding fmfilter_alt_defs by simp

lemma fmrestrict_fset_add_distrib[simp]:
  "fmrestrict_fset A (m ++\<^sub>f n) = fmrestrict_fset A m ++\<^sub>f fmrestrict_fset A n"
  unfolding fmfilter_alt_defs by simp

lemma fmadd_empty[simp]: "fmempty ++\<^sub>f m = m" "m ++\<^sub>f fmempty = m"
by (transfer'; auto)+

lemma fmadd_idempotent[simp]: "m ++\<^sub>f m = m"
by transfer' (auto simp: map_add_def split: option.splits)

lemma fmadd_assoc[simp]: "m ++\<^sub>f (n ++\<^sub>f p) = m ++\<^sub>f n ++\<^sub>f p"
by transfer' simp

lift_definition fmpred :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a, 'b) fmap \<Rightarrow> bool"
  is map_pred
  parametric map_pred_transfer
.

lemma fmpredI[intro]:
  assumes "\<And>x y. fmlookup m x = Some y \<Longrightarrow> P x y"
  shows "fmpred P m"
using assms
by transfer' (auto simp: map_pred_def split: option.splits)

lemma fmpredD[dest]: "fmpred P m \<Longrightarrow> fmlookup m x = Some y \<Longrightarrow> P x y" 
by transfer' (auto simp: map_pred_def split: option.split_asm)

lemma fmpred_iff: "fmpred P m \<longleftrightarrow> (\<forall>x y. fmlookup m x = Some y \<longrightarrow> P x y)"
by auto

lemma fmpred_alt_def: "fmpred P m \<longleftrightarrow> fBall (fmdom m) (\<lambda>x. P x (the (fmlookup m x)))"
unfolding fmpred_iff
apply auto
apply (subst (asm) fmlookup_dom_iff)
apply simp
apply (rename_tac x y)
apply (erule_tac x = x in fBallE)
apply simp
by (simp add: fmlookup_dom_iff)

lemma fmpred_empty[intro!, simp]: "fmpred P fmempty"
by auto

lemma fmpred_upd[intro]: "fmpred P m \<Longrightarrow> P x y \<Longrightarrow> fmpred P (fmupd x y m)"
by transfer' (auto simp: map_pred_def map_upd_def)

lemma fmpred_updD[dest]: "fmpred P (fmupd x y m) \<Longrightarrow> P x y"
by auto

lemma fmpred_add[intro]: "fmpred P m \<Longrightarrow> fmpred P n \<Longrightarrow> fmpred P (m ++\<^sub>f n)"
by transfer' (auto simp: map_pred_def map_add_def split: option.splits)

lemma fmpred_filter[intro]: "fmpred P m \<Longrightarrow> fmpred P (fmfilter Q m)"
by transfer' (auto simp: map_pred_def map_filter_def)

lemma fmpred_drop[intro]: "fmpred P m \<Longrightarrow> fmpred P (fmdrop a m)"
  by (auto simp: fmfilter_alt_defs)

lemma fmpred_drop_set[intro]: "fmpred P m \<Longrightarrow> fmpred P (fmdrop_set A m)"
  by (auto simp: fmfilter_alt_defs)

lemma fmpred_drop_fset[intro]: "fmpred P m \<Longrightarrow> fmpred P (fmdrop_fset A m)"
  by (auto simp: fmfilter_alt_defs)

lemma fmpred_restrict_set[intro]: "fmpred P m \<Longrightarrow> fmpred P (fmrestrict_set A m)"
  by (auto simp: fmfilter_alt_defs)

lemma fmpred_restrict_fset[intro]: "fmpred P m \<Longrightarrow> fmpred P (fmrestrict_fset A m)"
  by (auto simp: fmfilter_alt_defs)

lemma fmpred_cases[consumes 1]:
  assumes "fmpred P m"
  obtains (none) "fmlookup m x = None" | (some) y where "fmlookup m x = Some y" "P x y"
using assms by auto

lift_definition fmsubset :: "('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap \<Rightarrow> bool" (infix "\<subseteq>\<^sub>f" 50)
  is map_le
.

lemma fmsubset_alt_def: "m \<subseteq>\<^sub>f n \<longleftrightarrow> fmpred (\<lambda>k v. fmlookup n k = Some v) m"
by transfer' (auto simp: map_pred_def map_le_def dom_def split: option.splits)

lemma fmsubset_pred: "fmpred P m \<Longrightarrow> n \<subseteq>\<^sub>f m \<Longrightarrow> fmpred P n"
unfolding fmsubset_alt_def fmpred_iff
by auto

lemma fmsubset_filter_mono: "m \<subseteq>\<^sub>f n \<Longrightarrow> fmfilter P m \<subseteq>\<^sub>f fmfilter P n"
unfolding fmsubset_alt_def fmpred_iff
by auto

lemma fmsubset_drop_mono: "m \<subseteq>\<^sub>f n \<Longrightarrow> fmdrop a m \<subseteq>\<^sub>f fmdrop a n"
unfolding fmfilter_alt_defs by (rule fmsubset_filter_mono)

lemma fmsubset_drop_set_mono: "m \<subseteq>\<^sub>f n \<Longrightarrow> fmdrop_set A m \<subseteq>\<^sub>f fmdrop_set A n"
unfolding fmfilter_alt_defs by (rule fmsubset_filter_mono)

lemma fmsubset_drop_fset_mono: "m \<subseteq>\<^sub>f n \<Longrightarrow> fmdrop_fset A m \<subseteq>\<^sub>f fmdrop_fset A n"
unfolding fmfilter_alt_defs by (rule fmsubset_filter_mono)

lemma fmsubset_restrict_set_mono: "m \<subseteq>\<^sub>f n \<Longrightarrow> fmrestrict_set A m \<subseteq>\<^sub>f fmrestrict_set A n"
unfolding fmfilter_alt_defs by (rule fmsubset_filter_mono)

lemma fmsubset_restrict_fset_mono: "m \<subseteq>\<^sub>f n \<Longrightarrow> fmrestrict_fset A m \<subseteq>\<^sub>f fmrestrict_fset A n"
unfolding fmfilter_alt_defs by (rule fmsubset_filter_mono)

lift_definition fmap_of_list :: "('a \<times> 'b) list \<Rightarrow> ('a, 'b) fmap"
  is map_of
  parametric map_of_transfer
by (rule finite_dom_map_of)

lemma fmap_of_list_simps[simp]:
  "fmap_of_list [] = fmempty"
  "fmap_of_list ((k, v) # kvs) = fmupd k v (fmap_of_list kvs)"
by (transfer, simp add: map_upd_def)+

lemma fmap_of_list_app[simp]: "fmap_of_list (xs @ ys) = fmap_of_list ys ++\<^sub>f fmap_of_list xs"
by transfer' simp

lemma fmupd_alt_def: "fmupd k v m = m ++\<^sub>f fmap_of_list [(k, v)]"
by transfer' (auto simp: map_upd_def)

lemma fmpred_of_list[intro]:
  assumes "\<And>k v. (k, v) \<in> set xs \<Longrightarrow> P k v"
  shows "fmpred P (fmap_of_list xs)"
using assms
by (induction xs) (transfer'; auto simp: map_pred_def)+

lemma fmap_of_list_SomeD: "fmlookup (fmap_of_list xs) k = Some v \<Longrightarrow> (k, v) \<in> set xs"
by transfer' (auto dest: map_of_SomeD)

lift_definition fmrel_on_set :: "'a set \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'c) fmap \<Rightarrow> bool"
  is rel_map_on_set
.

lift_definition fmrel_on_fset :: "'a fset \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'c) fmap \<Rightarrow> bool"
  is rel_map_on_set
.

lemma fmrel_on_fset_alt_def: "fmrel_on_fset S P m n \<longleftrightarrow> fBall S (\<lambda>x. rel_option P (fmlookup m x) (fmlookup n x))"
by transfer' (auto simp: rel_map_on_set_def eq_onp_def rel_fun_def)

lemma fmrel_on_fsetI[intro]:
  assumes "\<And>x. x |\<in>| S \<Longrightarrow> rel_option P (fmlookup m x) (fmlookup n x)"
  shows "fmrel_on_fset S P m n"
using assms
unfolding fmrel_on_fset_alt_def by auto

lemma fmrel_on_fset_mono[mono]: "R \<le> Q \<Longrightarrow> fmrel_on_fset S R \<le> fmrel_on_fset S Q"
unfolding fmrel_on_fset_alt_def[abs_def]
apply (intro le_funI fBall_mono)
using option.rel_mono by auto

lemma fmrel_on_fsetD: "x |\<in>| S \<Longrightarrow> fmrel_on_fset S P m n \<Longrightarrow> rel_option P (fmlookup m x) (fmlookup n x)"
unfolding fmrel_on_fset_alt_def
by auto

lemma fmrel_on_fsubset: "fmrel_on_fset S R m n \<Longrightarrow> T |\<subseteq>| S \<Longrightarrow> fmrel_on_fset T R m n"
unfolding fmrel_on_fset_alt_def
by auto

end


subsection \<open>BNF setup\<close>

lift_bnf ('a, fmran': 'b) fmap [wits: Map.empty]
  for map: fmmap
      rel: fmrel
  by auto

text \<open>
  Unfortunately, @{command lift_bnf} doesn't register the definitional theorems. We're doing it
  manually below.
\<close>

local_setup \<open>fn lthy =>
  let
    val SOME bnf = BNF_Def.bnf_of lthy @{type_name fmap}
  in
    lthy
    |> Local_Theory.note ((@{binding fmmap_def}, []), [BNF_Def.map_def_of_bnf bnf]) |> #2
    |> Local_Theory.note ((@{binding fmran'_def}, []), BNF_Def.set_defs_of_bnf bnf) |> #2
    |> Local_Theory.note ((@{binding fmrel_def}, []), [BNF_Def.rel_def_of_bnf bnf]) |> #2
  end
\<close>

context includes lifting_syntax begin

lemma fmmap_transfer[transfer_rule]:
  "(op = ===> pcr_fmap op = op = ===> pcr_fmap op = op =) (\<lambda>f. op \<circ> (map_option f)) fmmap"
  unfolding fmmap_def
  by (rule rel_funI ext)+ (auto simp: fmap.Abs_fmap_inverse fmap.pcr_cr_eq cr_fmap_def)

lemma fmran'_transfer[transfer_rule]:
  "(pcr_fmap op = op = ===> op =) (\<lambda>x. UNION (range x) set_option) fmran'"
  unfolding fmran'_def fmap.pcr_cr_eq cr_fmap_def by fastforce

lemma fmrel_transfer[transfer_rule]:
  "(op = ===> pcr_fmap op = op = ===> pcr_fmap op = op = ===> op =) rel_map fmrel"
  unfolding fmrel_def fmap.pcr_cr_eq cr_fmap_def vimage2p_def by fastforce

end


lemma fmran'_alt_def: "fmran' = fset \<circ> fmran"
including fset.lifting
by transfer' (auto simp: ran_def fun_eq_iff)

lemma fmran'I: "fmlookup m x = Some y \<Longrightarrow> y \<in> fmran' m"
by transfer' auto

lemma fmrel_iff: "fmrel R m n \<longleftrightarrow> (\<forall>x. rel_option R (fmlookup m x) (fmlookup n x))"
by transfer' (auto simp: rel_fun_def)

lemma fmrelI[intro]:
  assumes "\<And>x. rel_option R (fmlookup m x) (fmlookup n x)"
  shows "fmrel R m n"
using assms
by transfer' auto

lemma fmempty_transfer[simp, intro, transfer_rule]: "fmrel P fmempty fmempty"
by transfer auto

lemma fmrel_upd[intro]: "fmrel P m n \<Longrightarrow> P x y \<Longrightarrow> fmrel P (fmupd k x m) (fmupd k y n)"
by transfer' (auto simp: map_upd_def rel_fun_def)

lemma fmrelD[dest]: "fmrel P m n \<Longrightarrow> rel_option P (fmlookup m x) (fmlookup n x)"
by transfer' (auto simp: rel_fun_def)

lemma fmrel_addI[intro]:
  assumes "fmrel P m n" "fmrel P a b"
  shows "fmrel P (m ++\<^sub>f a) (n ++\<^sub>f b)"
using assms
apply transfer'
apply (auto simp: rel_fun_def map_add_def)
by (metis option.case_eq_if option.collapse option.rel_sel)

lemma fmrel_cases[consumes 1]:
  assumes "fmrel P m n"
  obtains (none) "fmlookup m x = None" "fmlookup n x = None"
        | (some) a b where "fmlookup m x = Some a" "fmlookup n x = Some b" "P a b"
proof -
  from assms have "rel_option P (fmlookup m x) (fmlookup n x)"
    by auto
  then show thesis
    using none some
    by (cases rule: option.rel_cases) auto
qed

lemma fmrel_filter[intro]: "fmrel P m n \<Longrightarrow> fmrel P (fmfilter Q m) (fmfilter Q n)"
unfolding fmrel_iff by auto

lemma fmrel_drop[intro]: "fmrel P m n \<Longrightarrow> fmrel P (fmdrop a m) (fmdrop a n)"
  unfolding fmfilter_alt_defs by blast

lemma fmrel_drop_set[intro]: "fmrel P m n \<Longrightarrow> fmrel P (fmdrop_set A m) (fmdrop_set A n)"
  unfolding fmfilter_alt_defs by blast

lemma fmrel_drop_fset[intro]: "fmrel P m n \<Longrightarrow> fmrel P (fmdrop_fset A m) (fmdrop_fset A n)"
  unfolding fmfilter_alt_defs by blast

lemma fmrel_restrict_set[intro]: "fmrel P m n \<Longrightarrow> fmrel P (fmrestrict_set A m) (fmrestrict_set A n)"
  unfolding fmfilter_alt_defs by blast

lemma fmrel_restrict_fset[intro]: "fmrel P m n \<Longrightarrow> fmrel P (fmrestrict_fset A m) (fmrestrict_fset A n)"
  unfolding fmfilter_alt_defs by blast

lemma pred_fmap_fmpred[simp]: "pred_fmap P = fmpred (\<lambda>_. P)"
unfolding fmap.pred_set fmran'_alt_def
including fset.lifting
apply transfer'
apply (rule ext)
apply (auto simp: map_pred_def ran_def split: option.splits dest: )
done

lemma pred_fmap_id[simp]: "pred_fmap id (fmmap f m) \<longleftrightarrow> pred_fmap f m"
unfolding fmap.pred_set fmap.set_map
by simp

lemma fmlookup_map[simp]: "fmlookup (fmmap f m) x = map_option f (fmlookup m x)"
by transfer' auto

lemma fmpred_map[simp]: "fmpred P (fmmap f m) \<longleftrightarrow> fmpred (\<lambda>k v. P k (f v)) m"
unfolding fmpred_iff pred_fmap_def fmap.set_map
by auto

lemma fmpred_id[simp]: "fmpred (\<lambda>_. id) (fmmap f m) \<longleftrightarrow> fmpred (\<lambda>_. f) m"
by simp

lemma fmmap_add[simp]: "fmmap f (m ++\<^sub>f n) = fmmap f m ++\<^sub>f fmmap f n"
by transfer' (auto simp: map_add_def fun_eq_iff split: option.splits)

lemma fmmap_empty[simp]: "fmmap f fmempty = fmempty"
by transfer auto

lemma fmdom_map[simp]: "fmdom (fmmap f m) = fmdom m"
including fset.lifting
by transfer' simp

lemma fmdom'_map[simp]: "fmdom' (fmmap f m) = fmdom' m"
by transfer' simp

lemma fmfilter_fmmap[simp]: "fmfilter P (fmmap f m) = fmmap f (fmfilter P m)"
by transfer' (auto simp: map_filter_def)

lemma fmdrop_fmmap[simp]: "fmdrop a (fmmap f m) = fmmap f (fmdrop a m)" unfolding fmfilter_alt_defs by simp
lemma fmdrop_set_fmmap[simp]: "fmdrop_set A (fmmap f m) = fmmap f (fmdrop_set A m)" unfolding fmfilter_alt_defs by simp
lemma fmdrop_fset_fmmap[simp]: "fmdrop_fset A (fmmap f m) = fmmap f (fmdrop_fset A m)" unfolding fmfilter_alt_defs by simp
lemma fmrestrict_set_fmmap[simp]: "fmrestrict_set A (fmmap f m) = fmmap f (fmrestrict_set A m)" unfolding fmfilter_alt_defs by simp
lemma fmrestrict_fset_fmmap[simp]: "fmrestrict_fset A (fmmap f m) = fmmap f (fmrestrict_fset A m)" unfolding fmfilter_alt_defs by simp

lemma fmmap_subset[intro]: "m \<subseteq>\<^sub>f n \<Longrightarrow> fmmap f m \<subseteq>\<^sub>f fmmap f n"
by transfer' (auto simp: map_le_def)


subsection \<open>Code setup\<close>

instantiation fmap :: (type, equal) equal begin

definition "equal_fmap \<equiv> fmrel HOL.equal"

instance proof
  fix m n :: "('a, 'b) fmap"
  have "fmrel op = m n \<longleftrightarrow> (m = n)"
    by transfer' (simp add: option.rel_eq rel_fun_eq)
  then show "equal_class.equal m n \<longleftrightarrow> (m = n)"
    unfolding equal_fmap_def
    by (simp add: equal_eq[abs_def])
qed

end

lemma fBall_alt_def: "fBall S P \<longleftrightarrow> (\<forall>x. x |\<in>| S \<longrightarrow> P x)"
by force

lemma fmrel_code:
  "fmrel R m n \<longleftrightarrow>
    fBall (fmdom m) (\<lambda>x. rel_option R (fmlookup m x) (fmlookup n x)) \<and>
    fBall (fmdom n) (\<lambda>x. rel_option R (fmlookup m x) (fmlookup n x))"
unfolding fmrel_iff fmlookup_dom_iff fBall_alt_def
by (metis option.collapse option.rel_sel)

lemmas fmap_generic_code =
  fmrel_code
  fmran'_alt_def
  fmdom'_alt_def
  fmfilter_alt_defs
  pred_fmap_fmpred
  fmsubset_alt_def
  fmupd_alt_def
  fmrel_on_fset_alt_def
  fmpred_alt_def


code_datatype fmap_of_list
quickcheck_generator fmap constructors: fmap_of_list

context includes fset.lifting begin

lemma [code]: "fmlookup (fmap_of_list m) = map_of m"
by transfer simp

lemma [code]: "fmempty = fmap_of_list []"
by transfer simp

lemma [code]: "fmran (fmap_of_list m) = snd |`| fset_of_list (AList.clearjunk m)"
by transfer (auto simp: ran_map_of)

lemma [code]: "fmdom (fmap_of_list m) = fst |`| fset_of_list m"
by transfer (auto simp: dom_map_of_conv_image_fst)

lemma [code]: "fmfilter P (fmap_of_list m) = fmap_of_list (filter (\<lambda>(k, _). P k) m)"
by transfer' auto

lemma [code]: "fmap_of_list m ++\<^sub>f fmap_of_list n = fmap_of_list (AList.merge m n)"
by transfer (simp add: merge_conv')

lemma [code]: "fmmap f (fmap_of_list m) = fmap_of_list (map (apsnd f) m)"
apply transfer
apply (subst map_of_map[symmetric])
apply (auto simp: apsnd_def map_prod_def)
done

end

declare fmap_generic_code[code]

lifting_update fmap.lifting
lifting_forget fmap.lifting

end
