(*  Title:      HOL/Library/Sublist_Order.thy
    Author:     Peter Lammich, Uni Muenster <peter.lammich@uni-muenster.de>
    Author:     Florian Haftmann, , TU Muenchen
    Author:     Tobias Nipkow, TU Muenchen
*)

section \<open>Sublist Ordering\<close>

theory Sublist_Order
imports Sublist
begin

text \<open>
  This theory defines sublist ordering on lists. A list \<open>ys\<close> is a sublist of a
  list \<open>xs\<close>, iff one obtains \<open>ys\<close> by erasing some elements from \<open>xs\<close>.
\<close>

subsection \<open>Definitions and basic lemmas\<close>

instantiation list :: (type) ord
begin

definition "xs \<le> ys \<longleftrightarrow> sublisteq xs ys" for xs ys :: "'a list"
definition "xs < ys \<longleftrightarrow> xs \<le> ys \<and> \<not> ys \<le> xs" for xs ys :: "'a list"

instance ..

end

instance list :: (type) order
proof
  fix xs ys zs :: "'a list"
  show "xs < ys \<longleftrightarrow> xs \<le> ys \<and> \<not> ys \<le> xs"
    unfolding less_list_def ..
  show "xs \<le> xs"
    by (simp add: less_eq_list_def)
  show "xs = ys" if "xs \<le> ys" and "ys \<le> xs"
    using that unfolding less_eq_list_def by (rule sublisteq_antisym)
  show "xs \<le> zs" if "xs \<le> ys" and "ys \<le> zs"
    using that unfolding less_eq_list_def by (rule sublisteq_trans)
qed

lemmas less_eq_list_induct [consumes 1, case_names empty drop take] =
  list_emb.induct [of "op =", folded less_eq_list_def]
lemmas less_eq_list_drop = list_emb.list_emb_Cons [of "op =", folded less_eq_list_def]
lemmas le_list_Cons2_iff [simp, code] = sublisteq_Cons2_iff [folded less_eq_list_def]
lemmas le_list_map = sublisteq_map [folded less_eq_list_def]
lemmas le_list_filter = sublisteq_filter [folded less_eq_list_def]
lemmas le_list_length = list_emb_length [of "op =", folded less_eq_list_def]

lemma less_list_length: "xs < ys \<Longrightarrow> length xs < length ys"
  by (metis list_emb_length sublisteq_same_length le_neq_implies_less less_list_def less_eq_list_def)

lemma less_list_empty [simp]: "[] < xs \<longleftrightarrow> xs \<noteq> []"
  by (metis less_eq_list_def list_emb_Nil order_less_le)

lemma less_list_below_empty [simp]: "xs < [] \<longleftrightarrow> False"
  by (metis list_emb_Nil less_eq_list_def less_list_def)

lemma less_list_drop: "xs < ys \<Longrightarrow> xs < x # ys"
  by (unfold less_le less_eq_list_def) (auto)

lemma less_list_take_iff: "x # xs < x # ys \<longleftrightarrow> xs < ys"
  by (metis sublisteq_Cons2_iff less_list_def less_eq_list_def)

lemma less_list_drop_many: "xs < ys \<Longrightarrow> xs < zs @ ys"
  by (metis sublisteq_append_le_same_iff sublisteq_drop_many order_less_le
      self_append_conv2 less_eq_list_def)

lemma less_list_take_many_iff: "zs @ xs < zs @ ys \<longleftrightarrow> xs < ys"
  by (metis less_list_def less_eq_list_def sublisteq_append')

lemma less_list_rev_take: "xs @ zs < ys @ zs \<longleftrightarrow> xs < ys"
  by (unfold less_le less_eq_list_def) auto

end
