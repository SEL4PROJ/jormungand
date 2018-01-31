section \<open>Nested datatypes\<close>

theory Nested_Datatype
imports Main
begin

subsection \<open>Terms and substitution\<close>

datatype ('a, 'b) "term" =
  Var 'a
| App 'b "('a, 'b) term list"

primrec subst_term :: "('a \<Rightarrow> ('a, 'b) term) \<Rightarrow> ('a, 'b) term \<Rightarrow> ('a, 'b) term"
  and subst_term_list :: "('a \<Rightarrow> ('a, 'b) term) \<Rightarrow> ('a, 'b) term list \<Rightarrow> ('a, 'b) term list"
where
  "subst_term f (Var a) = f a"
| "subst_term f (App b ts) = App b (subst_term_list f ts)"
| "subst_term_list f [] = []"
| "subst_term_list f (t # ts) = subst_term f t # subst_term_list f ts"

lemmas subst_simps = subst_term.simps subst_term_list.simps

text \<open>\<^medskip> A simple lemma about composition of substitutions.\<close>

lemma
  "subst_term (subst_term f1 \<circ> f2) t =
    subst_term f1 (subst_term f2 t)"
  and
  "subst_term_list (subst_term f1 \<circ> f2) ts =
    subst_term_list f1 (subst_term_list f2 ts)"
  by (induct t and ts rule: subst_term.induct subst_term_list.induct) simp_all

lemma "subst_term (subst_term f1 \<circ> f2) t = subst_term f1 (subst_term f2 t)"
proof -
  let "?P t" = ?thesis
  let ?Q = "\<lambda>ts. subst_term_list (subst_term f1 \<circ> f2) ts =
    subst_term_list f1 (subst_term_list f2 ts)"
  show ?thesis
  proof (induct t rule: subst_term.induct)
    show "?P (Var a)" for a by simp
    show "?P (App b ts)" if "?Q ts" for b ts
      using that by (simp only: subst_simps)
    show "?Q []" by simp
    show "?Q (t # ts)" if "?P t" "?Q ts" for t ts
      using that by (simp only: subst_simps)
  qed
qed


subsection \<open>Alternative induction\<close>

lemma "subst_term (subst_term f1 \<circ> f2) t = subst_term f1 (subst_term f2 t)"
proof (induct t rule: term.induct)
  case (Var a)
  show ?case by (simp add: o_def)
next
  case (App b ts)
  then show ?case by (induct ts) simp_all
qed

end
