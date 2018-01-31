(* Author: Tobias Nipkow *)

section \<open>Leftist Heap\<close>

theory Leftist_Heap
imports Tree2 "~~/src/HOL/Library/Multiset" Complex_Main
begin

type_synonym 'a lheap = "('a,nat)tree"

fun rank :: "'a lheap \<Rightarrow> nat" where
"rank Leaf = 0" |
"rank (Node _ _ _ r) = rank r + 1"

fun rk :: "'a lheap \<Rightarrow> nat" where
"rk Leaf = 0" |
"rk (Node n _ _ _) = n"

text{* The invariant: *}

fun lheap :: "'a lheap \<Rightarrow> bool" where
"lheap Leaf = True" |
"lheap (Node n l a r) =
 (n = rank r + 1 \<and> rank l \<ge> rank r \<and> lheap l & lheap r)"

definition node :: "'a lheap \<Rightarrow> 'a \<Rightarrow> 'a lheap \<Rightarrow> 'a lheap" where
"node l a r =
 (let rl = rk l; rr = rk r
  in if rl \<ge> rr then Node (rr+1) l a r else Node (rl+1) r a l)"

fun get_min :: "'a lheap \<Rightarrow> 'a" where
"get_min(Node n l a r) = a"

function meld :: "'a::ord lheap \<Rightarrow> 'a lheap \<Rightarrow> 'a lheap" where
"meld Leaf t2 = t2" |
"meld t1 Leaf = t1" |
"meld (Node n1 l1 a1 r1) (Node n2 l2 a2 r2) =
   (if a1 \<le> a2 then node l1 a1 (meld r1 (Node n2 l2 a2 r2))
    else node l2 a2 (meld r2 (Node n1 l1 a1 r1)))"
by pat_completeness auto
termination by (relation "measure (%(t1,t2). rank t1 + rank t2)") auto

lemma meld_code: "meld t1 t2 = (case (t1,t2) of
  (Leaf, _) \<Rightarrow> t2 |
  (_, Leaf) \<Rightarrow> t1 |
  (Node n1 l1 a1 r1, Node n2 l2 a2 r2) \<Rightarrow>
    if a1 \<le> a2 then node l1 a1 (meld r1 t2) else node l2 a2 (meld r2 t1))"
by(induction t1 t2 rule: meld.induct) (simp_all split: tree.split)

definition insert :: "'a::ord \<Rightarrow> 'a lheap \<Rightarrow> 'a lheap" where
"insert x t = meld (Node 1 Leaf x Leaf) t"

fun del_min :: "'a::ord lheap \<Rightarrow> 'a lheap" where
"del_min Leaf = Leaf" |
"del_min (Node n l x r) = meld l r"


subsection "Lemmas"

declare Let_def [simp]

lemma rk_eq_rank[simp]: "lheap t \<Longrightarrow> rk t = rank t"
by(cases t) auto

lemma lheap_node: "lheap (node l a r) \<longleftrightarrow> lheap l \<and> lheap r"
by(auto simp add: node_def)


subsection "Functional Correctness"

locale Priority_Queue =
fixes empty :: "'pq"
and insert :: "'a \<Rightarrow> 'pq \<Rightarrow> 'pq"
and get_min :: "'pq \<Rightarrow> 'a"
and del_min :: "'pq \<Rightarrow> 'pq"
and invar :: "'pq \<Rightarrow> bool"
and mset :: "'pq \<Rightarrow> 'a multiset"
assumes mset_empty: "mset empty = {#}"
and mset_insert: "invar pq \<Longrightarrow> mset (insert x pq) = {#x#} + mset pq"
and mset_del_min: "invar pq \<Longrightarrow> mset (del_min pq) = mset pq - {#get_min pq#}"
and invar_insert: "invar pq \<Longrightarrow> invar (insert x pq)"
and invar_del_min: "invar pq \<Longrightarrow> invar (del_min pq)"


fun mset_tree :: "('a,'b) tree \<Rightarrow> 'a multiset" where
"mset_tree Leaf = {#}" |
"mset_tree (Node _ l a r) = {#a#} + mset_tree l + mset_tree r"


lemma mset_meld: "mset_tree (meld h1 h2) = mset_tree h1 + mset_tree h2"
by (induction h1 h2 rule: meld.induct) (auto simp add: node_def ac_simps)

lemma mset_insert: "mset_tree (insert x t) = {#x#} + mset_tree t"
by (auto simp add: insert_def mset_meld)

lemma mset_del_min: "mset_tree (del_min h) = mset_tree h - {# get_min h #}"
by (cases h) (auto simp: mset_meld ac_simps subset_mset.diff_add_assoc)


lemma lheap_meld: "\<lbrakk> lheap l; lheap r \<rbrakk> \<Longrightarrow> lheap (meld l r)"
proof(induction l r rule: meld.induct)
  case (3 n1 l1 a1 r1 n2 l2 a2 r2)
  show ?case (is "lheap(meld ?t1 ?t2)")
  proof cases
    assume "a1 \<le> a2"
    hence "lheap (meld ?t1 ?t2) = lheap (node l1 a1 (meld r1 ?t2))" by simp
    also have "\<dots> = (lheap l1 \<and> lheap(meld r1 ?t2))"
      by(simp add: lheap_node)
    also have "..." using "3.prems" "3.IH"(1)[OF `a1 \<le> a2`] by (simp)
    finally show ?thesis .
  next (* analogous but automatic *)
    assume "\<not> a1 \<le> a2"
    thus ?thesis using 3 by(simp)(auto simp: lheap_node)
  qed
qed simp_all

lemma lheap_insert: "lheap t \<Longrightarrow> lheap(insert x t)"
by(simp add: insert_def lheap_meld del: meld.simps split: tree.split)

lemma lheap_del_min: "lheap t \<Longrightarrow> lheap(del_min t)"
by(cases t)(auto simp add: lheap_meld simp del: meld.simps)


interpretation lheap: Priority_Queue
where empty = Leaf and insert = insert and del_min = del_min
and get_min = get_min and invar = lheap and mset = mset_tree
proof(standard, goal_cases)
  case 1 show ?case by simp
next
  case 2 show ?case by(rule mset_insert)
next
  case 3 show ?case by(rule mset_del_min)
next
  case 4 thus ?case by(rule lheap_insert)
next
  case 5 thus ?case by(rule lheap_del_min)
qed


subsection "Complexity"

lemma pow2_rank_size1: "lheap t \<Longrightarrow> 2 ^ rank t \<le> size1 t"
proof(induction t)
  case Leaf show ?case by simp
next
  case (Node n l a r)
  hence "rank r \<le> rank l" by simp
  hence *: "(2::nat) ^ rank r \<le> 2 ^ rank l" by simp
  have "(2::nat) ^ rank \<langle>n, l, a, r\<rangle> = 2 ^ rank r + 2 ^ rank r"
    by(simp add: mult_2)
  also have "\<dots> \<le> size1 l + size1 r"
    using Node * by (simp del: power_increasing_iff)
  also have "\<dots> = size1 \<langle>n, l, a, r\<rangle>" by simp
  finally show ?case .
qed

function t_meld :: "'a::ord lheap \<Rightarrow> 'a lheap \<Rightarrow> nat" where
"t_meld Leaf t2 = 1" |
"t_meld t2 Leaf = 1" |
"t_meld (Node n1 l1 a1 r1) (Node n2 l2 a2 r2) =
  (if a1 \<le> a2 then 1 + t_meld r1 (Node n2 l2 a2 r2)
   else 1 + t_meld r2 (Node n1 l1 a1 r1))"
by pat_completeness auto
termination by (relation "measure (%(t1,t2). rank t1 + rank t2)") auto

definition t_insert :: "'a::ord \<Rightarrow> 'a lheap \<Rightarrow> nat" where
"t_insert x t = t_meld (Node 1 Leaf x Leaf) t"

fun t_del_min :: "'a::ord lheap \<Rightarrow> nat" where
"t_del_min Leaf = 1" |
"t_del_min (Node n l a r) = t_meld l r"

lemma t_meld_rank: "t_meld l r \<le> rank l + rank r + 1"
proof(induction l r rule: meld.induct)
  case 3 thus ?case
    by(simp)(fastforce split: tree.splits simp del: t_meld.simps)
qed simp_all

corollary t_meld_log: assumes "lheap l" "lheap r"
  shows "t_meld l r \<le> log 2 (size1 l) + log 2 (size1 r) + 1"
using le_log2_of_power[OF pow2_rank_size1[OF assms(1)]]
  le_log2_of_power[OF pow2_rank_size1[OF assms(2)]] t_meld_rank[of l r]
by linarith

corollary t_insert_log: "lheap t \<Longrightarrow> t_insert x t \<le> log 2 (size1 t) + 2"
using t_meld_log[of "Node 1 Leaf x Leaf" t]
by(simp add: t_insert_def split: tree.split)

lemma ld_ld_1_less:
  assumes "x > 0" "y > 0" shows "1 + log 2 x + log 2 y < 2 * log 2 (x+y)"
proof -
  have 1: "2*x*y < (x+y)^2" using assms
    by(simp add: numeral_eq_Suc algebra_simps add_pos_pos)
  show ?thesis
    apply(rule powr_less_cancel_iff[of 2, THEN iffD1])
     apply simp
    using assms 1 by(simp add: powr_add log_powr[symmetric] powr_numeral)
qed

corollary t_del_min_log: assumes "lheap t"
  shows "t_del_min t \<le> 2 * log 2 (size1 t) + 1"
proof(cases t)
  case Leaf thus ?thesis using assms by simp
next
  case [simp]: (Node _ t1 _ t2)
  have "t_del_min t = t_meld t1 t2" by simp
  also have "\<dots> \<le> log 2 (size1 t1) + log 2 (size1 t2) + 1"
    using \<open>lheap t\<close> by (auto simp: t_meld_log simp del: t_meld.simps)
  also have "\<dots> \<le> 2 * log 2 (size1 t) + 1"
    using ld_ld_1_less[of "size1 t1" "size1 t2"] by (simp)
  finally show ?thesis .
qed

end
