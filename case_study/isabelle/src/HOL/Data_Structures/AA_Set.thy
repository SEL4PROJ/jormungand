(*
Author: Tobias Nipkow, Daniel Stüwe
*)

section \<open>AA Tree Implementation of Sets\<close>

theory AA_Set
imports
  Isin2
  Cmp
begin

type_synonym 'a aa_tree = "('a,nat) tree"

fun lvl :: "'a aa_tree \<Rightarrow> nat" where
"lvl Leaf = 0" |
"lvl (Node lv _ _ _) = lv"

fun invar :: "'a aa_tree \<Rightarrow> bool" where
"invar Leaf = True" |
"invar (Node h l a r) =
 (invar l \<and> invar r \<and>
  h = lvl l + 1 \<and> (h = lvl r + 1 \<or> (\<exists>lr b rr. r = Node h lr b rr \<and> h = lvl rr + 1)))"

fun skew :: "'a aa_tree \<Rightarrow> 'a aa_tree" where
"skew (Node lva (Node lvb t1 b t2) a t3) =
  (if lva = lvb then Node lva t1 b (Node lva t2 a t3) else Node lva (Node lvb t1 b t2) a t3)" |
"skew t = t"

fun split :: "'a aa_tree \<Rightarrow> 'a aa_tree" where
"split (Node lva t1 a (Node lvb t2 b (Node lvc t3 c t4))) =
   (if lva = lvb \<and> lvb = lvc (* lva = lvc suffices *)
    then Node (lva+1) (Node lva t1 a t2) b (Node lva t3 c t4)
    else Node lva t1 a (Node lvb t2 b (Node lvc t3 c t4)))" |
"split t = t"

hide_const (open) insert

fun insert :: "'a::linorder \<Rightarrow> 'a aa_tree \<Rightarrow> 'a aa_tree" where
"insert x Leaf = Node 1 Leaf x Leaf" |
"insert x (Node lv t1 a t2) =
  (case cmp x a of
     LT \<Rightarrow> split (skew (Node lv (insert x t1) a t2)) |
     GT \<Rightarrow> split (skew (Node lv t1 a (insert x t2))) |
     EQ \<Rightarrow> Node lv t1 x t2)"

fun sngl :: "'a aa_tree \<Rightarrow> bool" where
"sngl Leaf = False" |
"sngl (Node _ _ _ Leaf) = True" |
"sngl (Node lva _ _ (Node lvb _ _ _)) = (lva > lvb)"

definition adjust :: "'a aa_tree \<Rightarrow> 'a aa_tree" where
"adjust t =
 (case t of
  Node lv l x r \<Rightarrow>
   (if lvl l >= lv-1 \<and> lvl r >= lv-1 then t else
    if lvl r < lv-1 \<and> sngl l then skew (Node (lv-1) l x r) else
    if lvl r < lv-1
    then case l of
           Node lva t1 a (Node lvb t2 b t3)
             \<Rightarrow> Node (lvb+1) (Node lva t1 a t2) b (Node (lv-1) t3 x r) 
    else
    if lvl r < lv then split (Node (lv-1) l x r)
    else
      case r of
        Node lvb t1 b t4 \<Rightarrow>
          (case t1 of
             Node lva t2 a t3
               \<Rightarrow> Node (lva+1) (Node (lv-1) l x t2) a
                    (split (Node (if sngl t1 then lva else lva+1) t3 b t4)))))"

text{* In the paper, the last case of @{const adjust} is expressed with the help of an
incorrect auxiliary function \texttt{nlvl}.

Function @{text del_max} below is called \texttt{dellrg} in the paper.
The latter is incorrect for two reasons: \texttt{dellrg} is meant to delete the largest
element but recurses on the left instead of the right subtree; the invariant
is not restored.*}

fun del_max :: "'a aa_tree \<Rightarrow> 'a aa_tree * 'a" where
"del_max (Node lv l a Leaf) = (l,a)" |
"del_max (Node lv l a r) = (let (r',b) = del_max r in (adjust(Node lv l a r'), b))"

fun delete :: "'a::linorder \<Rightarrow> 'a aa_tree \<Rightarrow> 'a aa_tree" where
"delete _ Leaf = Leaf" |
"delete x (Node lv l a r) =
  (case cmp x a of
     LT \<Rightarrow> adjust (Node lv (delete x l) a r) |
     GT \<Rightarrow> adjust (Node lv l a (delete x r)) |
     EQ \<Rightarrow> (if l = Leaf then r
            else let (l',b) = del_max l in adjust (Node lv l' b r)))"

fun pre_adjust where
"pre_adjust (Node lv l a r) = (invar l \<and> invar r \<and>
    ((lv = lvl l + 1 \<and> (lv = lvl r + 1 \<or> lv = lvl r + 2 \<or> lv = lvl r \<and> sngl r)) \<or>
     (lv = lvl l + 2 \<and> (lv = lvl r + 1 \<or> lv = lvl r \<and> sngl r))))"

declare pre_adjust.simps [simp del]

subsection "Auxiliary Proofs"

lemma split_case: "split t = (case t of
  Node lvx a x (Node lvy b y (Node lvz c z d)) \<Rightarrow>
   (if lvx = lvy \<and> lvy = lvz
    then Node (lvx+1) (Node lvx a x b) y (Node lvx c z d)
    else t)
  | t \<Rightarrow> t)"
by(auto split: tree.split)

lemma skew_case: "skew t = (case t of
  Node lvx (Node lvy a y b) x c \<Rightarrow>
  (if lvx = lvy then Node lvx a y (Node lvx b x c) else t)
 | t \<Rightarrow> t)"
by(auto split: tree.split)

lemma lvl_0_iff: "invar t \<Longrightarrow> lvl t = 0 \<longleftrightarrow> t = Leaf"
by(cases t) auto

lemma lvl_Suc_iff: "lvl t = Suc n \<longleftrightarrow> (\<exists> l a r. t = Node (Suc n) l a r)"
by(cases t) auto

lemma lvl_skew: "lvl (skew t) = lvl t"
by(cases t rule: skew.cases) auto

lemma lvl_split: "lvl (split t) = lvl t \<or> lvl (split t) = lvl t + 1 \<and> sngl (split t)"
by(cases t rule: split.cases) auto

lemma invar_2Nodes:"invar (Node lv l x (Node rlv rl rx rr)) =
     (invar l \<and> invar \<langle>rlv, rl, rx, rr\<rangle> \<and> lv = Suc (lvl l) \<and>
     (lv = Suc rlv \<or> rlv = lv \<and> lv = Suc (lvl rr)))"
by simp

lemma invar_NodeLeaf[simp]:
  "invar (Node lv l x Leaf) = (invar l \<and> lv = Suc (lvl l) \<and> lv = Suc 0)"
by simp

lemma sngl_if_invar: "invar (Node n l a r) \<Longrightarrow> n = lvl r \<Longrightarrow> sngl r"
by(cases r rule: sngl.cases) clarsimp+


subsection "Invariance"

subsubsection "Proofs for insert"

lemma lvl_insert_aux:
  "lvl (insert x t) = lvl t \<or> lvl (insert x t) = lvl t + 1 \<and> sngl (insert x t)"
apply(induction t)
apply (auto simp: lvl_skew)
apply (metis Suc_eq_plus1 lvl.simps(2) lvl_split lvl_skew)+
done

lemma lvl_insert: obtains
  (Same) "lvl (insert x t) = lvl t" |
  (Incr) "lvl (insert x t) = lvl t + 1" "sngl (insert x t)"
using lvl_insert_aux by blast

lemma lvl_insert_sngl: "invar t \<Longrightarrow> sngl t \<Longrightarrow> lvl(insert x t) = lvl t"
proof (induction t rule: insert.induct)
  case (2 x lv t1 a t2)
  consider (LT) "x < a" | (GT) "x > a" | (EQ) "x = a" 
    using less_linear by blast 
  thus ?case proof cases
    case LT
    thus ?thesis using 2 by (auto simp add: skew_case split_case split: tree.splits)
  next
    case GT
    thus ?thesis using 2 proof (cases t1)
      case Node
      thus ?thesis using 2 GT  
        apply (auto simp add: skew_case split_case split: tree.splits)
        by (metis less_not_refl2 lvl.simps(2) lvl_insert_aux n_not_Suc_n sngl.simps(3))+ 
    qed (auto simp add: lvl_0_iff)
  qed simp
qed simp

lemma skew_invar: "invar t \<Longrightarrow> skew t = t"
by(cases t rule: skew.cases) auto

lemma split_invar: "invar t \<Longrightarrow> split t = t"
by(cases t rule: split.cases) clarsimp+

lemma invar_NodeL:
  "\<lbrakk> invar(Node n l x r); invar l'; lvl l' = lvl l \<rbrakk> \<Longrightarrow> invar(Node n l' x r)"
by(auto)

lemma invar_NodeR:
  "\<lbrakk> invar(Node n l x r); n = lvl r + 1; invar r'; lvl r' = lvl r \<rbrakk> \<Longrightarrow> invar(Node n l x r')"
by(auto)

lemma invar_NodeR2:
  "\<lbrakk> invar(Node n l x r); sngl r'; n = lvl r + 1; invar r'; lvl r' = n \<rbrakk> \<Longrightarrow> invar(Node n l x r')"
by(cases r' rule: sngl.cases) clarsimp+


lemma lvl_insert_incr_iff: "(lvl(insert a t) = lvl t + 1) \<longleftrightarrow>
  (EX l x r. insert a t = Node (lvl t + 1) l x r \<and> lvl l = lvl r)"
apply(cases t)
apply(auto simp add: skew_case split_case split: if_splits)
apply(auto split: tree.splits if_splits)
done

lemma invar_insert: "invar t \<Longrightarrow> invar(insert a t)"
proof(induction t)
  case (Node n l x r)
  hence il: "invar l" and ir: "invar r" by auto
  note N = Node
  let ?t = "Node n l x r"
  have "a < x \<or> a = x \<or> x < a" by auto
  moreover
  { assume "a < x"
    note iil = Node.IH(1)[OF il]
    have ?case
    proof (cases rule: lvl_insert[of a l])
      case (Same) thus ?thesis
        using \<open>a<x\<close> invar_NodeL[OF Node.prems iil Same]
        by (simp add: skew_invar split_invar del: invar.simps)
    next
      case (Incr)
      then obtain t1 w t2 where ial[simp]: "insert a l = Node n t1 w t2"
        using Node.prems by (auto simp: lvl_Suc_iff)
      have l12: "lvl t1 = lvl t2"
        by (metis Incr(1) ial lvl_insert_incr_iff tree.inject)
      have "insert a ?t = split(skew(Node n (insert a l) x r))"
        by(simp add: \<open>a<x\<close>)
      also have "skew(Node n (insert a l) x r) = Node n t1 w (Node n t2 x r)"
        by(simp)
      also have "invar(split \<dots>)"
      proof (cases r)
        case Leaf
        hence "l = Leaf" using Node.prems by(auto simp: lvl_0_iff)
        thus ?thesis using Leaf ial by simp
      next
        case [simp]: (Node m t3 y t4)
        show ?thesis (*using N(3) iil l12 by(auto)*)
        proof cases
          assume "m = n" thus ?thesis using N(3) iil by(auto)
        next
          assume "m \<noteq> n" thus ?thesis using N(3) iil l12 by(auto)
        qed
      qed
      finally show ?thesis .
    qed
  }
  moreover
  { assume "x < a"
    note iir = Node.IH(2)[OF ir]
    from \<open>invar ?t\<close> have "n = lvl r \<or> n = lvl r + 1" by auto
    hence ?case
    proof
      assume 0: "n = lvl r"
      have "insert a ?t = split(skew(Node n l x (insert a r)))"
        using \<open>a>x\<close> by(auto)
      also have "skew(Node n l x (insert a r)) = Node n l x (insert a r)"
        using Node.prems by(simp add: skew_case split: tree.split)
      also have "invar(split \<dots>)"
      proof -
        from lvl_insert_sngl[OF ir sngl_if_invar[OF \<open>invar ?t\<close> 0], of a]
        obtain t1 y t2 where iar: "insert a r = Node n t1 y t2"
          using Node.prems 0 by (auto simp: lvl_Suc_iff)
        from Node.prems iar 0 iir
        show ?thesis by (auto simp: split_case split: tree.splits)
      qed
      finally show ?thesis .
    next
      assume 1: "n = lvl r + 1"
      hence "sngl ?t" by(cases r) auto
      show ?thesis
      proof (cases rule: lvl_insert[of a r])
        case (Same)
        show ?thesis using \<open>x<a\<close> il ir invar_NodeR[OF Node.prems 1 iir Same]
          by (auto simp add: skew_invar split_invar)
      next
        case (Incr)
        thus ?thesis using invar_NodeR2[OF `invar ?t` Incr(2) 1 iir] 1 \<open>x < a\<close>
          by (auto simp add: skew_invar split_invar split: if_splits)
      qed
    qed
  }
  moreover { assume "a = x" hence ?case using Node.prems by auto }
  ultimately show ?case by blast
qed simp


subsubsection "Proofs for delete"

lemma invarL: "ASSUMPTION(invar \<langle>lv, l, a, r\<rangle>) \<Longrightarrow> invar l"
by(simp add: ASSUMPTION_def)

lemma invarR: "ASSUMPTION(invar \<langle>lv, l, a, r\<rangle>) \<Longrightarrow> invar r"
by(simp add: ASSUMPTION_def)

lemma sngl_NodeI:
  "sngl (Node lv l a r) \<Longrightarrow> sngl (Node lv l' a' r)"
by(cases r) (simp_all)


declare invarL[simp] invarR[simp]

lemma pre_cases:
assumes "pre_adjust (Node lv l x r)"
obtains
 (tSngl) "invar l \<and> invar r \<and>
    lv = Suc (lvl r) \<and> lvl l = lvl r" |
 (tDouble) "invar l \<and> invar r \<and>
    lv = lvl r \<and> Suc (lvl l) = lvl r \<and> sngl r " |
 (rDown) "invar l \<and> invar r \<and>
    lv = Suc (Suc (lvl r)) \<and>  lv = Suc (lvl l)" |
 (lDown_tSngl) "invar l \<and> invar r \<and>
    lv = Suc (lvl r) \<and> lv = Suc (Suc (lvl l))" |
 (lDown_tDouble) "invar l \<and> invar r \<and>
    lv = lvl r \<and> lv = Suc (Suc (lvl l)) \<and> sngl r"
using assms unfolding pre_adjust.simps
by auto

declare invar.simps(2)[simp del] invar_2Nodes[simp add]

lemma invar_adjust:
  assumes pre: "pre_adjust (Node lv l a r)"
  shows  "invar(adjust (Node lv l a r))"
using pre proof (cases rule: pre_cases)
  case (tDouble) thus ?thesis unfolding adjust_def by (cases r) (auto simp: invar.simps(2)) 
next 
  case (rDown)
  from rDown obtain llv ll la lr where l: "l = Node llv ll la lr" by (cases l) auto
  from rDown show ?thesis unfolding adjust_def by (auto simp: l invar.simps(2) split: tree.splits)
next
  case (lDown_tDouble)
  from lDown_tDouble obtain rlv rr ra rl where r: "r = Node rlv rl ra rr" by (cases r) auto
  from lDown_tDouble and r obtain rrlv rrr rra rrl where
    rr :"rr = Node rrlv rrr rra rrl" by (cases rr) auto
  from  lDown_tDouble show ?thesis unfolding adjust_def r rr
    apply (cases rl) apply (auto simp add: invar.simps(2) split!: if_split)
    using lDown_tDouble by (auto simp: split_case lvl_0_iff  elim:lvl.elims split: tree.split)
qed (auto simp: split_case invar.simps(2) adjust_def split: tree.splits)

lemma lvl_adjust:
  assumes "pre_adjust (Node lv l a r)"
  shows "lv = lvl (adjust(Node lv l a r)) \<or> lv = lvl (adjust(Node lv l a r)) + 1"
using assms(1) proof(cases rule: pre_cases)
  case lDown_tSngl thus ?thesis
    using lvl_split[of "\<langle>lvl r, l, a, r\<rangle>"] by (auto simp: adjust_def)
next
  case lDown_tDouble thus ?thesis
    by (auto simp: adjust_def invar.simps(2) split: tree.split)
qed (auto simp: adjust_def split: tree.splits)

lemma sngl_adjust: assumes "pre_adjust (Node lv l a r)"
  "sngl \<langle>lv, l, a, r\<rangle>" "lv = lvl (adjust \<langle>lv, l, a, r\<rangle>)"
  shows "sngl (adjust \<langle>lv, l, a, r\<rangle>)" 
using assms proof (cases rule: pre_cases)
  case rDown
  thus ?thesis using assms(2,3) unfolding adjust_def
    by (auto simp add: skew_case) (auto split: tree.split)
qed (auto simp: adjust_def skew_case split_case split: tree.split)

definition "post_del t t' ==
  invar t' \<and>
  (lvl t' = lvl t \<or> lvl t' + 1 = lvl t) \<and>
  (lvl t' = lvl t \<and> sngl t \<longrightarrow> sngl t')"

lemma pre_adj_if_postR:
  "invar\<langle>lv, l, a, r\<rangle> \<Longrightarrow> post_del r r' \<Longrightarrow> pre_adjust \<langle>lv, l, a, r'\<rangle>"
by(cases "sngl r")
  (auto simp: pre_adjust.simps post_del_def invar.simps(2) elim: sngl.elims)

lemma pre_adj_if_postL:
  "invar\<langle>lv, l, a, r\<rangle> \<Longrightarrow> post_del l l' \<Longrightarrow> pre_adjust \<langle>lv, l', b, r\<rangle>"
by(cases "sngl r")
  (auto simp: pre_adjust.simps post_del_def invar.simps(2) elim: sngl.elims)

lemma post_del_adjL:
  "\<lbrakk> invar\<langle>lv, l, a, r\<rangle>; pre_adjust \<langle>lv, l', b, r\<rangle> \<rbrakk>
  \<Longrightarrow> post_del \<langle>lv, l, a, r\<rangle> (adjust \<langle>lv, l', b, r\<rangle>)"
unfolding post_del_def
by (metis invar_adjust lvl_adjust sngl_NodeI sngl_adjust lvl.simps(2))

lemma post_del_adjR:
assumes "invar\<langle>lv, l, a, r\<rangle>" "pre_adjust \<langle>lv, l, a, r'\<rangle>" "post_del r r'"
shows "post_del \<langle>lv, l, a, r\<rangle> (adjust \<langle>lv, l, a, r'\<rangle>)"
proof(unfold post_del_def, safe del: disjCI)
  let ?t = "\<langle>lv, l, a, r\<rangle>"
  let ?t' = "adjust \<langle>lv, l, a, r'\<rangle>"
  show "invar ?t'" by(rule invar_adjust[OF assms(2)])
  show "lvl ?t' = lvl ?t \<or> lvl ?t' + 1 = lvl ?t"
    using lvl_adjust[OF assms(2)] by auto
  show "sngl ?t'" if as: "lvl ?t' = lvl ?t" "sngl ?t"
  proof -
    have s: "sngl \<langle>lv, l, a, r'\<rangle>"
    proof(cases r')
      case Leaf thus ?thesis by simp
    next
      case Node thus ?thesis using as(2) assms(1,3)
      by (cases r) (auto simp: post_del_def)
    qed
    show ?thesis using as(1) sngl_adjust[OF assms(2) s] by simp
  qed
qed

declare prod.splits[split]

theorem post_del_max:
 "\<lbrakk> invar t; (t', x) = del_max t; t \<noteq> Leaf \<rbrakk> \<Longrightarrow> post_del t t'"
proof (induction t arbitrary: t' rule: del_max.induct)
  case (2 lv l a lvr rl ra rr)
  let ?r =  "\<langle>lvr, rl, ra, rr\<rangle>"
  let ?t = "\<langle>lv, l, a, ?r\<rangle>"
  from "2.prems"(2) obtain r' where r': "(r', x) = del_max ?r"
    and [simp]: "t' = adjust \<langle>lv, l, a, r'\<rangle>" by auto
  from  "2.IH"[OF _ r'] \<open>invar ?t\<close> have post: "post_del ?r r'" by simp
  note preR = pre_adj_if_postR[OF \<open>invar ?t\<close> post]
  show ?case by (simp add: post_del_adjR[OF "2.prems"(1) preR post])
qed (auto simp: post_del_def)

theorem post_delete: "invar t \<Longrightarrow> post_del t (delete x t)"
proof (induction t)
  case (Node lv l a r)

  let ?l' = "delete x l" and ?r' = "delete x r"
  let ?t = "Node lv l a r" let ?t' = "delete x ?t"

  from Node.prems have inv_l: "invar l" and inv_r: "invar r" by (auto)

  note post_l' = Node.IH(1)[OF inv_l]
  note preL = pre_adj_if_postL[OF Node.prems post_l']

  note post_r' = Node.IH(2)[OF inv_r]
  note preR = pre_adj_if_postR[OF Node.prems post_r']

  show ?case
  proof (cases rule: linorder_cases[of x a])
    case less
    thus ?thesis using Node.prems by (simp add: post_del_adjL preL)
  next
    case greater
    thus ?thesis using Node.prems by (simp add: post_del_adjR preR post_r')
  next
    case equal
    show ?thesis
    proof cases
      assume "l = Leaf" thus ?thesis using equal Node.prems
        by(auto simp: post_del_def invar.simps(2))
    next
      assume "l \<noteq> Leaf" thus ?thesis using equal
        by simp (metis Node.prems inv_l post_del_adjL post_del_max pre_adj_if_postL)
    qed
  qed
qed (simp add: post_del_def)

declare invar_2Nodes[simp del]


subsection "Functional Correctness"


subsubsection "Proofs for insert"

lemma inorder_split: "inorder(split t) = inorder t"
by(cases t rule: split.cases) (auto)

lemma inorder_skew: "inorder(skew t) = inorder t"
by(cases t rule: skew.cases) (auto)

lemma inorder_insert:
  "sorted(inorder t) \<Longrightarrow> inorder(insert x t) = ins_list x (inorder t)"
by(induction t) (auto simp: ins_list_simps inorder_split inorder_skew)


subsubsection "Proofs for delete"

lemma inorder_adjust: "t \<noteq> Leaf \<Longrightarrow> pre_adjust t \<Longrightarrow> inorder(adjust t) = inorder t"
by(cases t)
  (auto simp: adjust_def inorder_skew inorder_split invar.simps(2) pre_adjust.simps
     split: tree.splits)

lemma del_maxD:
  "\<lbrakk> del_max t = (t',x); t \<noteq> Leaf; invar t \<rbrakk> \<Longrightarrow> inorder t' @ [x] = inorder t"
by(induction t arbitrary: t' rule: del_max.induct)
  (auto simp: sorted_lems inorder_adjust pre_adj_if_postR post_del_max split: prod.splits)

lemma inorder_delete:
  "invar t \<Longrightarrow> sorted(inorder t) \<Longrightarrow> inorder(delete x t) = del_list x (inorder t)"
by(induction t)
  (auto simp: del_list_simps inorder_adjust pre_adj_if_postL pre_adj_if_postR 
              post_del_max post_delete del_maxD split: prod.splits)

interpretation I: Set_by_Ordered
where empty = Leaf and isin = isin and insert = insert and delete = delete
and inorder = inorder and inv = invar
proof (standard, goal_cases)
  case 1 show ?case by simp
next
  case 2 thus ?case by(simp add: isin_set)
next
  case 3 thus ?case by(simp add: inorder_insert)
next
  case 4 thus ?case by(simp add: inorder_delete)
next
  case 5 thus ?case by(simp)
next
  case 6 thus ?case by(simp add: invar_insert)
next
  case 7 thus ?case using post_delete by(auto simp: post_del_def)
qed

end
