(* Author: Tobias Nipkow *)

theory Hoare_Total_EX
imports Hoare
begin

subsubsection "Hoare Logic for Total Correctness --- \<open>nat\<close>-Indexed Invariant"

text{* This is the standard set of rules that you find in many publications.
The While-rule is different from the one in Concrete Semantics in that the
invariant is indexed by natural numbers and goes down by 1 with
every iteration. The completeness proof is easier but the rule is harder
to apply in program proofs. *}

definition hoare_tvalid :: "assn \<Rightarrow> com \<Rightarrow> assn \<Rightarrow> bool"
  ("\<Turnstile>\<^sub>t {(1_)}/ (_)/ {(1_)}" 50) where
"\<Turnstile>\<^sub>t {P}c{Q}  \<longleftrightarrow>  (\<forall>s. P s \<longrightarrow> (\<exists>t. (c,s) \<Rightarrow> t \<and> Q t))"

inductive
  hoaret :: "assn \<Rightarrow> com \<Rightarrow> assn \<Rightarrow> bool" ("\<turnstile>\<^sub>t ({(1_)}/ (_)/ {(1_)})" 50)
where

Skip:  "\<turnstile>\<^sub>t {P} SKIP {P}"  |

Assign:  "\<turnstile>\<^sub>t {\<lambda>s. P(s[a/x])} x::=a {P}"  |

Seq: "\<lbrakk> \<turnstile>\<^sub>t {P\<^sub>1} c\<^sub>1 {P\<^sub>2}; \<turnstile>\<^sub>t {P\<^sub>2} c\<^sub>2 {P\<^sub>3} \<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>t {P\<^sub>1} c\<^sub>1;;c\<^sub>2 {P\<^sub>3}"  |

If: "\<lbrakk> \<turnstile>\<^sub>t {\<lambda>s. P s \<and> bval b s} c\<^sub>1 {Q}; \<turnstile>\<^sub>t {\<lambda>s. P s \<and> \<not> bval b s} c\<^sub>2 {Q} \<rbrakk>
  \<Longrightarrow> \<turnstile>\<^sub>t {P} IF b THEN c\<^sub>1 ELSE c\<^sub>2 {Q}"  |

While:
  "\<lbrakk> \<And>n::nat. \<turnstile>\<^sub>t {P (Suc n)} c {P n};
     \<forall>n s. P (Suc n) s \<longrightarrow> bval b s;  \<forall>s. P 0 s \<longrightarrow> \<not> bval b s \<rbrakk>
   \<Longrightarrow> \<turnstile>\<^sub>t {\<lambda>s. \<exists>n. P n s} WHILE b DO c {P 0}"  |

conseq: "\<lbrakk> \<forall>s. P' s \<longrightarrow> P s; \<turnstile>\<^sub>t {P}c{Q}; \<forall>s. Q s \<longrightarrow> Q' s  \<rbrakk> \<Longrightarrow>
           \<turnstile>\<^sub>t {P'}c{Q'}"

text{* Building in the consequence rule: *}

lemma strengthen_pre:
  "\<lbrakk> \<forall>s. P' s \<longrightarrow> P s;  \<turnstile>\<^sub>t {P} c {Q} \<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>t {P'} c {Q}"
by (metis conseq)

lemma weaken_post:
  "\<lbrakk> \<turnstile>\<^sub>t {P} c {Q};  \<forall>s. Q s \<longrightarrow> Q' s \<rbrakk> \<Longrightarrow>  \<turnstile>\<^sub>t {P} c {Q'}"
by (metis conseq)

lemma Assign': "\<forall>s. P s \<longrightarrow> Q(s[a/x]) \<Longrightarrow> \<turnstile>\<^sub>t {P} x ::= a {Q}"
by (simp add: strengthen_pre[OF _ Assign])

text{* The soundness theorem: *}

theorem hoaret_sound: "\<turnstile>\<^sub>t {P}c{Q}  \<Longrightarrow>  \<Turnstile>\<^sub>t {P}c{Q}"
proof(unfold hoare_tvalid_def, induction rule: hoaret.induct)
  case (While P c b)
  {
    fix n s
    have "\<lbrakk> P n s \<rbrakk> \<Longrightarrow> \<exists>t. (WHILE b DO c, s) \<Rightarrow> t \<and> P 0 t"
    proof(induction "n" arbitrary: s)
      case 0 thus ?case using While.hyps(3) WhileFalse by blast
    next
      case (Suc n)
      thus ?case by (meson While.IH While.hyps(2) WhileTrue)
    qed
  }
  thus ?case by auto
next
  case If thus ?case by auto blast
qed fastforce+


definition wpt :: "com \<Rightarrow> assn \<Rightarrow> assn" ("wp\<^sub>t") where
"wp\<^sub>t c Q  =  (\<lambda>s. \<exists>t. (c,s) \<Rightarrow> t \<and> Q t)"

lemma [simp]: "wp\<^sub>t SKIP Q = Q"
by(auto intro!: ext simp: wpt_def)

lemma [simp]: "wp\<^sub>t (x ::= e) Q = (\<lambda>s. Q(s(x := aval e s)))"
by(auto intro!: ext simp: wpt_def)

lemma [simp]: "wp\<^sub>t (c\<^sub>1;;c\<^sub>2) Q = wp\<^sub>t c\<^sub>1 (wp\<^sub>t c\<^sub>2 Q)"
unfolding wpt_def
apply(rule ext)
apply auto
done

lemma [simp]:
 "wp\<^sub>t (IF b THEN c\<^sub>1 ELSE c\<^sub>2) Q = (\<lambda>s. wp\<^sub>t (if bval b s then c\<^sub>1 else c\<^sub>2) Q s)"
apply(unfold wpt_def)
apply(rule ext)
apply auto
done


text{* Function @{text wpw} computes the weakest precondition of a While-loop
that is unfolded a fixed number of times. *}

fun wpw :: "bexp \<Rightarrow> com \<Rightarrow> nat \<Rightarrow> assn \<Rightarrow> assn" where
"wpw b c 0 Q s = (\<not> bval b s \<and> Q s)" |
"wpw b c (Suc n) Q s = (bval b s \<and> (\<exists>s'. (c,s) \<Rightarrow> s' \<and>  wpw b c n Q s'))"

lemma WHILE_Its: "(WHILE b DO c,s) \<Rightarrow> t \<Longrightarrow> Q t \<Longrightarrow> \<exists>n. wpw b c n Q s"
proof(induction "WHILE b DO c" s t rule: big_step_induct)
  case WhileFalse thus ?case using wpw.simps(1) by blast 
next
  case WhileTrue thus ?case using wpw.simps(2) by blast
qed

lemma wpt_is_pre: "\<turnstile>\<^sub>t {wp\<^sub>t c Q} c {Q}"
proof (induction c arbitrary: Q)
  case SKIP show ?case by (auto intro:hoaret.Skip)
next
  case Assign show ?case by (auto intro:hoaret.Assign)
next
  case Seq thus ?case by (auto intro:hoaret.Seq)
next
  case If thus ?case by (auto intro:hoaret.If hoaret.conseq)
next
  case (While b c)
  let ?w = "WHILE b DO c"
  have c1: "\<forall>s. wp\<^sub>t ?w Q s \<longrightarrow> (\<exists>n. wpw b c n Q s)"
    unfolding wpt_def by (metis WHILE_Its)
  have c3: "\<forall>s. wpw b c 0 Q s \<longrightarrow> Q s" by simp
  have w2: "\<forall>n s. wpw b c (Suc n) Q s \<longrightarrow> bval b s" by simp
  have w3: "\<forall>s. wpw b c 0 Q s \<longrightarrow> \<not> bval b s" by simp
  { fix n
    have 1: "\<forall>s. wpw b c (Suc n) Q s \<longrightarrow> (\<exists>t. (c, s) \<Rightarrow> t \<and> wpw b c n Q t)"
      by simp
    note strengthen_pre[OF 1 While.IH[of "wpw b c n Q", unfolded wpt_def]]
  }
  from conseq[OF c1 hoaret.While[OF this w2 w3] c3]
  show ?case .
qed

theorem hoaret_complete: "\<Turnstile>\<^sub>t {P}c{Q} \<Longrightarrow> \<turnstile>\<^sub>t {P}c{Q}"
apply(rule strengthen_pre[OF _ wpt_is_pre])
apply(auto simp: hoare_tvalid_def wpt_def)
done

corollary hoaret_sound_complete: "\<turnstile>\<^sub>t {P}c{Q} \<longleftrightarrow> \<Turnstile>\<^sub>t {P}c{Q}"
by (metis hoaret_sound hoaret_complete)

end
