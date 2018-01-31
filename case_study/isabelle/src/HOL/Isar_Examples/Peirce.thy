(*  Title:      HOL/Isar_Examples/Peirce.thy
    Author:     Makarius
*)

section \<open>Peirce's Law\<close>

theory Peirce
  imports Main
begin

text \<open>
  We consider Peirce's Law: \<open>((A \<longrightarrow> B) \<longrightarrow> A) \<longrightarrow> A\<close>. This is an inherently
  non-intuitionistic statement, so its proof will certainly involve some form
  of classical contradiction.

  The first proof is again a well-balanced combination of plain backward and
  forward reasoning. The actual classical step is where the negated goal may
  be introduced as additional assumption. This eventually leads to a
  contradiction.\<^footnote>\<open>The rule involved there is negation elimination; it holds in
  intuitionistic logic as well.\<close>\<close>

theorem "((A \<longrightarrow> B) \<longrightarrow> A) \<longrightarrow> A"
proof
  assume "(A \<longrightarrow> B) \<longrightarrow> A"
  show A
  proof (rule classical)
    assume "\<not> A"
    have "A \<longrightarrow> B"
    proof
      assume A
      with \<open>\<not> A\<close> show B by contradiction
    qed
    with \<open>(A \<longrightarrow> B) \<longrightarrow> A\<close> show A ..
  qed
qed

text \<open>
  In the subsequent version the reasoning is rearranged by means of ``weak
  assumptions'' (as introduced by \<^theory_text>\<open>presume\<close>). Before assuming the negated
  goal \<open>\<not> A\<close>, its intended consequence \<open>A \<longrightarrow> B\<close> is put into place in order to
  solve the main problem. Nevertheless, we do not get anything for free, but
  have to establish \<open>A \<longrightarrow> B\<close> later on. The overall effect is that of a logical
  \<^emph>\<open>cut\<close>.

  Technically speaking, whenever some goal is solved by \<^theory_text>\<open>show\<close> in the context
  of weak assumptions then the latter give rise to new subgoals, which may be
  established separately. In contrast, strong assumptions (as introduced by
  \<^theory_text>\<open>assume\<close>) are solved immediately.
\<close>

theorem "((A \<longrightarrow> B) \<longrightarrow> A) \<longrightarrow> A"
proof
  assume "(A \<longrightarrow> B) \<longrightarrow> A"
  show A
  proof (rule classical)
    presume "A \<longrightarrow> B"
    with \<open>(A \<longrightarrow> B) \<longrightarrow> A\<close> show A ..
  next
    assume "\<not> A"
    show "A \<longrightarrow> B"
    proof
      assume A
      with \<open>\<not> A\<close> show B by contradiction
    qed
  qed
qed

text \<open>
  Note that the goals stemming from weak assumptions may be even left until
  qed time, where they get eventually solved ``by assumption'' as well. In
  that case there is really no fundamental difference between the two kinds of
  assumptions, apart from the order of reducing the individual parts of the
  proof configuration.

  Nevertheless, the ``strong'' mode of plain assumptions is quite important in
  practice to achieve robustness of proof text interpretation. By forcing both
  the conclusion \<^emph>\<open>and\<close> the assumptions to unify with the pending goal to be
  solved, goal selection becomes quite deterministic. For example,
  decomposition with rules of the ``case-analysis'' type usually gives rise to
  several goals that only differ in there local contexts. With strong
  assumptions these may be still solved in any order in a predictable way,
  while weak ones would quickly lead to great confusion, eventually demanding
  even some backtracking.
\<close>

end
