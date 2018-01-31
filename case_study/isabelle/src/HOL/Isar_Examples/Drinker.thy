(*  Title:      HOL/Isar_Examples/Drinker.thy
    Author:     Makarius
*)

section \<open>The Drinker's Principle\<close>

theory Drinker
  imports Main
begin

text \<open>
  Here is another example of classical reasoning: the Drinker's Principle says
  that for some person, if he is drunk, everybody else is drunk!

  We first prove a classical part of de-Morgan's law.
\<close>

lemma de_Morgan:
  assumes "\<not> (\<forall>x. P x)"
  shows "\<exists>x. \<not> P x"
proof (rule classical)
  assume "\<nexists>x. \<not> P x"
  have "\<forall>x. P x"
  proof
    fix x show "P x"
    proof (rule classical)
      assume "\<not> P x"
      then have "\<exists>x. \<not> P x" ..
      with \<open>\<nexists>x. \<not> P x\<close> show ?thesis by contradiction
    qed
  qed
  with \<open>\<not> (\<forall>x. P x)\<close> show ?thesis by contradiction
qed

theorem Drinker's_Principle: "\<exists>x. drunk x \<longrightarrow> (\<forall>x. drunk x)"
proof cases
  assume "\<forall>x. drunk x"
  then have "drunk a \<longrightarrow> (\<forall>x. drunk x)" for a ..
  then show ?thesis ..
next
  assume "\<not> (\<forall>x. drunk x)"
  then have "\<exists>x. \<not> drunk x" by (rule de_Morgan)
  then obtain a where "\<not> drunk a" ..
  have "drunk a \<longrightarrow> (\<forall>x. drunk x)"
  proof
    assume "drunk a"
    with \<open>\<not> drunk a\<close> show "\<forall>x. drunk x" by contradiction
  qed
  then show ?thesis ..
qed

end
