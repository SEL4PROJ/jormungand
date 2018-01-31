section \<open>An old chestnut\<close>

theory Puzzle
  imports Main
begin

text_raw \<open>\<^footnote>\<open>A question from ``Bundeswettbewerb Mathematik''. Original
  pen-and-paper proof due to Herbert Ehler; Isabelle tactic script by Tobias
  Nipkow.\<close>\<close>

text \<open>
  \<^bold>\<open>Problem.\<close> Given some function \<open>f: \<nat> \<rightarrow> \<nat>\<close> such that \<open>f (f n) < f (Suc n)\<close>
  for all \<open>n\<close>. Demonstrate that \<open>f\<close> is the identity.
\<close>

theorem
  assumes f_ax: "\<And>n. f (f n) < f (Suc n)"
  shows "f n = n"
proof (rule order_antisym)
  show ge: "n \<le> f n" for n
  proof (induct "f n" arbitrary: n rule: less_induct)
    case less
    show "n \<le> f n"
    proof (cases n)
      case (Suc m)
      from f_ax have "f (f m) < f n" by (simp only: Suc)
      with less have "f m \<le> f (f m)" .
      also from f_ax have "\<dots> < f n" by (simp only: Suc)
      finally have "f m < f n" .
      with less have "m \<le> f m" .
      also note \<open>\<dots> < f n\<close>
      finally have "m < f n" .
      then have "n \<le> f n" by (simp only: Suc)
      then show ?thesis .
    next
      case 0
      then show ?thesis by simp
    qed
  qed

  have mono: "m \<le> n \<Longrightarrow> f m \<le> f n" for m n :: nat
  proof (induct n)
    case 0
    then have "m = 0" by simp
    then show ?case by simp
  next
    case (Suc n)
    from Suc.prems show "f m \<le> f (Suc n)"
    proof (rule le_SucE)
      assume "m \<le> n"
      with Suc.hyps have "f m \<le> f n" .
      also from ge f_ax have "\<dots> < f (Suc n)"
        by (rule le_less_trans)
      finally show ?thesis by simp
    next
      assume "m = Suc n"
      then show ?thesis by simp
    qed
  qed

  show "f n \<le> n"
  proof -
    have "\<not> n < f n"
    proof
      assume "n < f n"
      then have "Suc n \<le> f n" by simp
      then have "f (Suc n) \<le> f (f n)" by (rule mono)
      also have "\<dots> < f (Suc n)" by (rule f_ax)
      finally have "\<dots> < \<dots>" . then show False ..
    qed
    then show ?thesis by simp
  qed
qed

end
