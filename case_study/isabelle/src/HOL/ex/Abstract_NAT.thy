(*  Title:      HOL/ex/Abstract_NAT.thy
    Author:     Makarius
*)

section \<open>Abstract Natural Numbers primitive recursion\<close>

theory Abstract_NAT
imports Main
begin

text \<open>Axiomatic Natural Numbers (Peano) -- a monomorphic theory.\<close>

locale NAT =
  fixes zero :: 'n
    and succ :: "'n \<Rightarrow> 'n"
  assumes succ_inject [simp]: "succ m = succ n \<longleftrightarrow> m = n"
    and succ_neq_zero [simp]: "succ m \<noteq> zero"
    and induct [case_names zero succ, induct type: 'n]:
      "P zero \<Longrightarrow> (\<And>n. P n \<Longrightarrow> P (succ n)) \<Longrightarrow> P n"
begin

lemma zero_neq_succ [simp]: "zero \<noteq> succ m"
  by (rule succ_neq_zero [symmetric])


text \<open>\<^medskip> Primitive recursion as a (functional) relation -- polymorphic!\<close>

inductive Rec :: "'a \<Rightarrow> ('n \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'n \<Rightarrow> 'a \<Rightarrow> bool"
  for e :: 'a and r :: "'n \<Rightarrow> 'a \<Rightarrow> 'a"
where
  Rec_zero: "Rec e r zero e"
| Rec_succ: "Rec e r m n \<Longrightarrow> Rec e r (succ m) (r m n)"

lemma Rec_functional:
  fixes x :: 'n
  shows "\<exists>!y::'a. Rec e r x y"
proof -
  let ?R = "Rec e r"
  show ?thesis
  proof (induct x)
    case zero
    show "\<exists>!y. ?R zero y"
    proof
      show "?R zero e" ..
      show "y = e" if "?R zero y" for y
        using that by cases simp_all
    qed
  next
    case (succ m)
    from \<open>\<exists>!y. ?R m y\<close>
    obtain y where y: "?R m y" and yy': "\<And>y'. ?R m y' \<Longrightarrow> y = y'"
      by blast
    show "\<exists>!z. ?R (succ m) z"
    proof
      from y show "?R (succ m) (r m y)" ..
    next
      fix z
      assume "?R (succ m) z"
      then obtain u where "z = r m u" and "?R m u"
        by cases simp_all
      with yy' show "z = r m y"
        by (simp only:)
    qed
  qed
qed


text \<open>\<^medskip> The recursion operator -- polymorphic!\<close>

definition rec :: "'a \<Rightarrow> ('n \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'n \<Rightarrow> 'a"
  where "rec e r x = (THE y. Rec e r x y)"

lemma rec_eval:
  assumes Rec: "Rec e r x y"
  shows "rec e r x = y"
  unfolding rec_def
  using Rec_functional and Rec by (rule the1_equality)

lemma rec_zero [simp]: "rec e r zero = e"
proof (rule rec_eval)
  show "Rec e r zero e" ..
qed

lemma rec_succ [simp]: "rec e r (succ m) = r m (rec e r m)"
proof (rule rec_eval)
  let ?R = "Rec e r"
  have "?R m (rec e r m)"
    unfolding rec_def using Rec_functional by (rule theI')
  then show "?R (succ m) (r m (rec e r m))" ..
qed


text \<open>\<^medskip> Example: addition (monomorphic)\<close>

definition add :: "'n \<Rightarrow> 'n \<Rightarrow> 'n"
  where "add m n = rec n (\<lambda>_ k. succ k) m"

lemma add_zero [simp]: "add zero n = n"
  and add_succ [simp]: "add (succ m) n = succ (add m n)"
  unfolding add_def by simp_all

lemma add_assoc: "add (add k m) n = add k (add m n)"
  by (induct k) simp_all

lemma add_zero_right: "add m zero = m"
  by (induct m) simp_all

lemma add_succ_right: "add m (succ n) = succ (add m n)"
  by (induct m) simp_all

lemma "add (succ (succ (succ zero))) (succ (succ zero)) =
    succ (succ (succ (succ (succ zero))))"
  by simp


text \<open>\<^medskip> Example: replication (polymorphic)\<close>

definition repl :: "'n \<Rightarrow> 'a \<Rightarrow> 'a list"
  where "repl n x = rec [] (\<lambda>_ xs. x # xs) n"

lemma repl_zero [simp]: "repl zero x = []"
  and repl_succ [simp]: "repl (succ n) x = x # repl n x"
  unfolding repl_def by simp_all

lemma "repl (succ (succ (succ zero))) True = [True, True, True]"
  by simp

end


text \<open>\<^medskip> Just see that our abstract specification makes sense \dots\<close>

interpretation NAT 0 Suc
proof (rule NAT.intro)
  fix m n
  show "Suc m = Suc n \<longleftrightarrow> m = n" by simp
  show "Suc m \<noteq> 0" by simp
  show "P n"
    if zero: "P 0"
    and succ: "\<And>n. P n \<Longrightarrow> P (Suc n)"
    for P
  proof (induct n)
    case 0
    show ?case by (rule zero)
  next
    case Suc
    then show ?case by (rule succ)
  qed
qed

end
