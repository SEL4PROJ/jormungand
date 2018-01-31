(*  Title:      HOL/Isar_Examples/Fibonacci.thy
    Author:     Gertrud Bauer
    Copyright   1999 Technische Universitaet Muenchen

The Fibonacci function.  Original
tactic script by Lawrence C Paulson.

Fibonacci numbers: proofs of laws taken from

  R. L. Graham, D. E. Knuth, O. Patashnik.
  Concrete Mathematics.
  (Addison-Wesley, 1989)
*)

section \<open>Fib and Gcd commute\<close>

theory Fibonacci
  imports "../Number_Theory/Primes"
begin

text_raw \<open>\<^footnote>\<open>Isar version by Gertrud Bauer. Original tactic script by Larry
  Paulson. A few proofs of laws taken from @{cite "Concrete-Math"}.\<close>\<close>


declare One_nat_def [simp]


subsection \<open>Fibonacci numbers\<close>

fun fib :: "nat \<Rightarrow> nat"
  where
    "fib 0 = 0"
  | "fib (Suc 0) = 1"
  | "fib (Suc (Suc x)) = fib x + fib (Suc x)"

lemma [simp]: "fib (Suc n) > 0"
  by (induct n rule: fib.induct) simp_all


text \<open>Alternative induction rule.\<close>

theorem fib_induct: "P 0 \<Longrightarrow> P 1 \<Longrightarrow> (\<And>n. P (n + 1) \<Longrightarrow> P n \<Longrightarrow> P (n + 2)) \<Longrightarrow> P n"
  for n :: nat
  by (induct rule: fib.induct) simp_all


subsection \<open>Fib and gcd commute\<close>

text \<open>A few laws taken from @{cite "Concrete-Math"}.\<close>

lemma fib_add: "fib (n + k + 1) = fib (k + 1) * fib (n + 1) + fib k * fib n"
  (is "?P n")
  \<comment> \<open>see @{cite \<open>page 280\<close> "Concrete-Math"}\<close>
proof (induct n rule: fib_induct)
  show "?P 0" by simp
  show "?P 1" by simp
  fix n
  have "fib (n + 2 + k + 1)
    = fib (n + k + 1) + fib (n + 1 + k + 1)" by simp
  also assume "fib (n + k + 1) = fib (k + 1) * fib (n + 1) + fib k * fib n" (is " _ = ?R1")
  also assume "fib (n + 1 + k + 1) = fib (k + 1) * fib (n + 1 + 1) + fib k * fib (n + 1)"
    (is " _ = ?R2")
  also have "?R1 + ?R2 = fib (k + 1) * fib (n + 2 + 1) + fib k * fib (n + 2)"
    by (simp add: add_mult_distrib2)
  finally show "?P (n + 2)" .
qed

lemma gcd_fib_Suc_eq_1: "gcd (fib n) (fib (n + 1)) = 1"
  (is "?P n")
proof (induct n rule: fib_induct)
  show "?P 0" by simp
  show "?P 1" by simp
  fix n
  have "fib (n + 2 + 1) = fib (n + 1) + fib (n + 2)"
    by simp
  also have "\<dots> = fib (n + 2) + fib (n + 1)"
    by simp
  also have "gcd (fib (n + 2)) \<dots> = gcd (fib (n + 2)) (fib (n + 1))"
    by (rule gcd_add2)
  also have "\<dots> = gcd (fib (n + 1)) (fib (n + 1 + 1))"
    by (simp add: gcd.commute)
  also assume "\<dots> = 1"
  finally show "?P (n + 2)" .
qed

lemma gcd_mult_add: "(0::nat) < n \<Longrightarrow> gcd (n * k + m) n = gcd m n"
proof -
  assume "0 < n"
  then have "gcd (n * k + m) n = gcd n (m mod n)"
    by (simp add: gcd_non_0_nat add.commute)
  also from \<open>0 < n\<close> have "\<dots> = gcd m n"
    by (simp add: gcd_non_0_nat)
  finally show ?thesis .
qed

lemma gcd_fib_add: "gcd (fib m) (fib (n + m)) = gcd (fib m) (fib n)"
proof (cases m)
  case 0
  then show ?thesis by simp
next
  case (Suc k)
  then have "gcd (fib m) (fib (n + m)) = gcd (fib (n + k + 1)) (fib (k + 1))"
    by (simp add: gcd.commute)
  also have "fib (n + k + 1) = fib (k + 1) * fib (n + 1) + fib k * fib n"
    by (rule fib_add)
  also have "gcd \<dots> (fib (k + 1)) = gcd (fib k * fib n) (fib (k + 1))"
    by (simp add: gcd_mult_add)
  also have "\<dots> = gcd (fib n) (fib (k + 1))"
    by (simp only: gcd_fib_Suc_eq_1 gcd_mult_cancel)
  also have "\<dots> = gcd (fib m) (fib n)"
    using Suc by (simp add: gcd.commute)
  finally show ?thesis .
qed

lemma gcd_fib_diff: "gcd (fib m) (fib (n - m)) = gcd (fib m) (fib n)" if "m \<le> n"
proof -
  have "gcd (fib m) (fib (n - m)) = gcd (fib m) (fib (n - m + m))"
    by (simp add: gcd_fib_add)
  also from \<open>m \<le> n\<close> have "n - m + m = n"
    by simp
  finally show ?thesis .
qed

lemma gcd_fib_mod: "gcd (fib m) (fib (n mod m)) = gcd (fib m) (fib n)" if "0 < m"
proof (induct n rule: nat_less_induct)
  case hyp: (1 n)
  show ?case
  proof -
    have "n mod m = (if n < m then n else (n - m) mod m)"
      by (rule mod_if)
    also have "gcd (fib m) (fib \<dots>) = gcd (fib m) (fib n)"
    proof (cases "n < m")
      case True
      then show ?thesis by simp
    next
      case False
      then have "m \<le> n" by simp
      from \<open>0 < m\<close> and False have "n - m < n"
        by simp
      with hyp have "gcd (fib m) (fib ((n - m) mod m))
          = gcd (fib m) (fib (n - m))" by simp
      also have "\<dots> = gcd (fib m) (fib n)"
        using \<open>m \<le> n\<close> by (rule gcd_fib_diff)
      finally have "gcd (fib m) (fib ((n - m) mod m)) =
          gcd (fib m) (fib n)" .
      with False show ?thesis by simp
    qed
    finally show ?thesis .
  qed
qed

theorem fib_gcd: "fib (gcd m n) = gcd (fib m) (fib n)"
  (is "?P m n")
proof (induct m n rule: gcd_nat_induct)
  fix m n :: nat
  show "fib (gcd m 0) = gcd (fib m) (fib 0)"
    by simp
  assume n: "0 < n"
  then have "gcd m n = gcd n (m mod n)"
    by (simp add: gcd_non_0_nat)
  also assume hyp: "fib \<dots> = gcd (fib n) (fib (m mod n))"
  also from n have "\<dots> = gcd (fib n) (fib m)"
    by (rule gcd_fib_mod)
  also have "\<dots> = gcd (fib m) (fib n)"
    by (rule gcd.commute)
  finally show "fib (gcd m n) = gcd (fib m) (fib n)" .
qed

end
