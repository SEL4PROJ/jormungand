
section \<open>Various examples for transfer procedure\<close>

theory Transfer_Ex
imports Main Transfer_Int_Nat
begin

lemma ex1: "(x::nat) + y = y + x"
  by auto

lemma "0 \<le> (y::int) \<Longrightarrow> 0 \<le> (x::int) \<Longrightarrow> x + y = y + x"
  by (fact ex1 [transferred])

(* Using new transfer package *)
lemma "0 \<le> (x::int) \<Longrightarrow> 0 \<le> (y::int) \<Longrightarrow> x + y = y + x"
  by (fact ex1 [untransferred])

lemma ex2: "(a::nat) div b * b + a mod b = a"
  by (rule div_mult_mod_eq)

lemma "0 \<le> (b::int) \<Longrightarrow> 0 \<le> (a::int) \<Longrightarrow> a div b * b + a mod b = a"
  by (fact ex2 [transferred])

(* Using new transfer package *)
lemma "0 \<le> (a::int) \<Longrightarrow> 0 \<le> (b::int) \<Longrightarrow> a div b * b + a mod b = a"
  by (fact ex2 [untransferred])

lemma ex3: "ALL (x::nat). ALL y. EX z. z >= x + y"
  by auto

lemma "\<forall>x\<ge>0::int. \<forall>y\<ge>0. \<exists>z\<ge>0. x + y \<le> z"
  by (fact ex3 [transferred nat_int])

(* Using new transfer package *)
lemma "\<forall>x::int\<in>{0..}. \<forall>y\<in>{0..}. \<exists>z\<in>{0..}. x + y \<le> z"
  by (fact ex3 [untransferred])

lemma ex4: "(x::nat) >= y \<Longrightarrow> (x - y) + y = x"
  by auto

lemma "0 \<le> (x::int) \<Longrightarrow> 0 \<le> (y::int) \<Longrightarrow> y \<le> x \<Longrightarrow> tsub x y + y = x"
  by (fact ex4 [transferred])

(* Using new transfer package *)
lemma "0 \<le> (y::int) \<Longrightarrow> 0 \<le> (x::int) \<Longrightarrow> y \<le> x \<Longrightarrow> tsub x y + y = x"
  by (fact ex4 [untransferred])

lemma ex5: "(2::nat) * \<Sum>{..n} = n * (n + 1)"
  by (induct n rule: nat_induct, auto)

lemma "0 \<le> (n::int) \<Longrightarrow> 2 * \<Sum>{0..n} = n * (n + 1)"
  by (fact ex5 [transferred])

(* Using new transfer package *)
lemma "0 \<le> (n::int) \<Longrightarrow> 2 * \<Sum>{0..n} = n * (n + 1)"
  by (fact ex5 [untransferred])

lemma "0 \<le> (n::nat) \<Longrightarrow> 2 * \<Sum>{0..n} = n * (n + 1)"
  by (fact ex5 [transferred, transferred])

(* Using new transfer package *)
lemma "0 \<le> (n::nat) \<Longrightarrow> 2 * \<Sum>{..n} = n * (n + 1)"
  by (fact ex5 [untransferred, Transfer.transferred])

end
