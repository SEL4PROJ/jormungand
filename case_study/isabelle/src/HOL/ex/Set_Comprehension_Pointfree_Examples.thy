(*  Title:      HOL/ex/Set_Comprehension_Pointfree_Examples.thy
    Author:     Lukas Bulwahn, Rafal Kolanski
    Copyright   2012 TU Muenchen
*)

section \<open>Examples for the set comprehension to pointfree simproc\<close>

theory Set_Comprehension_Pointfree_Examples
imports Main
begin

declare [[simproc add: finite_Collect]]

lemma
  "finite (UNIV::'a set) ==> finite {p. EX x::'a. p = (x, x)}"
  by simp

lemma
  "finite A ==> finite B ==> finite {f a b| a b. a : A \<and> b : B}"
  by simp
  
lemma
  "finite B ==> finite A' ==> finite {f a b| a b. a : A \<and> a : A' \<and> b : B}"
  by simp

lemma
  "finite A ==> finite B ==> finite {f a b| a b. a : A \<and> b : B \<and> b : B'}"
  by simp

lemma
  "finite A ==> finite B ==> finite C ==> finite {f a b c| a b c. a : A \<and> b : B \<and> c : C}"
  by simp

lemma
  "finite A ==> finite B ==> finite C ==> finite D ==>
     finite {f a b c d| a b c d. a : A \<and> b : B \<and> c : C \<and> d : D}"
  by simp

lemma
  "finite A ==> finite B ==> finite C ==> finite D ==> finite E ==>
    finite {f a b c d e | a b c d e. a : A \<and> b : B \<and> c : C \<and> d : D \<and> e : E}"
  by simp

lemma
  "finite A ==> finite B ==> finite C ==> finite D ==> finite E \<Longrightarrow>
    finite {f a d c b e | e b c d a. b : B \<and> a : A \<and> e : E' \<and> c : C \<and> d : D \<and> e : E \<and> b : B'}"
  by simp

lemma
  "\<lbrakk> finite A ; finite B ; finite C ; finite D \<rbrakk>
  \<Longrightarrow> finite ({f a b c d| a b c d. a : A \<and> b : B \<and> c : C \<and> d : D})"
  by simp

lemma
  "finite ((\<lambda>(a,b,c,d). f a b c d) ` (A \<times> B \<times> C \<times> D))
  \<Longrightarrow> finite ({f a b c d| a b c d. a : A \<and> b : B \<and> c : C \<and> d : D})"
  by simp

lemma
  "finite S ==> finite {s'. EX s:S. s' = f a e s}"
  by simp

lemma
  "finite A ==> finite B ==> finite {f a b| a b. a : A \<and> b : B \<and> a \<notin> Z}"
  by simp

lemma
  "finite A ==> finite B ==> finite R ==> finite {f a b x y| a b x y. a : A \<and> b : B \<and> (x,y) \<in> R}"
by simp

lemma
  "finite A ==> finite B ==> finite R ==> finite {f a b x y| a b x y. a : A \<and> (x,y) \<in> R \<and> b : B}"
by simp

lemma
  "finite A ==> finite B ==> finite R ==> finite {f a (x, b) y| y b x a. a : A \<and> (x,y) \<in> R \<and> b : B}"
by simp

lemma
  "finite A ==> finite AA ==> finite B ==> finite {f a b| a b. (a : A \<or> a : AA) \<and> b : B \<and> a \<notin> Z}"
by simp

lemma
  "finite A1 ==> finite A2 ==> finite A3 ==> finite A4 ==> finite A5 ==> finite B ==>
     finite {f a b c | a b c. ((a : A1 \<and> a : A2) \<or> (a : A3 \<and> (a : A4 \<or> a : A5))) \<and> b : B \<and> a \<notin> Z}"
apply simp
oops

lemma "finite B ==> finite {c. EX x. x : B & c = a * x}"
by simp

lemma
  "finite A ==> finite B ==> finite {f a * g b |a b. a : A & b : B}"
by simp

lemma
  "finite S ==> inj (%(x, y). g x y) ==> finite {f x y| x y. g x y : S}"
  by (auto intro: finite_vimageI)

lemma
  "finite A ==> finite S ==> inj (%(x, y). g x y) ==> finite {f x y z | x y z. g x y : S & z : A}"
  by (auto intro: finite_vimageI)

lemma
  "finite S ==> finite A ==> inj (%(x, y). g x y) ==> inj (%(x, y). h x y)
    ==> finite {f a b c d | a b c d. g a c : S & h b d : A}"
  by (auto intro: finite_vimageI)

lemma
  assumes "finite S" shows "finite {(a,b,c,d). ([a, b], [c, d]) : S}"
using assms by (auto intro!: finite_vimageI simp add: inj_on_def)
  (* injectivity to be automated with further rules and automation *)

schematic_goal (* check interaction with schematics *)
  "finite {x :: ?'A \<Rightarrow> ?'B \<Rightarrow> bool. \<exists>a b. x = Pair_Rep a b}
   = finite ((\<lambda>(b :: ?'B, a:: ?'A). Pair_Rep a b) ` (UNIV \<times> UNIV))"
  by simp

declare [[simproc del: finite_Collect]]


section \<open>Testing simproc in code generation\<close>

definition union :: "nat set => nat set => nat set"
where
  "union A B = {x. x : A \<or> x : B}"

definition common_subsets :: "nat set => nat set => nat set set"
where
  "common_subsets S1 S2 = {S. S \<subseteq> S1 \<and> S \<subseteq> S2}"

definition products :: "nat set => nat set => nat set"
where
  "products A B = {c. EX a b. a : A & b : B & c = a * b}"

export_code products in Haskell

export_code union common_subsets products in Haskell

end
