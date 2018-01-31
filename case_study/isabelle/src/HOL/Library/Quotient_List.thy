(*  Title:      HOL/Library/Quotient_List.thy
    Author:     Cezary Kaliszyk and Christian Urban
*)

section \<open>Quotient infrastructure for the list type\<close>

theory Quotient_List
imports Quotient_Set Quotient_Product Quotient_Option
begin

subsection \<open>Rules for the Quotient package\<close>

lemma map_id [id_simps]:
  "map id = id"
  by (fact List.map.id)

lemma list_all2_eq [id_simps]:
  "list_all2 (op =) = (op =)"
proof (rule ext)+
  fix xs ys
  show "list_all2 (op =) xs ys \<longleftrightarrow> xs = ys"
    by (induct xs ys rule: list_induct2') simp_all
qed

lemma reflp_list_all2:
  assumes "reflp R"
  shows "reflp (list_all2 R)"
proof (rule reflpI)
  from assms have *: "\<And>xs. R xs xs" by (rule reflpE)
  fix xs
  show "list_all2 R xs xs"
    by (induct xs) (simp_all add: *)
qed

lemma list_symp:
  assumes "symp R"
  shows "symp (list_all2 R)"
proof (rule sympI)
  from assms have *: "\<And>xs ys. R xs ys \<Longrightarrow> R ys xs" by (rule sympE)
  fix xs ys
  assume "list_all2 R xs ys"
  then show "list_all2 R ys xs"
    by (induct xs ys rule: list_induct2') (simp_all add: *)
qed

lemma list_transp:
  assumes "transp R"
  shows "transp (list_all2 R)"
proof (rule transpI)
  from assms have *: "\<And>xs ys zs. R xs ys \<Longrightarrow> R ys zs \<Longrightarrow> R xs zs" by (rule transpE)
  fix xs ys zs
  assume "list_all2 R xs ys" and "list_all2 R ys zs"
  then show "list_all2 R xs zs"
    by (induct arbitrary: zs) (auto simp: list_all2_Cons1 intro: *)
qed

lemma list_equivp [quot_equiv]:
  "equivp R \<Longrightarrow> equivp (list_all2 R)"
  by (blast intro: equivpI reflp_list_all2 list_symp list_transp elim: equivpE)

lemma list_quotient3 [quot_thm]:
  assumes "Quotient3 R Abs Rep"
  shows "Quotient3 (list_all2 R) (map Abs) (map Rep)"
proof (rule Quotient3I)
  from assms have "\<And>x. Abs (Rep x) = x" by (rule Quotient3_abs_rep)
  then show "\<And>xs. map Abs (map Rep xs) = xs" by (simp add: comp_def)
next
  from assms have "\<And>x y. R (Rep x) (Rep y) \<longleftrightarrow> x = y" by (rule Quotient3_rel_rep)
  then show "\<And>xs. list_all2 R (map Rep xs) (map Rep xs)"
    by (simp add: list_all2_map1 list_all2_map2 list_all2_eq)
next
  fix xs ys
  from assms have "\<And>x y. R x x \<and> R y y \<and> Abs x = Abs y \<longleftrightarrow> R x y" by (rule Quotient3_rel)
  then show "list_all2 R xs ys \<longleftrightarrow> list_all2 R xs xs \<and> list_all2 R ys ys \<and> map Abs xs = map Abs ys"
    by (induct xs ys rule: list_induct2') auto
qed

declare [[mapQ3 list = (list_all2, list_quotient3)]]

lemma cons_prs [quot_preserve]:
  assumes q: "Quotient3 R Abs Rep"
  shows "(Rep ---> (map Rep) ---> (map Abs)) (op #) = (op #)"
  by (auto simp add: fun_eq_iff comp_def Quotient3_abs_rep [OF q])

lemma cons_rsp [quot_respect]:
  assumes q: "Quotient3 R Abs Rep"
  shows "(R ===> list_all2 R ===> list_all2 R) (op #) (op #)"
  by auto

lemma nil_prs [quot_preserve]:
  assumes q: "Quotient3 R Abs Rep"
  shows "map Abs [] = []"
  by simp

lemma nil_rsp [quot_respect]:
  assumes q: "Quotient3 R Abs Rep"
  shows "list_all2 R [] []"
  by simp

lemma map_prs_aux:
  assumes a: "Quotient3 R1 abs1 rep1"
  and     b: "Quotient3 R2 abs2 rep2"
  shows "(map abs2) (map ((abs1 ---> rep2) f) (map rep1 l)) = map f l"
  by (induct l)
     (simp_all add: Quotient3_abs_rep[OF a] Quotient3_abs_rep[OF b])

lemma map_prs [quot_preserve]:
  assumes a: "Quotient3 R1 abs1 rep1"
  and     b: "Quotient3 R2 abs2 rep2"
  shows "((abs1 ---> rep2) ---> (map rep1) ---> (map abs2)) map = map"
  and   "((abs1 ---> id) ---> map rep1 ---> id) map = map"
  by (simp_all only: fun_eq_iff map_prs_aux[OF a b] comp_def)
    (simp_all add: Quotient3_abs_rep[OF a] Quotient3_abs_rep[OF b])

lemma map_rsp [quot_respect]:
  assumes q1: "Quotient3 R1 Abs1 Rep1"
  and     q2: "Quotient3 R2 Abs2 Rep2"
  shows "((R1 ===> R2) ===> (list_all2 R1) ===> list_all2 R2) map map"
  and   "((R1 ===> op =) ===> (list_all2 R1) ===> op =) map map"
  unfolding list_all2_eq [symmetric] by (rule list.map_transfer)+

lemma foldr_prs_aux:
  assumes a: "Quotient3 R1 abs1 rep1"
  and     b: "Quotient3 R2 abs2 rep2"
  shows "abs2 (foldr ((abs1 ---> abs2 ---> rep2) f) (map rep1 l) (rep2 e)) = foldr f l e"
  by (induct l) (simp_all add: Quotient3_abs_rep[OF a] Quotient3_abs_rep[OF b])

lemma foldr_prs [quot_preserve]:
  assumes a: "Quotient3 R1 abs1 rep1"
  and     b: "Quotient3 R2 abs2 rep2"
  shows "((abs1 ---> abs2 ---> rep2) ---> (map rep1) ---> rep2 ---> abs2) foldr = foldr"
  apply (simp add: fun_eq_iff)
  by (simp only: fun_eq_iff foldr_prs_aux[OF a b])
     (simp)

lemma foldl_prs_aux:
  assumes a: "Quotient3 R1 abs1 rep1"
  and     b: "Quotient3 R2 abs2 rep2"
  shows "abs1 (foldl ((abs1 ---> abs2 ---> rep1) f) (rep1 e) (map rep2 l)) = foldl f e l"
  by (induct l arbitrary:e) (simp_all add: Quotient3_abs_rep[OF a] Quotient3_abs_rep[OF b])

lemma foldl_prs [quot_preserve]:
  assumes a: "Quotient3 R1 abs1 rep1"
  and     b: "Quotient3 R2 abs2 rep2"
  shows "((abs1 ---> abs2 ---> rep1) ---> rep1 ---> (map rep2) ---> abs1) foldl = foldl"
  by (simp add: fun_eq_iff foldl_prs_aux [OF a b])

lemma foldl_rsp[quot_respect]:
  assumes q1: "Quotient3 R1 Abs1 Rep1"
  and     q2: "Quotient3 R2 Abs2 Rep2"
  shows "((R1 ===> R2 ===> R1) ===> R1 ===> list_all2 R2 ===> R1) foldl foldl"
  by (rule foldl_transfer)

lemma foldr_rsp[quot_respect]:
  assumes q1: "Quotient3 R1 Abs1 Rep1"
  and     q2: "Quotient3 R2 Abs2 Rep2"
  shows "((R1 ===> R2 ===> R2) ===> list_all2 R1 ===> R2 ===> R2) foldr foldr"
  by (rule foldr_transfer)

lemma list_all2_rsp:
  assumes r: "\<forall>x y. R x y \<longrightarrow> (\<forall>a b. R a b \<longrightarrow> S x a = T y b)"
  and l1: "list_all2 R x y"
  and l2: "list_all2 R a b"
  shows "list_all2 S x a = list_all2 T y b"
  using l1 l2
  by (induct arbitrary: a b rule: list_all2_induct,
    auto simp: list_all2_Cons1 list_all2_Cons2 r)

lemma [quot_respect]:
  "((R ===> R ===> op =) ===> list_all2 R ===> list_all2 R ===> op =) list_all2 list_all2"
  by (rule list.rel_transfer)

lemma [quot_preserve]:
  assumes a: "Quotient3 R abs1 rep1"
  shows "((abs1 ---> abs1 ---> id) ---> map rep1 ---> map rep1 ---> id) list_all2 = list_all2"
  apply (simp add: fun_eq_iff)
  apply clarify
  apply (induct_tac xa xb rule: list_induct2')
  apply (simp_all add: Quotient3_abs_rep[OF a])
  done

lemma [quot_preserve]:
  assumes a: "Quotient3 R abs1 rep1"
  shows "(list_all2 ((rep1 ---> rep1 ---> id) R) l m) = (l = m)"
  by (induct l m rule: list_induct2') (simp_all add: Quotient3_rel_rep[OF a])

lemma list_all2_find_element:
  assumes a: "x \<in> set a"
  and b: "list_all2 R a b"
  shows "\<exists>y. (y \<in> set b \<and> R x y)"
  using b a by induct auto

lemma list_all2_refl:
  assumes a: "\<And>x y. R x y = (R x = R y)"
  shows "list_all2 R x x"
  by (induct x) (auto simp add: a)

end
