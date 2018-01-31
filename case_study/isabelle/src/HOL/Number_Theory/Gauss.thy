(*  Authors:    Jeremy Avigad, David Gray, and Adam Kramer

Ported by lcp but unfinished
*)

section \<open>Gauss' Lemma\<close>

theory Gauss
imports Euler_Criterion
begin

lemma cong_prime_prod_zero_nat: 
  fixes a::nat
  shows "\<lbrakk>[a * b = 0] (mod p); prime p\<rbrakk> \<Longrightarrow> [a = 0] (mod p) | [b = 0] (mod p)"
  by (auto simp add: cong_altdef_nat)

lemma cong_prime_prod_zero_int: 
  fixes a::int
  shows "\<lbrakk>[a * b = 0] (mod p); prime p\<rbrakk> \<Longrightarrow> [a = 0] (mod p) | [b = 0] (mod p)"
  by (auto simp add: cong_altdef_int)


locale GAUSS =
  fixes p :: "nat"
  fixes a :: "int"

  assumes p_prime: "prime p"
  assumes p_ge_2: "2 < p"
  assumes p_a_relprime: "[a \<noteq> 0](mod p)"
  assumes a_nonzero:    "0 < a"
begin

definition "A = {0::int <.. ((int p - 1) div 2)}"
definition "B = (\<lambda>x. x * a) ` A"
definition "C = (\<lambda>x. x mod p) ` B"
definition "D = C \<inter> {.. (int p - 1) div 2}"
definition "E = C \<inter> {(int p - 1) div 2 <..}"
definition "F = (\<lambda>x. (int p - x)) ` E"


subsection \<open>Basic properties of p\<close>

lemma odd_p: "odd p"
by (metis p_prime p_ge_2 prime_odd_nat)

lemma p_minus_one_l: "(int p - 1) div 2 < p"
proof -
  have "(p - 1) div 2 \<le> (p - 1) div 1"
    by (metis div_by_1 div_le_dividend)
  also have "\<dots> = p - 1" by simp
  finally show ?thesis using p_ge_2 by arith
qed

lemma p_eq2: "int p = (2 * ((int p - 1) div 2)) + 1"
  using odd_p p_ge_2 nonzero_mult_div_cancel_left [of 2 "p - 1"]   
  by simp

lemma p_odd_int: obtains z::int where "int p = 2*z+1" "0<z"
  using odd_p p_ge_2
  by (auto simp add: even_iff_mod_2_eq_zero) (metis p_eq2)


subsection \<open>Basic Properties of the Gauss Sets\<close>

lemma finite_A: "finite (A)"
by (auto simp add: A_def)

lemma finite_B: "finite (B)"
by (auto simp add: B_def finite_A)

lemma finite_C: "finite (C)"
by (auto simp add: C_def finite_B)

lemma finite_D: "finite (D)"
by (auto simp add: D_def finite_C)

lemma finite_E: "finite (E)"
by (auto simp add: E_def finite_C)

lemma finite_F: "finite (F)"
by (auto simp add: F_def finite_E)

lemma C_eq: "C = D \<union> E"
by (auto simp add: C_def D_def E_def)

lemma A_card_eq: "card A = nat ((int p - 1) div 2)"
  by (auto simp add: A_def)

lemma inj_on_xa_A: "inj_on (\<lambda>x. x * a) A"
  using a_nonzero by (simp add: A_def inj_on_def)

definition ResSet :: "int => int set => bool"
  where "ResSet m X = (\<forall>y1 y2. (y1 \<in> X & y2 \<in> X & [y1 = y2] (mod m) --> y1 = y2))"

lemma ResSet_image:
  "\<lbrakk> 0 < m; ResSet m A; \<forall>x \<in> A. \<forall>y \<in> A. ([f x = f y](mod m) --> x = y) \<rbrakk> \<Longrightarrow>
    ResSet m (f ` A)"
  by (auto simp add: ResSet_def)

lemma A_res: "ResSet p A"
  using p_ge_2
  by (auto simp add: A_def ResSet_def intro!: cong_less_imp_eq_int)

lemma B_res: "ResSet p B"
proof -
  {fix x fix y
    assume a: "[x * a = y * a] (mod p)"
    assume b: "0 < x"
    assume c: "x \<le> (int p - 1) div 2"
    assume d: "0 < y"
    assume e: "y \<le> (int p - 1) div 2"
    from p_a_relprime have "\<not>p dvd a"
      by (simp add: cong_altdef_int)
    with p_prime have "coprime a (int p)" 
       by (subst gcd.commute, intro prime_imp_coprime) auto
    with a cong_mult_rcancel_int [of a "int p" x y]
      have "[x = y] (mod p)" by simp
    with cong_less_imp_eq_int [of x y p] p_minus_one_l
        order_le_less_trans [of x "(int p - 1) div 2" p]
        order_le_less_trans [of y "(int p - 1) div 2" p] 
    have "x = y"
      by (metis b c cong_less_imp_eq_int d e zero_less_imp_eq_int of_nat_0_le_iff)
    } note xy = this
  show ?thesis
    apply (insert p_ge_2 p_a_relprime p_minus_one_l)
    apply (auto simp add: B_def)
    apply (rule ResSet_image)
    apply (auto simp add: A_res)
    apply (auto simp add: A_def xy)
    done
  qed

lemma SR_B_inj: "inj_on (\<lambda>x. x mod p) B"
proof -
{ fix x fix y
  assume a: "x * a mod p = y * a mod p"
  assume b: "0 < x"
  assume c: "x \<le> (int p - 1) div 2"
  assume d: "0 < y"
  assume e: "y \<le> (int p - 1) div 2"
  assume f: "x \<noteq> y"
  from a have a': "[x * a = y * a](mod p)" 
    by (metis cong_int_def)
  from p_a_relprime have "\<not>p dvd a"
    by (simp add: cong_altdef_int)
  with p_prime have "coprime a (int p)" 
     by (subst gcd.commute, intro prime_imp_coprime) auto
  with a' cong_mult_rcancel_int [of a "int p" x y]
    have "[x = y] (mod p)" by simp
  with cong_less_imp_eq_int [of x y p] p_minus_one_l
    order_le_less_trans [of x "(int p - 1) div 2" p]
    order_le_less_trans [of y "(int p - 1) div 2" p] 
  have "x = y"
    by (metis b c cong_less_imp_eq_int d e zero_less_imp_eq_int of_nat_0_le_iff)
  then have False
    by (simp add: f)}
  then show ?thesis
    by (auto simp add: B_def inj_on_def A_def) metis
qed

lemma inj_on_pminusx_E: "inj_on (\<lambda>x. p - x) E"
  apply (auto simp add: E_def C_def B_def A_def)
  apply (rule_tac g = "(op - (int p))" in inj_on_inverseI)
  apply auto
  done

lemma nonzero_mod_p:
  fixes x::int shows "\<lbrakk>0 < x; x < int p\<rbrakk> \<Longrightarrow> [x \<noteq> 0](mod p)"
  by (simp add: cong_int_def)

lemma A_ncong_p: "x \<in> A \<Longrightarrow> [x \<noteq> 0](mod p)"
  by (rule nonzero_mod_p) (auto simp add: A_def)

lemma A_greater_zero: "x \<in> A \<Longrightarrow> 0 < x"
  by (auto simp add: A_def)

lemma B_ncong_p: "x \<in> B \<Longrightarrow> [x \<noteq> 0](mod p)"
  by (auto simp: B_def p_prime p_a_relprime A_ncong_p dest: cong_prime_prod_zero_int) 

lemma B_greater_zero: "x \<in> B \<Longrightarrow> 0 < x"
  using a_nonzero by (auto simp add: B_def A_greater_zero)

lemma C_greater_zero: "y \<in> C \<Longrightarrow> 0 < y"
proof (auto simp add: C_def)
  fix x :: int
  assume a1: "x \<in> B"
  have f2: "\<And>x\<^sub>1. int x\<^sub>1 = 0 \<or> 0 < int x\<^sub>1" by linarith
  have "x mod int p \<noteq> 0" using a1 B_ncong_p cong_int_def by simp
  thus "0 < x mod int p" using a1 f2 
    by (metis (no_types) B_greater_zero Divides.transfer_int_nat_functions(2) zero_less_imp_eq_int)
qed

lemma F_subset: "F \<subseteq> {x. 0 < x & x \<le> ((int p - 1) div 2)}"
  apply (auto simp add: F_def E_def C_def)
  apply (metis p_ge_2 Divides.pos_mod_bound less_diff_eq nat_int plus_int_code(2) zless_nat_conj)
  apply (auto intro: p_odd_int)
  done

lemma D_subset: "D \<subseteq> {x. 0 < x & x \<le> ((p - 1) div 2)}"
  by (auto simp add: D_def C_greater_zero)

lemma F_eq: "F = {x. \<exists>y \<in> A. ( x = p - ((y*a) mod p) & (int p - 1) div 2 < (y*a) mod p)}"
  by (auto simp add: F_def E_def D_def C_def B_def A_def)

lemma D_eq: "D = {x. \<exists>y \<in> A. ( x = (y*a) mod p & (y*a) mod p \<le> (int p - 1) div 2)}"
  by (auto simp add: D_def C_def B_def A_def)

lemma all_A_relprime: assumes "x \<in> A" shows "gcd x p = 1"
  using p_prime A_ncong_p [OF assms]
  by (auto simp: cong_altdef_int gcd.commute[of _ "int p"] intro!: prime_imp_coprime)

lemma A_prod_relprime: "gcd (prod id A) p = 1"
  by (metis id_def all_A_relprime prod_coprime)


subsection \<open>Relationships Between Gauss Sets\<close>

lemma StandardRes_inj_on_ResSet: "ResSet m X \<Longrightarrow> (inj_on (\<lambda>b. b mod m) X)"
  by (auto simp add: ResSet_def inj_on_def cong_int_def)

lemma B_card_eq_A: "card B = card A"
  using finite_A by (simp add: finite_A B_def inj_on_xa_A card_image)

lemma B_card_eq: "card B = nat ((int p - 1) div 2)"
  by (simp add: B_card_eq_A A_card_eq)

lemma F_card_eq_E: "card F = card E"
  using finite_E 
  by (simp add: F_def inj_on_pminusx_E card_image)

lemma C_card_eq_B: "card C = card B"
proof -
  have "inj_on (\<lambda>x. x mod p) B"
    by (metis SR_B_inj) 
  then show ?thesis
    by (metis C_def card_image)
qed

lemma D_E_disj: "D \<inter> E = {}"
  by (auto simp add: D_def E_def)

lemma C_card_eq_D_plus_E: "card C = card D + card E"
  by (auto simp add: C_eq card_Un_disjoint D_E_disj finite_D finite_E)

lemma C_prod_eq_D_times_E: "prod id E * prod id D = prod id C"
  by (metis C_eq D_E_disj finite_D finite_E inf_commute prod.union_disjoint sup_commute)

lemma C_B_zcong_prod: "[prod id C = prod id B] (mod p)"
  apply (auto simp add: C_def)
  apply (insert finite_B SR_B_inj)
  apply (drule prod.reindex [of "\<lambda>x. x mod int p" B id])
  apply auto
  apply (rule cong_prod_int)
  apply (auto simp add: cong_int_def)
  done

lemma F_Un_D_subset: "(F \<union> D) \<subseteq> A"
  apply (intro Un_least subset_trans [OF F_subset] subset_trans [OF D_subset])
  apply (auto simp add: A_def)
  done

lemma F_D_disj: "(F \<inter> D) = {}"
proof (auto simp add: F_eq D_eq)
  fix y::int and z::int
  assume "p - (y*a) mod p = (z*a) mod p"
  then have "[(y*a) mod p + (z*a) mod p = 0] (mod p)"
    by (metis add.commute diff_eq_eq dvd_refl cong_int_def dvd_eq_mod_eq_0 mod_0)
  moreover have "[y * a = (y*a) mod p] (mod p)"
    by (metis cong_int_def mod_mod_trivial)
  ultimately have "[a * (y + z) = 0] (mod p)"
    by (metis cong_int_def mod_add_left_eq mod_add_right_eq mult.commute ring_class.ring_distribs(1))
  with p_prime a_nonzero p_a_relprime
  have a: "[y + z = 0] (mod p)"
    by (auto dest!: cong_prime_prod_zero_int)
  assume b: "y \<in> A" and c: "z \<in> A"
  with A_def have "0 < y + z"
    by auto
  moreover from b c p_eq2 A_def have "y + z < p"
    by auto
  ultimately show False
    by (metis a nonzero_mod_p)
qed

lemma F_Un_D_card: "card (F \<union> D) = nat ((p - 1) div 2)"
proof -
  have "card (F \<union> D) = card E + card D"
    by (auto simp add: finite_F finite_D F_D_disj card_Un_disjoint F_card_eq_E)
  then have "card (F \<union> D) = card C"
    by (simp add: C_card_eq_D_plus_E)
  then show "card (F \<union> D) = nat ((p - 1) div 2)"
    by (simp add: C_card_eq_B B_card_eq)
qed

lemma F_Un_D_eq_A: "F \<union> D = A"
  using finite_A F_Un_D_subset A_card_eq F_Un_D_card 
  by (auto simp add: card_seteq)

lemma prod_D_F_eq_prod_A: "(prod id D) * (prod id F) = prod id A"
  by (metis F_D_disj F_Un_D_eq_A Int_commute Un_commute finite_D finite_F prod.union_disjoint)

lemma prod_F_zcong: "[prod id F = ((-1) ^ (card E)) * (prod id E)] (mod p)"
proof -
  have FE: "prod id F = prod (op - p) E"
    apply (auto simp add: F_def)
    apply (insert finite_E inj_on_pminusx_E)
    apply (drule prod.reindex, auto)
    done
  then have "\<forall>x \<in> E. [(p-x) mod p = - x](mod p)"
    by (metis cong_int_def minus_mod_self1 mod_mod_trivial)
  then have "[prod ((\<lambda>x. x mod p) o (op - p)) E = prod (uminus) E](mod p)"
    using finite_E p_ge_2
          cong_prod_int [of E "(\<lambda>x. x mod p) o (op - p)" uminus p]
    by auto
  then have two: "[prod id F = prod (uminus) E](mod p)"
    by (metis FE cong_cong_mod_int cong_refl_int cong_prod_int minus_mod_self1)
  have "prod uminus E = (-1) ^ (card E) * (prod id E)"
    using finite_E by (induct set: finite) auto
  with two show ?thesis
    by simp
qed


subsection \<open>Gauss' Lemma\<close>

lemma aux: "prod id A * (- 1) ^ card E * a ^ card A * (- 1) ^ card E = prod id A * a ^ card A"
by (metis (no_types) minus_minus mult.commute mult.left_commute power_minus power_one)

theorem pre_gauss_lemma:
  "[a ^ nat((int p - 1) div 2) = (-1) ^ (card E)] (mod p)"
proof -
  have "[prod id A = prod id F * prod id D](mod p)"
    by (auto simp add: prod_D_F_eq_prod_A mult.commute cong del: prod.strong_cong)
  then have "[prod id A = ((-1)^(card E) * prod id E) * prod id D] (mod p)"
    apply (rule cong_trans_int)
    apply (metis cong_scalar_int prod_F_zcong)
    done
  then have "[prod id A = ((-1)^(card E) * prod id C)] (mod p)"
    by (metis C_prod_eq_D_times_E mult.commute mult.left_commute)
  then have "[prod id A = ((-1)^(card E) * prod id B)] (mod p)"
    by (rule cong_trans_int) (metis C_B_zcong_prod cong_scalar2_int)
  then have "[prod id A = ((-1)^(card E) *
    (prod id ((\<lambda>x. x * a) ` A)))] (mod p)"
    by (simp add: B_def)
  then have "[prod id A = ((-1)^(card E) * (prod (\<lambda>x. x * a) A))]
    (mod p)"
    by (simp add: inj_on_xa_A prod.reindex)
  moreover have "prod (\<lambda>x. x * a) A =
    prod (\<lambda>x. a) A * prod id A"
    using finite_A by (induct set: finite) auto
  ultimately have "[prod id A = ((-1)^(card E) * (prod (\<lambda>x. a) A *
    prod id A))] (mod p)"
    by simp
  then have "[prod id A = ((-1)^(card E) * a^(card A) *
      prod id A)](mod p)"
    apply (rule cong_trans_int)
    apply (simp add: cong_scalar2_int cong_scalar_int finite_A prod_constant mult.assoc)
    done
  then have a: "[prod id A * (-1)^(card E) =
      ((-1)^(card E) * a^(card A) * prod id A * (-1)^(card E))](mod p)"
    by (rule cong_scalar_int)
  then have "[prod id A * (-1)^(card E) = prod id A *
      (-1)^(card E) * a^(card A) * (-1)^(card E)](mod p)"
    apply (rule cong_trans_int)
    apply (simp add: a mult.commute mult.left_commute)
    done
  then have "[prod id A * (-1)^(card E) = prod id A * a^(card A)](mod p)"
    apply (rule cong_trans_int)
    apply (simp add: aux cong del: prod.strong_cong)
    done
  with A_prod_relprime have "[(- 1) ^ card E = a ^ card A](mod p)"
    by (metis cong_mult_lcancel_int)
  then show ?thesis
    by (simp add: A_card_eq cong_sym_int)
qed

theorem gauss_lemma: "(Legendre a p) = (-1) ^ (card E)"
proof -
  from euler_criterion p_prime p_ge_2 have
      "[(Legendre a p) = a^(nat (((p) - 1) div 2))] (mod p)"
    by auto
  moreover have "int ((p - 1) div 2) =(int p - 1) div 2" using p_eq2 by linarith
    hence "[a ^ nat (int ((p - 1) div 2)) = a ^ nat ((int p - 1) div 2)] (mod int p)" by force
  moreover note pre_gauss_lemma
  ultimately have "[(Legendre a p) = (-1) ^ (card E)] (mod p)" using cong_trans_int by blast
  moreover from p_a_relprime have "(Legendre a p) = 1 | (Legendre a p) = (-1)"
    by (auto simp add: Legendre_def)
  moreover have "(-1::int) ^ (card E) = 1 | (-1::int) ^ (card E) = -1"
    using neg_one_even_power neg_one_odd_power by blast
  moreover have "[1 \<noteq> - 1] (mod int p)"
    using cong_altdef_int nonzero_mod_p[of 2] p_odd_int by fastforce
  ultimately show ?thesis
    by (auto simp add: cong_sym_int)
qed

end

end
