(* Author: Jaime Mendizabal Roche *)

theory Euler_Criterion
imports Residues
begin

context
  fixes p :: "nat"
  fixes a :: "int"

  assumes p_prime: "prime p"
  assumes p_ge_2: "2 < p"
  assumes p_a_relprime: "[a \<noteq> 0](mod p)"
begin

private lemma odd_p: "odd p" using p_ge_2 p_prime prime_odd_nat by blast

private lemma p_minus_1_int: "int (p - 1) = int p - 1" using p_prime prime_ge_1_nat by force

private lemma E_1: assumes "QuadRes p a"
  shows "[a ^ ((p - 1) div 2) = 1] (mod (int p))"
proof -
  from assms obtain b where b: "[b ^ 2 = a] (mod p)" unfolding QuadRes_def by blast
  hence "[a ^ ((p - 1) div 2) = b ^ (2 * ((p - 1) div 2))] (mod p)"
    by (simp add: cong_exp_int cong_sym_int power_mult)
  hence "[a ^ ((p - 1) div 2) = b ^ (p - 1)] (mod p)" using odd_p by force
  moreover have "~ p dvd b"
    using b cong_altdef_int[of a 0 p] cong_dvd_eq_int[of "b ^ 2" a "int p"] p_a_relprime p_prime
    by (auto simp: prime_dvd_power_int_iff)
  ultimately show ?thesis using fermat_theorem[of p b] p_prime 
    by (auto intro: cong_trans_int)
qed

private definition S1 :: "int set" where "S1 = {0 <.. int p - 1}"

private definition P :: "int \<Rightarrow> int \<Rightarrow> bool" where
  "P x y \<longleftrightarrow> [x * y = a] (mod p) \<and> y \<in> S1"

private definition f_1 :: "int \<Rightarrow> int" where
  "f_1 x = (THE y. P x y)"

private definition f :: "int \<Rightarrow> int set" where
  "f x = {x, f_1 x}"

private definition S2 :: "int set set" where "S2 = f ` S1"

private lemma P_lemma: assumes "x \<in> S1"
  shows "\<exists>! y. P x y"
proof -
  have "~ p dvd x" using assms zdvd_not_zless S1_def by auto
  hence co_xp: "coprime x p" using p_prime prime_imp_coprime_int[of p x] 
    by (simp add: gcd.commute)
  then obtain y' where y': "[x * y' = 1] (mod p)" using cong_solve_coprime_int by blast
  moreover define y where "y = y' * a mod p"
  ultimately have "[x * y = a] (mod p)" using mod_mult_right_eq[of x "y' * a" p]
    cong_scalar_int[of "x * y'"] unfolding cong_int_def mult.assoc by auto
  moreover have "y \<in> {0 .. int p - 1}" unfolding y_def using p_ge_2 by auto
  hence "y \<in> S1" using calculation cong_altdef_int p_a_relprime S1_def by auto
  ultimately have "P x y" unfolding P_def by blast
  moreover {
    fix y1 y2
    assume "P x y1" "P x y2"
    moreover hence "[y1 = y2] (mod p)" unfolding P_def
      using co_xp cong_mult_lcancel_int[of x p y1 y2] cong_sym_int cong_trans_int by blast
    ultimately have "y1 = y2" unfolding P_def S1_def using cong_less_imp_eq_int by auto
  }
  ultimately show ?thesis by blast
qed

private lemma f_1_lemma_1: assumes "x \<in> S1"
  shows "P x (f_1 x)" using assms P_lemma theI'[of "P x"] f_1_def by presburger

private lemma f_1_lemma_2: assumes "x \<in> S1"
  shows "f_1 (f_1 x) = x"
  using assms f_1_lemma_1[of x] f_1_def P_lemma[of "f_1 x"] P_def by (auto simp: mult.commute)

private lemma f_lemma_1: assumes "x \<in> S1"
  shows "f x = f (f_1 x)" using f_def f_1_lemma_2[of x] assms by auto

private lemma l1: assumes "~ QuadRes p a" "x \<in> S1"
  shows "x \<noteq> f_1 x"
  using f_1_lemma_1[of x] assms unfolding P_def QuadRes_def power2_eq_square by fastforce

private lemma l2: assumes "~ QuadRes p a" "x \<in> S1"
  shows "[\<Prod> (f x) = a] (mod p)"
  using assms l1 f_1_lemma_1 P_def f_def by auto

private lemma l3: assumes "x \<in> S2"
  shows "finite x" using assms f_def S2_def by auto

private lemma l4: "S1 = \<Union> S2" using f_1_lemma_1 P_def f_def S2_def by auto

private lemma l5: assumes "x \<in> S2" "y \<in> S2" "x \<noteq> y"
  shows "x \<inter> y = {}"
proof -
  obtain a b where ab: "x = f a" "a \<in> S1" "y = f b" "b \<in> S1" using assms S2_def by auto
  hence "a \<noteq> b" "a \<noteq> f_1 b" "f_1 a \<noteq> b" using assms(3) f_lemma_1 by blast+
  moreover hence "f_1 a \<noteq> f_1 b" using f_1_lemma_2[of a] f_1_lemma_2[of b] ab by force
  ultimately show ?thesis using f_def ab by fastforce
qed

private lemma l6: "prod Prod S2 = \<Prod> S1" 
  using prod.Union_disjoint[of S2 "\<lambda>x. x"] l3 l4 l5 unfolding comp_def by auto

private lemma l7: "fact n = \<Prod> {0 <.. int n}"
proof (induction n)
case (Suc n)
  have "int (Suc n) = int n + 1" by simp
  hence "insert (int (Suc n)) {0<..int n} = {0<..int (Suc n)}" by auto
  thus ?case using prod.insert[of "{0<..int n}" "int (Suc n)" "\<lambda>x. x"] Suc fact_Suc by auto
qed simp

private lemma l8: "fact (p - 1) = \<Prod> S1" using l7[of "p - 1"] S1_def p_minus_1_int by presburger

private lemma l9: "[prod Prod S2 = -1] (mod p)"
  using l6 l8 wilson_theorem[of p] p_prime by presburger

private lemma l10: assumes "card S = n" "\<And>x. x \<in> S \<Longrightarrow> [g x = a] (mod p)"
  shows "[prod g S = a ^ n] (mod p)" using assms
proof (induction n arbitrary: S)
case 0
  thus ?case using card_0_eq[of S] prod.empty prod.infinite by fastforce
next
case (Suc n)
  then obtain x where x: "x \<in> S" by force
  define S' where "S' = S - {x}"
  hence "[prod g S' = a ^ n] (mod int p)"
    using x Suc(1)[of S'] Suc(2) Suc(3) by (simp add: card_ge_0_finite)
  moreover have "prod g S = g x * prod g S'"
    using x S'_def Suc(2) prod.remove[of S x g] by fastforce
  ultimately show ?case using x Suc(3) cong_mult_int by simp
qed

private lemma l11: assumes "~ QuadRes p a"
  shows "card S2 = (p - 1) div 2"
proof -
  have "sum card S2 = 2 * card S2"
    using sum.cong[of S2 S2 card "\<lambda>x. 2"] l1 f_def S2_def assms by fastforce
  moreover have "p - 1 = sum card S2"
    using l4 card_UN_disjoint[of S2 "\<lambda>x. x"] l3 l5 S1_def S2_def by auto
  ultimately show ?thesis by linarith
qed

private lemma l12: assumes "~ QuadRes p a"
  shows "[prod Prod S2 = a ^ ((p - 1) div 2)] (mod p)"
  using assms l2 l10 l11 unfolding S2_def by blast

private lemma E_2: assumes "~ QuadRes p a"
  shows "[a ^ ((p - 1) div 2) = -1] (mod p)" using l9 l12 cong_trans_int cong_sym_int assms by blast

lemma euler_criterion_aux: "[(Legendre a p) = a ^ ((p - 1) div 2)] (mod p)"
  using E_1 E_2 Legendre_def cong_sym_int p_a_relprime by presburger

end

theorem euler_criterion: assumes "prime p" "2 < p"
  shows "[(Legendre a p) = a ^ ((p - 1) div 2)] (mod p)"
proof (cases "[a = 0] (mod p)")
case True
  hence "[a ^ ((p - 1) div 2) = 0 ^ ((p - 1) div 2)] (mod p)" using cong_exp_int by blast
  moreover have "(0::int) ^ ((p - 1) div 2) = 0" using zero_power[of "(p - 1) div 2"] assms(2) by simp
  ultimately have "[a ^ ((p - 1) div 2) = 0] (mod p)" using cong_trans_int cong_refl_int by presburger
  thus ?thesis unfolding Legendre_def using True cong_sym_int by presburger
next
case False
  thus ?thesis using euler_criterion_aux assms by presburger
qed

hide_fact euler_criterion_aux

end
