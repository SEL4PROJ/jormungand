(*  Author:     Jacques D. Fleuriot, University of Edinburgh
    Conversion to Isar and new proofs by Lawrence C Paulson, 2004

    Replaced by ~~/src/HOL/Analysis/Henstock_Kurzweil_Integration and
    Bochner_Integration.
*)

section\<open>Theory of Integration on real intervals\<close>

theory Gauge_Integration
imports Complex_Main
begin

text \<open>

\textbf{Attention}: This theory defines the Integration on real
intervals.  This is just a example theory for historical / expository interests.
A better replacement is found in the Multivariate Analysis library. This defines
the gauge integral on real vector spaces and in the Real Integral theory
is a specialization to the integral on arbitrary real intervals.  The
Multivariate Analysis package also provides a better support for analysis on
integrals.

\<close>

text\<open>We follow John Harrison in formalizing the Gauge integral.\<close>

subsection \<open>Gauges\<close>

definition
  gauge :: "[real set, real => real] => bool" where
  "gauge E g = (\<forall>x\<in>E. 0 < g(x))"


subsection \<open>Gauge-fine divisions\<close>

inductive
  fine :: "[real \<Rightarrow> real, real \<times> real, (real \<times> real \<times> real) list] \<Rightarrow> bool"
for
  \<delta> :: "real \<Rightarrow> real"
where
  fine_Nil:
    "fine \<delta> (a, a) []"
| fine_Cons:
    "\<lbrakk>fine \<delta> (b, c) D; a < b; a \<le> x; x \<le> b; b - a < \<delta> x\<rbrakk>
      \<Longrightarrow> fine \<delta> (a, c) ((a, x, b) # D)"

lemmas fine_induct [induct set: fine] =
  fine.induct [of "\<delta>" "(a,b)" "D" "case_prod P", unfolded split_conv] for \<delta> a b D P

lemma fine_single:
  "\<lbrakk>a < b; a \<le> x; x \<le> b; b - a < \<delta> x\<rbrakk> \<Longrightarrow> fine \<delta> (a, b) [(a, x, b)]"
by (rule fine_Cons [OF fine_Nil])

lemma fine_append:
  "\<lbrakk>fine \<delta> (a, b) D; fine \<delta> (b, c) D'\<rbrakk> \<Longrightarrow> fine \<delta> (a, c) (D @ D')"
by (induct set: fine, simp, simp add: fine_Cons)

lemma fine_imp_le: "fine \<delta> (a, b) D \<Longrightarrow> a \<le> b"
by (induct set: fine, simp_all)

lemma nonempty_fine_imp_less: "\<lbrakk>fine \<delta> (a, b) D; D \<noteq> []\<rbrakk> \<Longrightarrow> a < b"
apply (induct set: fine, simp)
apply (drule fine_imp_le, simp)
done

lemma fine_Nil_iff: "fine \<delta> (a, b) [] \<longleftrightarrow> a = b"
by (auto elim: fine.cases intro: fine.intros)

lemma fine_same_iff: "fine \<delta> (a, a) D \<longleftrightarrow> D = []"
proof
  assume "fine \<delta> (a, a) D" thus "D = []"
    by (metis nonempty_fine_imp_less less_irrefl)
next
  assume "D = []" thus "fine \<delta> (a, a) D"
    by (simp add: fine_Nil)
qed

lemma empty_fine_imp_eq: "\<lbrakk>fine \<delta> (a, b) D; D = []\<rbrakk> \<Longrightarrow> a = b"
by (simp add: fine_Nil_iff)

lemma mem_fine:
  "\<lbrakk>fine \<delta> (a, b) D; (u, x, v) \<in> set D\<rbrakk> \<Longrightarrow> u < v \<and> u \<le> x \<and> x \<le> v"
by (induct set: fine, simp, force)

lemma mem_fine2: "\<lbrakk>fine \<delta> (a, b) D; (u, z, v) \<in> set D\<rbrakk> \<Longrightarrow> a \<le> u \<and> v \<le> b"
apply (induct arbitrary: z u v set: fine, auto)
apply (simp add: fine_imp_le)
apply (erule order_trans [OF less_imp_le], simp)
done

lemma mem_fine3: "\<lbrakk>fine \<delta> (a, b) D; (u, z, v) \<in> set D\<rbrakk> \<Longrightarrow> v - u < \<delta> z"
by (induct arbitrary: z u v set: fine) auto

lemma BOLZANO:
  fixes P :: "real \<Rightarrow> real \<Rightarrow> bool"
  assumes 1: "a \<le> b"
  assumes 2: "\<And>a b c. \<lbrakk>P a b; P b c; a \<le> b; b \<le> c\<rbrakk> \<Longrightarrow> P a c"
  assumes 3: "\<And>x. \<exists>d>0. \<forall>a b. a \<le> x & x \<le> b & (b-a) < d \<longrightarrow> P a b"
  shows "P a b"
  using 1 2 3 by (rule Bolzano)

text\<open>We can always find a division that is fine wrt any gauge\<close>

lemma fine_exists:
  assumes "a \<le> b" and "gauge {a..b} \<delta>" shows "\<exists>D. fine \<delta> (a, b) D"
proof -
  {
    fix u v :: real assume "u \<le> v"
    have "a \<le> u \<Longrightarrow> v \<le> b \<Longrightarrow> \<exists>D. fine \<delta> (u, v) D"
      apply (induct u v rule: BOLZANO, rule \<open>u \<le> v\<close>)
       apply (simp, fast intro: fine_append)
      apply (case_tac "a \<le> x \<and> x \<le> b")
       apply (rule_tac x="\<delta> x" in exI)
       apply (rule conjI)
        apply (simp add: \<open>gauge {a..b} \<delta>\<close> [unfolded gauge_def])
       apply (clarify, rename_tac u v)
       apply (case_tac "u = v")
        apply (fast intro: fine_Nil)
       apply (subgoal_tac "u < v", fast intro: fine_single, simp)
      apply (rule_tac x="1" in exI, clarsimp)
      done
  }
  with \<open>a \<le> b\<close> show ?thesis by auto
qed

lemma fine_covers_all:
  assumes "fine \<delta> (a, c) D" and "a < x" and "x \<le> c"
  shows "\<exists> N < length D. \<forall> d t e. D ! N = (d,t,e) \<longrightarrow> d < x \<and> x \<le> e"
  using assms
proof (induct set: fine)
  case (2 b c D a t)
  thus ?case
  proof (cases "b < x")
    case True
    with 2 obtain N where *: "N < length D"
      and **: "D ! N = (d,t,e) \<Longrightarrow> d < x \<and> x \<le> e" for d t e by auto
    hence "Suc N < length ((a,t,b)#D) \<and>
           (\<forall> d t' e. ((a,t,b)#D) ! Suc N = (d,t',e) \<longrightarrow> d < x \<and> x \<le> e)" by auto
    thus ?thesis by auto
  next
    case False with 2
    have "0 < length ((a,t,b)#D) \<and>
           (\<forall> d t' e. ((a,t,b)#D) ! 0 = (d,t',e) \<longrightarrow> d < x \<and> x \<le> e)" by auto
    thus ?thesis by auto
  qed
qed auto

lemma fine_append_split:
  assumes "fine \<delta> (a,b) D" and "D2 \<noteq> []" and "D = D1 @ D2"
  shows "fine \<delta> (a,fst (hd D2)) D1" (is "?fine1")
  and "fine \<delta> (fst (hd D2), b) D2" (is "?fine2")
proof -
  from assms
  have "?fine1 \<and> ?fine2"
  proof (induct arbitrary: D1 D2)
    case (2 b c D a' x D1 D2)
    note induct = this

    thus ?case
    proof (cases D1)
      case Nil
      hence "fst (hd D2) = a'" using 2 by auto
      with fine_Cons[OF \<open>fine \<delta> (b,c) D\<close> induct(3,4,5)] Nil induct
      show ?thesis by (auto intro: fine_Nil)
    next
      case (Cons d1 D1')
      with induct(2)[OF \<open>D2 \<noteq> []\<close>, of D1'] induct(8)
      have "fine \<delta> (b, fst (hd D2)) D1'" and "fine \<delta> (fst (hd D2), c) D2" and
        "d1 = (a', x, b)" by auto
      with fine_Cons[OF this(1) induct(3,4,5), OF induct(6)] Cons
      show ?thesis by auto
    qed
  qed auto
  thus ?fine1 and ?fine2 by auto
qed

lemma fine_\<delta>_expand:
  assumes "fine \<delta> (a,b) D"
  and "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> \<delta> x \<le> \<delta>' x"
  shows "fine \<delta>' (a,b) D"
using assms proof induct
  case 1 show ?case by (rule fine_Nil)
next
  case (2 b c D a x)
  show ?case
  proof (rule fine_Cons)
    show "fine \<delta>' (b,c) D" using 2 by auto
    from fine_imp_le[OF 2(1)] 2(6) \<open>x \<le> b\<close>
    show "b - a < \<delta>' x"
      using 2(7)[OF \<open>a \<le> x\<close>] by auto
  qed (auto simp add: 2)
qed

lemma fine_single_boundaries:
  assumes "fine \<delta> (a,b) D" and "D = [(d, t, e)]"
  shows "a = d \<and> b = e"
using assms proof induct
  case (2 b c  D a x)
  hence "D = []" and "a = d" and "b = e" by auto
  moreover
  from \<open>fine \<delta> (b,c) D\<close> \<open>D = []\<close> have "b = c"
    by (rule empty_fine_imp_eq)
  ultimately show ?case by simp
qed auto

lemma fine_sum_list_eq_diff:
  fixes f :: "real \<Rightarrow> real"
  shows "fine \<delta> (a, b) D \<Longrightarrow> (\<Sum>(u, x, v)\<leftarrow>D. f v - f u) = f b - f a"
by (induct set: fine) simp_all

text\<open>Lemmas about combining gauges\<close>

lemma gauge_min:
     "[| gauge(E) g1; gauge(E) g2 |]
      ==> gauge(E) (%x. min (g1(x)) (g2(x)))"
by (simp add: gauge_def)

lemma fine_min:
      "fine (%x. min (g1(x)) (g2(x))) (a,b) D
       ==> fine(g1) (a,b) D & fine(g2) (a,b) D"
apply (erule fine.induct)
apply (simp add: fine_Nil)
apply (simp add: fine_Cons)
done

subsection \<open>Riemann sum\<close>

definition
  rsum :: "[(real \<times> real \<times> real) list, real \<Rightarrow> real] \<Rightarrow> real" where
  "rsum D f = (\<Sum>(u, x, v)\<leftarrow>D. f x * (v - u))"

lemma rsum_Nil [simp]: "rsum [] f = 0"
unfolding rsum_def by simp

lemma rsum_Cons [simp]: "rsum ((u, x, v) # D) f = f x * (v - u) + rsum D f"
unfolding rsum_def by simp

lemma rsum_zero [simp]: "rsum D (\<lambda>x. 0) = 0"
by (induct D, auto)

lemma rsum_left_distrib: "rsum D f * c = rsum D (\<lambda>x. f x * c)"
by (induct D, auto simp add: algebra_simps)

lemma rsum_right_distrib: "c * rsum D f = rsum D (\<lambda>x. c * f x)"
by (induct D, auto simp add: algebra_simps)

lemma rsum_add: "rsum D (\<lambda>x. f x + g x) =  rsum D f + rsum D g"
by (induct D, auto simp add: algebra_simps)

lemma rsum_append: "rsum (D1 @ D2) f = rsum D1 f + rsum D2 f"
unfolding rsum_def map_append sum_list_append ..


subsection \<open>Gauge integrability (definite)\<close>

definition
  Integral :: "[(real*real),real=>real,real] => bool" where
  "Integral = (%(a,b) f k. \<forall>e > 0.
                               (\<exists>\<delta>. gauge {a .. b} \<delta> &
                               (\<forall>D. fine \<delta> (a,b) D -->
                                         \<bar>rsum D f - k\<bar> < e)))"

lemma Integral_eq:
  "Integral (a, b) f k \<longleftrightarrow>
    (\<forall>e>0. \<exists>\<delta>. gauge {a..b} \<delta> \<and> (\<forall>D. fine \<delta> (a,b) D \<longrightarrow> \<bar>rsum D f - k\<bar> < e))"
unfolding Integral_def by simp

lemma IntegralI:
  assumes "\<And>e. 0 < e \<Longrightarrow>
    \<exists>\<delta>. gauge {a..b} \<delta> \<and> (\<forall>D. fine \<delta> (a, b) D \<longrightarrow> \<bar>rsum D f - k\<bar> < e)"
  shows "Integral (a, b) f k"
using assms unfolding Integral_def by auto

lemma IntegralE:
  assumes "Integral (a, b) f k" and "0 < e"
  obtains \<delta> where "gauge {a..b} \<delta>" and "\<forall>D. fine \<delta> (a, b) D \<longrightarrow> \<bar>rsum D f - k\<bar> < e"
using assms unfolding Integral_def by auto

lemma Integral_def2:
  "Integral = (%(a,b) f k. \<forall>e>0. (\<exists>\<delta>. gauge {a..b} \<delta> &
                               (\<forall>D. fine \<delta> (a,b) D -->
                                         \<bar>rsum D f - k\<bar> \<le> e)))"
unfolding Integral_def
apply (safe intro!: ext)
apply (fast intro: less_imp_le)
apply (drule_tac x="e/2" in spec)
apply force
done

text\<open>The integral is unique if it exists\<close>

lemma Integral_unique:
  assumes le: "a \<le> b"
  assumes 1: "Integral (a, b) f k1"
  assumes 2: "Integral (a, b) f k2"
  shows "k1 = k2"
proof (rule ccontr)
  assume "k1 \<noteq> k2"
  hence e: "0 < \<bar>k1 - k2\<bar> / 2" by simp
  obtain d1 where "gauge {a..b} d1" and
    d1: "\<forall>D. fine d1 (a, b) D \<longrightarrow> \<bar>rsum D f - k1\<bar> < \<bar>k1 - k2\<bar> / 2"
    using 1 e by (rule IntegralE)
  obtain d2 where "gauge {a..b} d2" and
    d2: "\<forall>D. fine d2 (a, b) D \<longrightarrow> \<bar>rsum D f - k2\<bar> < \<bar>k1 - k2\<bar> / 2"
    using 2 e by (rule IntegralE)
  have "gauge {a..b} (\<lambda>x. min (d1 x) (d2 x))"
    using \<open>gauge {a..b} d1\<close> and \<open>gauge {a..b} d2\<close>
    by (rule gauge_min)
  then obtain D where "fine (\<lambda>x. min (d1 x) (d2 x)) (a, b) D"
    using fine_exists [OF le] by fast
  hence "fine d1 (a, b) D" and "fine d2 (a, b) D"
    by (auto dest: fine_min)
  hence "\<bar>rsum D f - k1\<bar> < \<bar>k1 - k2\<bar> / 2" and "\<bar>rsum D f - k2\<bar> < \<bar>k1 - k2\<bar> / 2"
    using d1 d2 by simp_all
  hence "\<bar>rsum D f - k1\<bar> + \<bar>rsum D f - k2\<bar> < \<bar>k1 - k2\<bar> / 2 + \<bar>k1 - k2\<bar> / 2"
    by (rule add_strict_mono)
  thus False by auto
qed

lemma Integral_zero: "Integral(a,a) f 0"
apply (rule IntegralI)
apply (rule_tac x = "\<lambda>x. 1" in exI)
apply (simp add: fine_same_iff gauge_def)
done

lemma Integral_same_iff [simp]: "Integral (a, a) f k \<longleftrightarrow> k = 0"
  by (auto intro: Integral_zero Integral_unique)

lemma Integral_zero_fun: "Integral (a,b) (\<lambda>x. 0) 0"
apply (rule IntegralI)
apply (rule_tac x="\<lambda>x. 1" in exI, simp add: gauge_def)
done

lemma fine_rsum_const: "fine \<delta> (a,b) D \<Longrightarrow> rsum D (\<lambda>x. c) = (c * (b - a))"
unfolding rsum_def
by (induct set: fine, auto simp add: algebra_simps)

lemma Integral_mult_const: "a \<le> b \<Longrightarrow> Integral(a,b) (\<lambda>x. c) (c * (b - a))"
apply (cases "a = b", simp)
apply (rule IntegralI)
apply (rule_tac x = "\<lambda>x. b - a" in exI)
apply (rule conjI, simp add: gauge_def)
apply (clarify)
apply (subst fine_rsum_const, assumption, simp)
done

lemma Integral_eq_diff_bounds: "a \<le> b \<Longrightarrow> Integral(a,b) (\<lambda>x. 1) (b - a)"
  using Integral_mult_const [of a b 1] by simp

lemma Integral_mult:
     "[| a \<le> b; Integral(a,b) f k |] ==> Integral(a,b) (%x. c * f x) (c * k)"
apply (auto simp add: order_le_less)
apply (cases "c = 0", simp add: Integral_zero_fun)
apply (rule IntegralI)
apply (erule_tac e="e / \<bar>c\<bar>" in IntegralE, simp)
apply (rule_tac x="\<delta>" in exI, clarify)
apply (drule_tac x="D" in spec, clarify)
apply (simp add: pos_less_divide_eq abs_mult [symmetric]
                 algebra_simps rsum_right_distrib)
done

lemma Integral_add:
  assumes "Integral (a, b) f x1"
  assumes "Integral (b, c) f x2"
  assumes "a \<le> b" and "b \<le> c"
  shows "Integral (a, c) f (x1 + x2)"
proof (cases "a < b \<and> b < c", rule IntegralI)
  fix \<epsilon> :: real assume "0 < \<epsilon>"
  hence "0 < \<epsilon> / 2" by auto

  assume "a < b \<and> b < c"
  hence "a < b" and "b < c" by auto

  obtain \<delta>1 where \<delta>1_gauge: "gauge {a..b} \<delta>1"
    and I1: "fine \<delta>1 (a,b) D \<Longrightarrow> \<bar> rsum D f - x1 \<bar> < (\<epsilon> / 2)" for D
    using IntegralE [OF \<open>Integral (a, b) f x1\<close> \<open>0 < \<epsilon>/2\<close>] by auto

  obtain \<delta>2 where \<delta>2_gauge: "gauge {b..c} \<delta>2"
    and I2: "fine \<delta>2 (b,c) D \<Longrightarrow> \<bar> rsum D f - x2 \<bar> < (\<epsilon> / 2)" for D
    using IntegralE [OF \<open>Integral (b, c) f x2\<close> \<open>0 < \<epsilon>/2\<close>] by auto

  define \<delta> where "\<delta> x =
    (if x < b then min (\<delta>1 x) (b - x)
     else if x = b then min (\<delta>1 b) (\<delta>2 b)
     else min (\<delta>2 x) (x - b))" for x

  have "gauge {a..c} \<delta>"
    using \<delta>1_gauge \<delta>2_gauge unfolding \<delta>_def gauge_def by auto

  moreover {
    fix D :: "(real \<times> real \<times> real) list"
    assume fine: "fine \<delta> (a,c) D"
    from fine_covers_all[OF this \<open>a < b\<close> \<open>b \<le> c\<close>]
    obtain N where "N < length D"
      and *: "\<forall> d t e. D ! N = (d, t, e) \<longrightarrow> d < b \<and> b \<le> e"
      by auto
    obtain d t e where D_eq: "D ! N = (d, t, e)" by (cases "D!N", auto)
    with * have "d < b" and "b \<le> e" by auto
    have in_D: "(d, t, e) \<in> set D"
      using D_eq[symmetric] using \<open>N < length D\<close> by auto

    from mem_fine[OF fine in_D]
    have "d < e" and "d \<le> t" and "t \<le> e" by auto

    have "t = b"
    proof (rule ccontr)
      assume "t \<noteq> b"
      with mem_fine3[OF fine in_D] \<open>b \<le> e\<close> \<open>d \<le> t\<close> \<open>t \<le> e\<close> \<open>d < b\<close> \<delta>_def
      show False by (cases "t < b") auto
    qed

    let ?D1 = "take N D"
    let ?D2 = "drop N D"
    define D1 where "D1 = take N D @ [(d, t, b)]"
    define D2 where "D2 = (if b = e then [] else [(b, t, e)]) @ drop (Suc N) D"

    from hd_drop_conv_nth[OF \<open>N < length D\<close>]
    have "fst (hd ?D2) = d" using \<open>D ! N = (d, t, e)\<close> by auto
    with fine_append_split[OF _ _ append_take_drop_id[symmetric]]
    have fine1: "fine \<delta> (a,d) ?D1" and fine2: "fine \<delta> (d,c) ?D2"
      using \<open>N < length D\<close> fine by auto

    have "fine \<delta>1 (a,b) D1" unfolding D1_def
    proof (rule fine_append)
      show "fine \<delta>1 (a, d) ?D1"
      proof (rule fine1[THEN fine_\<delta>_expand])
        fix x assume "a \<le> x" "x \<le> d"
        hence "x \<le> b" using \<open>d < b\<close> \<open>x \<le> d\<close> by auto
        thus "\<delta> x \<le> \<delta>1 x" unfolding \<delta>_def by auto
      qed

      have "b - d < \<delta>1 t"
        using mem_fine3[OF fine in_D] \<delta>_def \<open>b \<le> e\<close> \<open>t = b\<close> by auto
      from \<open>d < b\<close> \<open>d \<le> t\<close> \<open>t = b\<close> this
      show "fine \<delta>1 (d, b) [(d, t, b)]" using fine_single by auto
    qed
    note rsum1 = I1[OF this]

    have drop_split: "drop N D = [D ! N] @ drop (Suc N) D"
      using Cons_nth_drop_Suc[OF \<open>N < length D\<close>] by simp

    have fine2: "fine \<delta>2 (e,c) (drop (Suc N) D)"
    proof (cases "drop (Suc N) D = []")
      case True
      note * = fine2[simplified drop_split True D_eq append_Nil2]
      have "e = c" using fine_single_boundaries[OF * refl] by auto
      thus ?thesis unfolding True using fine_Nil by auto
    next
      case False
      note * = fine_append_split[OF fine2 False drop_split]
      from fine_single_boundaries[OF *(1)]
      have "fst (hd (drop (Suc N) D)) = e" using D_eq by auto
      with *(2) have "fine \<delta> (e,c) (drop (Suc N) D)" by auto
      thus ?thesis
      proof (rule fine_\<delta>_expand)
        fix x assume "e \<le> x" and "x \<le> c"
        thus "\<delta> x \<le> \<delta>2 x" using \<open>b \<le> e\<close> unfolding \<delta>_def by auto
      qed
    qed

    have "fine \<delta>2 (b, c) D2"
    proof (cases "e = b")
      case True thus ?thesis using fine2 by (simp add: D1_def D2_def)
    next
      case False
      have "e - b < \<delta>2 b"
        using mem_fine3[OF fine in_D] \<delta>_def \<open>d < b\<close> \<open>t = b\<close> by auto
      with False \<open>t = b\<close> \<open>b \<le> e\<close>
      show ?thesis using D2_def
        by (auto intro!: fine_append[OF _ fine2] fine_single
               simp del: append_Cons)
    qed
    note rsum2 = I2[OF this]

    have "rsum D f = rsum (take N D) f + rsum [D ! N] f + rsum (drop (Suc N) D) f"
      using rsum_append[symmetric] Cons_nth_drop_Suc[OF \<open>N < length D\<close>] by auto
    also have "\<dots> = rsum D1 f + rsum D2 f"
      by (cases "b = e", auto simp add: D1_def D2_def D_eq rsum_append algebra_simps)
    finally have "\<bar>rsum D f - (x1 + x2)\<bar> < \<epsilon>"
      using add_strict_mono[OF rsum1 rsum2] by simp
  }
  ultimately show "\<exists> \<delta>. gauge {a .. c} \<delta> \<and>
    (\<forall>D. fine \<delta> (a,c) D \<longrightarrow> \<bar>rsum D f - (x1 + x2)\<bar> < \<epsilon>)"
    by blast
next
  case False
  hence "a = b \<or> b = c" using \<open>a \<le> b\<close> and \<open>b \<le> c\<close> by auto
  thus ?thesis
  proof (rule disjE)
    assume "a = b" hence "x1 = 0"
      using \<open>Integral (a, b) f x1\<close> by simp
    thus ?thesis using \<open>a = b\<close> \<open>Integral (b, c) f x2\<close> by simp
  next
    assume "b = c" hence "x2 = 0"
      using \<open>Integral (b, c) f x2\<close> by simp
    thus ?thesis using \<open>b = c\<close> \<open>Integral (a, b) f x1\<close> by simp
  qed
qed

text\<open>Fundamental theorem of calculus (Part I)\<close>

text\<open>"Straddle Lemma" : Swartz and Thompson: AMM 95(7) 1988\<close>

lemma strad1:
  fixes z x s e :: real
  assumes P: "(\<And>z. z \<noteq> x \<Longrightarrow> \<bar>z - x\<bar> < s \<Longrightarrow> \<bar>(f z - f x) / (z - x) - f' x\<bar> < e / 2)"
  assumes "\<bar>z - x\<bar> < s"
  shows "\<bar>f z - f x - f' x * (z - x)\<bar> \<le> e / 2 * \<bar>z - x\<bar>"
proof (cases "z = x")
  case True then show ?thesis by simp
next
  case False
  then have "inverse (z - x) * (f z - f x - f' x * (z - x)) = (f z - f x) / (z - x) - f' x"
    apply (subst mult.commute)
    apply (simp add: left_diff_distrib)
    apply (simp add: mult.assoc divide_inverse)
    apply (simp add: ring_distribs)
    done
  moreover from False \<open>\<bar>z - x\<bar> < s\<close> have "\<bar>(f z - f x) / (z - x) - f' x\<bar> < e / 2"
    by (rule P)
  ultimately have "\<bar>inverse (z - x)\<bar> * (\<bar>f z - f x - f' x * (z - x)\<bar> * 2)
    \<le> \<bar>inverse (z - x)\<bar> * (e * \<bar>z - x\<bar>)"
    using False by (simp del: abs_inverse add: abs_mult [symmetric] ac_simps)
  with False have "\<bar>f z - f x - f' x * (z - x)\<bar> * 2 \<le> e * \<bar>z - x\<bar>"
    by simp
  then show ?thesis by simp
qed

lemma lemma_straddle:
  assumes f': "\<forall>x. a \<le> x & x \<le> b --> DERIV f x :> f'(x)" and "0 < e"
  shows "\<exists>g. gauge {a..b} g &
                (\<forall>x u v. a \<le> u & u \<le> x & x \<le> v & v \<le> b & (v - u) < g(x)
                  --> \<bar>(f(v) - f(u)) - (f'(x) * (v - u))\<bar> \<le> e * (v - u))"
proof -
  have "\<forall>x\<in>{a..b}.
        (\<exists>d > 0. \<forall>u v. u \<le> x & x \<le> v & (v - u) < d --> 
                       \<bar>(f(v) - f(u)) - (f'(x) * (v - u))\<bar> \<le> e * (v - u))"
  proof (clarsimp)
    fix x :: real assume "a \<le> x" and "x \<le> b"
    with f' have "DERIV f x :> f'(x)" by simp
    then have "\<forall>r>0. \<exists>s>0. \<forall>z. z \<noteq> x \<and> \<bar>z - x\<bar> < s \<longrightarrow> \<bar>(f z - f x) / (z - x) - f' x\<bar> < r"
      by (simp add: DERIV_iff2 LIM_eq)
    with \<open>0 < e\<close> obtain s
    where "z \<noteq> x \<Longrightarrow> \<bar>z - x\<bar> < s \<Longrightarrow> \<bar>(f z - f x) / (z - x) - f' x\<bar> < e/2" and "0 < s" for z
      by (drule_tac x="e/2" in spec, auto)
    with strad1 [of x s f f' e] have strad:
        "\<And>z. \<bar>z - x\<bar> < s \<Longrightarrow> \<bar>f z - f x - f' x * (z - x)\<bar> \<le> e/2 * \<bar>z - x\<bar>"
      by auto
    show "\<exists>d>0. \<forall>u v. u \<le> x \<and> x \<le> v \<and> v - u < d \<longrightarrow> \<bar>f v - f u - f' x * (v - u)\<bar> \<le> e * (v - u)"
    proof (safe intro!: exI)
      show "0 < s" by fact
    next
      fix u v :: real assume "u \<le> x" and "x \<le> v" and "v - u < s"
      have "\<bar>f v - f u - f' x * (v - u)\<bar> =
            \<bar>(f v - f x - f' x * (v - x)) + (f x - f u - f' x * (x - u))\<bar>"
        by (simp add: right_diff_distrib)
      also have "\<dots> \<le> \<bar>f v - f x - f' x * (v - x)\<bar> + \<bar>f x - f u - f' x * (x - u)\<bar>"
        by (rule abs_triangle_ineq)
      also have "\<dots> = \<bar>f v - f x - f' x * (v - x)\<bar> + \<bar>f u - f x - f' x * (u - x)\<bar>"
        by (simp add: right_diff_distrib)
      also have "\<dots> \<le> (e/2) * \<bar>v - x\<bar> + (e/2) * \<bar>u - x\<bar>"
        using \<open>u \<le> x\<close> \<open>x \<le> v\<close> \<open>v - u < s\<close> by (intro add_mono strad, simp_all)
      also have "\<dots> \<le> e * (v - u) / 2 + e * (v - u) / 2"
        using \<open>u \<le> x\<close> \<open>x \<le> v\<close> \<open>0 < e\<close> by (intro add_mono, simp_all)
      also have "\<dots> = e * (v - u)"
        by simp
      finally show "\<bar>f v - f u - f' x * (v - u)\<bar> \<le> e * (v - u)" .
    qed
  qed
  thus ?thesis
    by (simp add: gauge_def) (drule bchoice, auto)
qed

lemma fundamental_theorem_of_calculus:
  assumes "a \<le> b"
  assumes f': "\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> DERIV f x :> f'(x)"
  shows "Integral (a, b) f' (f(b) - f(a))"
proof (cases "a = b")
  assume "a = b" thus ?thesis by simp
next
  assume "a \<noteq> b" with \<open>a \<le> b\<close> have "a < b" by simp
  show ?thesis
  proof (simp add: Integral_def2, clarify)
    fix e :: real assume "0 < e"
    with \<open>a < b\<close> have "0 < e / (b - a)" by simp

    from lemma_straddle [OF f' this]
    obtain \<delta> where "gauge {a..b} \<delta>"
      and \<delta>: "\<lbrakk>a \<le> u; u \<le> x; x \<le> v; v \<le> b; v - u < \<delta> x\<rbrakk> \<Longrightarrow>
           \<bar>f v - f u - f' x * (v - u)\<bar> \<le> e * (v - u) / (b - a)" for x u v by auto

    have "\<forall>D. fine \<delta> (a, b) D \<longrightarrow> \<bar>rsum D f' - (f b - f a)\<bar> \<le> e"
    proof (clarify)
      fix D assume D: "fine \<delta> (a, b) D"
      hence "(\<Sum>(u, x, v)\<leftarrow>D. f v - f u) = f b - f a"
        by (rule fine_sum_list_eq_diff)
      hence "\<bar>rsum D f' - (f b - f a)\<bar> = \<bar>rsum D f' - (\<Sum>(u, x, v)\<leftarrow>D. f v - f u)\<bar>"
        by simp
      also have "\<dots> = \<bar>(\<Sum>(u, x, v)\<leftarrow>D. f v - f u) - rsum D f'\<bar>"
        by (rule abs_minus_commute)
      also have "\<dots> = \<bar>\<Sum>(u, x, v)\<leftarrow>D. (f v - f u) - f' x * (v - u)\<bar>"
        by (simp only: rsum_def sum_list_subtractf split_def)
      also have "\<dots> \<le> (\<Sum>(u, x, v)\<leftarrow>D. \<bar>(f v - f u) - f' x * (v - u)\<bar>)"
        by (rule ord_le_eq_trans [OF sum_list_abs], simp add: o_def split_def)
      also have "\<dots> \<le> (\<Sum>(u, x, v)\<leftarrow>D. (e / (b - a)) * (v - u))"
        apply (rule sum_list_mono, clarify, rename_tac u x v)
        using D apply (simp add: \<delta> mem_fine mem_fine2 mem_fine3)
        done
      also have "\<dots> = e"
        using fine_sum_list_eq_diff [OF D, where f="\<lambda>x. x"]
        unfolding split_def sum_list_const_mult
        using \<open>a < b\<close> by simp
      finally show "\<bar>rsum D f' - (f b - f a)\<bar> \<le> e" .
    qed

    with \<open>gauge {a..b} \<delta>\<close>
    show "\<exists>\<delta>. gauge {a..b} \<delta> \<and> (\<forall>D. fine \<delta> (a, b) D \<longrightarrow> \<bar>rsum D f' - (f b - f a)\<bar> \<le> e)"
      by auto
  qed
qed

end
