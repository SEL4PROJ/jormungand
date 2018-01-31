(*  Title:      HOL/Nonstandard_Analysis/HDeriv.thy
    Author:     Jacques D. Fleuriot
    Copyright:  1998  University of Cambridge
    Conversion to Isar and new proofs by Lawrence C Paulson, 2004
*)

section \<open>Differentiation (Nonstandard)\<close>

theory HDeriv
  imports HLim
begin

text \<open>Nonstandard Definitions.\<close>

definition nsderiv :: "['a::real_normed_field \<Rightarrow> 'a, 'a, 'a] \<Rightarrow> bool"
    ("(NSDERIV (_)/ (_)/ :> (_))" [1000, 1000, 60] 60)
  where "NSDERIV f x :> D \<longleftrightarrow>
    (\<forall>h \<in> Infinitesimal - {0}. (( *f* f)(star_of x + h) - star_of (f x)) / h \<approx> star_of D)"

definition NSdifferentiable :: "['a::real_normed_field \<Rightarrow> 'a, 'a] \<Rightarrow> bool"
    (infixl "NSdifferentiable" 60)
  where "f NSdifferentiable x \<longleftrightarrow> (\<exists>D. NSDERIV f x :> D)"

definition increment :: "(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> hypreal \<Rightarrow> hypreal"
  where "increment f x h =
    (SOME inc. f NSdifferentiable x \<and> inc = ( *f* f) (hypreal_of_real x + h) - hypreal_of_real (f x))"


subsection \<open>Derivatives\<close>

lemma DERIV_NS_iff: "(DERIV f x :> D) \<longleftrightarrow> (\<lambda>h. (f (x + h) - f x) / h) \<midarrow>0\<rightarrow>\<^sub>N\<^sub>S D"
  by (simp add: DERIV_def LIM_NSLIM_iff)

lemma NS_DERIV_D: "DERIV f x :> D \<Longrightarrow> (\<lambda>h. (f (x + h) - f x) / h) \<midarrow>0\<rightarrow>\<^sub>N\<^sub>S D"
  by (simp add: DERIV_def LIM_NSLIM_iff)

lemma hnorm_of_hypreal: "\<And>r. hnorm (( *f* of_real) r::'a::real_normed_div_algebra star) = \<bar>r\<bar>"
  by transfer (rule norm_of_real)

lemma Infinitesimal_of_hypreal:
  "x \<in> Infinitesimal \<Longrightarrow> (( *f* of_real) x::'a::real_normed_div_algebra star) \<in> Infinitesimal"
  apply (rule InfinitesimalI2)
  apply (drule (1) InfinitesimalD2)
  apply (simp add: hnorm_of_hypreal)
  done

lemma of_hypreal_eq_0_iff: "\<And>x. (( *f* of_real) x = (0::'a::real_algebra_1 star)) = (x = 0)"
  by transfer (rule of_real_eq_0_iff)

lemma NSDeriv_unique: "NSDERIV f x :> D \<Longrightarrow> NSDERIV f x :> E \<Longrightarrow> D = E"
  apply (subgoal_tac "( *f* of_real) \<epsilon> \<in> Infinitesimal - {0::'a star}")
   apply (simp only: nsderiv_def)
   apply (drule (1) bspec)+
   apply (drule (1) approx_trans3)
   apply simp
  apply (simp add: Infinitesimal_of_hypreal Infinitesimal_epsilon)
  apply (simp add: of_hypreal_eq_0_iff hypreal_epsilon_not_zero)
  done

text \<open>First \<open>NSDERIV\<close> in terms of \<open>NSLIM\<close>.\<close>

text \<open>First equivalence.\<close>
lemma NSDERIV_NSLIM_iff: "(NSDERIV f x :> D) \<longleftrightarrow> (\<lambda>h. (f (x + h) - f x) / h) \<midarrow>0\<rightarrow>\<^sub>N\<^sub>S D"
  apply (auto simp add: nsderiv_def NSLIM_def)
   apply (drule_tac x = xa in bspec)
    apply (rule_tac [3] ccontr)
    apply (drule_tac [3] x = h in spec)
    apply (auto simp add: mem_infmal_iff starfun_lambda_cancel)
  done

text \<open>Second equivalence.\<close>
lemma NSDERIV_NSLIM_iff2: "(NSDERIV f x :> D) \<longleftrightarrow> (\<lambda>z. (f z - f x) / (z - x)) \<midarrow>x\<rightarrow>\<^sub>N\<^sub>S D"
  by (simp add: NSDERIV_NSLIM_iff DERIV_LIM_iff LIM_NSLIM_iff [symmetric])

text \<open>While we're at it!\<close>
lemma NSDERIV_iff2:
  "(NSDERIV f x :> D) \<longleftrightarrow>
    (\<forall>w. w \<noteq> star_of x & w \<approx> star_of x \<longrightarrow> ( *f* (%z. (f z - f x) / (z-x))) w \<approx> star_of D)"
  by (simp add: NSDERIV_NSLIM_iff2 NSLIM_def)

(* FIXME delete *)
lemma hypreal_not_eq_minus_iff: "x \<noteq> a \<longleftrightarrow> x - a \<noteq> (0::'a::ab_group_add)"
  by auto

lemma NSDERIVD5:
  "(NSDERIV f x :> D) \<Longrightarrow>
   (\<forall>u. u \<approx> hypreal_of_real x \<longrightarrow>
     ( *f* (\<lambda>z. f z - f x)) u \<approx> hypreal_of_real D * (u - hypreal_of_real x))"
  apply (auto simp add: NSDERIV_iff2)
  apply (case_tac "u = hypreal_of_real x", auto)
  apply (drule_tac x = u in spec, auto)
  apply (drule_tac c = "u - hypreal_of_real x" and b = "hypreal_of_real D" in approx_mult1)
   apply (drule_tac [!] hypreal_not_eq_minus_iff [THEN iffD1])
   apply (subgoal_tac [2] "( *f* (%z. z-x)) u \<noteq> (0::hypreal) ")
    apply (auto simp: approx_minus_iff [THEN iffD1, THEN mem_infmal_iff [THEN iffD2]]
      Infinitesimal_subset_HFinite [THEN subsetD])
  done

lemma NSDERIVD4:
  "(NSDERIV f x :> D) \<Longrightarrow>
    (\<forall>h \<in> Infinitesimal.
      ( *f* f)(hypreal_of_real x + h) - hypreal_of_real (f x) \<approx> hypreal_of_real D * h)"
  apply (auto simp add: nsderiv_def)
  apply (case_tac "h = 0")
   apply auto
  apply (drule_tac x = h in bspec)
   apply (drule_tac [2] c = h in approx_mult1)
    apply (auto intro: Infinitesimal_subset_HFinite [THEN subsetD])
  done

lemma NSDERIVD3:
  "(NSDERIV f x :> D) \<Longrightarrow>
    \<forall>h \<in> Infinitesimal - {0}.
      (( *f* f) (hypreal_of_real x + h) - hypreal_of_real (f x)) \<approx> hypreal_of_real D * h"
  apply (auto simp add: nsderiv_def)
  apply (rule ccontr, drule_tac x = h in bspec)
   apply (drule_tac [2] c = h in approx_mult1)
    apply (auto intro: Infinitesimal_subset_HFinite [THEN subsetD] simp add: mult.assoc)
  done

text \<open>Differentiability implies continuity nice and simple "algebraic" proof.\<close>
lemma NSDERIV_isNSCont: "NSDERIV f x :> D \<Longrightarrow> isNSCont f x"
  apply (auto simp add: nsderiv_def isNSCont_NSLIM_iff NSLIM_def)
  apply (drule approx_minus_iff [THEN iffD1])
  apply (drule hypreal_not_eq_minus_iff [THEN iffD1])
  apply (drule_tac x = "xa - star_of x" in bspec)
   prefer 2 apply (simp add: add.assoc [symmetric])
   apply (auto simp add: mem_infmal_iff [symmetric] add.commute)
  apply (drule_tac c = "xa - star_of x" in approx_mult1)
   apply (auto intro: Infinitesimal_subset_HFinite [THEN subsetD] simp add: mult.assoc)
  apply (drule_tac x3=D in
      HFinite_star_of [THEN [2] Infinitesimal_HFinite_mult, THEN mem_infmal_iff [THEN iffD1]])
  apply (auto simp add: mult.commute intro: approx_trans approx_minus_iff [THEN iffD2])
  done

text \<open>Differentiation rules for combinations of functions
  follow from clear, straightforard, algebraic manipulations.\<close>

text \<open>Constant function.\<close>

(* use simple constant nslimit theorem *)
lemma NSDERIV_const [simp]: "NSDERIV (\<lambda>x. k) x :> 0"
  by (simp add: NSDERIV_NSLIM_iff)

text \<open>Sum of functions- proved easily.\<close>

lemma NSDERIV_add:
  "NSDERIV f x :> Da \<Longrightarrow> NSDERIV g x :> Db \<Longrightarrow> NSDERIV (\<lambda>x. f x + g x) x :> Da + Db"
  apply (auto simp add: NSDERIV_NSLIM_iff NSLIM_def)
  apply (auto simp add: add_divide_distrib diff_divide_distrib dest!: spec)
  apply (drule_tac b = "star_of Da" and d = "star_of Db" in approx_add)
   apply (auto simp add: ac_simps algebra_simps)
  done

text \<open>Product of functions - Proof is trivial but tedious
  and long due to rearrangement of terms.\<close>

lemma lemma_nsderiv1: "(a * b) - (c * d) = (b * (a - c)) + (c * (b - d))"
  for a b c d :: "'a::comm_ring star"
  by (simp add: right_diff_distrib ac_simps)

lemma lemma_nsderiv2: "(x - y) / z = star_of D + yb \<Longrightarrow> z \<noteq> 0 \<Longrightarrow>
  z \<in> Infinitesimal \<Longrightarrow> yb \<in> Infinitesimal \<Longrightarrow> x - y \<approx> 0"
  for x y z :: "'a::real_normed_field star"
  apply (simp add: nonzero_divide_eq_eq)
  apply (auto intro!: Infinitesimal_HFinite_mult2 HFinite_add
      simp add: mult.assoc mem_infmal_iff [symmetric])
  apply (erule Infinitesimal_subset_HFinite [THEN subsetD])
  done

lemma NSDERIV_mult:
  "NSDERIV f x :> Da \<Longrightarrow> NSDERIV g x :> Db \<Longrightarrow>
    NSDERIV (\<lambda>x. f x * g x) x :> (Da * g x) + (Db * f x)"
  apply (auto simp add: NSDERIV_NSLIM_iff NSLIM_def)
  apply (auto dest!: spec simp add: starfun_lambda_cancel lemma_nsderiv1)
  apply (simp (no_asm) add: add_divide_distrib diff_divide_distrib)
  apply (drule bex_Infinitesimal_iff2 [THEN iffD2])+
  apply (auto simp add: times_divide_eq_right [symmetric]
      simp del: times_divide_eq_right times_divide_eq_left)
  apply (drule_tac D = Db in lemma_nsderiv2, assumption+)
  apply (drule_tac approx_minus_iff [THEN iffD2, THEN bex_Infinitesimal_iff2 [THEN iffD2]])
  apply (auto intro!: approx_add_mono1 simp: distrib_right distrib_left mult.commute add.assoc)
  apply (rule_tac b1 = "star_of Db * star_of (f x)" in add.commute [THEN subst])
  apply (auto intro!: Infinitesimal_add_approx_self2 [THEN approx_sym]
      Infinitesimal_add Infinitesimal_mult Infinitesimal_star_of_mult Infinitesimal_star_of_mult2
      simp add: add.assoc [symmetric])
  done

text \<open>Multiplying by a constant.\<close>
lemma NSDERIV_cmult: "NSDERIV f x :> D \<Longrightarrow> NSDERIV (\<lambda>x. c * f x) x :> c * D"
  apply (simp only: times_divide_eq_right [symmetric] NSDERIV_NSLIM_iff
      minus_mult_right right_diff_distrib [symmetric])
  apply (erule NSLIM_const [THEN NSLIM_mult])
  done

text \<open>Negation of function.\<close>
lemma NSDERIV_minus: "NSDERIV f x :> D \<Longrightarrow> NSDERIV (\<lambda>x. - f x) x :> - D"
proof (simp add: NSDERIV_NSLIM_iff)
  assume "(\<lambda>h. (f (x + h) - f x) / h) \<midarrow>0\<rightarrow>\<^sub>N\<^sub>S D"
  then have deriv: "(\<lambda>h. - ((f(x+h) - f x) / h)) \<midarrow>0\<rightarrow>\<^sub>N\<^sub>S - D"
    by (rule NSLIM_minus)
  have "\<forall>h. - ((f (x + h) - f x) / h) = (- f (x + h) + f x) / h"
    by (simp add: minus_divide_left)
  with deriv have "(\<lambda>h. (- f (x + h) + f x) / h) \<midarrow>0\<rightarrow>\<^sub>N\<^sub>S - D"
    by simp
  then show "(\<lambda>h. (f (x + h) - f x) / h) \<midarrow>0\<rightarrow>\<^sub>N\<^sub>S D \<Longrightarrow> (\<lambda>h. (f x - f (x + h)) / h) \<midarrow>0\<rightarrow>\<^sub>N\<^sub>S - D"
    by simp
qed

text \<open>Subtraction.\<close>
lemma NSDERIV_add_minus:
  "NSDERIV f x :> Da \<Longrightarrow> NSDERIV g x :> Db \<Longrightarrow> NSDERIV (\<lambda>x. f x + - g x) x :> Da + - Db"
  by (blast dest: NSDERIV_add NSDERIV_minus)

lemma NSDERIV_diff:
  "NSDERIV f x :> Da \<Longrightarrow> NSDERIV g x :> Db \<Longrightarrow> NSDERIV (\<lambda>x. f x - g x) x :> Da - Db"
  using NSDERIV_add_minus [of f x Da g Db] by simp

text \<open>Similarly to the above, the chain rule admits an entirely
  straightforward derivation. Compare this with Harrison's
  HOL proof of the chain rule, which proved to be trickier and
  required an alternative characterisation of differentiability-
  the so-called Carathedory derivative. Our main problem is
  manipulation of terms.\<close>


subsection \<open>Lemmas\<close>

lemma NSDERIV_zero:
  "NSDERIV g x :> D \<Longrightarrow> ( *f* g) (star_of x + xa) = star_of (g x) \<Longrightarrow>
    xa \<in> Infinitesimal \<Longrightarrow> xa \<noteq> 0 \<Longrightarrow> D = 0"
  apply (simp add: nsderiv_def)
  apply (drule bspec)
   apply auto
  done

text \<open>Can be proved differently using \<open>NSLIM_isCont_iff\<close>.\<close>
lemma NSDERIV_approx:
  "NSDERIV f x :> D \<Longrightarrow> h \<in> Infinitesimal \<Longrightarrow> h \<noteq> 0 \<Longrightarrow>
    ( *f* f) (star_of x + h) - star_of (f x) \<approx> 0"
  apply (simp add: nsderiv_def)
  apply (simp add: mem_infmal_iff [symmetric])
  apply (rule Infinitesimal_ratio)
    apply (rule_tac [3] approx_star_of_HFinite, auto)
  done

text \<open>From one version of differentiability

        \<open>f x - f a\<close>
      \<open>-------------- \<approx> Db\<close>
          \<open>x - a\<close>
\<close>

lemma NSDERIVD1: "[| NSDERIV f (g x) :> Da;
         ( *f* g) (star_of(x) + xa) \<noteq> star_of (g x);
         ( *f* g) (star_of(x) + xa) \<approx> star_of (g x)
      |] ==> (( *f* f) (( *f* g) (star_of(x) + xa))
                   - star_of (f (g x)))
              / (( *f* g) (star_of(x) + xa) - star_of (g x))
             \<approx> star_of(Da)"
  by (auto simp add: NSDERIV_NSLIM_iff2 NSLIM_def)

text \<open>From other version of differentiability

      \<open>f (x + h) - f x\<close>
     \<open>------------------ \<approx> Db\<close>
             \<open>h\<close>
\<close>

lemma NSDERIVD2: "[| NSDERIV g x :> Db; xa \<in> Infinitesimal; xa \<noteq> 0 |]
      ==> (( *f* g) (star_of(x) + xa) - star_of(g x)) / xa
          \<approx> star_of(Db)"
  by (auto simp add: NSDERIV_NSLIM_iff NSLIM_def mem_infmal_iff starfun_lambda_cancel)

lemma lemma_chain: "z \<noteq> 0 \<Longrightarrow> x * y = (x * inverse z) * (z * y)"
  for x y z :: "'a::real_normed_field star"
proof -
  assume z: "z \<noteq> 0"
  have "x * y = x * (inverse z * z) * y" by (simp add: z)
  then show ?thesis by (simp add: mult.assoc)
qed

text \<open>This proof uses both definitions of differentiability.\<close>
lemma NSDERIV_chain:
  "NSDERIV f (g x) :> Da \<Longrightarrow> NSDERIV g x :> Db \<Longrightarrow> NSDERIV (f \<circ> g) x :> Da * Db"
  apply (simp (no_asm_simp) add: NSDERIV_NSLIM_iff NSLIM_def mem_infmal_iff [symmetric])
  apply clarify
  apply (frule_tac f = g in NSDERIV_approx)
    apply (auto simp add: starfun_lambda_cancel2 starfun_o [symmetric])
  apply (case_tac "( *f* g) (star_of (x) + xa) = star_of (g x) ")
   apply (drule_tac g = g in NSDERIV_zero)
      apply (auto simp add: divide_inverse)
  apply (rule_tac z1 = "( *f* g) (star_of (x) + xa) - star_of (g x) " and y1 = "inverse xa" in lemma_chain [THEN ssubst])
   apply (erule hypreal_not_eq_minus_iff [THEN iffD1])
  apply (rule approx_mult_star_of)
   apply (simp_all add: divide_inverse [symmetric])
   apply (blast intro: NSDERIVD1 approx_minus_iff [THEN iffD2])
  apply (blast intro: NSDERIVD2)
  done

text \<open>Differentiation of natural number powers.\<close>
lemma NSDERIV_Id [simp]: "NSDERIV (\<lambda>x. x) x :> 1"
  by (simp add: NSDERIV_NSLIM_iff NSLIM_def del: divide_self_if)

lemma NSDERIV_cmult_Id [simp]: "NSDERIV (op * c) x :> c"
  using NSDERIV_Id [THEN NSDERIV_cmult] by simp

lemma NSDERIV_inverse:
  fixes x :: "'a::real_normed_field"
  assumes "x \<noteq> 0" \<comment> \<open>can't get rid of @{term "x \<noteq> 0"} because it isn't continuous at zero\<close>
  shows "NSDERIV (\<lambda>x. inverse x) x :> - (inverse x ^ Suc (Suc 0))"
proof -
  {
    fix h :: "'a star"
    assume h_Inf: "h \<in> Infinitesimal"
    from this assms have not_0: "star_of x + h \<noteq> 0"
      by (rule Infinitesimal_add_not_zero)
    assume "h \<noteq> 0"
    from h_Inf have "h * star_of x \<in> Infinitesimal"
      by (rule Infinitesimal_HFinite_mult) simp
    with assms have "inverse (- (h * star_of x) + - (star_of x * star_of x)) \<approx>
      inverse (- (star_of x * star_of x))"
      apply -
      apply (rule inverse_add_Infinitesimal_approx2)
      apply (auto dest!: hypreal_of_real_HFinite_diff_Infinitesimal
        simp add: inverse_minus_eq [symmetric] HFinite_minus_iff)
      done
    moreover from not_0 \<open>h \<noteq> 0\<close> assms
    have "inverse (- (h * star_of x) + - (star_of x * star_of x)) =
      (inverse (star_of x + h) - inverse (star_of x)) / h"
      apply (simp add: division_ring_inverse_diff nonzero_inverse_mult_distrib [symmetric]
          nonzero_inverse_minus_eq [symmetric] ac_simps ring_distribs)
      apply (subst nonzero_inverse_minus_eq [symmetric])
      using distrib_right [symmetric, of h "star_of x" "star_of x"] apply simp
      apply (simp add: field_simps)
      done
    ultimately have "(inverse (star_of x + h) - inverse (star_of x)) / h \<approx>
      - (inverse (star_of x) * inverse (star_of x))"
      using assms by simp
  }
  then show ?thesis by (simp add: nsderiv_def)
qed


subsubsection \<open>Equivalence of NS and Standard definitions\<close>

lemma divideR_eq_divide: "x /\<^sub>R y = x / y"
  by (simp add: divide_inverse mult.commute)

text \<open>Now equivalence between \<open>NSDERIV\<close> and \<open>DERIV\<close>.\<close>
lemma NSDERIV_DERIV_iff: "NSDERIV f x :> D \<longleftrightarrow> DERIV f x :> D"
  by (simp add: DERIV_def NSDERIV_NSLIM_iff LIM_NSLIM_iff)

text \<open>NS version.\<close>
lemma NSDERIV_pow: "NSDERIV (\<lambda>x. x ^ n) x :> real n * (x ^ (n - Suc 0))"
  by (simp add: NSDERIV_DERIV_iff DERIV_pow)

text \<open>Derivative of inverse.\<close>
lemma NSDERIV_inverse_fun:
  "NSDERIV f x :> d \<Longrightarrow> f x \<noteq> 0 \<Longrightarrow>
    NSDERIV (\<lambda>x. inverse (f x)) x :> (- (d * inverse (f x ^ Suc (Suc 0))))"
  for x :: "'a::{real_normed_field}"
  by (simp add: NSDERIV_DERIV_iff DERIV_inverse_fun del: power_Suc)

text \<open>Derivative of quotient.\<close>
lemma NSDERIV_quotient:
  fixes x :: "'a::real_normed_field"
  shows "NSDERIV f x :> d \<Longrightarrow> NSDERIV g x :> e \<Longrightarrow> g x \<noteq> 0 \<Longrightarrow>
    NSDERIV (\<lambda>y. f y / g y) x :> (d * g x - (e * f x)) / (g x ^ Suc (Suc 0))"
  by (simp add: NSDERIV_DERIV_iff DERIV_quotient del: power_Suc)

lemma CARAT_NSDERIV:
  "NSDERIV f x :> l \<Longrightarrow> \<exists>g. (\<forall>z. f z - f x = g z * (z - x)) \<and> isNSCont g x \<and> g x = l"
  by (auto simp add: NSDERIV_DERIV_iff isNSCont_isCont_iff CARAT_DERIV mult.commute)

lemma hypreal_eq_minus_iff3: "x = y + z \<longleftrightarrow> x + - z = y"
  for x y z :: hypreal
  by auto

lemma CARAT_DERIVD:
  assumes all: "\<forall>z. f z - f x = g z * (z - x)"
    and nsc: "isNSCont g x"
  shows "NSDERIV f x :> g x"
proof -
  from nsc have "\<forall>w. w \<noteq> star_of x \<and> w \<approx> star_of x \<longrightarrow>
       ( *f* g) w * (w - star_of x) / (w - star_of x) \<approx> star_of (g x)"
    by (simp add: isNSCont_def)
  with all show ?thesis
    by (simp add: NSDERIV_iff2 starfun_if_eq cong: if_cong)
qed


subsubsection \<open>Differentiability predicate\<close>

lemma NSdifferentiableD: "f NSdifferentiable x \<Longrightarrow> \<exists>D. NSDERIV f x :> D"
  by (simp add: NSdifferentiable_def)

lemma NSdifferentiableI: "NSDERIV f x :> D \<Longrightarrow> f NSdifferentiable x"
  by (force simp add: NSdifferentiable_def)


subsection \<open>(NS) Increment\<close>

lemma incrementI:
  "f NSdifferentiable x \<Longrightarrow>
    increment f x h = ( *f* f) (hypreal_of_real x + h) - hypreal_of_real (f x)"
  by (simp add: increment_def)

lemma incrementI2:
  "NSDERIV f x :> D \<Longrightarrow>
    increment f x h = ( *f* f) (hypreal_of_real x + h) - hypreal_of_real (f x)"
  by (erule NSdifferentiableI [THEN incrementI])

text \<open>The Increment theorem -- Keisler p. 65.\<close>
lemma increment_thm:
  "NSDERIV f x :> D \<Longrightarrow> h \<in> Infinitesimal \<Longrightarrow> h \<noteq> 0 \<Longrightarrow>
    \<exists>e \<in> Infinitesimal. increment f x h = hypreal_of_real D * h + e * h"
  apply (frule_tac h = h in incrementI2, simp add: nsderiv_def)
  apply (drule bspec, auto)
  apply (drule bex_Infinitesimal_iff2 [THEN iffD2], clarify)
  apply (frule_tac b1 = "hypreal_of_real D + y" in mult_right_cancel [THEN iffD2])
   apply (erule_tac [2]
      V = "(( *f* f) (hypreal_of_real x + h) - hypreal_of_real (f x)) / h = hypreal_of_real (D) + y"
      in thin_rl)
   apply assumption
  apply (simp add: times_divide_eq_right [symmetric])
  apply (auto simp add: distrib_right)
  done

lemma increment_thm2:
  "NSDERIV f x :> D \<Longrightarrow> h \<approx> 0 \<Longrightarrow> h \<noteq> 0 \<Longrightarrow>
    \<exists>e \<in> Infinitesimal. increment f x h = hypreal_of_real D * h + e * h"
  by (blast dest!: mem_infmal_iff [THEN iffD2] intro!: increment_thm)

lemma increment_approx_zero: "NSDERIV f x :> D \<Longrightarrow> h \<approx> 0 \<Longrightarrow> h \<noteq> 0 \<Longrightarrow> increment f x h \<approx> 0"
  apply (drule increment_thm2)
    apply (auto intro!: Infinitesimal_HFinite_mult2 HFinite_add
      simp add: distrib_right [symmetric] mem_infmal_iff [symmetric])
  apply (erule Infinitesimal_subset_HFinite [THEN subsetD])
  done

end
