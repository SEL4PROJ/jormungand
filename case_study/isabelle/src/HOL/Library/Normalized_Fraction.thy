theory Normalized_Fraction
imports 
  Main 
  "~~/src/HOL/Number_Theory/Euclidean_Algorithm" 
  "~~/src/HOL/Library/Fraction_Field"
begin

lemma dvd_neg_div': "y dvd (x :: 'a :: idom_divide) \<Longrightarrow> -x div y = - (x div y)"
apply (case_tac "y = 0") apply simp
apply (auto simp add: dvd_def)
apply (subgoal_tac "-(y * k) = y * - k")
apply (simp only:)
apply (erule nonzero_mult_div_cancel_left)
apply simp
done

(* TODO Move *)
lemma (in semiring_gcd) coprime_mul_eq': "coprime (a * b) d \<longleftrightarrow> coprime a d \<and> coprime b d"
  using coprime_mul_eq[of d a b] by (simp add: gcd.commute)

lemma dvd_div_eq_0_iff:
  assumes "b dvd (a :: 'a :: semidom_divide)"
  shows   "a div b = 0 \<longleftrightarrow> a = 0"
  using assms by (elim dvdE, cases "b = 0") simp_all  

lemma dvd_div_eq_0_iff':
  assumes "b dvd (a :: 'a :: semiring_div)"
  shows   "a div b = 0 \<longleftrightarrow> a = 0"
  using assms by (elim dvdE, cases "b = 0") simp_all

lemma unit_div_eq_0_iff:
  assumes "is_unit (b :: 'a :: {algebraic_semidom,semidom_divide})"
  shows   "a div b = 0 \<longleftrightarrow> a = 0"
  by (rule dvd_div_eq_0_iff) (insert assms, auto)  

lemma unit_div_eq_0_iff':
  assumes "is_unit (b :: 'a :: semiring_div)"
  shows   "a div b = 0 \<longleftrightarrow> a = 0"
  by (rule dvd_div_eq_0_iff) (insert assms, auto)

lemma dvd_div_eq_cancel:
  "a div c = b div c \<Longrightarrow> (c :: 'a :: semiring_div) dvd a \<Longrightarrow> c dvd b \<Longrightarrow> a = b"
  by (elim dvdE, cases "c = 0") simp_all

lemma dvd_div_eq_iff:
  "(c :: 'a :: semiring_div) dvd a \<Longrightarrow> c dvd b \<Longrightarrow> a div c = b div c \<longleftrightarrow> a = b"
  by (elim dvdE, cases "c = 0") simp_all

lemma normalize_imp_eq:
  "normalize a = normalize b \<Longrightarrow> unit_factor a = unit_factor b \<Longrightarrow> a = b"
  by (cases "a = 0 \<or> b = 0")
     (auto simp add: div_unit_factor [symmetric] unit_div_cancel simp del: div_unit_factor)
    
lemma coprime_crossproduct':
  fixes a b c d :: "'a :: semiring_gcd"
  assumes nz: "b \<noteq> 0"
  assumes unit_factors: "unit_factor b = unit_factor d"
  assumes coprime: "coprime a b" "coprime c d"
  shows "a * d = b * c \<longleftrightarrow> a = c \<and> b = d"
proof safe
  assume eq: "a * d = b * c"
  hence "normalize a * normalize d = normalize c * normalize b"
    by (simp only: normalize_mult [symmetric] mult_ac)
  with coprime have "normalize b = normalize d"
    by (subst (asm) coprime_crossproduct) simp_all
  from this and unit_factors show "b = d" by (rule normalize_imp_eq)
  from eq have "a * d = c * d" by (simp only: \<open>b = d\<close> mult_ac)
  with nz \<open>b = d\<close> show "a = c" by simp
qed (simp_all add: mult_ac)
  
     
lemma div_mult_unit2: "is_unit c \<Longrightarrow> b dvd a \<Longrightarrow> a div (b * c) = a div b div c"
  by (subst dvd_div_mult2_eq) (simp_all add: mult_unit_dvd_iff)
(* END TODO *)


definition quot_to_fract :: "'a :: {idom} \<times> 'a \<Rightarrow> 'a fract" where
  "quot_to_fract = (\<lambda>(a,b). Fraction_Field.Fract a b)"

definition normalize_quot :: "'a :: {ring_gcd,idom_divide} \<times> 'a \<Rightarrow> 'a \<times> 'a" where
  "normalize_quot = 
     (\<lambda>(a,b). if b = 0 then (0,1) else let d = gcd a b * unit_factor b in (a div d, b div d))" 

definition normalized_fracts :: "('a :: {ring_gcd,idom_divide} \<times> 'a) set" where
  "normalized_fracts = {(a,b). coprime a b \<and> unit_factor b = 1}"
  
lemma not_normalized_fracts_0_denom [simp]: "(a, 0) \<notin> normalized_fracts"
  by (auto simp: normalized_fracts_def)

lemma unit_factor_snd_normalize_quot [simp]:
  "unit_factor (snd (normalize_quot x)) = 1"
  by (simp add: normalize_quot_def case_prod_unfold Let_def dvd_unit_factor_div
                mult_unit_dvd_iff unit_factor_mult unit_factor_gcd)
  
lemma snd_normalize_quot_nonzero [simp]: "snd (normalize_quot x) \<noteq> 0"
  using unit_factor_snd_normalize_quot[of x] 
  by (auto simp del: unit_factor_snd_normalize_quot)
  
lemma normalize_quot_aux:
  fixes a b
  assumes "b \<noteq> 0"
  defines "d \<equiv> gcd a b * unit_factor b"
  shows   "a = fst (normalize_quot (a,b)) * d" "b = snd (normalize_quot (a,b)) * d"
          "d dvd a" "d dvd b" "d \<noteq> 0"
proof -
  from assms show "d dvd a" "d dvd b"
    by (simp_all add: d_def mult_unit_dvd_iff)
  thus "a = fst (normalize_quot (a,b)) * d" "b = snd (normalize_quot (a,b)) * d" "d \<noteq> 0"
    by (auto simp: normalize_quot_def Let_def d_def \<open>b \<noteq> 0\<close>)
qed

lemma normalize_quotE:
  assumes "b \<noteq> 0"
  obtains d where "a = fst (normalize_quot (a,b)) * d" "b = snd (normalize_quot (a,b)) * d"
                  "d dvd a" "d dvd b" "d \<noteq> 0"
  using that[OF normalize_quot_aux[OF assms]] .
  
lemma normalize_quotE':
  assumes "snd x \<noteq> 0"
  obtains d where "fst x = fst (normalize_quot x) * d" "snd x = snd (normalize_quot x) * d"
                  "d dvd fst x" "d dvd snd x" "d \<noteq> 0"
proof -
  from normalize_quotE[OF assms, of "fst x"] guess d .
  from this show ?thesis unfolding prod.collapse by (intro that[of d])
qed
  
lemma coprime_normalize_quot:
  "coprime (fst (normalize_quot x)) (snd (normalize_quot x))"
  by (simp add: normalize_quot_def case_prod_unfold Let_def
        div_mult_unit2 gcd_div_unit1 gcd_div_unit2 div_gcd_coprime)

lemma normalize_quot_in_normalized_fracts [simp]: "normalize_quot x \<in> normalized_fracts"
  by (simp add: normalized_fracts_def coprime_normalize_quot case_prod_unfold)

lemma normalize_quot_eq_iff:
  assumes "b \<noteq> 0" "d \<noteq> 0"
  shows   "normalize_quot (a,b) = normalize_quot (c,d) \<longleftrightarrow> a * d = b * c"
proof -
  define x y where "x = normalize_quot (a,b)" and "y = normalize_quot (c,d)" 
  from normalize_quotE[OF assms(1), of a] normalize_quotE[OF assms(2), of c]
    obtain d1 d2 
      where "a = fst x * d1" "b = snd x * d1" "c = fst y * d2" "d = snd y * d2" "d1 \<noteq> 0" "d2 \<noteq> 0"
    unfolding x_def y_def by metis
  hence "a * d = b * c \<longleftrightarrow> fst x * snd y = snd x * fst y" by simp
  also have "\<dots> \<longleftrightarrow> fst x = fst y \<and> snd x = snd y"
    by (intro coprime_crossproduct') (simp_all add: x_def y_def coprime_normalize_quot)
  also have "\<dots> \<longleftrightarrow> x = y" using prod_eqI by blast
  finally show "x = y \<longleftrightarrow> a * d = b * c" ..
qed

lemma normalize_quot_eq_iff':
  assumes "snd x \<noteq> 0" "snd y \<noteq> 0"
  shows   "normalize_quot x = normalize_quot y \<longleftrightarrow> fst x * snd y = snd x * fst y"
  using assms by (cases x, cases y, hypsubst) (subst normalize_quot_eq_iff, simp_all)

lemma normalize_quot_id: "x \<in> normalized_fracts \<Longrightarrow> normalize_quot x = x"
  by (auto simp: normalized_fracts_def normalize_quot_def case_prod_unfold)

lemma normalize_quot_idem [simp]: "normalize_quot (normalize_quot x) = normalize_quot x"
  by (rule normalize_quot_id) simp_all

lemma fractrel_iff_normalize_quot_eq:
  "fractrel x y \<longleftrightarrow> normalize_quot x = normalize_quot y \<and> snd x \<noteq> 0 \<and> snd y \<noteq> 0"
  by (cases x, cases y) (auto simp: fractrel_def normalize_quot_eq_iff)
  
lemma fractrel_normalize_quot_left:
  assumes "snd x \<noteq> 0"
  shows   "fractrel (normalize_quot x) y \<longleftrightarrow> fractrel x y"
  using assms by (subst (1 2) fractrel_iff_normalize_quot_eq) auto

lemma fractrel_normalize_quot_right:
  assumes "snd x \<noteq> 0"
  shows   "fractrel y (normalize_quot x) \<longleftrightarrow> fractrel y x"
  using assms by (subst (1 2) fractrel_iff_normalize_quot_eq) auto

  
lift_definition quot_of_fract :: "'a :: {ring_gcd,idom_divide} fract \<Rightarrow> 'a \<times> 'a" 
    is normalize_quot
  by (subst (asm) fractrel_iff_normalize_quot_eq) simp_all
  
lemma quot_to_fract_quot_of_fract [simp]: "quot_to_fract (quot_of_fract x) = x"
  unfolding quot_to_fract_def
proof transfer
  fix x :: "'a \<times> 'a" assume rel: "fractrel x x"
  define x' where "x' = normalize_quot x"
  obtain a b where [simp]: "x = (a, b)" by (cases x)
  from rel have "b \<noteq> 0" by simp
  from normalize_quotE[OF this, of a] guess d .
  hence "a = fst x' * d" "b = snd x' * d" "d \<noteq> 0" "snd x' \<noteq> 0" by (simp_all add: x'_def)
  thus "fractrel (case x' of (a, b) \<Rightarrow> if b = 0 then (0, 1) else (a, b)) x"
    by (auto simp add: case_prod_unfold)
qed

lemma quot_of_fract_quot_to_fract: "quot_of_fract (quot_to_fract x) = normalize_quot x"
proof (cases "snd x = 0")
  case True
  thus ?thesis unfolding quot_to_fract_def
    by transfer (simp add: case_prod_unfold normalize_quot_def)
next
  case False
  thus ?thesis unfolding quot_to_fract_def by transfer (simp add: case_prod_unfold)
qed

lemma quot_of_fract_quot_to_fract': 
  "x \<in> normalized_fracts \<Longrightarrow> quot_of_fract (quot_to_fract x) = x"
  unfolding quot_to_fract_def by transfer (auto simp: normalize_quot_id)

lemma quot_of_fract_in_normalized_fracts [simp]: "quot_of_fract x \<in> normalized_fracts"
  by transfer simp

lemma normalize_quotI:
  assumes "a * d = b * c" "b \<noteq> 0" "(c, d) \<in> normalized_fracts"
  shows   "normalize_quot (a, b) = (c, d)"
proof -
  from assms have "normalize_quot (a, b) = normalize_quot (c, d)"
    by (subst normalize_quot_eq_iff) auto
  also have "\<dots> = (c, d)" by (intro normalize_quot_id) fact
  finally show ?thesis .
qed

lemma td_normalized_fract:
  "type_definition quot_of_fract quot_to_fract normalized_fracts"
  by standard (simp_all add: quot_of_fract_quot_to_fract')

lemma quot_of_fract_add_aux:
  assumes "snd x \<noteq> 0" "snd y \<noteq> 0" 
  shows   "(fst x * snd y + fst y * snd x) * (snd (normalize_quot x) * snd (normalize_quot y)) =
             snd x * snd y * (fst (normalize_quot x) * snd (normalize_quot y) +
             snd (normalize_quot x) * fst (normalize_quot y))"
proof -
  from normalize_quotE'[OF assms(1)] guess d . note d = this
  from normalize_quotE'[OF assms(2)] guess e . note e = this
  show ?thesis by (simp_all add: d e algebra_simps)
qed


locale fract_as_normalized_quot
begin
setup_lifting td_normalized_fract
end


lemma quot_of_fract_add:
  "quot_of_fract (x + y) = 
     (let (a,b) = quot_of_fract x; (c,d) = quot_of_fract y
      in  normalize_quot (a * d + b * c, b * d))"
  by transfer (insert quot_of_fract_add_aux, 
               simp_all add: Let_def case_prod_unfold normalize_quot_eq_iff)

lemma quot_of_fract_uminus:
  "quot_of_fract (-x) = (let (a,b) = quot_of_fract x in (-a, b))"
  by transfer (auto simp: case_prod_unfold Let_def normalize_quot_def dvd_neg_div' mult_unit_dvd_iff)

lemma quot_of_fract_diff:
  "quot_of_fract (x - y) = 
     (let (a,b) = quot_of_fract x; (c,d) = quot_of_fract y
      in  normalize_quot (a * d - b * c, b * d))" (is "_ = ?rhs")
proof -
  have "x - y = x + -y" by simp
  also have "quot_of_fract \<dots> = ?rhs"
    by (simp only: quot_of_fract_add quot_of_fract_uminus Let_def case_prod_unfold) simp_all
  finally show ?thesis .
qed

lemma normalize_quot_mult_coprime:
  assumes "coprime a b" "coprime c d" "unit_factor b = 1" "unit_factor d = 1"
  defines "e \<equiv> fst (normalize_quot (a, d))" and "f \<equiv> snd (normalize_quot (a, d))"
     and  "g \<equiv> fst (normalize_quot (c, b))" and "h \<equiv> snd (normalize_quot (c, b))"
  shows   "normalize_quot (a * c, b * d) = (e * g, f * h)"
proof (rule normalize_quotI)
  from assms have "b \<noteq> 0" "d \<noteq> 0" by auto
  from normalize_quotE[OF \<open>b \<noteq> 0\<close>, of c] guess k . note k = this [folded assms]
  from normalize_quotE[OF \<open>d \<noteq> 0\<close>, of a] guess l . note l = this [folded assms]
  from k l show "a * c * (f * h) = b * d * (e * g)" by (simp_all)
  from assms have [simp]: "unit_factor f = 1" "unit_factor h = 1"
    by simp_all
  from assms have "coprime e f" "coprime g h" by (simp_all add: coprime_normalize_quot)
  with k l assms(1,2) show "(e * g, f * h) \<in> normalized_fracts"
    by (simp add: normalized_fracts_def unit_factor_mult coprime_mul_eq coprime_mul_eq')
qed (insert assms(3,4), auto)

lemma normalize_quot_mult:
  assumes "snd x \<noteq> 0" "snd y \<noteq> 0"
  shows   "normalize_quot (fst x * fst y, snd x * snd y) = normalize_quot 
             (fst (normalize_quot x) * fst (normalize_quot y),
              snd (normalize_quot x) * snd (normalize_quot y))"
proof -
  from normalize_quotE'[OF assms(1)] guess d . note d = this
  from normalize_quotE'[OF assms(2)] guess e . note e = this
  show ?thesis by (simp_all add: d e algebra_simps normalize_quot_eq_iff)
qed

lemma quot_of_fract_mult:
  "quot_of_fract (x * y) = 
     (let (a,b) = quot_of_fract x; (c,d) = quot_of_fract y;
          (e,f) = normalize_quot (a,d); (g,h) = normalize_quot (c,b)
      in  (e*g, f*h))"
  by transfer (simp_all add: Let_def case_prod_unfold normalize_quot_mult_coprime [symmetric]
                 coprime_normalize_quot normalize_quot_mult [symmetric])
  
lemma normalize_quot_0 [simp]: 
    "normalize_quot (0, x) = (0, 1)" "normalize_quot (x, 0) = (0, 1)"
  by (simp_all add: normalize_quot_def)
  
lemma normalize_quot_eq_0_iff [simp]: "fst (normalize_quot x) = 0 \<longleftrightarrow> fst x = 0 \<or> snd x = 0"
  by (auto simp: normalize_quot_def case_prod_unfold Let_def div_mult_unit2 dvd_div_eq_0_iff)
  find_theorems "_ div _ = 0"
  
lemma fst_quot_of_fract_0_imp: "fst (quot_of_fract x) = 0 \<Longrightarrow> snd (quot_of_fract x) = 1"
  by transfer auto

lemma normalize_quot_swap:
  assumes "a \<noteq> 0" "b \<noteq> 0"
  defines "a' \<equiv> fst (normalize_quot (a, b))" and "b' \<equiv> snd (normalize_quot (a, b))"
  shows   "normalize_quot (b, a) = (b' div unit_factor a', a' div unit_factor a')"
proof (rule normalize_quotI)
  from normalize_quotE[OF assms(2), of a] guess d . note d = this [folded assms(3,4)]
  show "b * (a' div unit_factor a') = a * (b' div unit_factor a')"
    using assms(1,2) d 
    by (simp add: div_unit_factor [symmetric] unit_div_mult_swap mult_ac del: div_unit_factor)
  have "coprime a' b'" by (simp add: a'_def b'_def coprime_normalize_quot)
  thus "(b' div unit_factor a', a' div unit_factor a') \<in> normalized_fracts"
    using assms(1,2) d by (auto simp: normalized_fracts_def gcd_div_unit1 gcd_div_unit2 gcd.commute)
qed fact+
  
lemma quot_of_fract_inverse:
  "quot_of_fract (inverse x) = 
     (let (a,b) = quot_of_fract x; d = unit_factor a 
      in  if d = 0 then (0, 1) else (b div d, a div d))"
proof (transfer, goal_cases)
  case (1 x)
  from normalize_quot_swap[of "fst x" "snd x"] show ?case
    by (auto simp: Let_def case_prod_unfold)
qed

lemma normalize_quot_div_unit_left:
  fixes x y u
  assumes "is_unit u"
  defines "x' \<equiv> fst (normalize_quot (x, y))" and "y' \<equiv> snd (normalize_quot (x, y))"
  shows "normalize_quot (x div u, y) = (x' div u, y')"
proof (cases "y = 0")
  case False
  from normalize_quotE[OF this, of x] guess d . note d = this[folded assms(2,3)]
  from assms have "coprime x' y'" "unit_factor y' = 1" by (simp_all add: coprime_normalize_quot)
  with False d \<open>is_unit u\<close> show ?thesis
    by (intro normalize_quotI)
       (auto simp: normalized_fracts_def unit_div_mult_swap unit_div_commute unit_div_cancel
          gcd_div_unit1)
qed (simp_all add: assms)

lemma normalize_quot_div_unit_right:
  fixes x y u
  assumes "is_unit u"
  defines "x' \<equiv> fst (normalize_quot (x, y))" and "y' \<equiv> snd (normalize_quot (x, y))"
  shows "normalize_quot (x, y div u) = (x' * u, y')"
proof (cases "y = 0")
  case False
  from normalize_quotE[OF this, of x] guess d . note d = this[folded assms(2,3)]
  from assms have "coprime x' y'" "unit_factor y' = 1" by (simp_all add: coprime_normalize_quot)
  with False d \<open>is_unit u\<close> show ?thesis
    by (intro normalize_quotI)
       (auto simp: normalized_fracts_def unit_div_mult_swap unit_div_commute unit_div_cancel
          gcd_mult_unit1 unit_div_eq_0_iff mult.assoc [symmetric])
qed (simp_all add: assms)

lemma normalize_quot_normalize_left:
  fixes x y u
  defines "x' \<equiv> fst (normalize_quot (x, y))" and "y' \<equiv> snd (normalize_quot (x, y))"
  shows "normalize_quot (normalize x, y) = (x' div unit_factor x, y')"
  using normalize_quot_div_unit_left[of "unit_factor x" x y]
  by (cases "x = 0") (simp_all add: assms)
  
lemma normalize_quot_normalize_right:
  fixes x y u
  defines "x' \<equiv> fst (normalize_quot (x, y))" and "y' \<equiv> snd (normalize_quot (x, y))"
  shows "normalize_quot (x, normalize y) = (x' * unit_factor y, y')"
  using normalize_quot_div_unit_right[of "unit_factor y" x y]
  by (cases "y = 0") (simp_all add: assms)
  
lemma quot_of_fract_0 [simp]: "quot_of_fract 0 = (0, 1)"
  by transfer auto

lemma quot_of_fract_1 [simp]: "quot_of_fract 1 = (1, 1)"
  by transfer (rule normalize_quotI, simp_all add: normalized_fracts_def)

lemma quot_of_fract_divide:
  "quot_of_fract (x / y) = (if y = 0 then (0, 1) else
     (let (a,b) = quot_of_fract x; (c,d) = quot_of_fract y;
          (e,f) = normalize_quot (a,c); (g,h) = normalize_quot (d,b)
      in  (e * g, f * h)))" (is "_ = ?rhs")
proof (cases "y = 0")
  case False
  hence A: "fst (quot_of_fract y) \<noteq> 0" by transfer auto
  have "x / y = x * inverse y" by (simp add: divide_inverse)
  also from False A have "quot_of_fract \<dots> = ?rhs"
    by (simp only: quot_of_fract_mult quot_of_fract_inverse)
       (simp_all add: Let_def case_prod_unfold fst_quot_of_fract_0_imp
          normalize_quot_div_unit_left normalize_quot_div_unit_right 
          normalize_quot_normalize_right normalize_quot_normalize_left)
  finally show ?thesis .
qed simp_all

end
