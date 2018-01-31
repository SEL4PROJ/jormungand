(*  Author:     Bernhard Haeupler

Proving equalities in commutative rings done "right" in Isabelle/HOL.
*)

section \<open>Proving equalities in commutative rings\<close>

theory Commutative_Ring
imports Main
begin

text \<open>Syntax of multivariate polynomials (pol) and polynomial expressions.\<close>

datatype 'a pol =
    Pc 'a
  | Pinj nat "'a pol"
  | PX "'a pol" nat "'a pol"

datatype 'a polex =
    Pol "'a pol"
  | Add "'a polex" "'a polex"
  | Sub "'a polex" "'a polex"
  | Mul "'a polex" "'a polex"
  | Pow "'a polex" nat
  | Neg "'a polex"

text \<open>Interpretation functions for the shadow syntax.\<close>

primrec Ipol :: "'a::comm_ring_1 list \<Rightarrow> 'a pol \<Rightarrow> 'a"
where
    "Ipol l (Pc c) = c"
  | "Ipol l (Pinj i P) = Ipol (drop i l) P"
  | "Ipol l (PX P x Q) = Ipol l P * (hd l)^x + Ipol (drop 1 l) Q"

primrec Ipolex :: "'a::comm_ring_1 list \<Rightarrow> 'a polex \<Rightarrow> 'a"
where
    "Ipolex l (Pol P) = Ipol l P"
  | "Ipolex l (Add P Q) = Ipolex l P + Ipolex l Q"
  | "Ipolex l (Sub P Q) = Ipolex l P - Ipolex l Q"
  | "Ipolex l (Mul P Q) = Ipolex l P * Ipolex l Q"
  | "Ipolex l (Pow p n) = Ipolex l p ^ n"
  | "Ipolex l (Neg P) = - Ipolex l P"

text \<open>Create polynomial normalized polynomials given normalized inputs.\<close>

definition mkPinj :: "nat \<Rightarrow> 'a pol \<Rightarrow> 'a pol"
where
  "mkPinj x P =
    (case P of
      Pc c \<Rightarrow> Pc c
    | Pinj y P \<Rightarrow> Pinj (x + y) P
    | PX p1 y p2 \<Rightarrow> Pinj x P)"

definition mkPX :: "'a::comm_ring pol \<Rightarrow> nat \<Rightarrow> 'a pol \<Rightarrow> 'a pol"
where
  "mkPX P i Q =
    (case P of
      Pc c \<Rightarrow> if c = 0 then mkPinj 1 Q else PX P i Q
    | Pinj j R \<Rightarrow> PX P i Q
    | PX P2 i2 Q2 \<Rightarrow> if Q2 = Pc 0 then PX P2 (i + i2) Q else PX P i Q)"

text \<open>Defining the basic ring operations on normalized polynomials\<close>

lemma pol_size_nz[simp]: "size (p :: 'a pol) \<noteq> 0"
  by (cases p) simp_all

function add :: "'a::comm_ring pol \<Rightarrow> 'a pol \<Rightarrow> 'a pol"  (infixl "\<oplus>" 65)
where
  "Pc a \<oplus> Pc b = Pc (a + b)"
| "Pc c \<oplus> Pinj i P = Pinj i (P \<oplus> Pc c)"
| "Pinj i P \<oplus> Pc c = Pinj i (P \<oplus> Pc c)"
| "Pc c \<oplus> PX P i Q = PX P i (Q \<oplus> Pc c)"
| "PX P i Q \<oplus> Pc c = PX P i (Q \<oplus> Pc c)"
| "Pinj x P \<oplus> Pinj y Q =
    (if x = y then mkPinj x (P \<oplus> Q)
     else (if x > y then mkPinj y (Pinj (x - y) P \<oplus> Q)
       else mkPinj x (Pinj (y - x) Q \<oplus> P)))"
| "Pinj x P \<oplus> PX Q y R =
    (if x = 0 then P \<oplus> PX Q y R
     else (if x = 1 then PX Q y (R \<oplus> P)
       else PX Q y (R \<oplus> Pinj (x - 1) P)))"
| "PX P x R \<oplus> Pinj y Q =
    (if y = 0 then PX P x R \<oplus> Q
     else (if y = 1 then PX P x (R \<oplus> Q)
       else PX P x (R \<oplus> Pinj (y - 1) Q)))"
| "PX P1 x P2 \<oplus> PX Q1 y Q2 =
    (if x = y then mkPX (P1 \<oplus> Q1) x (P2 \<oplus> Q2)
     else (if x > y then mkPX (PX P1 (x - y) (Pc 0) \<oplus> Q1) y (P2 \<oplus> Q2)
       else mkPX (PX Q1 (y-x) (Pc 0) \<oplus> P1) x (P2 \<oplus> Q2)))"
by pat_completeness auto
termination by (relation "measure (\<lambda>(x, y). size x + size y)") auto

function mul :: "'a::comm_ring pol \<Rightarrow> 'a pol \<Rightarrow> 'a pol"  (infixl "\<otimes>" 70)
where
  "Pc a \<otimes> Pc b = Pc (a * b)"
| "Pc c \<otimes> Pinj i P =
    (if c = 0 then Pc 0 else mkPinj i (P \<otimes> Pc c))"
| "Pinj i P \<otimes> Pc c =
    (if c = 0 then Pc 0 else mkPinj i (P \<otimes> Pc c))"
| "Pc c \<otimes> PX P i Q =
    (if c = 0 then Pc 0 else mkPX (P \<otimes> Pc c) i (Q \<otimes> Pc c))"
| "PX P i Q \<otimes> Pc c =
    (if c = 0 then Pc 0 else mkPX (P \<otimes> Pc c) i (Q \<otimes> Pc c))"
| "Pinj x P \<otimes> Pinj y Q =
    (if x = y then mkPinj x (P \<otimes> Q)
     else
       (if x > y then mkPinj y (Pinj (x-y) P \<otimes> Q)
        else mkPinj x (Pinj (y - x) Q \<otimes> P)))"
| "Pinj x P \<otimes> PX Q y R =
    (if x = 0 then P \<otimes> PX Q y R
     else
       (if x = 1 then mkPX (Pinj x P \<otimes> Q) y (R \<otimes> P)
        else mkPX (Pinj x P \<otimes> Q) y (R \<otimes> Pinj (x - 1) P)))"
| "PX P x R \<otimes> Pinj y Q =
    (if y = 0 then PX P x R \<otimes> Q
     else
       (if y = 1 then mkPX (Pinj y Q \<otimes> P) x (R \<otimes> Q)
        else mkPX (Pinj y Q \<otimes> P) x (R \<otimes> Pinj (y - 1) Q)))"
| "PX P1 x P2 \<otimes> PX Q1 y Q2 =
    mkPX (P1 \<otimes> Q1) (x + y) (P2 \<otimes> Q2) \<oplus>
      (mkPX (P1 \<otimes> mkPinj 1 Q2) x (Pc 0) \<oplus>
        (mkPX (Q1 \<otimes> mkPinj 1 P2) y (Pc 0)))"
by pat_completeness auto
termination by (relation "measure (\<lambda>(x, y). size x + size y)")
  (auto simp add: mkPinj_def split: pol.split)

text \<open>Negation\<close>
primrec neg :: "'a::comm_ring pol \<Rightarrow> 'a pol"
where
  "neg (Pc c) = Pc (-c)"
| "neg (Pinj i P) = Pinj i (neg P)"
| "neg (PX P x Q) = PX (neg P) x (neg Q)"

text \<open>Substraction\<close>
definition sub :: "'a::comm_ring pol \<Rightarrow> 'a pol \<Rightarrow> 'a pol"  (infixl "\<ominus>" 65)
  where "sub P Q = P \<oplus> neg Q"

text \<open>Square for Fast Exponentation\<close>
primrec sqr :: "'a::comm_ring_1 pol \<Rightarrow> 'a pol"
where
  "sqr (Pc c) = Pc (c * c)"
| "sqr (Pinj i P) = mkPinj i (sqr P)"
| "sqr (PX A x B) =
    mkPX (sqr A) (x + x) (sqr B) \<oplus> mkPX (Pc (1 + 1) \<otimes> A \<otimes> mkPinj 1 B) x (Pc 0)"

text \<open>Fast Exponentation\<close>

fun pow :: "nat \<Rightarrow> 'a::comm_ring_1 pol \<Rightarrow> 'a pol"
where
  pow_if [simp del]: "pow n P =
   (if n = 0 then Pc 1
    else if even n then pow (n div 2) (sqr P)
    else P \<otimes> pow (n div 2) (sqr P))"

lemma pow_simps [simp]:
  "pow 0 P = Pc 1"
  "pow (2 * n) P = pow n (sqr P)"
  "pow (Suc (2 * n)) P = P \<otimes> pow n (sqr P)"
  by (simp_all add: pow_if)

lemma even_pow: "even n \<Longrightarrow> pow n P = pow (n div 2) (sqr P)"
  by (erule evenE) simp

lemma odd_pow: "odd n \<Longrightarrow> pow n P = P \<otimes> pow (n div 2) (sqr P)"
  by (erule oddE) simp


text \<open>Normalization of polynomial expressions\<close>

primrec norm :: "'a::comm_ring_1 polex \<Rightarrow> 'a pol"
where
  "norm (Pol P) = P"
| "norm (Add P Q) = norm P \<oplus> norm Q"
| "norm (Sub P Q) = norm P \<ominus> norm Q"
| "norm (Mul P Q) = norm P \<otimes> norm Q"
| "norm (Pow P n) = pow n (norm P)"
| "norm (Neg P) = neg (norm P)"

text \<open>mkPinj preserve semantics\<close>
lemma mkPinj_ci: "Ipol l (mkPinj a B) = Ipol l (Pinj a B)"
  by (induct B) (auto simp add: mkPinj_def algebra_simps)

text \<open>mkPX preserves semantics\<close>
lemma mkPX_ci: "Ipol l (mkPX A b C) = Ipol l (PX A b C)"
  by (cases A) (auto simp add: mkPX_def mkPinj_ci power_add algebra_simps)

text \<open>Correctness theorems for the implemented operations\<close>

text \<open>Negation\<close>
lemma neg_ci: "Ipol l (neg P) = -(Ipol l P)"
  by (induct P arbitrary: l) auto

text \<open>Addition\<close>
lemma add_ci: "Ipol l (P \<oplus> Q) = Ipol l P + Ipol l Q"
proof (induct P Q arbitrary: l rule: add.induct)
  case (6 x P y Q)
  consider "x < y" | "x = y" | "x > y" by arith
  then
  show ?case
  proof cases
    case 1
    with 6 show ?thesis by (simp add: mkPinj_ci algebra_simps)
  next
    case 2
    with 6 show ?thesis by (simp add: mkPinj_ci)
  next
    case 3
    with 6 show ?thesis by (simp add: mkPinj_ci algebra_simps)
  qed
next
  case (7 x P Q y R)
  consider "x = 0" | "x = 1" | "x > 1" by arith
  then show ?case
  proof cases
    case 1
    with 7 show ?thesis by simp
  next
    case 2
    with 7 show ?thesis by (simp add: algebra_simps)
  next
    case 3
    from 7 show ?thesis by (cases x) simp_all
  qed
next
  case (8 P x R y Q)
  then show ?case by simp
next
  case (9 P1 x P2 Q1 y Q2)
  consider "x = y" | d where "d + x = y" | d where "d + y = x"
    by atomize_elim arith
  then show ?case
  proof cases
    case 1
    with 9 show ?thesis by (simp add: mkPX_ci algebra_simps)
  next
    case 2
    with 9 show ?thesis by (auto simp add: mkPX_ci power_add algebra_simps)
  next
    case 3
    with 9 show ?thesis by (auto simp add: power_add mkPX_ci algebra_simps)
  qed
qed (auto simp add: algebra_simps)

text \<open>Multiplication\<close>
lemma mul_ci: "Ipol l (P \<otimes> Q) = Ipol l P * Ipol l Q"
  by (induct P Q arbitrary: l rule: mul.induct)
    (simp_all add: mkPX_ci mkPinj_ci algebra_simps add_ci power_add)

text \<open>Substraction\<close>
lemma sub_ci: "Ipol l (P \<ominus> Q) = Ipol l P - Ipol l Q"
  by (simp add: add_ci neg_ci sub_def)

text \<open>Square\<close>
lemma sqr_ci: "Ipol ls (sqr P) = Ipol ls P * Ipol ls P"
  by (induct P arbitrary: ls)
    (simp_all add: add_ci mkPinj_ci mkPX_ci mul_ci algebra_simps power_add)

text \<open>Power\<close>
lemma pow_ci: "Ipol ls (pow n P) = Ipol ls P ^ n"
proof (induct n arbitrary: P rule: less_induct)
  case (less k)
  consider "k = 0" | "k > 0" by arith
  then
  show ?case
  proof cases
    case 1
    then show ?thesis by simp
  next
    case 2
    then have "k div 2 < k" by arith
    with less have *: "Ipol ls (pow (k div 2) (sqr P)) = Ipol ls (sqr P) ^ (k div 2)"
      by simp
    show ?thesis
    proof (cases "even k")
      case True
      with * show ?thesis
        by (simp add: even_pow sqr_ci power_mult_distrib power_add [symmetric]
          mult_2 [symmetric] even_two_times_div_two)
    next
      case False
      with * show ?thesis
        by (simp add: odd_pow mul_ci sqr_ci power_mult_distrib power_add [symmetric]
          mult_2 [symmetric] power_Suc [symmetric])
    qed
  qed
qed

text \<open>Normalization preserves semantics\<close>
lemma norm_ci: "Ipolex l Pe = Ipol l (norm Pe)"
  by (induct Pe) (simp_all add: add_ci sub_ci mul_ci neg_ci pow_ci)

text \<open>Reflection lemma: Key to the (incomplete) decision procedure\<close>
lemma norm_eq:
  assumes "norm P1 = norm P2"
  shows "Ipolex l P1 = Ipolex l P2"
proof -
  from assms have "Ipol l (norm P1) = Ipol l (norm P2)"
    by simp
  then show ?thesis
    by (simp only: norm_ci)
qed


ML_file "commutative_ring_tac.ML"

method_setup comm_ring = \<open>
  Scan.succeed (SIMPLE_METHOD' o Commutative_Ring_Tac.tac)
\<close> "reflective decision procedure for equalities over commutative rings"

end
