(*  Title:      HOL/ex/Cubic_Quartic.thy
    Author:     Amine Chaieb
*)

section \<open>The Cubic and Quartic Root Formulas\<close>

theory Cubic_Quartic
imports Complex_Main
begin

section \<open>The Cubic Formula\<close>

definition "ccbrt z = (SOME (w::complex). w^3 = z)"

lemma ccbrt: "(ccbrt z) ^ 3 = z"
proof -
  from rcis_Ex obtain r a where ra: "z = rcis r a"
    by blast
  let ?r' = "if r < 0 then - root 3 (-r) else root 3 r"
  let ?a' = "a/3"
  have "rcis ?r' ?a' ^ 3 = rcis r a"
    by (cases "r < 0") (simp_all add: DeMoivre2)
  then have *: "\<exists>w. w^3 = z"
    unfolding ra by blast
  from someI_ex [OF *] show ?thesis
    unfolding ccbrt_def by blast
qed


text \<open>The reduction to a simpler form:\<close>

lemma cubic_reduction:
  fixes a :: complex
  assumes
    "a \<noteq> 0 \<and> x = y - b / (3 * a) \<and>  p = (3* a * c - b^2) / (9 * a^2) \<and>
      q = (9 * a * b * c - 2 * b^3 - 27 * a^2 * d) / (54 * a^3)"
  shows "a * x^3 + b * x^2 + c * x + d = 0 \<longleftrightarrow> y^3 + 3 * p * y - 2 * q = 0"
proof -
  from assms have "3 * a \<noteq> 0" "9 * a^2 \<noteq> 0" "54 * a^3 \<noteq> 0" by auto
  then have *:
      "x = y - b / (3 * a) \<longleftrightarrow> (3*a) * x = (3*a) * y - b"
      "p = (3* a * c - b^2) / (9 * a^2) \<longleftrightarrow> (9 * a^2) * p = (3* a * c - b^2)"
      "q = (9 * a * b * c - 2 * b^3 - 27 * a^2 * d) / (54 * a^3) \<longleftrightarrow>
        (54 * a^3) * q = (9 * a * b * c - 2 * b^3 - 27 * a^2 * d)"
    by (simp_all add: field_simps)
  from assms [unfolded *] show ?thesis
    by algebra
qed


text \<open>The solutions of the special form:\<close>

lemma cubic_basic:
  fixes s :: complex
  assumes
    "s^2 = q^2 + p^3 \<and>
      s1^3 = (if p = 0 then 2 * q else q + s) \<and>
      s2 = -s1 * (1 + i * t) / 2 \<and>
      s3 = -s1 * (1 - i * t) / 2 \<and>
      i^2 + 1 = 0 \<and>
      t^2 = 3"
  shows
    "if p = 0
     then y^3 + 3 * p * y - 2 * q = 0 \<longleftrightarrow> y = s1 \<or> y = s2 \<or> y = s3
     else s1 \<noteq> 0 \<and>
      (y^3 + 3 * p * y - 2 * q = 0 \<longleftrightarrow> (y = s1 - p / s1 \<or> y = s2 - p / s2 \<or> y = s3 - p / s3))"
proof (cases "p = 0")
  case True
  with assms show ?thesis
    by (simp add: field_simps) algebra
next
  case False
  with assms have *: "s1 \<noteq> 0" by (simp add: field_simps) algebra
  with assms False have "s2 \<noteq> 0" "s3 \<noteq> 0"
    by (simp_all add: field_simps) algebra+
  with * have **:
      "y = s1 - p / s1 \<longleftrightarrow> s1 * y = s1^2 - p"
      "y = s2 - p / s2 \<longleftrightarrow> s2 * y = s2^2 - p"
      "y = s3 - p / s3 \<longleftrightarrow> s3 * y = s3^2 - p"
    by (simp_all add: field_simps power2_eq_square)
  from assms False show ?thesis
    unfolding ** by (simp add: field_simps) algebra
qed


text \<open>Explicit formula for the roots:\<close>

lemma cubic:
  assumes a0: "a \<noteq> 0"
  shows
    "let
      p = (3 * a * c - b^2) / (9 * a^2);
      q = (9 * a * b * c - 2 * b^3 - 27 * a^2 * d) / (54 * a^3);
      s = csqrt(q^2 + p^3);
      s1 = (if p = 0 then ccbrt(2 * q) else ccbrt(q + s));
      s2 = -s1 * (1 + \<i> * csqrt 3) / 2;
      s3 = -s1 * (1 - \<i> * csqrt 3) / 2
     in
      if p = 0 then
        a * x^3 + b * x^2 + c * x + d = 0 \<longleftrightarrow>
          x = s1 - b / (3 * a) \<or>
          x = s2 - b / (3 * a) \<or>
          x = s3 - b / (3 * a)
      else
        s1 \<noteq> 0 \<and>
          (a * x^3 + b * x^2 + c * x + d = 0 \<longleftrightarrow>
            x = s1 - p / s1 - b / (3 * a) \<or>
            x = s2 - p / s2 - b / (3 * a) \<or>
            x = s3 - p / s3 - b / (3 * a))"
proof -
  let ?p = "(3 * a * c - b^2) / (9 * a^2)"
  let ?q = "(9 * a * b * c - 2 * b^3 - 27 * a^2 * d) / (54 * a^3)"
  let ?s = "csqrt (?q^2 + ?p^3)"
  let ?s1 = "if ?p = 0 then ccbrt(2 * ?q) else ccbrt(?q + ?s)"
  let ?s2 = "- ?s1 * (1 + \<i> * csqrt 3) / 2"
  let ?s3 = "- ?s1 * (1 - \<i> * csqrt 3) / 2"
  let ?y = "x + b / (3 * a)"
  from a0 have zero: "9 * a^2 \<noteq> 0" "a^3 * 54 \<noteq> 0" "(a * 3) \<noteq> 0"
    by auto
  have eq: "a * x^3 + b * x^2 + c * x + d = 0 \<longleftrightarrow> ?y^3 + 3 * ?p * ?y - 2 * ?q = 0"
    by (rule cubic_reduction) (auto simp add: field_simps zero a0)
  have "csqrt 3^2 = 3" by (rule power2_csqrt)
  then have th0:
    "?s^2 = ?q^2 + ?p ^ 3 \<and> ?s1^ 3 = (if ?p = 0 then 2 * ?q else ?q + ?s) \<and>
      ?s2 = - ?s1 * (1 + \<i> * csqrt 3) / 2 \<and>
      ?s3 = - ?s1 * (1 - \<i> * csqrt 3) / 2 \<and>
      \<i>^2 + 1 = 0 \<and> csqrt 3^2 = 3"
    using zero by (simp add: field_simps ccbrt)
  from cubic_basic[OF th0, of ?y]
  show ?thesis
    apply (simp only: Let_def eq)
    using zero apply (simp add: field_simps ccbrt)
    using zero
    apply (cases "a * (c * 3) = b^2")
    apply (simp_all add: field_simps)
    done
qed


section \<open>The Quartic Formula\<close>

lemma quartic:
  "(y::real)^3 - b * y^2 + (a * c - 4 * d) * y - a^2 * d + 4 * b * d - c^2 = 0 \<and>
    R^2 = a^2 / 4 - b + y \<and>
    s^2 = y^2 - 4 * d \<and>
    (D^2 = (if R = 0 then 3 * a^2 / 4 - 2 * b + 2 * s
                     else 3 * a^2 / 4 - R^2 - 2 * b + (4 * a * b - 8 * c - a^3) / (4 * R))) \<and>
    (E^2 = (if R = 0 then 3 * a^2 / 4 - 2 * b - 2 * s
                     else 3 * a^2 / 4 - R^2 - 2 * b - (4 * a * b - 8 * c - a^3) / (4 * R)))
  \<Longrightarrow> x^4 + a * x^3 + b * x^2 + c * x + d = 0 \<longleftrightarrow>
      x = -a / 4 + R / 2 + D / 2 \<or>
      x = -a / 4 + R / 2 - D / 2 \<or>
      x = -a / 4 - R / 2 + E / 2 \<or>
      x = -a / 4 - R / 2 - E / 2"
  apply (cases "R = 0")
   apply (simp_all add: field_simps divide_minus_left[symmetric] del: divide_minus_left)
   apply algebra
  apply algebra
  done

end
