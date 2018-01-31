(*  Title:      HOL/ex/Dedekind_Real.thy
    Author:     Jacques D. Fleuriot, University of Cambridge
    Conversion to Isar and new proofs by Lawrence C Paulson, 2003/4

The positive reals as Dedekind sections of positive
rationals. Fundamentals of Abstract Analysis [Gleason- p. 121]
provides some of the definitions.
*)

theory Dedekind_Real
imports Complex_Main
begin

section \<open>Positive real numbers\<close>

text\<open>Could be generalized and moved to \<open>Groups\<close>\<close>
lemma add_eq_exists: "\<exists>x. a+x = (b::rat)"
by (rule_tac x="b-a" in exI, simp)

definition
  cut :: "rat set => bool" where
  "cut A = ({} \<subset> A &
            A < {r. 0 < r} &
            (\<forall>y \<in> A. ((\<forall>z. 0<z & z < y --> z \<in> A) & (\<exists>u \<in> A. y < u))))"

lemma interval_empty_iff:
  "{y. (x::'a::unbounded_dense_linorder) < y \<and> y < z} = {} \<longleftrightarrow> \<not> x < z"
  by (auto dest: dense)


lemma cut_of_rat: 
  assumes q: "0 < q" shows "cut {r::rat. 0 < r & r < q}" (is "cut ?A")
proof -
  from q have pos: "?A < {r. 0 < r}" by force
  have nonempty: "{} \<subset> ?A"
  proof
    show "{} \<subseteq> ?A" by simp
    show "{} \<noteq> ?A"
      by (force simp only: q eq_commute [of "{}"] interval_empty_iff)
  qed
  show ?thesis
    by (simp add: cut_def pos nonempty,
        blast dest: dense intro: order_less_trans)
qed


typedef preal = "Collect cut"
  by (blast intro: cut_of_rat [OF zero_less_one])

lemma Abs_preal_induct [induct type: preal]:
  "(\<And>x. cut x \<Longrightarrow> P (Abs_preal x)) \<Longrightarrow> P x"
  using Abs_preal_induct [of P x] by simp

lemma Rep_preal:
  "cut (Rep_preal x)"
  using Rep_preal [of x] by simp

definition
  psup :: "preal set => preal" where
  "psup P = Abs_preal (\<Union>X \<in> P. Rep_preal X)"

definition
  add_set :: "[rat set,rat set] => rat set" where
  "add_set A B = {w. \<exists>x \<in> A. \<exists>y \<in> B. w = x + y}"

definition
  diff_set :: "[rat set,rat set] => rat set" where
  "diff_set A B = {w. \<exists>x. 0 < w & 0 < x & x \<notin> B & x + w \<in> A}"

definition
  mult_set :: "[rat set,rat set] => rat set" where
  "mult_set A B = {w. \<exists>x \<in> A. \<exists>y \<in> B. w = x * y}"

definition
  inverse_set :: "rat set => rat set" where
  "inverse_set A = {x. \<exists>y. 0 < x & x < y & inverse y \<notin> A}"

instantiation preal :: "{ord, plus, minus, times, inverse, one}"
begin

definition
  preal_less_def:
    "R < S == Rep_preal R < Rep_preal S"

definition
  preal_le_def:
    "R \<le> S == Rep_preal R \<subseteq> Rep_preal S"

definition
  preal_add_def:
    "R + S == Abs_preal (add_set (Rep_preal R) (Rep_preal S))"

definition
  preal_diff_def:
    "R - S == Abs_preal (diff_set (Rep_preal R) (Rep_preal S))"

definition
  preal_mult_def:
    "R * S == Abs_preal (mult_set (Rep_preal R) (Rep_preal S))"

definition
  preal_inverse_def:
    "inverse R == Abs_preal (inverse_set (Rep_preal R))"

definition "R div S = R * inverse (S::preal)"

definition
  preal_one_def:
    "1 == Abs_preal {x. 0 < x & x < 1}"

instance ..

end


text\<open>Reduces equality on abstractions to equality on representatives\<close>
declare Abs_preal_inject [simp]
declare Abs_preal_inverse [simp]

lemma rat_mem_preal: "0 < q ==> cut {r::rat. 0 < r & r < q}"
by (simp add: cut_of_rat)

lemma preal_nonempty: "cut A ==> \<exists>x\<in>A. 0 < x"
  unfolding cut_def [abs_def] by blast

lemma preal_Ex_mem: "cut A \<Longrightarrow> \<exists>x. x \<in> A"
  apply (drule preal_nonempty)
  apply fast
  done

lemma preal_imp_psubset_positives: "cut A ==> A < {r. 0 < r}"
  by (force simp add: cut_def)

lemma preal_exists_bound: "cut A ==> \<exists>x. 0 < x & x \<notin> A"
  apply (drule preal_imp_psubset_positives)
  apply auto
  done

lemma preal_exists_greater: "[| cut A; y \<in> A |] ==> \<exists>u \<in> A. y < u"
  unfolding cut_def [abs_def] by blast

lemma preal_downwards_closed: "[| cut A; y \<in> A; 0 < z; z < y |] ==> z \<in> A"
  unfolding cut_def [abs_def] by blast

text\<open>Relaxing the final premise\<close>
lemma preal_downwards_closed':
     "[| cut A; y \<in> A; 0 < z; z \<le> y |] ==> z \<in> A"
apply (simp add: order_le_less)
apply (blast intro: preal_downwards_closed)
done

text\<open>A positive fraction not in a positive real is an upper bound.
 Gleason p. 122 - Remark (1)\<close>

lemma not_in_preal_ub:
  assumes A: "cut A"
    and notx: "x \<notin> A"
    and y: "y \<in> A"
    and pos: "0 < x"
  shows "y < x"
proof (cases rule: linorder_cases)
  assume "x<y"
  with notx show ?thesis
    by (simp add:  preal_downwards_closed [OF A y] pos)
next
  assume "x=y"
  with notx and y show ?thesis by simp
next
  assume "y<x"
  thus ?thesis .
qed

text \<open>preal lemmas instantiated to @{term "Rep_preal X"}\<close>

lemma mem_Rep_preal_Ex: "\<exists>x. x \<in> Rep_preal X"
thm preal_Ex_mem
by (rule preal_Ex_mem [OF Rep_preal])

lemma Rep_preal_exists_bound: "\<exists>x>0. x \<notin> Rep_preal X"
by (rule preal_exists_bound [OF Rep_preal])

lemmas not_in_Rep_preal_ub = not_in_preal_ub [OF Rep_preal]


subsection\<open>Properties of Ordering\<close>

instance preal :: order
proof
  fix w :: preal
  show "w \<le> w" by (simp add: preal_le_def)
next
  fix i j k :: preal
  assume "i \<le> j" and "j \<le> k"
  then show "i \<le> k" by (simp add: preal_le_def)
next
  fix z w :: preal
  assume "z \<le> w" and "w \<le> z"
  then show "z = w" by (simp add: preal_le_def Rep_preal_inject)
next
  fix z w :: preal
  show "z < w \<longleftrightarrow> z \<le> w \<and> \<not> w \<le> z"
  by (auto simp add: preal_le_def preal_less_def Rep_preal_inject)
qed  

lemma preal_imp_pos: "[|cut A; r \<in> A|] ==> 0 < r"
by (insert preal_imp_psubset_positives, blast)

instance preal :: linorder
proof
  fix x y :: preal
  show "x <= y | y <= x"
    apply (auto simp add: preal_le_def)
    apply (rule ccontr)
    apply (blast dest: not_in_Rep_preal_ub intro: preal_imp_pos [OF Rep_preal]
             elim: order_less_asym)
    done
qed

instantiation preal :: distrib_lattice
begin

definition
  "(inf :: preal \<Rightarrow> preal \<Rightarrow> preal) = min"

definition
  "(sup :: preal \<Rightarrow> preal \<Rightarrow> preal) = max"

instance
  by intro_classes
    (auto simp add: inf_preal_def sup_preal_def max_min_distrib2)

end

subsection\<open>Properties of Addition\<close>

lemma preal_add_commute: "(x::preal) + y = y + x"
apply (unfold preal_add_def add_set_def)
apply (rule_tac f = Abs_preal in arg_cong)
apply (force simp add: add.commute)
done

text\<open>Lemmas for proving that addition of two positive reals gives
 a positive real\<close>

text\<open>Part 1 of Dedekind sections definition\<close>
lemma add_set_not_empty:
     "[|cut A; cut B|] ==> {} \<subset> add_set A B"
apply (drule preal_nonempty)+
apply (auto simp add: add_set_def)
done

text\<open>Part 2 of Dedekind sections definition.  A structured version of
this proof is \<open>preal_not_mem_mult_set_Ex\<close> below.\<close>
lemma preal_not_mem_add_set_Ex:
     "[|cut A; cut B|] ==> \<exists>q>0. q \<notin> add_set A B"
apply (insert preal_exists_bound [of A] preal_exists_bound [of B], auto) 
apply (rule_tac x = "x+xa" in exI)
apply (simp add: add_set_def, clarify)
apply (drule (3) not_in_preal_ub)+
apply (force dest: add_strict_mono)
done

lemma add_set_not_rat_set:
   assumes A: "cut A" 
       and B: "cut B"
     shows "add_set A B < {r. 0 < r}"
proof
  from preal_imp_pos [OF A] preal_imp_pos [OF B]
  show "add_set A B \<subseteq> {r. 0 < r}" by (force simp add: add_set_def) 
next
  show "add_set A B \<noteq> {r. 0 < r}"
    by (insert preal_not_mem_add_set_Ex [OF A B], blast) 
qed

text\<open>Part 3 of Dedekind sections definition\<close>
lemma add_set_lemma3:
     "[|cut A; cut B; u \<in> add_set A B; 0 < z; z < u|] 
      ==> z \<in> add_set A B"
proof (unfold add_set_def, clarify)
  fix x::rat and y::rat
  assume A: "cut A" 
    and B: "cut B"
    and [simp]: "0 < z"
    and zless: "z < x + y"
    and x:  "x \<in> A"
    and y:  "y \<in> B"
  have xpos [simp]: "0<x" by (rule preal_imp_pos [OF A x])
  have ypos [simp]: "0<y" by (rule preal_imp_pos [OF B y])
  have xypos [simp]: "0 < x+y" by (simp add: pos_add_strict)
  let ?f = "z/(x+y)"
  have fless: "?f < 1" by (simp add: zless pos_divide_less_eq)
  show "\<exists>x' \<in> A. \<exists>y'\<in>B. z = x' + y'"
  proof (intro bexI)
    show "z = x*?f + y*?f"
      by (simp add: distrib_right [symmetric] divide_inverse ac_simps
          order_less_imp_not_eq2)
  next
    show "y * ?f \<in> B"
    proof (rule preal_downwards_closed [OF B y])
      show "0 < y * ?f"
        by (simp add: divide_inverse zero_less_mult_iff)
    next
      show "y * ?f < y"
        by (insert mult_strict_left_mono [OF fless ypos], simp)
    qed
  next
    show "x * ?f \<in> A"
    proof (rule preal_downwards_closed [OF A x])
      show "0 < x * ?f"
        by (simp add: divide_inverse zero_less_mult_iff)
    next
      show "x * ?f < x"
        by (insert mult_strict_left_mono [OF fless xpos], simp)
    qed
  qed
qed

text\<open>Part 4 of Dedekind sections definition\<close>
lemma add_set_lemma4:
     "[|cut A; cut B; y \<in> add_set A B|] ==> \<exists>u \<in> add_set A B. y < u"
apply (auto simp add: add_set_def)
apply (frule preal_exists_greater [of A], auto) 
apply (rule_tac x="u + ya" in exI)
apply (auto intro: add_strict_left_mono)
done

lemma mem_add_set:
     "[|cut A; cut B|] ==> cut (add_set A B)"
apply (simp (no_asm_simp) add: cut_def)
apply (blast intro!: add_set_not_empty add_set_not_rat_set
                     add_set_lemma3 add_set_lemma4)
done

lemma preal_add_assoc: "((x::preal) + y) + z = x + (y + z)"
apply (simp add: preal_add_def mem_add_set Rep_preal)
apply (force simp add: add_set_def ac_simps)
done

instance preal :: ab_semigroup_add
proof
  fix a b c :: preal
  show "(a + b) + c = a + (b + c)" by (rule preal_add_assoc)
  show "a + b = b + a" by (rule preal_add_commute)
qed


subsection\<open>Properties of Multiplication\<close>

text\<open>Proofs essentially same as for addition\<close>

lemma preal_mult_commute: "(x::preal) * y = y * x"
apply (unfold preal_mult_def mult_set_def)
apply (rule_tac f = Abs_preal in arg_cong)
apply (force simp add: mult.commute)
done

text\<open>Multiplication of two positive reals gives a positive real.\<close>

text\<open>Lemmas for proving positive reals multiplication set in @{typ preal}\<close>

text\<open>Part 1 of Dedekind sections definition\<close>
lemma mult_set_not_empty:
     "[|cut A; cut B|] ==> {} \<subset> mult_set A B"
apply (insert preal_nonempty [of A] preal_nonempty [of B]) 
apply (auto simp add: mult_set_def)
done

text\<open>Part 2 of Dedekind sections definition\<close>
lemma preal_not_mem_mult_set_Ex:
  assumes A: "cut A" 
    and B: "cut B"
  shows "\<exists>q. 0 < q & q \<notin> mult_set A B"
proof -
  from preal_exists_bound [OF A] obtain x where 1 [simp]: "0 < x" "x \<notin> A" by blast
  from preal_exists_bound [OF B] obtain y where 2 [simp]: "0 < y" "y \<notin> B" by blast
  show ?thesis
  proof (intro exI conjI)
    show "0 < x*y" by simp
    show "x * y \<notin> mult_set A B"
    proof -
      {
        fix u::rat and v::rat
        assume u: "u \<in> A" and v: "v \<in> B" and xy: "x*y = u*v"
        moreover from A B 1 2 u v have "u<x" and "v<y" by (blast dest: not_in_preal_ub)+
        moreover
        from A B 1 2 u v have "0\<le>v"
          by (blast intro: preal_imp_pos [OF B] order_less_imp_le)
        moreover
        from A B 1 \<open>u < x\<close> \<open>v < y\<close> \<open>0 \<le> v\<close>
        have "u*v < x*y" by (blast intro: mult_strict_mono)
        ultimately have False by force
      }
      thus ?thesis by (auto simp add: mult_set_def)
    qed
  qed
qed

lemma mult_set_not_rat_set:
  assumes A: "cut A" 
    and B: "cut B"
  shows "mult_set A B < {r. 0 < r}"
proof
  show "mult_set A B \<subseteq> {r. 0 < r}"
    by (force simp add: mult_set_def
      intro: preal_imp_pos [OF A] preal_imp_pos [OF B] mult_pos_pos)
  show "mult_set A B \<noteq> {r. 0 < r}"
    using preal_not_mem_mult_set_Ex [OF A B] by blast
qed



text\<open>Part 3 of Dedekind sections definition\<close>
lemma mult_set_lemma3:
     "[|cut A; cut B; u \<in> mult_set A B; 0 < z; z < u|] 
      ==> z \<in> mult_set A B"
proof (unfold mult_set_def, clarify)
  fix x::rat and y::rat
  assume A: "cut A" 
    and B: "cut B"
    and [simp]: "0 < z"
    and zless: "z < x * y"
    and x:  "x \<in> A"
    and y:  "y \<in> B"
  have [simp]: "0<y" by (rule preal_imp_pos [OF B y])
  show "\<exists>x' \<in> A. \<exists>y' \<in> B. z = x' * y'"
  proof
    show "\<exists>y'\<in>B. z = (z/y) * y'"
    proof
      show "z = (z/y)*y"
        by (simp add: divide_inverse mult.commute [of y] mult.assoc
                      order_less_imp_not_eq2)
      show "y \<in> B" by fact
    qed
  next
    show "z/y \<in> A"
    proof (rule preal_downwards_closed [OF A x])
      show "0 < z/y"
        by (simp add: zero_less_divide_iff)
      show "z/y < x" by (simp add: pos_divide_less_eq zless)
    qed
  qed
qed

text\<open>Part 4 of Dedekind sections definition\<close>
lemma mult_set_lemma4:
     "[|cut A; cut B; y \<in> mult_set A B|] ==> \<exists>u \<in> mult_set A B. y < u"
apply (auto simp add: mult_set_def)
apply (frule preal_exists_greater [of A], auto) 
apply (rule_tac x="u * ya" in exI)
apply (auto intro: preal_imp_pos [of A] preal_imp_pos [of B] 
                   mult_strict_right_mono)
done


lemma mem_mult_set:
     "[|cut A; cut B|] ==> cut (mult_set A B)"
apply (simp (no_asm_simp) add: cut_def)
apply (blast intro!: mult_set_not_empty mult_set_not_rat_set
                     mult_set_lemma3 mult_set_lemma4)
done

lemma preal_mult_assoc: "((x::preal) * y) * z = x * (y * z)"
apply (simp add: preal_mult_def mem_mult_set Rep_preal)
apply (force simp add: mult_set_def ac_simps)
done

instance preal :: ab_semigroup_mult
proof
  fix a b c :: preal
  show "(a * b) * c = a * (b * c)" by (rule preal_mult_assoc)
  show "a * b = b * a" by (rule preal_mult_commute)
qed


text\<open>Positive real 1 is the multiplicative identity element\<close>

lemma preal_mult_1: "(1::preal) * z = z"
proof (induct z)
  fix A :: "rat set"
  assume A: "cut A"
  have "{w. \<exists>u. 0 < u \<and> u < 1 & (\<exists>v \<in> A. w = u * v)} = A" (is "?lhs = A")
  proof
    show "?lhs \<subseteq> A"
    proof clarify
      fix x::rat and u::rat and v::rat
      assume upos: "0<u" and "u<1" and v: "v \<in> A"
      have vpos: "0<v" by (rule preal_imp_pos [OF A v])
      hence "u*v < 1*v" by (simp only: mult_strict_right_mono upos \<open>u < 1\<close> v)
      thus "u * v \<in> A"
        by (force intro: preal_downwards_closed [OF A v] mult_pos_pos 
          upos vpos)
    qed
  next
    show "A \<subseteq> ?lhs"
    proof clarify
      fix x::rat
      assume x: "x \<in> A"
      have xpos: "0<x" by (rule preal_imp_pos [OF A x])
      from preal_exists_greater [OF A x]
      obtain v where v: "v \<in> A" and xlessv: "x < v" ..
      have vpos: "0<v" by (rule preal_imp_pos [OF A v])
      show "\<exists>u. 0 < u \<and> u < 1 \<and> (\<exists>v\<in>A. x = u * v)"
      proof (intro exI conjI)
        show "0 < x/v"
          by (simp add: zero_less_divide_iff xpos vpos)
        show "x / v < 1"
          by (simp add: pos_divide_less_eq vpos xlessv)
        show "\<exists>v'\<in>A. x = (x / v) * v'"
        proof
          show "x = (x/v)*v"
            by (simp add: divide_inverse mult.assoc vpos
                          order_less_imp_not_eq2)
          show "v \<in> A" by fact
        qed
      qed
    qed
  qed
  thus "1 * Abs_preal A = Abs_preal A"
    by (simp add: preal_one_def preal_mult_def mult_set_def 
                  rat_mem_preal A)
qed

instance preal :: comm_monoid_mult
by intro_classes (rule preal_mult_1)


subsection\<open>Distribution of Multiplication across Addition\<close>

lemma mem_Rep_preal_add_iff:
      "(z \<in> Rep_preal(R+S)) = (\<exists>x \<in> Rep_preal R. \<exists>y \<in> Rep_preal S. z = x + y)"
apply (simp add: preal_add_def mem_add_set Rep_preal)
apply (simp add: add_set_def) 
done

lemma mem_Rep_preal_mult_iff:
      "(z \<in> Rep_preal(R*S)) = (\<exists>x \<in> Rep_preal R. \<exists>y \<in> Rep_preal S. z = x * y)"
apply (simp add: preal_mult_def mem_mult_set Rep_preal)
apply (simp add: mult_set_def) 
done

lemma distrib_subset1:
     "Rep_preal (w * (x + y)) \<subseteq> Rep_preal (w * x + w * y)"
apply (auto simp add: Bex_def mem_Rep_preal_add_iff mem_Rep_preal_mult_iff)
apply (force simp add: distrib_left)
done

lemma preal_add_mult_distrib_mean:
  assumes a: "a \<in> Rep_preal w"
    and b: "b \<in> Rep_preal w"
    and d: "d \<in> Rep_preal x"
    and e: "e \<in> Rep_preal y"
  shows "\<exists>c \<in> Rep_preal w. a * d + b * e = c * (d + e)"
proof
  let ?c = "(a*d + b*e)/(d+e)"
  have [simp]: "0<a" "0<b" "0<d" "0<e" "0<d+e"
    by (blast intro: preal_imp_pos [OF Rep_preal] a b d e pos_add_strict)+
  have cpos: "0 < ?c"
    by (simp add: zero_less_divide_iff zero_less_mult_iff pos_add_strict)
  show "a * d + b * e = ?c * (d + e)"
    by (simp add: divide_inverse mult.assoc order_less_imp_not_eq2)
  show "?c \<in> Rep_preal w"
  proof (cases rule: linorder_le_cases)
    assume "a \<le> b"
    hence "?c \<le> b"
      by (simp add: pos_divide_le_eq distrib_left mult_right_mono
                    order_less_imp_le)
    thus ?thesis by (rule preal_downwards_closed' [OF Rep_preal b cpos])
  next
    assume "b \<le> a"
    hence "?c \<le> a"
      by (simp add: pos_divide_le_eq distrib_left mult_right_mono
                    order_less_imp_le)
    thus ?thesis by (rule preal_downwards_closed' [OF Rep_preal a cpos])
  qed
qed

lemma distrib_subset2:
     "Rep_preal (w * x + w * y) \<subseteq> Rep_preal (w * (x + y))"
apply (auto simp add: Bex_def mem_Rep_preal_add_iff mem_Rep_preal_mult_iff)
apply (drule_tac w=w and x=x and y=y in preal_add_mult_distrib_mean, auto)
done

lemma preal_add_mult_distrib2: "(w * ((x::preal) + y)) = (w * x) + (w * y)"
apply (rule Rep_preal_inject [THEN iffD1])
apply (rule equalityI [OF distrib_subset1 distrib_subset2])
done

lemma preal_add_mult_distrib: "(((x::preal) + y) * w) = (x * w) + (y * w)"
by (simp add: preal_mult_commute preal_add_mult_distrib2)

instance preal :: comm_semiring
by intro_classes (rule preal_add_mult_distrib)


subsection\<open>Existence of Inverse, a Positive Real\<close>

lemma mem_inv_set_ex:
  assumes A: "cut A" shows "\<exists>x y. 0 < x & x < y & inverse y \<notin> A"
proof -
  from preal_exists_bound [OF A]
  obtain x where [simp]: "0<x" "x \<notin> A" by blast
  show ?thesis
  proof (intro exI conjI)
    show "0 < inverse (x+1)"
      by (simp add: order_less_trans [OF _ less_add_one]) 
    show "inverse(x+1) < inverse x"
      by (simp add: less_imp_inverse_less less_add_one)
    show "inverse (inverse x) \<notin> A"
      by (simp add: order_less_imp_not_eq2)
  qed
qed

text\<open>Part 1 of Dedekind sections definition\<close>
lemma inverse_set_not_empty:
     "cut A ==> {} \<subset> inverse_set A"
apply (insert mem_inv_set_ex [of A])
apply (auto simp add: inverse_set_def)
done

text\<open>Part 2 of Dedekind sections definition\<close>

lemma preal_not_mem_inverse_set_Ex:
   assumes A: "cut A"  shows "\<exists>q. 0 < q & q \<notin> inverse_set A"
proof -
  from preal_nonempty [OF A]
  obtain x where x: "x \<in> A" and  xpos [simp]: "0<x" ..
  show ?thesis
  proof (intro exI conjI)
    show "0 < inverse x" by simp
    show "inverse x \<notin> inverse_set A"
    proof -
      { fix y::rat 
        assume ygt: "inverse x < y"
        have [simp]: "0 < y" by (simp add: order_less_trans [OF _ ygt])
        have iyless: "inverse y < x" 
          by (simp add: inverse_less_imp_less [of x] ygt)
        have "inverse y \<in> A"
          by (simp add: preal_downwards_closed [OF A x] iyless)}
     thus ?thesis by (auto simp add: inverse_set_def)
    qed
  qed
qed

lemma inverse_set_not_rat_set:
   assumes A: "cut A"  shows "inverse_set A < {r. 0 < r}"
proof
  show "inverse_set A \<subseteq> {r. 0 < r}"  by (force simp add: inverse_set_def)
next
  show "inverse_set A \<noteq> {r. 0 < r}"
    by (insert preal_not_mem_inverse_set_Ex [OF A], blast)
qed

text\<open>Part 3 of Dedekind sections definition\<close>
lemma inverse_set_lemma3:
     "[|cut A; u \<in> inverse_set A; 0 < z; z < u|] 
      ==> z \<in> inverse_set A"
apply (auto simp add: inverse_set_def)
apply (auto intro: order_less_trans)
done

text\<open>Part 4 of Dedekind sections definition\<close>
lemma inverse_set_lemma4:
     "[|cut A; y \<in> inverse_set A|] ==> \<exists>u \<in> inverse_set A. y < u"
apply (auto simp add: inverse_set_def)
apply (drule dense [of y]) 
apply (blast intro: order_less_trans)
done


lemma mem_inverse_set:
     "cut A ==> cut (inverse_set A)"
apply (simp (no_asm_simp) add: cut_def)
apply (blast intro!: inverse_set_not_empty inverse_set_not_rat_set
                     inverse_set_lemma3 inverse_set_lemma4)
done


subsection\<open>Gleason's Lemma 9-3.4, page 122\<close>

lemma Gleason9_34_exists:
  assumes A: "cut A"
    and "\<forall>x\<in>A. x + u \<in> A"
    and "0 \<le> z"
  shows "\<exists>b\<in>A. b + (of_int z) * u \<in> A"
proof (cases z rule: int_cases)
  case (nonneg n)
  show ?thesis
  proof (simp add: nonneg, induct n)
    case 0
    from preal_nonempty [OF A]
    show ?case  by force 
  next
    case (Suc k)
    then obtain b where b: "b \<in> A" "b + of_nat k * u \<in> A" ..
    hence "b + of_int (int k)*u + u \<in> A" by (simp add: assms)
    thus ?case by (force simp add: algebra_simps b)
  qed
next
  case (neg n)
  with assms show ?thesis by simp
qed

lemma Gleason9_34_contra:
  assumes A: "cut A"
    shows "[|\<forall>x\<in>A. x + u \<in> A; 0 < u; 0 < y; y \<notin> A|] ==> False"
proof (induct u, induct y)
  fix a::int and b::int
  fix c::int and d::int
  assume bpos [simp]: "0 < b"
    and dpos [simp]: "0 < d"
    and closed: "\<forall>x\<in>A. x + (Fract c d) \<in> A"
    and upos: "0 < Fract c d"
    and ypos: "0 < Fract a b"
    and notin: "Fract a b \<notin> A"
  have cpos [simp]: "0 < c" 
    by (simp add: zero_less_Fract_iff [OF dpos, symmetric] upos) 
  have apos [simp]: "0 < a" 
    by (simp add: zero_less_Fract_iff [OF bpos, symmetric] ypos) 
  let ?k = "a*d"
  have frle: "Fract a b \<le> Fract ?k 1 * (Fract c d)" 
  proof -
    have "?thesis = ((a * d * b * d) \<le> c * b * (a * d * b * d))"
      by (simp add: order_less_imp_not_eq2 ac_simps) 
    moreover
    have "(1 * (a * d * b * d)) \<le> c * b * (a * d * b * d)"
      by (rule mult_mono, 
          simp_all add: int_one_le_iff_zero_less zero_less_mult_iff 
                        order_less_imp_le)
    ultimately
    show ?thesis by simp
  qed
  have k: "0 \<le> ?k" by (simp add: order_less_imp_le zero_less_mult_iff)  
  from Gleason9_34_exists [OF A closed k]
  obtain z where z: "z \<in> A" 
             and mem: "z + of_int ?k * Fract c d \<in> A" ..
  have less: "z + of_int ?k * Fract c d < Fract a b"
    by (rule not_in_preal_ub [OF A notin mem ypos])
  have "0<z" by (rule preal_imp_pos [OF A z])
  with frle and less show False by (simp add: Fract_of_int_eq) 
qed


lemma Gleason9_34:
  assumes A: "cut A"
    and upos: "0 < u"
  shows "\<exists>r \<in> A. r + u \<notin> A"
proof (rule ccontr, simp)
  assume closed: "\<forall>r\<in>A. r + u \<in> A"
  from preal_exists_bound [OF A]
  obtain y where y: "y \<notin> A" and ypos: "0 < y" by blast
  show False
    by (rule Gleason9_34_contra [OF A closed upos ypos y])
qed



subsection\<open>Gleason's Lemma 9-3.6\<close>

lemma lemma_gleason9_36:
  assumes A: "cut A"
    and x: "1 < x"
  shows "\<exists>r \<in> A. r*x \<notin> A"
proof -
  from preal_nonempty [OF A]
  obtain y where y: "y \<in> A" and  ypos: "0<y" ..
  show ?thesis 
  proof (rule classical)
    assume "~(\<exists>r\<in>A. r * x \<notin> A)"
    with y have ymem: "y * x \<in> A" by blast 
    from ypos mult_strict_left_mono [OF x]
    have yless: "y < y*x" by simp 
    let ?d = "y*x - y"
    from yless have dpos: "0 < ?d" and eq: "y + ?d = y*x" by auto
    from Gleason9_34 [OF A dpos]
    obtain r where r: "r\<in>A" and notin: "r + ?d \<notin> A" ..
    have rpos: "0<r" by (rule preal_imp_pos [OF A r])
    with dpos have rdpos: "0 < r + ?d" by arith
    have "~ (r + ?d \<le> y + ?d)"
    proof
      assume le: "r + ?d \<le> y + ?d" 
      from ymem have yd: "y + ?d \<in> A" by (simp add: eq)
      have "r + ?d \<in> A" by (rule preal_downwards_closed' [OF A yd rdpos le])
      with notin show False by simp
    qed
    hence "y < r" by simp
    with ypos have  dless: "?d < (r * ?d)/y"
      using dpos less_divide_eq_1 by fastforce
    have "r + ?d < r*x"
    proof -
      have "r + ?d < r + (r * ?d)/y" by (simp add: dless)
      also from ypos have "... = (r/y) * (y + ?d)"
        by (simp only: algebra_simps divide_inverse, simp)
      also have "... = r*x" using ypos
        by simp
      finally show "r + ?d < r*x" .
    qed
    with r notin rdpos
    show "\<exists>r\<in>A. r * x \<notin> A" by (blast dest:  preal_downwards_closed [OF A])
  qed  
qed

subsection\<open>Existence of Inverse: Part 2\<close>

lemma mem_Rep_preal_inverse_iff:
      "(z \<in> Rep_preal(inverse R)) = 
       (0 < z \<and> (\<exists>y. z < y \<and> inverse y \<notin> Rep_preal R))"
apply (simp add: preal_inverse_def mem_inverse_set Rep_preal)
apply (simp add: inverse_set_def) 
done

lemma Rep_preal_one:
     "Rep_preal 1 = {x. 0 < x \<and> x < 1}"
by (simp add: preal_one_def rat_mem_preal)

lemma subset_inverse_mult_lemma:
  assumes xpos: "0 < x" and xless: "x < 1"
  shows "\<exists>r u y. 0 < r & r < y & inverse y \<notin> Rep_preal R & 
    u \<in> Rep_preal R & x = r * u"
proof -
  from xpos and xless have "1 < inverse x" by (simp add: one_less_inverse_iff)
  from lemma_gleason9_36 [OF Rep_preal this]
  obtain r where r: "r \<in> Rep_preal R" 
             and notin: "r * (inverse x) \<notin> Rep_preal R" ..
  have rpos: "0<r" by (rule preal_imp_pos [OF Rep_preal r])
  from preal_exists_greater [OF Rep_preal r]
  obtain u where u: "u \<in> Rep_preal R" and rless: "r < u" ..
  have upos: "0<u" by (rule preal_imp_pos [OF Rep_preal u])
  show ?thesis
  proof (intro exI conjI)
    show "0 < x/u" using xpos upos
      by (simp add: zero_less_divide_iff)  
    show "x/u < x/r" using xpos upos rpos
      by (simp add: divide_inverse mult_less_cancel_left rless) 
    show "inverse (x / r) \<notin> Rep_preal R" using notin
      by (simp add: divide_inverse mult.commute) 
    show "u \<in> Rep_preal R" by (rule u) 
    show "x = x / u * u" using upos 
      by (simp add: divide_inverse mult.commute) 
  qed
qed

lemma subset_inverse_mult: 
     "Rep_preal 1 \<subseteq> Rep_preal(inverse R * R)"
apply (auto simp add: Bex_def Rep_preal_one mem_Rep_preal_inverse_iff 
                      mem_Rep_preal_mult_iff)
apply (blast dest: subset_inverse_mult_lemma) 
done

lemma inverse_mult_subset_lemma:
  assumes rpos: "0 < r" 
    and rless: "r < y"
    and notin: "inverse y \<notin> Rep_preal R"
    and q: "q \<in> Rep_preal R"
  shows "r*q < 1"
proof -
  have "q < inverse y" using rpos rless
    by (simp add: not_in_preal_ub [OF Rep_preal notin] q)
  hence "r * q < r/y" using rpos
    by (simp add: divide_inverse mult_less_cancel_left)
  also have "... \<le> 1" using rpos rless
    by (simp add: pos_divide_le_eq)
  finally show ?thesis .
qed

lemma inverse_mult_subset:
     "Rep_preal(inverse R * R) \<subseteq> Rep_preal 1"
apply (auto simp add: Bex_def Rep_preal_one mem_Rep_preal_inverse_iff
                      mem_Rep_preal_mult_iff)
apply (simp add: zero_less_mult_iff preal_imp_pos [OF Rep_preal]) 
apply (blast intro: inverse_mult_subset_lemma) 
done

lemma preal_mult_inverse: "inverse R * R = (1::preal)"
apply (rule Rep_preal_inject [THEN iffD1])
apply (rule equalityI [OF inverse_mult_subset subset_inverse_mult]) 
done

lemma preal_mult_inverse_right: "R * inverse R = (1::preal)"
apply (rule preal_mult_commute [THEN subst])
apply (rule preal_mult_inverse)
done


text\<open>Theorems needing \<open>Gleason9_34\<close>\<close>

lemma Rep_preal_self_subset: "Rep_preal (R) \<subseteq> Rep_preal(R + S)"
proof 
  fix r
  assume r: "r \<in> Rep_preal R"
  have rpos: "0<r" by (rule preal_imp_pos [OF Rep_preal r])
  from mem_Rep_preal_Ex 
  obtain y where y: "y \<in> Rep_preal S" ..
  have ypos: "0<y" by (rule preal_imp_pos [OF Rep_preal y])
  have ry: "r+y \<in> Rep_preal(R + S)" using r y
    by (auto simp add: mem_Rep_preal_add_iff)
  show "r \<in> Rep_preal(R + S)" using r ypos rpos 
    by (simp add:  preal_downwards_closed [OF Rep_preal ry]) 
qed

lemma Rep_preal_sum_not_subset: "~ Rep_preal (R + S) \<subseteq> Rep_preal(R)"
proof -
  from mem_Rep_preal_Ex 
  obtain y where y: "y \<in> Rep_preal S" ..
  have ypos: "0<y" by (rule preal_imp_pos [OF Rep_preal y])
  from  Gleason9_34 [OF Rep_preal ypos]
  obtain r where r: "r \<in> Rep_preal R" and notin: "r + y \<notin> Rep_preal R" ..
  have "r + y \<in> Rep_preal (R + S)" using r y
    by (auto simp add: mem_Rep_preal_add_iff)
  thus ?thesis using notin by blast
qed

lemma Rep_preal_sum_not_eq: "Rep_preal (R + S) \<noteq> Rep_preal(R)"
by (insert Rep_preal_sum_not_subset, blast)

text\<open>at last, Gleason prop. 9-3.5(iii) page 123\<close>
lemma preal_self_less_add_left: "(R::preal) < R + S"
apply (unfold preal_less_def less_le)
apply (simp add: Rep_preal_self_subset Rep_preal_sum_not_eq [THEN not_sym])
done


subsection\<open>Subtraction for Positive Reals\<close>

text\<open>Gleason prop. 9-3.5(iv), page 123: proving @{prop "A < B ==> \<exists>D. A + D =
B"}. We define the claimed @{term D} and show that it is a positive real\<close>

text\<open>Part 1 of Dedekind sections definition\<close>
lemma diff_set_not_empty:
     "R < S ==> {} \<subset> diff_set (Rep_preal S) (Rep_preal R)"
apply (auto simp add: preal_less_def diff_set_def elim!: equalityE) 
apply (frule_tac x1 = S in Rep_preal [THEN preal_exists_greater])
apply (drule preal_imp_pos [OF Rep_preal], clarify)
apply (cut_tac a=x and b=u in add_eq_exists, force) 
done

text\<open>Part 2 of Dedekind sections definition\<close>
lemma diff_set_nonempty:
     "\<exists>q. 0 < q & q \<notin> diff_set (Rep_preal S) (Rep_preal R)"
apply (cut_tac X = S in Rep_preal_exists_bound)
apply (erule exE)
apply (rule_tac x = x in exI, auto)
apply (simp add: diff_set_def) 
apply (auto dest: Rep_preal [THEN preal_downwards_closed])
done

lemma diff_set_not_rat_set:
  "diff_set (Rep_preal S) (Rep_preal R) < {r. 0 < r}" (is "?lhs < ?rhs")
proof
  show "?lhs \<subseteq> ?rhs" by (auto simp add: diff_set_def) 
  show "?lhs \<noteq> ?rhs" using diff_set_nonempty by blast
qed

text\<open>Part 3 of Dedekind sections definition\<close>
lemma diff_set_lemma3:
     "[|R < S; u \<in> diff_set (Rep_preal S) (Rep_preal R); 0 < z; z < u|] 
      ==> z \<in> diff_set (Rep_preal S) (Rep_preal R)"
apply (auto simp add: diff_set_def) 
apply (rule_tac x=x in exI) 
apply (drule Rep_preal [THEN preal_downwards_closed], auto)
done

text\<open>Part 4 of Dedekind sections definition\<close>
lemma diff_set_lemma4:
     "[|R < S; y \<in> diff_set (Rep_preal S) (Rep_preal R)|] 
      ==> \<exists>u \<in> diff_set (Rep_preal S) (Rep_preal R). y < u"
apply (auto simp add: diff_set_def) 
apply (drule Rep_preal [THEN preal_exists_greater], clarify) 
apply (cut_tac a="x+y" and b=u in add_eq_exists, clarify)  
apply (rule_tac x="y+xa" in exI) 
apply (auto simp add: ac_simps)
done

lemma mem_diff_set:
     "R < S ==> cut (diff_set (Rep_preal S) (Rep_preal R))"
apply (unfold cut_def)
apply (blast intro!: diff_set_not_empty diff_set_not_rat_set
                     diff_set_lemma3 diff_set_lemma4)
done

lemma mem_Rep_preal_diff_iff:
      "R < S ==>
       (z \<in> Rep_preal(S-R)) = 
       (\<exists>x. 0 < x & 0 < z & x \<notin> Rep_preal R & x + z \<in> Rep_preal S)"
apply (simp add: preal_diff_def mem_diff_set Rep_preal)
apply (force simp add: diff_set_def) 
done


text\<open>proving that @{term "R + D \<le> S"}\<close>

lemma less_add_left_lemma:
  assumes Rless: "R < S"
    and a: "a \<in> Rep_preal R"
    and cb: "c + b \<in> Rep_preal S"
    and "c \<notin> Rep_preal R"
    and "0 < b"
    and "0 < c"
  shows "a + b \<in> Rep_preal S"
proof -
  have "0<a" by (rule preal_imp_pos [OF Rep_preal a])
  moreover
  have "a < c" using assms by (blast intro: not_in_Rep_preal_ub ) 
  ultimately show ?thesis
    using assms by (simp add: preal_downwards_closed [OF Rep_preal cb])
qed

lemma less_add_left_le1:
       "R < (S::preal) ==> R + (S-R) \<le> S"
apply (auto simp add: Bex_def preal_le_def mem_Rep_preal_add_iff 
                      mem_Rep_preal_diff_iff)
apply (blast intro: less_add_left_lemma) 
done

subsection\<open>proving that @{term "S \<le> R + D"} --- trickier\<close>

lemma lemma_sum_mem_Rep_preal_ex:
     "x \<in> Rep_preal S ==> \<exists>e. 0 < e & x + e \<in> Rep_preal S"
apply (drule Rep_preal [THEN preal_exists_greater], clarify) 
apply (cut_tac a=x and b=u in add_eq_exists, auto) 
done

lemma less_add_left_lemma2:
  assumes Rless: "R < S"
    and x:     "x \<in> Rep_preal S"
    and xnot: "x \<notin>  Rep_preal R"
  shows "\<exists>u v z. 0 < v & 0 < z & u \<in> Rep_preal R & z \<notin> Rep_preal R & 
                     z + v \<in> Rep_preal S & x = u + v"
proof -
  have xpos: "0<x" by (rule preal_imp_pos [OF Rep_preal x])
  from lemma_sum_mem_Rep_preal_ex [OF x]
  obtain e where epos: "0 < e" and xe: "x + e \<in> Rep_preal S" by blast
  from  Gleason9_34 [OF Rep_preal epos]
  obtain r where r: "r \<in> Rep_preal R" and notin: "r + e \<notin> Rep_preal R" ..
  with x xnot xpos have rless: "r < x" by (blast intro: not_in_Rep_preal_ub)
  from add_eq_exists [of r x]
  obtain y where eq: "x = r+y" by auto
  show ?thesis 
  proof (intro exI conjI)
    show "r \<in> Rep_preal R" by (rule r)
    show "r + e \<notin> Rep_preal R" by (rule notin)
    show "r + e + y \<in> Rep_preal S" using xe eq by (simp add: ac_simps)
    show "x = r + y" by (simp add: eq)
    show "0 < r + e" using epos preal_imp_pos [OF Rep_preal r]
      by simp
    show "0 < y" using rless eq by arith
  qed
qed

lemma less_add_left_le2: "R < (S::preal) ==> S \<le> R + (S-R)"
apply (auto simp add: preal_le_def)
apply (case_tac "x \<in> Rep_preal R")
apply (cut_tac Rep_preal_self_subset [of R], force)
apply (auto simp add: Bex_def mem_Rep_preal_add_iff mem_Rep_preal_diff_iff)
apply (blast dest: less_add_left_lemma2)
done

lemma less_add_left: "R < (S::preal) ==> R + (S-R) = S"
by (blast intro: antisym [OF less_add_left_le1 less_add_left_le2])

lemma less_add_left_Ex: "R < (S::preal) ==> \<exists>D. R + D = S"
by (fast dest: less_add_left)

lemma preal_add_less2_mono1: "R < (S::preal) ==> R + T < S + T"
apply (auto dest!: less_add_left_Ex simp add: preal_add_assoc)
apply (rule_tac y1 = D in preal_add_commute [THEN subst])
apply (auto intro: preal_self_less_add_left simp add: preal_add_assoc [symmetric])
done

lemma preal_add_less2_mono2: "R < (S::preal) ==> T + R < T + S"
by (auto intro: preal_add_less2_mono1 simp add: preal_add_commute [of T])

lemma preal_add_right_less_cancel: "R + T < S + T ==> R < (S::preal)"
apply (insert linorder_less_linear [of R S], auto)
apply (drule_tac R = S and T = T in preal_add_less2_mono1)
apply (blast dest: order_less_trans) 
done

lemma preal_add_left_less_cancel: "T + R < T + S ==> R <  (S::preal)"
by (auto elim: preal_add_right_less_cancel simp add: preal_add_commute [of T])

lemma preal_add_less_cancel_left [simp]: "(T + (R::preal) < T + S) = (R < S)"
by (blast intro: preal_add_less2_mono2 preal_add_left_less_cancel)

lemma preal_add_less_cancel_right [simp]: "((R::preal) + T < S + T) = (R < S)"
  using preal_add_less_cancel_left [symmetric, of R S T] by (simp add: ac_simps)

lemma preal_add_le_cancel_left [simp]: "(T + (R::preal) \<le> T + S) = (R \<le> S)"
by (simp add: linorder_not_less [symmetric]) 

lemma preal_add_le_cancel_right [simp]: "((R::preal) + T \<le> S + T) = (R \<le> S)"
  using preal_add_le_cancel_left [symmetric, of R S T] by (simp add: ac_simps)

lemma preal_add_right_cancel: "(R::preal) + T = S + T ==> R = S"
apply (insert linorder_less_linear [of R S], safe)
apply (drule_tac [!] T = T in preal_add_less2_mono1, auto)
done

lemma preal_add_left_cancel: "C + A = C + B ==> A = (B::preal)"
by (auto intro: preal_add_right_cancel simp add: preal_add_commute)

instance preal :: linordered_ab_semigroup_add
proof
  fix a b c :: preal
  show "a \<le> b \<Longrightarrow> c + a \<le> c + b" by (simp only: preal_add_le_cancel_left)
qed


subsection\<open>Completeness of type @{typ preal}\<close>

text\<open>Prove that supremum is a cut\<close>

text\<open>Part 1 of Dedekind sections definition\<close>

lemma preal_sup_set_not_empty:
     "P \<noteq> {} ==> {} \<subset> (\<Union>X \<in> P. Rep_preal(X))"
apply auto
apply (cut_tac X = x in mem_Rep_preal_Ex, auto)
done


text\<open>Part 2 of Dedekind sections definition\<close>

lemma preal_sup_not_exists:
     "\<forall>X \<in> P. X \<le> Y ==> \<exists>q. 0 < q & q \<notin> (\<Union>X \<in> P. Rep_preal(X))"
apply (cut_tac X = Y in Rep_preal_exists_bound)
apply (auto simp add: preal_le_def)
done

lemma preal_sup_set_not_rat_set:
     "\<forall>X \<in> P. X \<le> Y ==> (\<Union>X \<in> P. Rep_preal(X)) < {r. 0 < r}"
apply (drule preal_sup_not_exists)
apply (blast intro: preal_imp_pos [OF Rep_preal])  
done

text\<open>Part 3 of Dedekind sections definition\<close>
lemma preal_sup_set_lemma3:
     "[|P \<noteq> {}; \<forall>X \<in> P. X \<le> Y; u \<in> (\<Union>X \<in> P. Rep_preal(X)); 0 < z; z < u|]
      ==> z \<in> (\<Union>X \<in> P. Rep_preal(X))"
by (auto elim: Rep_preal [THEN preal_downwards_closed])

text\<open>Part 4 of Dedekind sections definition\<close>
lemma preal_sup_set_lemma4:
     "[|P \<noteq> {}; \<forall>X \<in> P. X \<le> Y; y \<in> (\<Union>X \<in> P. Rep_preal(X)) |]
          ==> \<exists>u \<in> (\<Union>X \<in> P. Rep_preal(X)). y < u"
by (blast dest: Rep_preal [THEN preal_exists_greater])

lemma preal_sup:
     "[|P \<noteq> {}; \<forall>X \<in> P. X \<le> Y|] ==> cut (\<Union>X \<in> P. Rep_preal(X))"
apply (unfold cut_def)
apply (blast intro!: preal_sup_set_not_empty preal_sup_set_not_rat_set
                     preal_sup_set_lemma3 preal_sup_set_lemma4)
done

lemma preal_psup_le:
     "[| \<forall>X \<in> P. X \<le> Y;  x \<in> P |] ==> x \<le> psup P"
apply (simp (no_asm_simp) add: preal_le_def) 
apply (subgoal_tac "P \<noteq> {}") 
apply (auto simp add: psup_def preal_sup) 
done

lemma psup_le_ub: "[| P \<noteq> {}; \<forall>X \<in> P. X \<le> Y |] ==> psup P \<le> Y"
apply (simp (no_asm_simp) add: preal_le_def)
apply (simp add: psup_def preal_sup) 
apply (auto simp add: preal_le_def)
done

text\<open>Supremum property\<close>
lemma preal_complete:
     "[| P \<noteq> {}; \<forall>X \<in> P. X \<le> Y |] ==> (\<exists>X \<in> P. Z < X) = (Z < psup P)"
apply (simp add: preal_less_def psup_def preal_sup)
apply (auto simp add: preal_le_def)
apply (rename_tac U) 
apply (cut_tac x = U and y = Z in linorder_less_linear)
apply (auto simp add: preal_less_def)
done

section \<open>Defining the Reals from the Positive Reals\<close>

definition
  realrel   ::  "((preal * preal) * (preal * preal)) set" where
  "realrel = {p. \<exists>x1 y1 x2 y2. p = ((x1,y1),(x2,y2)) & x1+y2 = x2+y1}"

definition "Real = UNIV//realrel"

typedef real = Real
  morphisms Rep_Real Abs_Real
  unfolding Real_def by (auto simp add: quotient_def)

definition
  (** these don't use the overloaded "real" function: users don't see them **)
  real_of_preal :: "preal => real" where
  "real_of_preal m = Abs_Real (realrel `` {(m + 1, 1)})"

instantiation real :: "{zero, one, plus, minus, uminus, times, inverse, ord, abs, sgn}"
begin

definition
  real_zero_def: "0 = Abs_Real(realrel``{(1, 1)})"

definition
  real_one_def: "1 = Abs_Real(realrel``{(1 + 1, 1)})"

definition
  real_add_def: "z + w =
       the_elem (\<Union>(x,y) \<in> Rep_Real(z). \<Union>(u,v) \<in> Rep_Real(w).
                 { Abs_Real(realrel``{(x+u, y+v)}) })"

definition
  real_minus_def: "- r =  the_elem (\<Union>(x,y) \<in> Rep_Real(r). { Abs_Real(realrel``{(y,x)}) })"

definition
  real_diff_def: "r - (s::real) = r + - s"

definition
  real_mult_def:
    "z * w =
       the_elem (\<Union>(x,y) \<in> Rep_Real(z). \<Union>(u,v) \<in> Rep_Real(w).
                 { Abs_Real(realrel``{(x*u + y*v, x*v + y*u)}) })"

definition
  real_inverse_def: "inverse (R::real) = (THE S. (R = 0 & S = 0) | S * R = 1)"

definition
  real_divide_def: "R div (S::real) = R * inverse S"

definition
  real_le_def: "z \<le> (w::real) \<longleftrightarrow>
    (\<exists>x y u v. x+v \<le> u+y & (x,y) \<in> Rep_Real z & (u,v) \<in> Rep_Real w)"

definition
  real_less_def: "x < (y::real) \<longleftrightarrow> x \<le> y \<and> x \<noteq> y"

definition
  real_abs_def: "\<bar>r::real\<bar> = (if r < 0 then - r else r)"

definition
  real_sgn_def: "sgn (x::real) = (if x=0 then 0 else if 0<x then 1 else - 1)"

instance ..

end

subsection \<open>Equivalence relation over positive reals\<close>

lemma preal_trans_lemma:
  assumes "x + y1 = x1 + y"
    and "x + y2 = x2 + y"
  shows "x1 + y2 = x2 + (y1::preal)"
proof -
  have "(x1 + y2) + x = (x + y2) + x1" by (simp add: ac_simps)
  also have "... = (x2 + y) + x1"  by (simp add: assms)
  also have "... = x2 + (x1 + y)"  by (simp add: ac_simps)
  also have "... = x2 + (x + y1)"  by (simp add: assms)
  also have "... = (x2 + y1) + x"  by (simp add: ac_simps)
  finally have "(x1 + y2) + x = (x2 + y1) + x" .
  thus ?thesis by (rule preal_add_right_cancel)
qed


lemma realrel_iff [simp]: "(((x1,y1),(x2,y2)) \<in> realrel) = (x1 + y2 = x2 + y1)"
by (simp add: realrel_def)

lemma equiv_realrel: "equiv UNIV realrel"
apply (auto simp add: equiv_def refl_on_def sym_def trans_def realrel_def)
apply (blast dest: preal_trans_lemma) 
done

text\<open>Reduces equality of equivalence classes to the @{term realrel} relation:
  @{term "(realrel `` {x} = realrel `` {y}) = ((x,y) \<in> realrel)"}\<close>
lemmas equiv_realrel_iff = 
       eq_equiv_class_iff [OF equiv_realrel UNIV_I UNIV_I]

declare equiv_realrel_iff [simp]


lemma realrel_in_real [simp]: "realrel``{(x,y)}: Real"
by (simp add: Real_def realrel_def quotient_def, blast)

declare Abs_Real_inject [simp]
declare Abs_Real_inverse [simp]


text\<open>Case analysis on the representation of a real number as an equivalence
      class of pairs of positive reals.\<close>
lemma eq_Abs_Real [case_names Abs_Real, cases type: real]: 
     "(!!x y. z = Abs_Real(realrel``{(x,y)}) ==> P) ==> P"
apply (rule Rep_Real [of z, unfolded Real_def, THEN quotientE])
apply (drule arg_cong [where f=Abs_Real])
apply (auto simp add: Rep_Real_inverse)
done


subsection \<open>Addition and Subtraction\<close>

lemma real_add_congruent2_lemma:
     "[|a + ba = aa + b; ab + bc = ac + bb|]
      ==> a + ab + (ba + bc) = aa + ac + (b + (bb::preal))"
apply (simp add: add.assoc)
apply (rule add.left_commute [of ab, THEN ssubst])
apply (simp add: add.assoc [symmetric])
apply (simp add: ac_simps)
done

lemma real_add:
     "Abs_Real (realrel``{(x,y)}) + Abs_Real (realrel``{(u,v)}) =
      Abs_Real (realrel``{(x+u, y+v)})"
proof -
  have "(\<lambda>z w. (\<lambda>(x,y). (\<lambda>(u,v). {Abs_Real (realrel `` {(x+u, y+v)})}) w) z)
        respects2 realrel"
    by (auto simp add: congruent2_def, blast intro: real_add_congruent2_lemma) 
  thus ?thesis
    by (simp add: real_add_def UN_UN_split_split_eq
                  UN_equiv_class2 [OF equiv_realrel equiv_realrel])
qed

lemma real_minus: "- Abs_Real(realrel``{(x,y)}) = Abs_Real(realrel `` {(y,x)})"
proof -
  have "(\<lambda>(x,y). {Abs_Real (realrel``{(y,x)})}) respects realrel"
    by (auto simp add: congruent_def add.commute) 
  thus ?thesis
    by (simp add: real_minus_def UN_equiv_class [OF equiv_realrel])
qed

instance real :: ab_group_add
proof
  fix x y z :: real
  show "(x + y) + z = x + (y + z)"
    by (cases x, cases y, cases z, simp add: real_add add.assoc)
  show "x + y = y + x"
    by (cases x, cases y, simp add: real_add add.commute)
  show "0 + x = x"
    by (cases x, simp add: real_add real_zero_def ac_simps)
  show "- x + x = 0"
    by (cases x, simp add: real_minus real_add real_zero_def add.commute)
  show "x - y = x + - y"
    by (simp add: real_diff_def)
qed


subsection \<open>Multiplication\<close>

lemma real_mult_congruent2_lemma:
     "!!(x1::preal). [| x1 + y2 = x2 + y1 |] ==>
          x * x1 + y * y1 + (x * y2 + y * x2) =
          x * x2 + y * y2 + (x * y1 + y * x1)"
apply (simp add: add.left_commute add.assoc [symmetric])
apply (simp add: add.assoc distrib_left [symmetric])
apply (simp add: add.commute)
done

lemma real_mult_congruent2:
    "(%p1 p2.
        (%(x1,y1). (%(x2,y2). 
          { Abs_Real (realrel``{(x1*x2 + y1*y2, x1*y2+y1*x2)}) }) p2) p1)
     respects2 realrel"
apply (rule congruent2_commuteI [OF equiv_realrel], clarify)
apply (simp add: mult.commute add.commute)
apply (auto simp add: real_mult_congruent2_lemma)
done

lemma real_mult:
      "Abs_Real((realrel``{(x1,y1)})) * Abs_Real((realrel``{(x2,y2)})) =
       Abs_Real(realrel `` {(x1*x2+y1*y2,x1*y2+y1*x2)})"
by (simp add: real_mult_def UN_UN_split_split_eq
         UN_equiv_class2 [OF equiv_realrel equiv_realrel real_mult_congruent2])

lemma real_mult_commute: "(z::real) * w = w * z"
by (cases z, cases w, simp add: real_mult ac_simps)

lemma real_mult_assoc: "((z1::real) * z2) * z3 = z1 * (z2 * z3)"
apply (cases z1, cases z2, cases z3)
apply (simp add: real_mult algebra_simps)
done

lemma real_mult_1: "(1::real) * z = z"
apply (cases z)
apply (simp add: real_mult real_one_def algebra_simps)
done

lemma real_add_mult_distrib: "((z1::real) + z2) * w = (z1 * w) + (z2 * w)"
apply (cases z1, cases z2, cases w)
apply (simp add: real_add real_mult algebra_simps)
done

text\<open>one and zero are distinct\<close>
lemma real_zero_not_eq_one: "0 \<noteq> (1::real)"
proof -
  have "(1::preal) < 1 + 1"
    by (simp add: preal_self_less_add_left)
  then show ?thesis
    by (simp add: real_zero_def real_one_def neq_iff)
qed

instance real :: comm_ring_1
proof
  fix x y z :: real
  show "(x * y) * z = x * (y * z)" by (rule real_mult_assoc)
  show "x * y = y * x" by (rule real_mult_commute)
  show "1 * x = x" by (rule real_mult_1)
  show "(x + y) * z = x * z + y * z" by (rule real_add_mult_distrib)
  show "0 \<noteq> (1::real)" by (rule real_zero_not_eq_one)
qed

subsection \<open>Inverse and Division\<close>

lemma real_zero_iff: "Abs_Real (realrel `` {(x, x)}) = 0"
by (simp add: real_zero_def add.commute)

text\<open>Instead of using an existential quantifier and constructing the inverse
within the proof, we could define the inverse explicitly.\<close>

lemma real_mult_inverse_left_ex: "x \<noteq> 0 ==> \<exists>y. y*x = (1::real)"
apply (simp add: real_zero_def real_one_def, cases x)
apply (cut_tac x = xa and y = y in linorder_less_linear)
apply (auto dest!: less_add_left_Ex simp add: real_zero_iff)
apply (rule_tac
        x = "Abs_Real (realrel``{(1, inverse (D) + 1)})"
       in exI)
apply (rule_tac [2]
        x = "Abs_Real (realrel``{(inverse (D) + 1, 1)})" 
       in exI)
apply (auto simp add: real_mult preal_mult_inverse_right algebra_simps)
done

lemma real_mult_inverse_left: "x \<noteq> 0 ==> inverse(x)*x = (1::real)"
apply (simp add: real_inverse_def)
apply (drule real_mult_inverse_left_ex, safe)
apply (rule theI, assumption, rename_tac z)
apply (subgoal_tac "(z * x) * y = z * (x * y)")
apply (simp add: mult.commute)
apply (rule mult.assoc)
done


subsection\<open>The Real Numbers form a Field\<close>

instance real :: field
proof
  fix x y z :: real
  show "x \<noteq> 0 ==> inverse x * x = 1" by (rule real_mult_inverse_left)
  show "x / y = x * inverse y" by (simp add: real_divide_def)
  show "inverse 0 = (0::real)" by (simp add: real_inverse_def)
qed


subsection\<open>The \<open>\<le>\<close> Ordering\<close>

lemma real_le_refl: "w \<le> (w::real)"
by (cases w, force simp add: real_le_def)

text\<open>The arithmetic decision procedure is not set up for type preal.
  This lemma is currently unused, but it could simplify the proofs of the
  following two lemmas.\<close>
lemma preal_eq_le_imp_le:
  assumes eq: "a+b = c+d" and le: "c \<le> a"
  shows "b \<le> (d::preal)"
proof -
  from le have "c+d \<le> a+d" by simp
  hence "a+b \<le> a+d" by (simp add: eq)
  thus "b \<le> d" by simp
qed

lemma real_le_lemma:
  assumes l: "u1 + v2 \<le> u2 + v1"
    and "x1 + v1 = u1 + y1"
    and "x2 + v2 = u2 + y2"
  shows "x1 + y2 \<le> x2 + (y1::preal)"
proof -
  have "(x1+v1) + (u2+y2) = (u1+y1) + (x2+v2)" by (simp add: assms)
  hence "(x1+y2) + (u2+v1) = (x2+y1) + (u1+v2)" by (simp add: ac_simps)
  also have "... \<le> (x2+y1) + (u2+v1)" by (simp add: assms)
  finally show ?thesis by simp
qed

lemma real_le: 
     "(Abs_Real(realrel``{(x1,y1)}) \<le> Abs_Real(realrel``{(x2,y2)})) =  
      (x1 + y2 \<le> x2 + y1)"
apply (simp add: real_le_def)
apply (auto intro: real_le_lemma)
done

lemma real_le_antisym: "[| z \<le> w; w \<le> z |] ==> z = (w::real)"
by (cases z, cases w, simp add: real_le)

lemma real_trans_lemma:
  assumes "x + v \<le> u + y"
    and "u + v' \<le> u' + v"
    and "x2 + v2 = u2 + y2"
  shows "x + v' \<le> u' + (y::preal)"
proof -
  have "(x+v') + (u+v) = (x+v) + (u+v')" by (simp add: ac_simps)
  also have "... \<le> (u+y) + (u+v')" by (simp add: assms)
  also have "... \<le> (u+y) + (u'+v)" by (simp add: assms)
  also have "... = (u'+y) + (u+v)"  by (simp add: ac_simps)
  finally show ?thesis by simp
qed

lemma real_le_trans: "[| i \<le> j; j \<le> k |] ==> i \<le> (k::real)"
apply (cases i, cases j, cases k)
apply (simp add: real_le)
apply (blast intro: real_trans_lemma)
done

instance real :: order
proof
  fix u v :: real
  show "u < v \<longleftrightarrow> u \<le> v \<and> \<not> v \<le> u" 
    by (auto simp add: real_less_def intro: real_le_antisym)
qed (assumption | rule real_le_refl real_le_trans real_le_antisym)+

(* Axiom 'linorder_linear' of class 'linorder': *)
lemma real_le_linear: "(z::real) \<le> w | w \<le> z"
apply (cases z, cases w)
apply (auto simp add: real_le real_zero_def ac_simps)
done

instance real :: linorder
  by (intro_classes, rule real_le_linear)

lemma real_le_eq_diff: "(x \<le> y) = (x-y \<le> (0::real))"
apply (cases x, cases y) 
apply (auto simp add: real_le real_zero_def real_diff_def real_add real_minus
                      ac_simps)
apply (simp_all add: add.assoc [symmetric])
done

lemma real_add_left_mono: 
  assumes le: "x \<le> y" shows "z + x \<le> z + (y::real)"
proof -
  have "z + x - (z + y) = (z + -z) + (x - y)" 
    by (simp add: algebra_simps) 
  with le show ?thesis 
    by (simp add: real_le_eq_diff[of x] real_le_eq_diff[of "z+x"])
qed

lemma real_sum_gt_zero_less: "(0 < S + (-W::real)) ==> (W < S)"
by (simp add: linorder_not_le [symmetric] real_le_eq_diff [of S])

lemma real_less_sum_gt_zero: "(W < S) ==> (0 < S + (-W::real))"
by (simp add: linorder_not_le [symmetric] real_le_eq_diff [of S])

lemma real_mult_order: "[| 0 < x; 0 < y |] ==> (0::real) < x * y"
apply (cases x, cases y)
apply (simp add: linorder_not_le [where 'a = real, symmetric] 
                 linorder_not_le [where 'a = preal] 
                  real_zero_def real_le real_mult)
  \<comment>\<open>Reduce to the (simpler) \<open>\<le>\<close> relation\<close>
apply (auto dest!: less_add_left_Ex
     simp add: algebra_simps preal_self_less_add_left)
done

lemma real_mult_less_mono2: "[| (0::real) < z; x < y |] ==> z * x < z * y"
apply (rule real_sum_gt_zero_less)
apply (drule real_less_sum_gt_zero [of x y])
apply (drule real_mult_order, assumption)
apply (simp add: algebra_simps)
done

instantiation real :: distrib_lattice
begin

definition
  "(inf :: real \<Rightarrow> real \<Rightarrow> real) = min"

definition
  "(sup :: real \<Rightarrow> real \<Rightarrow> real) = max"

instance
  by standard (auto simp add: inf_real_def sup_real_def max_min_distrib2)

end


subsection\<open>The Reals Form an Ordered Field\<close>

instance real :: linordered_field
proof
  fix x y z :: real
  show "x \<le> y ==> z + x \<le> z + y" by (rule real_add_left_mono)
  show "x < y ==> 0 < z ==> z * x < z * y" by (rule real_mult_less_mono2)
  show "\<bar>x\<bar> = (if x < 0 then -x else x)" by (simp only: real_abs_def)
  show "sgn x = (if x=0 then 0 else if 0<x then 1 else - 1)"
    by (simp only: real_sgn_def)
qed

text\<open>The function @{term real_of_preal} requires many proofs, but it seems
to be essential for proving completeness of the reals from that of the
positive reals.\<close>

lemma real_of_preal_add:
     "real_of_preal ((x::preal) + y) = real_of_preal x + real_of_preal y"
by (simp add: real_of_preal_def real_add algebra_simps)

lemma real_of_preal_mult:
     "real_of_preal ((x::preal) * y) = real_of_preal x* real_of_preal y"
by (simp add: real_of_preal_def real_mult algebra_simps)


text\<open>Gleason prop 9-4.4 p 127\<close>
lemma real_of_preal_trichotomy:
      "\<exists>m. (x::real) = real_of_preal m | x = 0 | x = -(real_of_preal m)"
apply (simp add: real_of_preal_def real_zero_def, cases x)
apply (auto simp add: real_minus ac_simps)
apply (cut_tac x = xa and y = y in linorder_less_linear)
apply (auto dest!: less_add_left_Ex simp add: add.assoc [symmetric])
done

lemma real_of_preal_leD:
      "real_of_preal m1 \<le> real_of_preal m2 ==> m1 \<le> m2"
by (simp add: real_of_preal_def real_le)

lemma real_of_preal_lessI: "m1 < m2 ==> real_of_preal m1 < real_of_preal m2"
by (auto simp add: real_of_preal_leD linorder_not_le [symmetric])

lemma real_of_preal_lessD:
      "real_of_preal m1 < real_of_preal m2 ==> m1 < m2"
by (simp add: real_of_preal_def real_le linorder_not_le [symmetric])

lemma real_of_preal_less_iff [simp]:
     "(real_of_preal m1 < real_of_preal m2) = (m1 < m2)"
by (blast intro: real_of_preal_lessI real_of_preal_lessD)

lemma real_of_preal_le_iff:
     "(real_of_preal m1 \<le> real_of_preal m2) = (m1 \<le> m2)"
by (simp add: linorder_not_less [symmetric])

lemma real_of_preal_zero_less: "0 < real_of_preal m"
using preal_self_less_add_left [of 1 m]
apply (auto simp add: real_zero_def real_of_preal_def real_less_def real_le_def ac_simps neq_iff)
apply (metis Rep_preal_self_subset add.commute preal_le_def)
done

lemma real_of_preal_minus_less_zero: "- real_of_preal m < 0"
by (simp add: real_of_preal_zero_less)

lemma real_of_preal_not_minus_gt_zero: "~ 0 < - real_of_preal m"
proof -
  from real_of_preal_minus_less_zero
  show ?thesis by (blast dest: order_less_trans)
qed


subsection\<open>Theorems About the Ordering\<close>

lemma real_gt_zero_preal_Ex: "(0 < x) = (\<exists>y. x = real_of_preal y)"
apply (auto simp add: real_of_preal_zero_less)
apply (cut_tac x = x in real_of_preal_trichotomy)
apply (blast elim!: real_of_preal_not_minus_gt_zero [THEN notE])
done

lemma real_gt_preal_preal_Ex:
     "real_of_preal z < x ==> \<exists>y. x = real_of_preal y"
by (blast dest!: real_of_preal_zero_less [THEN order_less_trans]
             intro: real_gt_zero_preal_Ex [THEN iffD1])

lemma real_ge_preal_preal_Ex:
     "real_of_preal z \<le> x ==> \<exists>y. x = real_of_preal y"
by (blast dest: order_le_imp_less_or_eq real_gt_preal_preal_Ex)

lemma real_less_all_preal: "y \<le> 0 ==> \<forall>x. y < real_of_preal x"
by (auto elim: order_le_imp_less_or_eq [THEN disjE] 
            intro: real_of_preal_zero_less [THEN [2] order_less_trans] 
            simp add: real_of_preal_zero_less)

lemma real_less_all_real2: "~ 0 < y ==> \<forall>x. y < real_of_preal x"
by (blast intro!: real_less_all_preal linorder_not_less [THEN iffD1])

subsection \<open>Completeness of Positive Reals\<close>

text \<open>
  Supremum property for the set of positive reals

  Let \<open>P\<close> be a non-empty set of positive reals, with an upper
  bound \<open>y\<close>.  Then \<open>P\<close> has a least upper bound
  (written \<open>S\<close>).

  FIXME: Can the premise be weakened to \<open>\<forall>x \<in> P. x\<le> y\<close>?
\<close>

lemma posreal_complete:
  assumes positive_P: "\<forall>x \<in> P. (0::real) < x"
    and not_empty_P: "\<exists>x. x \<in> P"
    and upper_bound_Ex: "\<exists>y. \<forall>x \<in> P. x<y"
  shows "\<exists>S. \<forall>y. (\<exists>x \<in> P. y < x) = (y < S)"
proof (rule exI, rule allI)
  fix y
  let ?pP = "{w. real_of_preal w \<in> P}"

  show "(\<exists>x\<in>P. y < x) = (y < real_of_preal (psup ?pP))"
  proof (cases "0 < y")
    assume neg_y: "\<not> 0 < y"
    show ?thesis
    proof
      assume "\<exists>x\<in>P. y < x"
      have "\<forall>x. y < real_of_preal x"
        using neg_y by (rule real_less_all_real2)
      thus "y < real_of_preal (psup ?pP)" ..
    next
      assume "y < real_of_preal (psup ?pP)"
      obtain "x" where x_in_P: "x \<in> P" using not_empty_P ..
      hence "0 < x" using positive_P by simp
      hence "y < x" using neg_y by simp
      thus "\<exists>x \<in> P. y < x" using x_in_P ..
    qed
  next
    assume pos_y: "0 < y"

    then obtain py where y_is_py: "y = real_of_preal py"
      by (auto simp add: real_gt_zero_preal_Ex)

    obtain a where "a \<in> P" using not_empty_P ..
    with positive_P have a_pos: "0 < a" ..
    then obtain pa where "a = real_of_preal pa"
      by (auto simp add: real_gt_zero_preal_Ex)
    hence "pa \<in> ?pP" using \<open>a \<in> P\<close> by auto
    hence pP_not_empty: "?pP \<noteq> {}" by auto

    obtain sup where sup: "\<forall>x \<in> P. x < sup"
      using upper_bound_Ex ..
    from this and \<open>a \<in> P\<close> have "a < sup" ..
    hence "0 < sup" using a_pos by arith
    then obtain possup where "sup = real_of_preal possup"
      by (auto simp add: real_gt_zero_preal_Ex)
    hence "\<forall>X \<in> ?pP. X \<le> possup"
      using sup by (auto simp add: real_of_preal_lessI)
    with pP_not_empty have psup: "\<And>Z. (\<exists>X \<in> ?pP. Z < X) = (Z < psup ?pP)"
      by (rule preal_complete)

    show ?thesis
    proof
      assume "\<exists>x \<in> P. y < x"
      then obtain x where x_in_P: "x \<in> P" and y_less_x: "y < x" ..
      hence "0 < x" using pos_y by arith
      then obtain px where x_is_px: "x = real_of_preal px"
        by (auto simp add: real_gt_zero_preal_Ex)

      have py_less_X: "\<exists>X \<in> ?pP. py < X"
      proof
        show "py < px" using y_is_py and x_is_px and y_less_x
          by (simp add: real_of_preal_lessI)
        show "px \<in> ?pP" using x_in_P and x_is_px by simp
      qed

      have "(\<exists>X \<in> ?pP. py < X) ==> (py < psup ?pP)"
        using psup by simp
      hence "py < psup ?pP" using py_less_X by simp
      thus "y < real_of_preal (psup {w. real_of_preal w \<in> P})"
        using y_is_py and pos_y by (simp add: real_of_preal_lessI)
    next
      assume y_less_psup: "y < real_of_preal (psup ?pP)"

      hence "py < psup ?pP" using y_is_py
        by (simp add: real_of_preal_lessI)
      then obtain "X" where py_less_X: "py < X" and X_in_pP: "X \<in> ?pP"
        using psup by auto
      then obtain x where x_is_X: "x = real_of_preal X"
        by (simp add: real_gt_zero_preal_Ex)
      hence "y < x" using py_less_X and y_is_py
        by (simp add: real_of_preal_lessI)

      moreover have "x \<in> P" using x_is_X and X_in_pP by simp

      ultimately show "\<exists> x \<in> P. y < x" ..
    qed
  qed
qed

text \<open>
  \medskip Completeness
\<close>

lemma reals_complete:
  fixes S :: "real set"
  assumes notempty_S: "\<exists>X. X \<in> S"
    and exists_Ub: "bdd_above S"
  shows "\<exists>x. (\<forall>s\<in>S. s \<le> x) \<and> (\<forall>y. (\<forall>s\<in>S. s \<le> y) \<longrightarrow> x \<le> y)"
proof -
  obtain X where X_in_S: "X \<in> S" using notempty_S ..
  obtain Y where Y_isUb: "\<forall>s\<in>S. s \<le> Y"
    using exists_Ub by (auto simp: bdd_above_def)
  let ?SHIFT = "{z. \<exists>x \<in>S. z = x + (-X) + 1} \<inter> {x. 0 < x}"

  {
    fix x
    assume S_le_x: "\<forall>s\<in>S. s \<le> x"
    {
      fix s
      assume "s \<in> {z. \<exists>x\<in>S. z = x + - X + 1}"
      hence "\<exists> x \<in> S. s = x + -X + 1" ..
      then obtain x1 where x1: "x1 \<in> S" "s = x1 + (-X) + 1" ..
      then have "x1 \<le> x" using S_le_x by simp
      with x1 have "s \<le> x + - X + 1" by arith
    }
    then have "\<forall>s\<in>?SHIFT. s \<le> x + (-X) + 1"
      by auto
  } note S_Ub_is_SHIFT_Ub = this

  have *: "\<forall>s\<in>?SHIFT. s \<le> Y + (-X) + 1" using Y_isUb by (rule S_Ub_is_SHIFT_Ub)
  have "\<forall>s\<in>?SHIFT. s < Y + (-X) + 2"
  proof
    fix s assume "s\<in>?SHIFT"
    with * have "s \<le> Y + (-X) + 1" by simp
    also have "\<dots> < Y + (-X) + 2" by simp
    finally show "s < Y + (-X) + 2" .
  qed
  moreover have "\<forall>y \<in> ?SHIFT. 0 < y" by auto
  moreover have shifted_not_empty: "\<exists>u. u \<in> ?SHIFT"
    using X_in_S and Y_isUb by auto
  ultimately obtain t where t_is_Lub: "\<forall>y. (\<exists>x\<in>?SHIFT. y < x) = (y < t)"
    using posreal_complete [of ?SHIFT] unfolding bdd_above_def by blast

  show ?thesis
  proof
    show "(\<forall>s\<in>S. s \<le> (t + X + (-1))) \<and> (\<forall>y. (\<forall>s\<in>S. s \<le> y) \<longrightarrow> (t + X + (-1)) \<le> y)"
    proof safe
      fix x
      assume "\<forall>s\<in>S. s \<le> x"
      hence "\<forall>s\<in>?SHIFT. s \<le> x + (-X) + 1"
        using S_Ub_is_SHIFT_Ub by simp
      then have "\<not> x + (-X) + 1 < t"
        by (subst t_is_Lub[rule_format, symmetric]) (simp add: not_less)
      thus "t + X + -1 \<le> x" by arith
    next
      fix y
      assume y_in_S: "y \<in> S"
      obtain "u" where u_in_shift: "u \<in> ?SHIFT" using shifted_not_empty ..
      hence "\<exists> x \<in> S. u = x + - X + 1" by simp
      then obtain "x" where x_and_u: "u = x + - X + 1" ..
      have u_le_t: "u \<le> t"
      proof (rule dense_le)
        fix x assume "x < u" then have "x < t"
          using u_in_shift t_is_Lub by auto
        then show "x \<le> t"  by simp
      qed

      show "y \<le> t + X + -1"
      proof cases
        assume "y \<le> x"
        moreover have "x = u + X + - 1" using x_and_u by arith
        moreover have "u + X + - 1  \<le> t + X + -1" using u_le_t by arith
        ultimately show "y  \<le> t + X + -1" by arith
      next
        assume "~(y \<le> x)"
        hence x_less_y: "x < y" by arith

        have "x + (-X) + 1 \<in> ?SHIFT" using x_and_u and u_in_shift by simp
        hence "0 < x + (-X) + 1" by simp
        hence "0 < y + (-X) + 1" using x_less_y by arith
        hence *: "y + (-X) + 1 \<in> ?SHIFT" using y_in_S by simp
        have "y + (-X) + 1 \<le> t"
        proof (rule dense_le)
          fix x assume "x < y + (-X) + 1" then have "x < t"
            using * t_is_Lub by auto
          then show "x \<le> t"  by simp
        qed
        thus ?thesis by simp
      qed
    qed
  qed
qed

subsection \<open>The Archimedean Property of the Reals\<close>

theorem reals_Archimedean:
  fixes x :: real
  assumes x_pos: "0 < x"
  shows "\<exists>n. inverse (of_nat (Suc n)) < x"
proof (rule ccontr)
  assume contr: "\<not> ?thesis"
  have "\<forall>n. x * of_nat (Suc n) <= 1"
  proof
    fix n
    from contr have "x \<le> inverse (of_nat (Suc n))"
      by (simp add: linorder_not_less)
    hence "x \<le> (1 / (of_nat (Suc n)))"
      by (simp add: inverse_eq_divide)
    moreover have "(0::real) \<le> of_nat (Suc n)"
      by (rule of_nat_0_le_iff)
    ultimately have "x * of_nat (Suc n) \<le> (1 / of_nat (Suc n)) * of_nat (Suc n)"
      by (rule mult_right_mono)
    thus "x * of_nat (Suc n) \<le> 1" by (simp del: of_nat_Suc)
  qed
  hence 2: "bdd_above {z. \<exists>n. z = x * (of_nat (Suc n))}"
    by (auto intro!: bdd_aboveI[of _ 1])
  have 1: "\<exists>X. X \<in> {z. \<exists>n. z = x* (of_nat (Suc n))}" by auto
  obtain t where
    upper: "\<And>z. z \<in> {z. \<exists>n. z = x * of_nat (Suc n)} \<Longrightarrow> z \<le> t" and
    least: "\<And>y. (\<And>a. a \<in> {z. \<exists>n. z = x * of_nat (Suc n)} \<Longrightarrow> a \<le> y) \<Longrightarrow> t \<le> y"
    using reals_complete[OF 1 2] by auto


  have "t \<le> t + - x"
  proof (rule least)
    fix a assume a: "a \<in> {z. \<exists>n. z = x * (of_nat (Suc n))}"
    have "\<forall>n::nat. x * of_nat n \<le> t + - x"
    proof
      fix n
      have "x * of_nat (Suc n) \<le> t"
        by (simp add: upper)
      hence  "x * (of_nat n) + x \<le> t"
        by (simp add: distrib_left)
      thus  "x * (of_nat n) \<le> t + - x" by arith
    qed    hence "\<forall>m. x * of_nat (Suc m) \<le> t + - x" by (simp del: of_nat_Suc)
    with a show "a \<le> t + - x"
      by auto
  qed
  thus False using x_pos by arith
qed

text \<open>
  There must be other proofs, e.g. \<open>Suc\<close> of the largest
  integer in the cut representing \<open>x\<close>.
\<close>

lemma reals_Archimedean2: "\<exists>n. (x::real) < of_nat (n::nat)"
proof cases
  assume "x \<le> 0"
  hence "x < of_nat (1::nat)" by simp
  thus ?thesis ..
next
  assume "\<not> x \<le> 0"
  hence x_greater_zero: "0 < x" by simp
  hence "0 < inverse x" by simp
  then obtain n where "inverse (of_nat (Suc n)) < inverse x"
    using reals_Archimedean by blast
  hence "inverse (of_nat (Suc n)) * x < inverse x * x"
    using x_greater_zero by (rule mult_strict_right_mono)
  hence "inverse (of_nat (Suc n)) * x < 1"
    using x_greater_zero by simp
  hence "of_nat (Suc n) * (inverse (of_nat (Suc n)) * x) < of_nat (Suc n) * 1"
    by (rule mult_strict_left_mono) (simp del: of_nat_Suc)
  hence "x < of_nat (Suc n)"
    by (simp add: algebra_simps del: of_nat_Suc)
  thus "\<exists>(n::nat). x < of_nat n" ..
qed

instance real :: archimedean_field
proof
  fix r :: real
  obtain n :: nat where "r < of_nat n"
    using reals_Archimedean2 ..
  then have "r \<le> of_int (int n)"
    by simp
  then show "\<exists>z. r \<le> of_int z" ..
qed

end
