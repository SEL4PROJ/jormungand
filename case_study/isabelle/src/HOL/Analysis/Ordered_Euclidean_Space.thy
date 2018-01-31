theory Ordered_Euclidean_Space
imports
  Cartesian_Euclidean_Space
  "~~/src/HOL/Library/Product_Order"
begin

subsection \<open>An ordering on euclidean spaces that will allow us to talk about intervals\<close>

class ordered_euclidean_space = ord + inf + sup + abs + Inf + Sup + euclidean_space +
  assumes eucl_le: "x \<le> y \<longleftrightarrow> (\<forall>i\<in>Basis. x \<bullet> i \<le> y \<bullet> i)"
  assumes eucl_less_le_not_le: "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"
  assumes eucl_inf: "inf x y = (\<Sum>i\<in>Basis. inf (x \<bullet> i) (y \<bullet> i) *\<^sub>R i)"
  assumes eucl_sup: "sup x y = (\<Sum>i\<in>Basis. sup (x \<bullet> i) (y \<bullet> i) *\<^sub>R i)"
  assumes eucl_Inf: "Inf X = (\<Sum>i\<in>Basis. (INF x:X. x \<bullet> i) *\<^sub>R i)"
  assumes eucl_Sup: "Sup X = (\<Sum>i\<in>Basis. (SUP x:X. x \<bullet> i) *\<^sub>R i)"
  assumes eucl_abs: "\<bar>x\<bar> = (\<Sum>i\<in>Basis. \<bar>x \<bullet> i\<bar> *\<^sub>R i)"
begin

subclass order
  by standard
    (auto simp: eucl_le eucl_less_le_not_le intro!: euclidean_eqI antisym intro: order.trans)

subclass ordered_ab_group_add_abs
  by standard (auto simp: eucl_le inner_add_left eucl_abs abs_leI)

subclass ordered_real_vector
  by standard (auto simp: eucl_le intro!: mult_left_mono mult_right_mono)

subclass lattice
  by standard (auto simp: eucl_inf eucl_sup eucl_le)

subclass distrib_lattice
  by standard (auto simp: eucl_inf eucl_sup sup_inf_distrib1 intro!: euclidean_eqI)

subclass conditionally_complete_lattice
proof
  fix z::'a and X::"'a set"
  assume "X \<noteq> {}"
  hence "\<And>i. (\<lambda>x. x \<bullet> i) ` X \<noteq> {}" by simp
  thus "(\<And>x. x \<in> X \<Longrightarrow> z \<le> x) \<Longrightarrow> z \<le> Inf X" "(\<And>x. x \<in> X \<Longrightarrow> x \<le> z) \<Longrightarrow> Sup X \<le> z"
    by (auto simp: eucl_Inf eucl_Sup eucl_le
      intro!: cInf_greatest cSup_least)
qed (force intro!: cInf_lower cSup_upper
      simp: bdd_below_def bdd_above_def preorder_class.bdd_below_def preorder_class.bdd_above_def
        eucl_Inf eucl_Sup eucl_le)+

lemma inner_Basis_inf_left: "i \<in> Basis \<Longrightarrow> inf x y \<bullet> i = inf (x \<bullet> i) (y \<bullet> i)"
  and inner_Basis_sup_left: "i \<in> Basis \<Longrightarrow> sup x y \<bullet> i = sup (x \<bullet> i) (y \<bullet> i)"
  by (simp_all add: eucl_inf eucl_sup inner_sum_left inner_Basis if_distrib comm_monoid_add_class.sum.delta
      cong: if_cong)

lemma inner_Basis_INF_left: "i \<in> Basis \<Longrightarrow> (INF x:X. f x) \<bullet> i = (INF x:X. f x \<bullet> i)"
  and inner_Basis_SUP_left: "i \<in> Basis \<Longrightarrow> (SUP x:X. f x) \<bullet> i = (SUP x:X. f x \<bullet> i)"
  using eucl_Sup [of "f ` X"] eucl_Inf [of "f ` X"] by (simp_all add: comp_def)

lemma abs_inner: "i \<in> Basis \<Longrightarrow> \<bar>x\<bar> \<bullet> i = \<bar>x \<bullet> i\<bar>"
  by (auto simp: eucl_abs)

lemma
  abs_scaleR: "\<bar>a *\<^sub>R b\<bar> = \<bar>a\<bar> *\<^sub>R \<bar>b\<bar>"
  by (auto simp: eucl_abs abs_mult intro!: euclidean_eqI)

lemma interval_inner_leI:
  assumes "x \<in> {a .. b}" "0 \<le> i"
  shows "a\<bullet>i \<le> x\<bullet>i" "x\<bullet>i \<le> b\<bullet>i"
  using assms
  unfolding euclidean_inner[of a i] euclidean_inner[of x i] euclidean_inner[of b i]
  by (auto intro!: ordered_comm_monoid_add_class.sum_mono mult_right_mono simp: eucl_le)

lemma inner_nonneg_nonneg:
  shows "0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> 0 \<le> a \<bullet> b"
  using interval_inner_leI[of a 0 a b]
  by auto

lemma inner_Basis_mono:
  shows "a \<le> b \<Longrightarrow> c \<in> Basis  \<Longrightarrow> a \<bullet> c \<le> b \<bullet> c"
  by (simp add: eucl_le)

lemma Basis_nonneg[intro, simp]: "i \<in> Basis \<Longrightarrow> 0 \<le> i"
  by (auto simp: eucl_le inner_Basis)

lemma Sup_eq_maximum_componentwise:
  fixes s::"'a set"
  assumes i: "\<And>b. b \<in> Basis \<Longrightarrow> X \<bullet> b = i b \<bullet> b"
  assumes sup: "\<And>b x. b \<in> Basis \<Longrightarrow> x \<in> s \<Longrightarrow> x \<bullet> b \<le> X \<bullet> b"
  assumes i_s: "\<And>b. b \<in> Basis \<Longrightarrow> (i b \<bullet> b) \<in> (\<lambda>x. x \<bullet> b) ` s"
  shows "Sup s = X"
  using assms
  unfolding eucl_Sup euclidean_representation_sum
  by (auto intro!: conditionally_complete_lattice_class.cSup_eq_maximum)

lemma Inf_eq_minimum_componentwise:
  assumes i: "\<And>b. b \<in> Basis \<Longrightarrow> X \<bullet> b = i b \<bullet> b"
  assumes sup: "\<And>b x. b \<in> Basis \<Longrightarrow> x \<in> s \<Longrightarrow> X \<bullet> b \<le> x \<bullet> b"
  assumes i_s: "\<And>b. b \<in> Basis \<Longrightarrow> (i b \<bullet> b) \<in> (\<lambda>x. x \<bullet> b) ` s"
  shows "Inf s = X"
  using assms
  unfolding eucl_Inf euclidean_representation_sum
  by (auto intro!: conditionally_complete_lattice_class.cInf_eq_minimum)

end

lemma
  compact_attains_Inf_componentwise:
  fixes b::"'a::ordered_euclidean_space"
  assumes "b \<in> Basis" assumes "X \<noteq> {}" "compact X"
  obtains x where "x \<in> X" "x \<bullet> b = Inf X \<bullet> b" "\<And>y. y \<in> X \<Longrightarrow> x \<bullet> b \<le> y \<bullet> b"
proof atomize_elim
  let ?proj = "(\<lambda>x. x \<bullet> b) ` X"
  from assms have "compact ?proj" "?proj \<noteq> {}"
    by (auto intro!: compact_continuous_image continuous_intros)
  from compact_attains_inf[OF this]
  obtain s x
    where s: "s\<in>(\<lambda>x. x \<bullet> b) ` X" "\<And>t. t\<in>(\<lambda>x. x \<bullet> b) ` X \<Longrightarrow> s \<le> t"
      and x: "x \<in> X" "s = x \<bullet> b" "\<And>y. y \<in> X \<Longrightarrow> x \<bullet> b \<le> y \<bullet> b"
    by auto
  hence "Inf ?proj = x \<bullet> b"
    by (auto intro!: conditionally_complete_lattice_class.cInf_eq_minimum)
  hence "x \<bullet> b = Inf X \<bullet> b"
    by (auto simp: eucl_Inf inner_sum_left inner_Basis if_distrib \<open>b \<in> Basis\<close> sum.delta
      cong: if_cong)
  with x show "\<exists>x. x \<in> X \<and> x \<bullet> b = Inf X \<bullet> b \<and> (\<forall>y. y \<in> X \<longrightarrow> x \<bullet> b \<le> y \<bullet> b)" by blast
qed

lemma
  compact_attains_Sup_componentwise:
  fixes b::"'a::ordered_euclidean_space"
  assumes "b \<in> Basis" assumes "X \<noteq> {}" "compact X"
  obtains x where "x \<in> X" "x \<bullet> b = Sup X \<bullet> b" "\<And>y. y \<in> X \<Longrightarrow> y \<bullet> b \<le> x \<bullet> b"
proof atomize_elim
  let ?proj = "(\<lambda>x. x \<bullet> b) ` X"
  from assms have "compact ?proj" "?proj \<noteq> {}"
    by (auto intro!: compact_continuous_image continuous_intros)
  from compact_attains_sup[OF this]
  obtain s x
    where s: "s\<in>(\<lambda>x. x \<bullet> b) ` X" "\<And>t. t\<in>(\<lambda>x. x \<bullet> b) ` X \<Longrightarrow> t \<le> s"
      and x: "x \<in> X" "s = x \<bullet> b" "\<And>y. y \<in> X \<Longrightarrow> y \<bullet> b \<le> x \<bullet> b"
    by auto
  hence "Sup ?proj = x \<bullet> b"
    by (auto intro!: cSup_eq_maximum)
  hence "x \<bullet> b = Sup X \<bullet> b"
    by (auto simp: eucl_Sup[where 'a='a] inner_sum_left inner_Basis if_distrib \<open>b \<in> Basis\<close> sum.delta
      cong: if_cong)
  with x show "\<exists>x. x \<in> X \<and> x \<bullet> b = Sup X \<bullet> b \<and> (\<forall>y. y \<in> X \<longrightarrow> y \<bullet> b \<le> x \<bullet> b)" by blast
qed

lemma (in order) atLeastatMost_empty'[simp]:
  "(~ a <= b) \<Longrightarrow> {a..b} = {}"
  by (auto)

instance real :: ordered_euclidean_space
  by standard auto

lemma in_Basis_prod_iff:
  fixes i::"'a::euclidean_space*'b::euclidean_space"
  shows "i \<in> Basis \<longleftrightarrow> fst i = 0 \<and> snd i \<in> Basis \<or> snd i = 0 \<and> fst i \<in> Basis"
  by (cases i) (auto simp: Basis_prod_def)

instantiation prod :: (abs, abs) abs
begin

definition "\<bar>x\<bar> = (\<bar>fst x\<bar>, \<bar>snd x\<bar>)"

instance ..

end

instance prod :: (ordered_euclidean_space, ordered_euclidean_space) ordered_euclidean_space
  by standard
    (auto intro!: add_mono simp add: euclidean_representation_sum'  Ball_def inner_prod_def
      in_Basis_prod_iff inner_Basis_inf_left inner_Basis_sup_left inner_Basis_INF_left Inf_prod_def
      inner_Basis_SUP_left Sup_prod_def less_prod_def less_eq_prod_def eucl_le[where 'a='a]
      eucl_le[where 'a='b] abs_prod_def abs_inner)

text\<open>Instantiation for intervals on \<open>ordered_euclidean_space\<close>\<close>

lemma
  fixes a :: "'a::ordered_euclidean_space"
  shows cbox_interval: "cbox a b = {a..b}"
    and interval_cbox: "{a..b} = cbox a b"
    and eucl_le_atMost: "{x. \<forall>i\<in>Basis. x \<bullet> i <= a \<bullet> i} = {..a}"
    and eucl_le_atLeast: "{x. \<forall>i\<in>Basis. a \<bullet> i <= x \<bullet> i} = {a..}"
    by (auto simp: eucl_le[where 'a='a] eucl_less_def box_def cbox_def)

lemma closed_eucl_atLeastAtMost[simp, intro]:
  fixes a :: "'a::ordered_euclidean_space"
  shows "closed {a..b}"
  by (simp add: cbox_interval[symmetric] closed_cbox)

lemma closed_eucl_atMost[simp, intro]:
  fixes a :: "'a::ordered_euclidean_space"
  shows "closed {..a}"
  by (simp add: eucl_le_atMost[symmetric])

lemma closed_eucl_atLeast[simp, intro]:
  fixes a :: "'a::ordered_euclidean_space"
  shows "closed {a..}"
  by (simp add: eucl_le_atLeast[symmetric])

lemma bounded_closed_interval:
  fixes a :: "'a::ordered_euclidean_space"
  shows "bounded {a .. b}"
  using bounded_cbox[of a b]
  by (metis interval_cbox)

lemma convex_closed_interval:
  fixes a :: "'a::ordered_euclidean_space"
  shows "convex {a .. b}"
  using convex_box[of a b]
  by (metis interval_cbox)

lemma image_smult_interval:"(\<lambda>x. m *\<^sub>R (x::_::ordered_euclidean_space)) ` {a .. b} =
  (if {a .. b} = {} then {} else if 0 \<le> m then {m *\<^sub>R a .. m *\<^sub>R b} else {m *\<^sub>R b .. m *\<^sub>R a})"
  using image_smult_cbox[of m a b]
  by (simp add: cbox_interval)

lemma is_interval_closed_interval:
  "is_interval {a .. (b::'a::ordered_euclidean_space)}"
  by (metis cbox_interval is_interval_cbox)

lemma compact_interval:
  fixes a b::"'a::ordered_euclidean_space"
  shows "compact {a .. b}"
  by (metis compact_cbox interval_cbox)

lemma homeomorphic_closed_intervals:
  fixes a :: "'a::euclidean_space" and b and c :: "'a::euclidean_space" and d
  assumes "box a b \<noteq> {}" and "box c d \<noteq> {}"
    shows "(cbox a b) homeomorphic (cbox c d)"
apply (rule homeomorphic_convex_compact)
using assms apply auto
done

lemma homeomorphic_closed_intervals_real:
  fixes a::real and b and c::real and d
  assumes "a<b" and "c<d"
    shows "{a..b} homeomorphic {c..d}"
by (metis assms compact_interval continuous_on_id convex_real_interval(5) emptyE homeomorphic_convex_compact interior_atLeastAtMost_real mvt)

no_notation
  eucl_less (infix "<e" 50)

lemma One_nonneg: "0 \<le> (\<Sum>Basis::'a::ordered_euclidean_space)"
  by (auto intro: sum_nonneg)

lemma
  fixes a b::"'a::ordered_euclidean_space"
  shows bdd_above_cbox[intro, simp]: "bdd_above (cbox a b)"
    and bdd_below_cbox[intro, simp]: "bdd_below (cbox a b)"
    and bdd_above_box[intro, simp]: "bdd_above (box a b)"
    and bdd_below_box[intro, simp]: "bdd_below (box a b)"
  unfolding atomize_conj
  by (metis bdd_above_Icc bdd_above_mono bdd_below_Icc bdd_below_mono bounded_box
    bounded_subset_cbox interval_cbox)

instantiation vec :: (ordered_euclidean_space, finite) ordered_euclidean_space
begin

definition "inf x y = (\<chi> i. inf (x $ i) (y $ i))"
definition "sup x y = (\<chi> i. sup (x $ i) (y $ i))"
definition "Inf X = (\<chi> i. (INF x:X. x $ i))"
definition "Sup X = (\<chi> i. (SUP x:X. x $ i))"
definition "\<bar>x\<bar> = (\<chi> i. \<bar>x $ i\<bar>)"

instance
  apply standard
  unfolding euclidean_representation_sum'
  apply (auto simp: less_eq_vec_def inf_vec_def sup_vec_def Inf_vec_def Sup_vec_def inner_axis
    Basis_vec_def inner_Basis_inf_left inner_Basis_sup_left inner_Basis_INF_left
    inner_Basis_SUP_left eucl_le[where 'a='a] less_le_not_le abs_vec_def abs_inner)
  done

end

lemma ANR_interval [iff]:
    fixes a :: "'a::ordered_euclidean_space"
    shows "ANR{a..b}"
by (simp add: interval_cbox)

lemma ENR_interval [iff]:
    fixes a :: "'a::ordered_euclidean_space"
    shows "ENR{a..b}"
  by (auto simp: interval_cbox)

end

