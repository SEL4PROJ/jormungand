(* Additional definitions and tweaks for the paper *)

theory Paper_Defs
  imports
  "~~/src/HOL/Library/LaTeXsugar"
  "lib/Hoare_Sep_Tactics/Unified_Correctness"
	"lib/Hoare_Sep_Tactics/Simple_Separation_Example"
begin

definition "Nf = nf"

lemma sep_collapsing: "(Nf -& (not Nf)) s \<Longrightarrow> \<not> Nf s"
unfolding Nf_def 
   apply (clarsimp simp: pred_neg_def sept_def plus_prod_def plus_bool_def)
  done   

lemma sept_paraconsistent: "\<exists>s. (p \<mapsto>u v -& \<box>) s"
 apply (rule_tac x="(undefined, False)" in exI)
 apply (clarsimp simp: sept_def sep_empty_def)
done


lemma sept_paraconsistent'': "\<exists>s. (p \<mapsto>u - -& \<box>) s \<and> \<not>Nf s"
  unfolding Nf_def 
 apply (rule_tac x="(undefined, False)" in exI)
  apply (clarsimp simp: sept_def sep_empty_def)
  using maps_to_ex_simp by blast

lemma sept_success_prettier:"( p \<mapsto>u - -& (p \<mapsto>u - \<and>* (R and Nf))) s \<Longrightarrow> (R and (Nf)) s"
unfolding Nf_def 
apply (clarsimp simp: sept_def sep_conj_def Unified_Correctness.maps_to_ex_def split: if_splits)
  apply (erule disjE, clarsimp simp: pred_conj_def)
  apply (subgoal_tac "y = ya", clarsimp)
  apply (metis Extended_Separation_Algebra.cancellative_sep_algebra_class.sep_add_cancelD sep_add_commute sep_disj_commuteI) 
  apply (clarsimp simp: plus_prod_def)
apply (drule fun_cong[where x=p], clarsimp simp: plus_fun_def plus_option_def split: option.splits)
apply (clarsimp simp: plus_fun_def plus_option_def sep_disj_fun_def sep_disj_prod_def sep_disj_option_def plus_bool_def sep_disj_bool_def split: if_splits)
apply (fastforce)
apply (clarsimp simp: plus_fun_def plus_prod_def plus_option_def sep_disj_fun_def sep_disj_prod_def sep_disj_option_def plus_bool_def sep_disj_bool_def split: if_splits)
apply (fastforce)
done


(* EXS variant with \<exists> output *)
definition
  exs :: "('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> bool"
where
  "exs (\<lambda>s. P s) \<equiv> \<lambda>s. \<exists>x. P x s"

notation (input)
  exs (binder "exs " 10)

notation (output)
  exs (binder "\<exists>" 10)

term "ALLS x. P x"

(* ALLS variant with \<forall> output *)
definition
  alls :: "('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> bool"
where
  "alls (\<lambda>s. P s) \<equiv> \<lambda>s. \<forall>x. P x s"

notation (input)
  alls (binder "alls " 10)

notation (output)
  alls (binder "\<forall>" 10)

thm new_ptr_wp[no_vars]

lemma new_ptr_wp_pretty: "\<lbrace>(alls x. x \<mapsto> - \<longrightarrow>* R x)\<rbrace> new_ptr \<lbrace>R\<rbrace>"
 unfolding alls_def
 by (simp add: new_ptr_wp)

thm copy_ptr_sp[no_vars]

lemma copy_ptr_valid_pretty: "\<lbrace>exs x. (p \<mapsto> x \<and>* (p \<mapsto> x \<longrightarrow>* p' \<mapsto> - \<and>* (p' \<mapsto> x \<longrightarrow>* R)))\<rbrace> copy_ptr p p' \<lbrace>\<lambda>_. R\<rbrace>"
  unfolding exs_def
  by (simp add: copy_ptr_wp)

lemma copy_ptr_sp_pretty: "\<lbrace>R\<rbrace> copy_ptr p p' \<lbrace>\<lambda>_. exs x. (p' \<mapsto> x \<and>* (p' \<mapsto> - -* p \<mapsto> x \<and>* (p \<mapsto> x -* R)))\<rbrace>"
  unfolding exs_def
  by (simp add: copy_ptr_sp)

lemma swap_ptr_valid'_pretty: "\<lbrace>(p \<mapsto> v \<and>* p' \<mapsto> v' \<and>* R)\<rbrace> swap_ptr p p' \<lbrace>\<lambda>_. (p \<mapsto> v' \<and>* p' \<mapsto> v \<and>* R)\<rbrace>"
  apply (clarsimp simp: swap_ptr_def, intro seq_ext)
      apply (rule new_ptr_sp)
     apply (rule copy_ptr_sp_pretty)+
  apply (rule hoare_strengthen_post[OF delete_ptr_sp'])
    apply (clarsimp simp: sep_conj_exists2 sep_conj_assoc exs_def)
  apply (septract_cancel , (clarsimp simp: sep_conj_assoc)?)+
 apply (sep_solve)
done

lemma swap_ptr_valid_pretty: "\<lbrace>(p \<mapsto> v \<and>* p' \<mapsto> v' \<and>* R)\<rbrace> swap_ptr p p' \<lbrace>\<lambda>_. (p \<mapsto> v' \<and>* p' \<mapsto> v \<and>* R)\<rbrace>"
   apply (clarsimp simp: swap_ptr_def)
   apply (wp delete_ptr_valid)
   apply (wp copy_ptr_valid_pretty new_ptr_wp)+ 
   apply (clarsimp simp: sep_conj_exists exs_def)
   apply (sep_cancel)
   apply (rule_tac x=v in exI)
   apply (sep_cancel)+
   apply (rule_tac x=v' in exI)
   apply (sep_cancel add: maps_to_maps_to_ex)+
   apply (rule exI)
   by (sep_solve add: maps_to_maps_to_ex)

lemma swap_ptr_wp_problem: "(p \<mapsto> v \<and>* p' \<mapsto> v' \<and>* R) s \<Longrightarrow>
         \<forall>x. (x \<mapsto> - \<longrightarrow>*
              (exs pv. p \<mapsto> pv \<and>*
                    (p \<mapsto> pv \<longrightarrow>*
                     x \<mapsto> - \<and>*
                     (x \<mapsto> pv \<longrightarrow>*
                      (exs pv'. p' \<mapsto> pv' \<and>*
                            (p' \<mapsto> pv' \<longrightarrow>*
                             p \<mapsto> - \<and>* (p \<mapsto> pv' \<longrightarrow>* (exs y. x \<mapsto> y \<and>* (x \<mapsto> y \<longrightarrow>* p' \<mapsto> - \<and>* (p' \<mapsto> y \<longrightarrow>* x \<mapsto> - \<and>* p \<mapsto> v' \<and>* p' \<mapsto> v \<and>* R))))))))))
              s"
     apply (clarsimp simp: sep_conj_exists exs_def)
      apply (sep_cancel)
   apply (rule_tac x=v in exI)
   apply (sep_cancel)+
   apply (rule_tac x=v' in exI)
   apply (sep_cancel add: maps_to_maps_to_ex)+
   apply (rule exI)
   by (sep_solve add: maps_to_maps_to_ex)

lemma swap_ptr_sp_problem: 
    "\<exists>np. (np \<mapsto> - -*
        (exs x. p' \<mapsto> x \<and>*
             (p' \<mapsto> - -*
              np \<mapsto> x \<and>*
              (np \<mapsto> x -*
               (exs x. p \<mapsto> x \<and>* (p \<mapsto> - -* p' \<mapsto> x \<and>* (p' \<mapsto> x -* (exs x. np \<mapsto> x \<and>* (np \<mapsto> - -* p \<mapsto> x \<and>* (p \<mapsto> x -* np \<mapsto> - \<and>* p \<mapsto> v \<and>* p' \<mapsto> v' \<and>* R))))))))))
        s \<Longrightarrow>
       (p \<mapsto> v' \<and>* p' \<mapsto> v \<and>* R) s"
  apply (clarsimp simp: sep_conj_exists2 sep_conj_assoc exs_def)
  apply (septract_cancel , (clarsimp simp: sep_conj_assoc)?)+
 apply (sep_solve)
done
   



notation (output)
  Unified_Correctness.valid ("\<lbrace>_\<rbrace>/ _ /\<lbrace>_\<rbrace>")

syntax (no_break output)
  "_do_block" :: "do_binds \<Rightarrow> 'a" ("do { (_) }" [12] 62)
  "_do_cons" :: "[do_bind, do_binds] \<Rightarrow> do_binds" ("_; _" [13, 12] 12)


(* lifted meta implication *)
definition
  ximp :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> prop"
where
  "ximp P Q \<equiv> (\<And>s. P s \<Longrightarrow> Q s)"

notation (output)
  ximp (infixr "\<Longrightarrow>" 0)

declare ximp_def [simp]

notation (XRule output)
  ximp  ("\<^latex>\<open>\\mbox{}\\inferrule{\\mbox{\<close>_\<^latex>\<open>}}\<close>\<^latex>\<open>{\\mbox{\<close>_\<^latex>\<open>}}\<close>")

(* would be nice but we can't extract the premises/conclusion using the (concl|prem) attribute *)

ML \<open>
fun strip_ximp_concl (Const(@{const_name "ximp"}, _) $ _ $ B) = strip_ximp_concl B
  | strip_ximp_concl A = A : term;

fun strip_ximp_prems (Const(@{const_name "ximp"}, _) $ A $ B) = A :: strip_ximp_prems B
  | strip_ximp_prems _ = [];

val style_xprem = Parse.nat >> (fn i => fn ctxt => fn t =>
  let
    val prems = strip_ximp_prems t;
  in
    if i <= length prems then nth prems (i - 1)
    else
      error ("Not enough premises for prem " ^ string_of_int i ^
        " in propositon: " ^ Syntax.string_of_term ctxt t)
  end);
\<close>

setup \<open>
  Term_Style.setup @{binding xprem} style_xprem #>
  Term_Style.setup @{binding xconcl} (Scan.succeed (K strip_ximp_concl))
\<close>

lemma swap_ptr_wp_problem_ximp: "PROP ximp (p \<mapsto> v \<and>* p' \<mapsto> v' \<and>* R) 
         (alls x. (x \<mapsto> - \<longrightarrow>*
              (exs pv. p \<mapsto> pv \<and>*
                    (p \<mapsto> pv \<longrightarrow>*
                     x \<mapsto> - \<and>*
                     (x \<mapsto> pv \<longrightarrow>*
                      (exs pv'. p' \<mapsto> pv' \<and>*
                            (p' \<mapsto> pv' \<longrightarrow>*
                             p \<mapsto> - \<and>* (p \<mapsto> pv' \<longrightarrow>* (exs y. x \<mapsto> y \<and>* (x \<mapsto> y \<longrightarrow>* p' \<mapsto> - \<and>* (p' \<mapsto> y \<longrightarrow>* x \<mapsto> - \<and>* p \<mapsto> v' \<and>* p' \<mapsto> v \<and>* R)))))))))))
              "
 unfolding ximp_def alls_def
 by (rule swap_ptr_wp_problem)

lemma swap_ptr_sp_problem_ximp: 
    "PROP ximp (exs np. (np \<mapsto> - -*
        (exs x. p' \<mapsto> x \<and>*
             (p' \<mapsto> - -*
              np \<mapsto> x \<and>*
              (np \<mapsto> x -*
               (exs x. p \<mapsto> x \<and>* (p \<mapsto> - -* p' \<mapsto> x \<and>* (p' \<mapsto> x -* (exs x. np \<mapsto> x \<and>* (np \<mapsto> - -* p \<mapsto> x \<and>* (p \<mapsto> x -* np \<mapsto> - \<and>* p \<mapsto> v \<and>* p' \<mapsto> v' \<and>* R))))))))))
        ) 
       (p \<mapsto> v' \<and>* p' \<mapsto> v \<and>* R) "
  apply (clarsimp simp: sep_conj_exists2 sep_conj_assoc exs_def)
  apply (septract_cancel , (clarsimp simp: sep_conj_assoc)?)+
 apply (sep_solve)
done

definition "invisible = undefined"

notation (latex output) invisible ("")


definition "pred_impl P Q = (\<forall>s. P s \<longrightarrow> Q s)"
         

theorem sep_wp:
  "(\<And>R. \<lbrace>(P \<and>* R) \<rbrace> f \<lbrace>\<lambda>rv. (Q rv \<and>* R)\<rbrace>) \<Longrightarrow> \<lbrace>(P \<and>* (ALLS x. (Q x \<longrightarrow>* R x)))\<rbrace> f \<lbrace> R\<rbrace>"  
  by (erule strong_sep_impl_sep_wp_rv)

thm maps_to_maps_to_ex[no_vars]

lemma maps_to_maps_to_ex':
  "PROP ximp (p \<mapsto> v) (p \<mapsto> -)"
  by auto

lemma sep_cancellation: "pred_impl R  R' \<Longrightarrow> PROP ximp (P \<and>* R) (P \<and>* R')"
  unfolding ximp_def pred_impl_def
  apply (rule sep_erule, assumption+)
  apply simp
  done

lemma new_ptr_valid: "\<lbrace>R\<rbrace> new_ptr \<lbrace>\<lambda>rv. (rv \<mapsto> - \<and>* R )\<rbrace>"
 by (rule new_ptr_sp)



(* added by PH *)
lemma delete_ptr_valid_simple: "\<lbrace>p \<mapsto> -\<rbrace> delete_ptr p \<lbrace>\<lambda>_. \<box> \<rbrace>"
  by (metis delete_ptr_valid sep.right_neutral)

lemma set_ptr_valid: "\<lbrace>(p \<mapsto> - \<and>* R )\<rbrace> set_ptr p v \<lbrace>\<lambda>_. (p \<mapsto> v \<and>* R) \<rbrace>"
 apply (wp set_ptr_wp, sep_solve)
done




lemma get_ptr_valid: "\<lbrace>(p \<mapsto> x \<and>* R x )\<rbrace> get_ptr p  \<lbrace>\<lambda>rv. (p \<mapsto> rv \<and>* R rv) \<rbrace>"
  apply (wp get_ptr_wp, rule_tac x=x in exI, sep_solve)
  done

lemma sep_septraction_subheap': "(\<And>s. R s \<Longrightarrow> (P \<and>* (\<lambda>s. True)) s) \<equiv>  (\<And>s. R s \<Longrightarrow> (P \<and>* (P -* R)) s)" 
  apply (rule) 
   apply (clarsimp simp: sep_conj_def)
   apply (atomize)
   apply (erule allE, drule (1) mp, clarsimp)
   apply (rule_tac x=x in exI, rule_tac x=y in exI, clarsimp)
   apply (clarsimp simp: septraction_def pred_neg_def sep_impl_def)
   apply (rule_tac x=x in exI)
   apply (clarsimp simp: sep_disj_commute sep_add_commute)
  apply (atomize)
  apply (erule allE, drule (1) mp)
  apply (sep_solve)
  done

lemma sep_septraction_subheap: "PROP ximp R (P \<and>* (\<lambda>s. True)) \<equiv> PROP ximp R (P \<and>* (P -* R))" 
  by (auto simp: sep_septraction_subheap')

lemma bad_strongest_post: 
"(\<And>s. R s \<Longrightarrow> (P \<and>* sep_true) s) \<Longrightarrow> (\<And>s. (Q \<and>* (P -* R)) s \<Longrightarrow> R' s) \<Longrightarrow>
   (\<And>R. \<lbrace>(P \<and>* R)\<rbrace> f \<lbrace>\<lambda>_. (Q \<and>* R)\<rbrace>) \<Longrightarrow>
   \<lbrace>R\<rbrace> f \<lbrace>\<lambda>_. R'\<rbrace>"
  apply (rule NonDetMonadVCG.hoare_chain)
    apply (atomize)
    apply (erule_tac x="(P -* R)" in allE, assumption)
   apply (metis sep_antimp' sep_snake_mp)
  apply (fastforce)
  done

lemma sep_antimp: "PROP ximp P (Q \<leadsto>* (Q -* P))" unfolding ximp_def by (drule sep_antimp', blast)    
lemma sep_mp: "(P \<and>* (P \<longrightarrow>* Q)) s \<Longrightarrow> (Q) s" by sep_solve   

notation (latex output) maps_to_ex ("_ \<^latex>\<open>\\!\<close>\<mapsto> \<^latex>\<open>\\!\\_\<close>")
notation (latex output) maps_to  ("_ \<^latex>\<open>\\!\<close>\<mapsto> \<^latex>\<open>\\!\<close>_")

notation (latex output) Unified_Correctness.maps_to_ex ("_ \<^latex>\<open>\\!\<close>\<mapsto> \<^latex>\<open>\\!\\_\<close>")
notation (latex output) Unified_Correctness.maps_to  ("_ \<^latex>\<open>\\!\<close>\<mapsto> \<^latex>\<open>\\!\<close>_")

notation (latex output) Some ("\<lfloor>_\<rfloor>")
(* added by PH *)
notation (latex output) sep_empty ("emp")
notation (latex output) sep_conj ("_ */ _" [36,36] 36)
notation (latex output) sep_impl ("_ \<longrightarrow>*/ _" [25,25] 25)
notation (latex output) pred_neg ("\<not>_" [40] 40)
notation (latex output) pred_conj (infixl "\<and>" 35)
notation (latex output) pred_impl (infixl "\<Longrightarrow>" 35)
(* notation (latex output) less_eq  ("(_/ \<Rightarrow> \<le> _)"  [51, 51] 50) *)
notation (latex output) sept ("_ -*/ _" [50,50] 50)
notation (latex output) sep_con ("_ */ _" [51,51] 51)
notation (latex output) sep_imp (infix "\<longrightarrow>*" 50)


(* when more parentheses are desired *)
notation (paren)
  sep_conj (infixr "*" 25)

notation (paren output)
  sep_coimpl (infix "\<leadsto>*" 25)

(* Some advance Isabelle output styles by David Greenaway. *)

ML {*
fun map_term_bot f (t $ u) = f (map_term_bot f t $ map_term_bot f u)
  | map_term_bot f (Abs (a, T, t)) = f (Abs (a, T, map_term_bot f t))
  | map_term_bot f t = f t;
*}

definition multiline_equiv where
  "multiline_equiv \<equiv> (op \<equiv>)"
notation (latex output) multiline_equiv ("(_) \<equiv>//\<^latex>\<open>\\phantom{mm}\<close>(_)")

(* Split a definition across multiple lines with a little indentation. *)
ML {*
val split_def = map_term_bot
  (fn t =>
     case t of
       (Const (@{const_name "Pure.eq"}, T) $ L $ R) =>
         (Const (@{const_name multiline_equiv}, T) $ L $ R)
     | x => x)
*}

setup {* Term_Style.setup @{binding split_def} (Scan.succeed (K split_def)) *}

(*
definition "sept_naive P Q \<equiv> (\<lambda>s. (\<exists>h h'. P h \<and> Q h' \<and> 
                              (h \<preceq> h' \<longleftrightarrow> (flag h' = flag h \<and> flag s) ) \<and>
                              (flag s \<and> flag h \<longrightarrow> s ## h \<and> (h' = h + s) )  ))" 

lemma "sept_naive flag (not flag) s \<Longrightarrow> \<not> flag s" 
   apply (clarsimp simp: sept_naive_def pred_neg_def plus_prod_def plus_bool_def)
done
*)
definition
  "sep_true' \<equiv> \<langle>True\<rangle>"

definition
  "sep_false' \<equiv> \<langle>False\<rangle>"

notation (latex output) sep_true' ("True") (* or any other symbol *)
notation (latex output) sep_false' ("False")


(*
ML {*
val backslash = "\\"

(* Quote unscore characters with single quotes to go into Isabelle's syntax printer. *)
fun quote_underscores s =
let
  fun q [] = []
    | q (#"_"::xs) = (#"'" :: #"_" :: (q xs))
    | q (#"'"::xs) = (#"'" :: #"'" :: (q xs))
    | q (x::xs) = x::(q xs)
in
  String.explode s |> (fn x => q x) |> String.implode
end

(* Setup constants to emit in latex surrounded by the "isafun" macro. *)
fun setup_const name =
  Specification.notation_cmd true ("", false)
    [(name, Delimfix (backslash ^ "<^raw:" ^ backslash ^ "isafun{>" ^ (quote_underscores name) ^ backslash ^ "<^raw:}>"))]

fun setup_consts consts lthy = fold setup_const consts lthy
*}

local_setup {*
setup_consts [
  "return", "bind", "range",
  "None", "Some", "id", "the"
]
*}
*)

(* Peter's add ons - please check carefully since I am not an expert in Isabelle *)
(* not all theories are needed (any more)*)
  
lemma conj_impl_curry:
  "PROP ximp (P \<and>* Q) R \<Longrightarrow> PROP ximp P (Q \<longrightarrow>* R)"
  by (simp add: sep_conj_sep_impl)
  
lemma conj_impl_curry_prettyprint:
  "PROP ximp (P \<and>* Q) R \<Longrightarrow> PROP ximp P (Q \<longrightarrow>* R)"
  by (simp add: sep_conj_sep_impl)
    
lemma conj_impl_decurry:
  "PROP ximp P (Q \<longrightarrow>* R) \<Longrightarrow> PROP ximp (P \<and>* Q) R" 
  unfolding  ximp_def using sep_conj_sep_impl2 by blast

lemma conj_impl_decurry_prettyprint:
  "PROP ximp P (Q \<longrightarrow>* R) \<Longrightarrow> PROP ximp (P \<and>* Q) R" 
  unfolding  ximp_def using sep_conj_sep_impl2 by blast
    
(*lemma conj_impl__Galois:
  "(\<And>h. P h \<Longrightarrow> (Q \<longrightarrow>* R) h) \<equiv> (\<And>h. (P \<and>* Q) h \<Longrightarrow> R h)" 
(* immediately from  conj_impl_curry  conj_impl_decurry *)
  sorry
*)
lemma conj_impl_inference:
  "PROP ximp (Q \<and>* (Q \<longrightarrow>* P)) P"
  unfolding ximp_def
  apply (sep_solve)
  done

lemma sept_impl_dual:
  "(P -* Q) = (not (P \<longrightarrow>* (not Q)))"
  by (simp add: septraction_def)

lemma conj_semantics: (*just renaming of sep_conj_def *)
  "P \<and>* Q \<equiv> \<lambda>h. \<exists>h\<^sub>1 h\<^sub>2. h\<^sub>1 ## h\<^sub>2 \<and> h = h\<^sub>1 + h\<^sub>2 \<and> P h\<^sub>1 \<and> Q h\<^sub>2" 
  by(rule sep_conj_def)
    
lemma sep_impl_def_rename:
  "P \<longrightarrow>* Q \<equiv> \<lambda>h. \<forall>h\<^sub>1. h ## h\<^sub>1 \<and> P h\<^sub>1 \<longrightarrow> Q (h + h\<^sub>1)"
  by(rule sep_impl_def)
  
lemma septration_semantics':
  "(P -* Q) = (\<lambda>h. \<exists>h\<^sub>1 h\<^sub>2. h\<^sub>1 ## h \<and> h\<^sub>2 = h\<^sub>1 + h \<and> P h\<^sub>1 \<and> Q h\<^sub>2)"
  apply (clarsimp simp: septraction_def sep_impl_def pred_neg_def) 
  using sep_add_commute sep_disj_commuteI by fastforce 

lemma septration_semantics:
  "P -* Q \<equiv> \<lambda>h. \<exists>h\<^sub>1 h\<^sub>2. h\<^sub>1 ## h \<and> h\<^sub>2 = h\<^sub>1 + h \<and> P h\<^sub>1 \<and> Q h\<^sub>2"
  by (simp add: septration_semantics')
 
lemma snake_semantics':
  "(P \<leadsto>* Q) = (\<lambda> h. \<forall> h\<^sub>1 h\<^sub>2. h\<^sub>1 ## h\<^sub>2 \<and> h = h\<^sub>1 + h\<^sub>2 \<and> P h\<^sub>1 \<longrightarrow> Q h\<^sub>2)"
  apply (clarsimp simp: sep_coimpl_def sep_conj_def pred_neg_def) 
  by blast
    
lemma snake_semantics:
  "P \<leadsto>* Q \<equiv> \<lambda>h. \<forall> h\<^sub>1 h\<^sub>2. h\<^sub>1 ## h\<^sub>2 \<and> h = h\<^sub>1 + h\<^sub>2 \<and> P h\<^sub>1 \<longrightarrow> Q h\<^sub>2"
  by (simp add: snake_semantics')

lemma sep_snake_curry: 
  "PROP ximp (P -* Q) R \<Longrightarrow> PROP ximp Q (P \<leadsto>* R)"    
  by (simp add: sep_snake_septraction)

lemma sep_snake_curry_prettyprint: 
  "PROP ximp (P -* Q) R \<Longrightarrow> PROP ximp Q (P \<leadsto>* R)"    
  by (simp add: sep_snake_septraction)

lemma sep_snake_decurry:
  "PROP ximp Q (P \<leadsto>* R) \<Longrightarrow> PROP ximp (P -* Q) R"    
  unfolding ximp_def using sep_septraction_snake by blast

lemmas sep_snake_decurry_prettyprint = sep_snake_decurry
(*
  "\<lbrakk>(\<And>h. Q h \<Longrightarrow> (P \<leadsto>* R) h); (P -* Q) h\<rbrakk> \<Longrightarrow> R h"    
  using sep_septraction_snake by blast  
*)
    (*   
lemma snake_sept_Galois:
  "(\<And>h. R h \<Longrightarrow> (P \<leadsto>* Q) h) \<equiv> (\<And>h. (P \<and>* Q) h \<Longrightarrow> R h)" 
  (* immediately from  snake_sept_curry  snake_sept_decurry *)
  sorry
*)
    
lemma sep_snake_inf:
  "PROP ximp (Q -* ( Q \<leadsto>* P)) P"
  unfolding ximp_def by (rule septraction_snake_trivial)

lemma p_snake_false:
  "(P \<leadsto>* sep_false') = (\<lambda>h. \<forall> h\<^sub>1 h\<^sub>2. h\<^sub>1 ## h\<^sub>2 \<and> h = h\<^sub>1 + h\<^sub>2 \<longrightarrow> \<not>(P h\<^sub>1))"
  apply (clarsimp simp: sep_true'_def sep_false'_def)
  by (fastforce simp: sep_coimpl_def pred_neg_def sep_conj_def)


lemma p_snake_false_subheap:
  "(P \<leadsto>* sep_false') = (\<lambda>h. \<forall> h\<^sub>1. h\<^sub>1 \<preceq> h \<longrightarrow> \<not>(P h\<^sub>1))"  
  apply (subst p_snake_false)
  apply (rule ext, rule iffI;  clarsimp)
   apply (metis sep_substate_def)
  apply (metis sep_substate_def)
  done
    
lemma precise_pretty_print:
  "precise P \<equiv> \<forall> h h\<^sub>1 h\<^sub>2. h\<^sub>1 \<preceq> h \<and> P h\<^sub>1 \<and> h\<^sub>2 \<preceq> h \<and> P h\<^sub>2 \<longrightarrow> h\<^sub>1 =  h\<^sub>2"
  unfolding precise_def
  by(simp)

definition
  "pred_impl2 P Q R \<equiv> \<forall>h. P h \<longrightarrow> Q h \<longrightarrow> R h"

notation (output)
  pred_impl2 ("_ \<Longrightarrow> _ \<Longrightarrow> _")

notation (XRule output)
  pred_impl2  ("\<^latex>\<open>\\mbox{}\\inferrule{\\mbox{\<close>_\<^latex>\<open>}\\qquad\\mbox{\<close>_\<^latex>\<open>}}{\\mbox{\<close>_\<^latex>\<open>}}\<close>")

lemma conj_snake_mp': 
  "(P \<leadsto>* Q) h \<Longrightarrow>  (P \<and>* R) h \<Longrightarrow>  (P \<and>* (Q and R) ) h"
  by (smt pred_andI sep_conj_def snake_semantics)

lemma conj_snake_mp:
  "pred_impl2 (P \<leadsto>* Q) (P \<and>* R) (P \<and>* (Q and R))"
  by (simp add: pred_impl2_def conj_snake_mp')

lemma conj_snake_mt': 
  "(P \<leadsto>* (not Q)) h \<Longrightarrow> (P \<and>* R) h \<Longrightarrow> (((not Q) and R) \<and>* P)h" 
  apply (sep_drule (direct) sep_conj_coimpl_contrapos_mp[where P=R])
   apply (subst sep_coimpl_contrapos, clarsimp simp: pred_neg_def, assumption)
  apply (clarsimp simp: pred_neg_def pred_conj_def conj_commute)
  apply (sep_solve)
  done

lemma conj_snake_mt: 
  "pred_impl2 (P \<leadsto>* (not Q)) (P \<and>* R) (((not Q) and R) \<and>* P)" 
  by (simp add: pred_impl2_def conj_snake_mt')  

lemma precise_characterise_var_inclheap: 
  "precise P = (\<forall> R h. (P \<and>* R) h \<longrightarrow> (P \<leadsto>* R) h)"
  using conj_coimpl_precise precise_conj_coimpl' by blast

lemma precise_characterise_var:
  "precise P = (\<forall>R. pred_impl (P \<and>* R) (P \<leadsto>* R))"
  using conj_coimpl_precise precise_conj_coimpl' pred_impl_def by fastforce

lemma septraction_precise_conj':
  "precise P \<Longrightarrow> PROP ximp (P -* (P \<and>* R)) R"
  unfolding ximp_def by (rule septraction_precise_conj)

(* (P \<and>\<^emph> R) h \<longrightarrow> (P \<leadsto>\<^emph> R) h
lemma disjointness_equiv: "(\<forall>P (s :: 'a :: sep_algebra). strictly_exact P \<longrightarrow> \<not>P 0 \<longrightarrow> (P \<leadsto>* (P \<leadsto>* sep_false)) s) = (\<forall>(h :: 'a). h ## h \<longrightarrow> h = 0)"
*) 
lemma septraction_precise_conj_rename: "precise P \<Longrightarrow> PROP ximp (P -* (P \<and>* R)) R"
  unfolding ximp_def by (rule septraction_precise_conj)


lemma 	some_name: 
 "PROP ximp (P \<longrightarrow>* (R and (P \<leadsto>* sep_false'))) ((not P) \<and>* (P \<longrightarrow>* (not R)))"
  apply (clarsimp simp: sep_true'_def sep_false'_def)
  apply (clarsimp simp: sep_impl_def pred_neg_def sep_conj_def sep_coimpl_def)
  by (metis sep_add_commute sep_add_zero sep_disj_commuteI sep_disj_zero)

    
lemma snake_dual: (* I did not want to have a heap *)
   "(P \<leadsto>* Q) = (not (P \<and>* not Q))"
    by (rule ext, clarsimp simp: sep_coimpl_def pred_neg_def)

lemma precise_subdistribute:
  "precise P = (\<forall>Q R. pred_impl ((Q \<and>* P) and (R \<and>* P))  ((Q and R) \<and>* P))"
  unfolding pred_impl_def
  apply (rule iffI)
  apply (clarsimp)
  apply (simp add: conj_snake_mp' precise_conj_coimpl sep_conj_commuteI)
  apply (clarsimp simp: precise_def)
  apply (clarsimp simp: sep_substate_def)
  apply (erule_tac x="\<lambda>h. h = z" in allE)
  apply (erule_tac x="\<lambda>h. h = za" in allE)
  apply (erule_tac x="hp' + za" in allE)
  apply (clarsimp simp: pred_conj_def sep_conj_def)
  apply (drule mp)
  apply (safe) 
  using sep_add_commute sep_disj_commuteI apply blast
  using sep_add_commute sep_disj_commuteI apply force
  using Extended_Separation_Algebra.cancellative_sep_algebra_class.sep_add_cancel by blast


lemma snake_impl1': "(P \<leadsto>* Q) s \<Longrightarrow> pred_impl P' P  \<Longrightarrow> (P' \<leadsto>* Q) s "
  unfolding pred_impl_def
  by (erule sep_coimpl_weaken, fastforce)

lemma snake_impl1: "pred_impl P' P \<Longrightarrow> PROP ximp (P \<leadsto>* Q) (P' \<leadsto>* Q)"
  unfolding ximp_def by (rule snake_impl1')

lemma snake_impl2': "(P \<leadsto>* Q) s \<Longrightarrow> pred_impl Q  Q'  \<Longrightarrow> (P \<leadsto>* Q') s "
  unfolding pred_impl_def
  by (metis sep_snake_inf[unfolded ximp_def] sep_snake_septraction)

lemma snake_impl2: "pred_impl Q  Q' \<Longrightarrow> PROP ximp (P \<leadsto>* Q) (P \<leadsto>* Q')"
  unfolding ximp_def by (rule snake_impl2')

lemma sep_snake_dne': 
  "PROP ximp (sep_true' \<leadsto>* P) ((P \<leadsto>* sep_false') \<leadsto>* sep_false')"
  apply (clarsimp simp: sep_true'_def sep_false'_def)
  by(rule sep_snake_dne)
    
lemma sep_coimpl_dne': "PROP ximp ((P \<leadsto>* sep_false') \<leadsto>* sep_false') (P \<and>* sep_true')"
  apply (clarsimp simp: sep_true'_def sep_false'_def)
  by(rule sep_coimpl_dne)   
    
lemma sep_wp_simple:
 "(\<And>R. \<lbrace>P \<and>* R\<rbrace> f \<lbrace>\<lambda>_. (Q \<and>* R)\<rbrace>) \<equiv>
                (\<And>R. \<lbrace>P \<and>* (Q \<longrightarrow>* R)\<rbrace> f \<lbrace>\<lambda>_. R\<rbrace>)"
  apply (rule)
   apply (smt NonDetMonadVCG.hoare_chain Paper_Defs.sep_mp)
  apply (rule NonDetMonadVCG.hoare_chain, assumption)
   apply (sep_solve)
  apply (sep_solve)
  done

lemma sep_wp_simple':
 "(\<forall>R. \<lbrace>P \<and>* R\<rbrace> f \<lbrace>\<lambda>_. (Q \<and>* R)\<rbrace>) = (\<forall>R. \<lbrace>P \<and>* (Q \<longrightarrow>* R)\<rbrace> f \<lbrace>\<lambda>_. R\<rbrace>)"
  apply (rule)
   apply (smt NonDetMonadVCG.hoare_chain Paper_Defs.sep_mp)
  apply clarify
  apply (rule_tac Q="\<lambda>_. R \<and>* Q" in NonDetMonadVCG.hoare_chain, erule (1) allE)
   apply (sep_solve)
  apply (sep_solve)
  done

lemma copy_ptr_wp': 
  "\<lbrace>exs x. (p \<mapsto> x \<and>* (p \<mapsto> x \<longrightarrow>* p' \<mapsto> - \<and>* (p' \<mapsto> x \<longrightarrow>* R)))\<rbrace> copy_ptr p p' \<lbrace>\<lambda> _. R\<rbrace>"
  unfolding exs_def by(rule copy_ptr_wp)

lemma strong_sep_impl_sep_wp_rv:
  "(\<And>R x. \<lbrace>(P x \<and>* R x)\<rbrace> f \<lbrace>\<lambda>x. (Q x \<and>* R x)\<rbrace>) \<Longrightarrow> \<lbrace>( P x \<and>*  (Q x  \<longrightarrow>* R x) )\<rbrace> f \<lbrace>R \<rbrace>"
  apply (rule NonDetMonadVCG.hoare_chain, assumption)
   apply (sep_solve)
  apply (sep_select_asm 2, erule sep_conj_sep_impl2)
  apply (fastforce)
  done

lemma exsI:
  "(\<And>x. \<lbrace>P x\<rbrace> f \<lbrace>Q\<rbrace>) \<Longrightarrow> \<lbrace>exs x. P x\<rbrace> f \<lbrace>Q\<rbrace>"
  unfolding NonDetMonad.valid_def exs_def by fastforce

lemma get_ptr_valid': "\<lbrace>p \<mapsto> x \<and>* R x\<rbrace> get_ptr p  \<lbrace>\<lambda>rv. (p \<mapsto> rv \<and>* R rv) \<rbrace>"
  by (rule get_ptr_valid)



thm get_ptr_valid'[THEN strong_sep_impl_sep_wp_rv, simplified]
 
lemma get_ptr_valid'': "\<lbrace>exs x. (p \<mapsto> x \<and>* R x)\<rbrace> get_ptr p  \<lbrace>\<lambda>rv. (p \<mapsto> rv \<and>* R rv) \<rbrace>"
  apply (rule exsI)
  apply (rule get_ptr_valid)
  done

lemma get_ptr_valid_pretty: "\<lbrace>exs x. (p \<mapsto> x \<and>* R)\<rbrace> get_ptr p  \<lbrace>\<lambda>rv. (p \<mapsto> rv \<and>* R ) \<rbrace>"
  by(rule get_ptr_valid'')


lemma get_ptr_wp_ex: "\<lbrace>exs x. (p \<mapsto> x \<and>* (p \<mapsto> x \<longrightarrow>* R x ))\<rbrace> get_ptr p \<lbrace>R \<rbrace>"
  apply (rule NonDetMonadVCG.hoare_chain, rule get_ptr_valid'', clarsimp simp: exs_def)
   apply (fastforce)
  apply (sep_solve)
  done

lemma get_ptr_wp: "\<lbrace>(p \<mapsto> x \<and>* (p \<mapsto> x \<longrightarrow>* R x ))\<rbrace> get_ptr p \<lbrace>R \<rbrace>"
  by (wp get_ptr_valid'[THEN strong_sep_impl_sep_wp_rv, simplified])
    
(* 
lemma bad_strongest_post: 
"(\<And>s. R s \<Longrightarrow> (P \<and>* sep_true) s) \<Longrightarrow> (\<And>s. (Q \<and>* (P -* R)) s \<Longrightarrow> R' s) \<Longrightarrow>
   (\<And>R. \<lbrace>(P \<and>* R)\<rbrace> f \<lbrace>\<lambda>_. (Q \<and>* R)\<rbrace>) \<Longrightarrow>
   \<lbrace>R\<rbrace> f \<lbrace>\<lambda>_. R'\<rbrace>"
apply (rule hoare_chain)
apply (atomize)
apply (erule_tac x="(P -* R)" in allE, assumption)
  apply (metis sep_antimp' sep_snake_mp)
apply (fastforce)
done 
*)
lemma bad_strongest_post': 
"\<lbrakk>\<forall>F. \<lbrace>(P \<and>* F)\<rbrace> f \<lbrace>\<lambda>_. (Q \<and>* F)\<rbrace> ;
  (pred_impl R (P \<and>* sep_true')) ; 
  (pred_impl (Q \<and>* (P -* R))  R')\<rbrakk> \<Longrightarrow>  
   \<lbrace>R\<rbrace> f \<lbrace>\<lambda>_. R'\<rbrace>"
  apply(rule bad_strongest_post)
  by(auto simp add:  sep_true'_def pred_impl_def)
  
lemma bad_strongest_post_simple: 
" \<lbrakk>(\<And>F. \<lbrace>(P \<and>* F)\<rbrace> f \<lbrace>\<lambda>_. (Q \<and>* F)\<rbrace>) ; pred_impl R  (P \<and>* sep_true')\<rbrakk> \<Longrightarrow> \<lbrace>R\<rbrace> f \<lbrace>\<lambda>_. (Q \<and>* (P -* R))\<rbrace>"
  apply(rule  bad_strongest_post')
   by(auto simp add:  sep_true'_def pred_impl_def)

lemma bad_strongest_post_simple'': 
" (\<forall>F. \<lbrace>(P \<and>* F)\<rbrace> f \<lbrace>\<lambda>_. (Q \<and>* F)\<rbrace>) \<and> pred_impl R (P \<and>* sep_true') \<Longrightarrow> \<lbrace>R\<rbrace> f \<lbrace>\<lambda>_. (Q \<and>* (P -* R))\<rbrace>"
  apply(rule  bad_strongest_post')
   by(auto simp add:  sep_true'_def pred_impl_def)

lemma subheap_pretty:
  "h\<^sub>1 \<preceq> h \<equiv> \<exists>h\<^sub>2. h\<^sub>1 ## h\<^sub>2 \<and> h\<^sub>1 + h\<^sub>2 = h"
  by(rule sep_substate_def)
  
lemma sep_sp_simple:
 "(\<forall>R. \<lbrace>P \<leadsto>* R\<rbrace> f \<lbrace>\<lambda>_. (Q \<and>* R)\<rbrace>) =
                (\<forall>R. \<lbrace>R\<rbrace> f \<lbrace>\<lambda>_. Q \<and>* (P -* R)\<rbrace>)"
  apply (rule iffI)
  apply (meson hoare_weaken_pre sep_antimp')
  apply (clarsimp)
  apply (erule_tac x="P \<leadsto>* R" in allE)
  apply (erule hoare_strengthen_post)
  apply (sep_cancel)
  using sep_septraction_snake by blast

lemma sep_collapsing':
  "PROP ximp (Nf -& (not Nf)) (not Nf)"
  unfolding ximp_def by (drule sep_collapsing) (simp add: pred_neg_def)

lemma sept_success_prettier':
  "PROP ximp (p \<mapsto>u - -& (p \<mapsto>u - \<and>* (R and Nf))) (R and Nf)"
  unfolding ximp_def by (rule sept_success_prettier)

(* suppress \<lambda>_. Q in postconditions *)
abbreviation
  valid_dc :: "('s \<Rightarrow> bool) \<Rightarrow> ('s,'a) nondet_monad \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> bool"
where
  "valid_dc P f Q \<equiv> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. Q\<rbrace>"

notation (output)
  valid_dc ("\<lbrace>_\<rbrace>/ _ /\<lbrace>_\<rbrace>")

abbreviation
  "validU_dc P f Q \<equiv> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. Q\<rbrace>u"

notation (output)
  validU_dc ("\<lbrace>_\<rbrace>/ _ /\<lbrace>_\<rbrace>u")

(* equality with very low syntax priority to make Isabelle drop parentheses;
   use with thm .. [folded eq'_def]  *)
definition
  "eq' a b = (a = b)"

notation (output)
  eq' (infixl "=" 2)

notation (latex output)
  Unified_Correctness.validNF ("\<lbrace>_\<rbrace> _ \<lbrace>_\<rbrace>")  

notation (latex output) sep_snake (infix "\<leadsto>*" 50)

declare [[eta_contract = false]]
                                                    
adhoc_overloading
  Monad_Syntax.bind NonDetMonad.bind 

syntax
  "_no_bind" :: "'a => dobind"  ("_")
                    
translations
  "_do_block (_do_cons (_no_bind t) (_do_final e))"
    \<rightleftharpoons> "CONST bind_do t (CONST K_bind e)"

lemma sep_con_renamed: 
  "sep_con P Q \<equiv> (\<lambda>h. \<exists>h\<^sub>1 h\<^sub>2. P h\<^sub>1 \<and>  Q h\<^sub>2 \<and>  (if (nf h\<^sub>1 \<and> nf h\<^sub>2) then ( h\<^sub>2 + h\<^sub>1 = h \<and> h\<^sub>1 ## h\<^sub>2) 
                      else (nf h \<longrightarrow>((nf h\<^sub>1 \<longrightarrow> h\<^sub>1 ## h) \<and> (nf h\<^sub>2 \<longrightarrow>  h ## h\<^sub>2)))))"
  by(rule sep_con_def)

lemma sept_renamed:
"sept P Q \<equiv> (\<lambda>h. \<exists>h\<^sub>1 h\<^sub>2. P h\<^sub>1 \<and> Q h\<^sub>2  \<and>
            (if (nf h\<^sub>1 \<and> nf h) then 
                 (h\<^sub>1 + h = h\<^sub>2 \<and> h\<^sub>1 ## h) 
                 else (nf h\<^sub>2 \<longrightarrow> ((nf h\<^sub>1  \<longrightarrow> h\<^sub>1 ## h\<^sub>2) \<and> (nf h \<longrightarrow> h ## h\<^sub>2)))))"
   by(rule sept_def)   
 
lemmas plus_prod_pretty = plus_prod_def[of "h\<^sub>1 :: (nat \<Rightarrow> nat option) \<times> bool" h\<^sub>2]
lemmas sep_disj_prod_pretty = sep_disj_prod_def[of "h\<^sub>1 :: (nat \<Rightarrow> nat option) \<times> bool" h\<^sub>2, unfolded sep_disj_bool_def]

lemma maps_to_renamed:
  "p \<mapsto>u v \<equiv> \<lambda>h. heap h = [p \<mapsto> v] \<and> nf h " 
  by(rule Unified_Correctness.maps_to_def)
    
lemma maps_to_ex_renamed:
  "p \<mapsto>u - \<equiv> (\<lambda>h. \<exists>v. (p \<mapsto>u v) h)"
  by(rule Unified_Correctness.maps_to_ex_def)



    
end