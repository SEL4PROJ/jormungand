(*  Title:      HOL/Auth/Shared.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Theory of Shared Keys (common to all symmetric-key protocols)

Shared, long-term keys; initial states of agents
*)

theory Shared
imports Event All_Symmetric
begin

consts
  shrK    :: "agent => key"  (*symmetric keys*)

specification (shrK)
  inj_shrK: "inj shrK"
  \<comment>\<open>No two agents have the same long-term key\<close>
   apply (rule exI [of _ "case_agent 0 (\<lambda>n. n + 2) 1"]) 
   apply (simp add: inj_on_def split: agent.split) 
   done

text\<open>Server knows all long-term keys; other agents know only their own\<close>

overloading
  initState \<equiv> initState
begin

primrec initState where
  initState_Server:  "initState Server     = Key ` range shrK"
| initState_Friend:  "initState (Friend i) = {Key (shrK (Friend i))}"
| initState_Spy:     "initState Spy        = Key`shrK`bad"

end


subsection\<open>Basic properties of shrK\<close>

(*Injectiveness: Agents' long-term keys are distinct.*)
lemmas shrK_injective = inj_shrK [THEN inj_eq]
declare shrK_injective [iff]

lemma invKey_K [simp]: "invKey K = K"
apply (insert isSym_keys)
apply (simp add: symKeys_def) 
done


lemma analz_Decrypt' [dest]:
     "[| Crypt K X \<in> analz H;  Key K  \<in> analz H |] ==> X \<in> analz H"
by auto

text\<open>Now cancel the \<open>dest\<close> attribute given to
 \<open>analz.Decrypt\<close> in its declaration.\<close>
declare analz.Decrypt [rule del]

text\<open>Rewrites should not refer to  @{term "initState(Friend i)"} because
  that expression is not in normal form.\<close>

lemma keysFor_parts_initState [simp]: "keysFor (parts (initState C)) = {}"
apply (unfold keysFor_def)
apply (induct_tac "C", auto)
done

(*Specialized to shared-key model: no @{term invKey}*)
lemma keysFor_parts_insert:
     "[| K \<in> keysFor (parts (insert X G));  X \<in> synth (analz H) |]
      ==> K \<in> keysFor (parts (G \<union> H)) | Key K \<in> parts H"
by (metis invKey_K keysFor_parts_insert)

lemma Crypt_imp_keysFor: "Crypt K X \<in> H ==> K \<in> keysFor H"
by (metis Crypt_imp_invKey_keysFor invKey_K)


subsection\<open>Function "knows"\<close>

(*Spy sees shared keys of agents!*)
lemma Spy_knows_Spy_bad [intro!]: "A: bad ==> Key (shrK A) \<in> knows Spy evs"
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) add: imageI knows_Cons split: event.split)
done

(*For case analysis on whether or not an agent is compromised*)
lemma Crypt_Spy_analz_bad: "[| Crypt (shrK A) X \<in> analz (knows Spy evs);  A: bad |]  
      ==> X \<in> analz (knows Spy evs)"
by (metis Spy_knows_Spy_bad analz.Inj analz_Decrypt')


(** Fresh keys never clash with long-term shared keys **)

(*Agents see their own shared keys!*)
lemma shrK_in_initState [iff]: "Key (shrK A) \<in> initState A"
by (induct_tac "A", auto)

lemma shrK_in_used [iff]: "Key (shrK A) \<in> used evs"
by (rule initState_into_used, blast)

(*Used in parts_induct_tac and analz_Fake_tac to distinguish session keys
  from long-term shared keys*)
lemma Key_not_used [simp]: "Key K \<notin> used evs ==> K \<notin> range shrK"
by blast

lemma shrK_neq [simp]: "Key K \<notin> used evs ==> shrK B \<noteq> K"
by blast

lemmas shrK_sym_neq = shrK_neq [THEN not_sym]
declare shrK_sym_neq [simp]


subsection\<open>Fresh nonces\<close>

lemma Nonce_notin_initState [iff]: "Nonce N \<notin> parts (initState B)"
by (induct_tac "B", auto)

lemma Nonce_notin_used_empty [simp]: "Nonce N \<notin> used []"
by (simp add: used_Nil)


subsection\<open>Supply fresh nonces for possibility theorems.\<close>

(*In any trace, there is an upper bound N on the greatest nonce in use.*)
lemma Nonce_supply_lemma: "\<exists>N. ALL n. N<=n --> Nonce n \<notin> used evs"
apply (induct_tac "evs")
apply (rule_tac x = 0 in exI)
apply (simp_all (no_asm_simp) add: used_Cons split: event.split)
apply (metis le_sup_iff msg_Nonce_supply)
done

lemma Nonce_supply1: "\<exists>N. Nonce N \<notin> used evs"
by (metis Nonce_supply_lemma order_eq_iff)

lemma Nonce_supply2: "\<exists>N N'. Nonce N \<notin> used evs & Nonce N' \<notin> used evs' & N \<noteq> N'"
apply (cut_tac evs = evs in Nonce_supply_lemma)
apply (cut_tac evs = "evs'" in Nonce_supply_lemma, clarify)
apply (metis Suc_n_not_le_n nat_le_linear)
done

lemma Nonce_supply3: "\<exists>N N' N''. Nonce N \<notin> used evs & Nonce N' \<notin> used evs' &  
                    Nonce N'' \<notin> used evs'' & N \<noteq> N' & N' \<noteq> N'' & N \<noteq> N''"
apply (cut_tac evs = evs in Nonce_supply_lemma)
apply (cut_tac evs = "evs'" in Nonce_supply_lemma)
apply (cut_tac evs = "evs''" in Nonce_supply_lemma, clarify)
apply (rule_tac x = N in exI)
apply (rule_tac x = "Suc (N+Na)" in exI)
apply (rule_tac x = "Suc (Suc (N+Na+Nb))" in exI)
apply (simp (no_asm_simp) add: less_not_refl3 le_add1 le_add2 less_Suc_eq_le)
done

lemma Nonce_supply: "Nonce (@ N. Nonce N \<notin> used evs) \<notin> used evs"
apply (rule Nonce_supply_lemma [THEN exE])
apply (rule someI, blast)
done

text\<open>Unlike the corresponding property of nonces, we cannot prove
    @{term "finite KK ==> \<exists>K. K \<notin> KK & Key K \<notin> used evs"}.
    We have infinitely many agents and there is nothing to stop their
    long-term keys from exhausting all the natural numbers.  Instead,
    possibility theorems must assume the existence of a few keys.\<close>


subsection\<open>Specialized Rewriting for Theorems About @{term analz} and Image\<close>

lemma subset_Compl_range: "A <= - (range shrK) ==> shrK x \<notin> A"
by blast

lemma insert_Key_singleton: "insert (Key K) H = Key ` {K} \<union> H"
by blast

lemma insert_Key_image: "insert (Key K) (Key`KK \<union> C) = Key`(insert K KK) \<union> C"
by blast

(** Reverse the normal simplification of "image" to build up (not break down)
    the set of keys.  Use analz_insert_eq with (Un_upper2 RS analz_mono) to
    erase occurrences of forwarded message components (X). **)

lemmas analz_image_freshK_simps =
       simp_thms mem_simps \<comment>\<open>these two allow its use with \<open>only:\<close>\<close>
       disj_comms 
       image_insert [THEN sym] image_Un [THEN sym] empty_subsetI insert_subset
       analz_insert_eq Un_upper2 [THEN analz_mono, THEN [2] rev_subsetD]
       insert_Key_singleton subset_Compl_range
       Key_not_used insert_Key_image Un_assoc [THEN sym]

(*Lemma for the trivial direction of the if-and-only-if*)
lemma analz_image_freshK_lemma:
     "(Key K \<in> analz (Key`nE \<union> H)) --> (K \<in> nE | Key K \<in> analz H)  ==>  
         (Key K \<in> analz (Key`nE \<union> H)) = (K \<in> nE | Key K \<in> analz H)"
by (blast intro: analz_mono [THEN [2] rev_subsetD])


subsection\<open>Tactics for possibility theorems\<close>

ML
\<open>
structure Shared =
struct

(*Omitting used_Says makes the tactic much faster: it leaves expressions
    such as  Nonce ?N \<notin> used evs that match Nonce_supply*)
fun possibility_tac ctxt =
   (REPEAT 
    (ALLGOALS (simp_tac (ctxt
          delsimps [@{thm used_Says}, @{thm used_Notes}, @{thm used_Gets}] 
          setSolver safe_solver))
     THEN
     REPEAT_FIRST (eq_assume_tac ORELSE' 
                   resolve_tac ctxt [refl, conjI, @{thm Nonce_supply}])))

(*For harder protocols (such as Recur) where we have to set up some
  nonces and keys initially*)
fun basic_possibility_tac ctxt =
    REPEAT 
    (ALLGOALS (asm_simp_tac (ctxt setSolver safe_solver))
     THEN
     REPEAT_FIRST (resolve_tac ctxt [refl, conjI]))


val analz_image_freshK_ss =
  simpset_of
   (@{context} delsimps [image_insert, image_Un]
      delsimps [@{thm imp_disjL}]    (*reduces blow-up*)
      addsimps @{thms analz_image_freshK_simps})

end
\<close>



(*Lets blast_tac perform this step without needing the simplifier*)
lemma invKey_shrK_iff [iff]:
     "(Key (invKey K) \<in> X) = (Key K \<in> X)"
by auto

(*Specialized methods*)

method_setup analz_freshK = \<open>
    Scan.succeed (fn ctxt =>
     (SIMPLE_METHOD
      (EVERY [REPEAT_FIRST (resolve_tac ctxt [allI, ballI, impI]),
          REPEAT_FIRST (resolve_tac ctxt @{thms analz_image_freshK_lemma}),
          ALLGOALS (asm_simp_tac (put_simpset Shared.analz_image_freshK_ss ctxt))])))\<close>
    "for proving the Session Key Compromise theorem"

method_setup possibility = \<open>
    Scan.succeed (fn ctxt => SIMPLE_METHOD (Shared.possibility_tac ctxt))\<close>
    "for proving possibility theorems"

method_setup basic_possibility = \<open>
    Scan.succeed (fn ctxt => SIMPLE_METHOD (Shared.basic_possibility_tac ctxt))\<close>
    "for proving possibility theorems"

lemma knows_subset_knows_Cons: "knows A evs <= knows A (e # evs)"
by (cases e) (auto simp: knows_Cons)

end
