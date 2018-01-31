(*  Title:      CCL/ex/Stream.thy
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge
*)

section \<open>Programs defined over streams\<close>

theory Stream
imports List
begin

definition iter1 :: "[i\<Rightarrow>i,i]\<Rightarrow>i"
  where "iter1(f,a) == letrec iter x be x$iter(f(x)) in iter(a)"

definition iter2 :: "[i\<Rightarrow>i,i]\<Rightarrow>i"
  where "iter2(f,a) == letrec iter x be x$map(f,iter(x)) in iter(a)"

(*
Proving properties about infinite lists using coinduction:
    Lists(A)  is the set of all finite and infinite lists of elements of A.
    ILists(A) is the set of infinite lists of elements of A.
*)


subsection \<open>Map of composition is composition of maps\<close>

lemma map_comp:
  assumes 1: "l:Lists(A)"
  shows "map(f \<circ> g,l) = map(f,map(g,l))"
  apply (eq_coinduct3 "{p. EX x y. p=<x,y> \<and> (EX l:Lists (A) .x=map (f \<circ> g,l) \<and> y=map (f,map (g,l)))}")
   apply (blast intro: 1)
  apply safe
  apply (drule ListsXH [THEN iffD1])
  apply EQgen
   apply fastforce
  done

(*** Mapping the identity function leaves a list unchanged ***)

lemma map_id:
  assumes 1: "l:Lists(A)"
  shows "map(\<lambda>x. x, l) = l"
  apply (eq_coinduct3 "{p. EX x y. p=<x,y> \<and> (EX l:Lists (A) .x=map (\<lambda>x. x,l) \<and> y=l) }")
  apply (blast intro: 1)
  apply safe
  apply (drule ListsXH [THEN iffD1])
  apply EQgen
  apply blast
  done


subsection \<open>Mapping distributes over append\<close>

lemma map_append:
  assumes "l:Lists(A)"
    and "m:Lists(A)"
  shows "map(f,l@m) = map(f,l) @ map(f,m)"
  apply (eq_coinduct3
    "{p. EX x y. p=<x,y> \<and> (EX l:Lists (A). EX m:Lists (A). x=map (f,l@m) \<and> y=map (f,l) @ map (f,m))}")
  apply (blast intro: assms)
  apply safe
  apply (drule ListsXH [THEN iffD1])
  apply EQgen
  apply (drule ListsXH [THEN iffD1])
  apply EQgen
  apply blast
  done


subsection \<open>Append is associative\<close>

lemma append_assoc:
  assumes "k:Lists(A)"
    and "l:Lists(A)"
    and "m:Lists(A)"
  shows "k @ l @ m = (k @ l) @ m"
  apply (eq_coinduct3
    "{p. EX x y. p=<x,y> \<and> (EX k:Lists (A). EX l:Lists (A). EX m:Lists (A). x=k @ l @ m \<and> y= (k @ l) @ m) }")
  apply (blast intro: assms)
  apply safe
  apply (drule ListsXH [THEN iffD1])
  apply EQgen
   prefer 2
   apply blast
  apply (tactic \<open>DEPTH_SOLVE (eresolve_tac @{context} [XH_to_E @{thm ListsXH}] 1
    THEN EQgen_tac @{context} [] 1)\<close>)
  done


subsection \<open>Appending anything to an infinite list doesn't alter it\<close>

lemma ilist_append:
  assumes "l:ILists(A)"
  shows "l @ m = l"
  apply (eq_coinduct3 "{p. EX x y. p=<x,y> \<and> (EX l:ILists (A) .EX m. x=l@m \<and> y=l)}")
  apply (blast intro: assms)
  apply safe
  apply (drule IListsXH [THEN iffD1])
  apply EQgen
  apply blast
  done

(*** The equivalance of two versions of an iteration function       ***)
(*                                                                    *)
(*        fun iter1(f,a) = a$iter1(f,f(a))                            *)
(*        fun iter2(f,a) = a$map(f,iter2(f,a))                        *)

lemma iter1B: "iter1(f,a) = a$iter1(f,f(a))"
  apply (unfold iter1_def)
  apply (rule letrecB [THEN trans])
  apply simp
  done

lemma iter2B: "iter2(f,a) = a $ map(f,iter2(f,a))"
  apply (unfold iter2_def)
  apply (rule letrecB [THEN trans])
  apply (rule refl)
  done

lemma iter2Blemma:
  "n:Nat \<Longrightarrow>  
    map(f) ^ n ` iter2(f,a) = (f ^ n ` a) $ (map(f) ^ n ` map(f,iter2(f,a)))"
  apply (rule_tac P = "\<lambda>x. lhs(x) = rhs" for lhs rhs in iter2B [THEN ssubst])
  apply (simp add: nmapBcons)
  done

lemma iter1_iter2_eq: "iter1(f,a) = iter2(f,a)"
  apply (eq_coinduct3
    "{p. EX x y. p=<x,y> \<and> (EX n:Nat. x=iter1 (f,f^n`a) \<and> y=map (f) ^n`iter2 (f,a))}")
  apply (fast intro!: napplyBzero [symmetric] napplyBzero [symmetric, THEN arg_cong])
  apply (EQgen iter1B iter2Blemma)
  apply (subst napply_f, assumption)
  apply (rule_tac f1 = f in napplyBsucc [THEN subst])
  apply blast
  done

end
