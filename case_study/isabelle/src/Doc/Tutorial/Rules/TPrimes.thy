(* EXTRACT from HOL/ex/Primes.thy*)

(*Euclid's algorithm 
  This material now appears AFTER that of Forward.thy *)
theory TPrimes imports Main begin

fun gcd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "gcd m n = (if n=0 then m else gcd n (m mod n))"


text {*Now in Basic.thy!
@{thm[display]"dvd_def"}
\rulename{dvd_def}
*}


(*** Euclid's Algorithm ***)

lemma gcd_0 [simp]: "gcd m 0 = m"
apply (simp)
done

lemma gcd_non_0 [simp]: "0<n \<Longrightarrow> gcd m n = gcd n (m mod n)"
apply (simp)
done

declare gcd.simps [simp del]

(*gcd(m,n) divides m and n.  The conjunctions don't seem provable separately*)
lemma gcd_dvd_both: "(gcd m n dvd m) \<and> (gcd m n dvd n)"
apply (induct_tac m n rule: gcd.induct)
  --{* @{subgoals[display,indent=0,margin=65]} *}
apply (case_tac "n=0")
txt{*subgoals after the case tac
@{subgoals[display,indent=0,margin=65]}
*}
apply (simp_all) 
  --{* @{subgoals[display,indent=0,margin=65]} *}
by (blast dest: dvd_mod_imp_dvd)



text {*
@{thm[display] dvd_mod_imp_dvd}
\rulename{dvd_mod_imp_dvd}

@{thm[display] dvd_trans}
\rulename{dvd_trans}
*}

lemmas gcd_dvd1 [iff] = gcd_dvd_both [THEN conjunct1]
lemmas gcd_dvd2 [iff] = gcd_dvd_both [THEN conjunct2]


text {*
\begin{quote}
@{thm[display] gcd_dvd1}
\rulename{gcd_dvd1}

@{thm[display] gcd_dvd2}
\rulename{gcd_dvd2}
\end{quote}
*}

(*Maximality: for all m,n,k naturals, 
                if k divides m and k divides n then k divides gcd(m,n)*)
lemma gcd_greatest [rule_format]:
      "k dvd m \<longrightarrow> k dvd n \<longrightarrow> k dvd gcd m n"
apply (induct_tac m n rule: gcd.induct)
apply (case_tac "n=0")
txt{*subgoals after the case tac
@{subgoals[display,indent=0,margin=65]}
*}
apply (simp_all add: dvd_mod)
done

text {*
@{thm[display] dvd_mod}
\rulename{dvd_mod}
*}

(*just checking the claim that case_tac "n" works too*)
lemma "k dvd m \<longrightarrow> k dvd n \<longrightarrow> k dvd gcd m n"
apply (induct_tac m n rule: gcd.induct)
apply (case_tac "n")
apply (simp_all add: dvd_mod)
done


theorem gcd_greatest_iff [iff]: 
        "(k dvd gcd m n) = (k dvd m \<and> k dvd n)"
by (blast intro!: gcd_greatest intro: dvd_trans)


(**** The material below was omitted from the book ****)

definition is_gcd :: "[nat,nat,nat] \<Rightarrow> bool" where        (*gcd as a relation*)
    "is_gcd p m n == p dvd m  \<and>  p dvd n  \<and>
                     (ALL d. d dvd m \<and> d dvd n \<longrightarrow> d dvd p)"

(*Function gcd yields the Greatest Common Divisor*)
lemma is_gcd: "is_gcd (gcd m n) m n"
apply (simp add: is_gcd_def gcd_greatest)
done

(*uniqueness of GCDs*)
lemma is_gcd_unique: "\<lbrakk> is_gcd m a b; is_gcd n a b \<rbrakk> \<Longrightarrow> m=n"
apply (simp add: is_gcd_def)
apply (blast intro: dvd_antisym)
done


text {*
@{thm[display] dvd_antisym}
\rulename{dvd_antisym}

\begin{isabelle}
proof\ (prove):\ step\ 1\isanewline
\isanewline
goal\ (lemma\ is_gcd_unique):\isanewline
\isasymlbrakk is_gcd\ m\ a\ b;\ is_gcd\ n\ a\ b\isasymrbrakk \ \isasymLongrightarrow \ m\ =\ n\isanewline
\ 1.\ \isasymlbrakk m\ dvd\ a\ \isasymand \ m\ dvd\ b\ \isasymand \ (\isasymforall d.\ d\ dvd\ a\ \isasymand \ d\ dvd\ b\ \isasymlongrightarrow \ d\ dvd\ m);\isanewline
\ \ \ \ \ \ \ n\ dvd\ a\ \isasymand \ n\ dvd\ b\ \isasymand \ (\isasymforall d.\ d\ dvd\ a\ \isasymand \ d\ dvd\ b\ \isasymlongrightarrow \ d\ dvd\ n)\isasymrbrakk \isanewline
\ \ \ \ \isasymLongrightarrow \ m\ =\ n
\end{isabelle}
*}

lemma gcd_assoc: "gcd (gcd k m) n = gcd k (gcd m n)"
  apply (rule is_gcd_unique)
  apply (rule is_gcd)
  apply (simp add: is_gcd_def)
  apply (blast intro: dvd_trans)
  done

text{*
\begin{isabelle}
proof\ (prove):\ step\ 3\isanewline
\isanewline
goal\ (lemma\ gcd_assoc):\isanewline
gcd\ (gcd\ (k,\ m),\ n)\ =\ gcd\ (k,\ gcd\ (m,\ n))\isanewline
\ 1.\ gcd\ (k,\ gcd\ (m,\ n))\ dvd\ k\ \isasymand \isanewline
\ \ \ \ gcd\ (k,\ gcd\ (m,\ n))\ dvd\ m\ \isasymand \ gcd\ (k,\ gcd\ (m,\ n))\ dvd\ n
\end{isabelle}
*}


lemma gcd_dvd_gcd_mult: "gcd m n dvd gcd (k*m) n"
  apply (auto intro: dvd_trans [of _ m])
  done

(*This is half of the proof (by dvd_antisym) of*)
lemma gcd_mult_cancel: "gcd k n = 1 \<Longrightarrow> gcd (k*m) n = gcd m n"
  oops

end
