theory BExp imports AExp begin

subsection "Boolean Expressions"

datatype bexp = Bc bool | Not bexp | And bexp bexp | Less aexp aexp

text_raw{*\snip{BExpbvaldef}{1}{2}{% *}
fun bval :: "bexp \<Rightarrow> state \<Rightarrow> bool" where
"bval (Bc v) s = v" |
"bval (Not b) s = (\<not> bval b s)" |
"bval (And b\<^sub>1 b\<^sub>2) s = (bval b\<^sub>1 s \<and> bval b\<^sub>2 s)" |
"bval (Less a\<^sub>1 a\<^sub>2) s = (aval a\<^sub>1 s < aval a\<^sub>2 s)"
text_raw{*}%endsnip*}

value "bval (Less (V ''x'') (Plus (N 3) (V ''y'')))
            <''x'' := 3, ''y'' := 1>"


subsection "Constant Folding"

text{* Optimizing constructors: *}

text_raw{*\snip{BExplessdef}{0}{2}{% *}
fun less :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"less (N n\<^sub>1) (N n\<^sub>2) = Bc(n\<^sub>1 < n\<^sub>2)" |
"less a\<^sub>1 a\<^sub>2 = Less a\<^sub>1 a\<^sub>2"
text_raw{*}%endsnip*}

lemma [simp]: "bval (less a1 a2) s = (aval a1 s < aval a2 s)"
apply(induction a1 a2 rule: less.induct)
apply simp_all
done

text_raw{*\snip{BExpanddef}{2}{2}{% *}
fun "and" :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
"and (Bc True) b = b" |
"and b (Bc True) = b" |
"and (Bc False) b = Bc False" |
"and b (Bc False) = Bc False" |
"and b\<^sub>1 b\<^sub>2 = And b\<^sub>1 b\<^sub>2"
text_raw{*}%endsnip*}

lemma bval_and[simp]: "bval (and b1 b2) s = (bval b1 s \<and> bval b2 s)"
apply(induction b1 b2 rule: and.induct)
apply simp_all
done

text_raw{*\snip{BExpnotdef}{2}{2}{% *}
fun not :: "bexp \<Rightarrow> bexp" where
"not (Bc True) = Bc False" |
"not (Bc False) = Bc True" |
"not b = Not b"
text_raw{*}%endsnip*}

lemma bval_not[simp]: "bval (not b) s = (\<not> bval b s)"
apply(induction b rule: not.induct)
apply simp_all
done

text{* Now the overall optimizer: *}

text_raw{*\snip{BExpbsimpdef}{0}{2}{% *}
fun bsimp :: "bexp \<Rightarrow> bexp" where
"bsimp (Bc v) = Bc v" |
"bsimp (Not b) = not(bsimp b)" |
"bsimp (And b\<^sub>1 b\<^sub>2) = and (bsimp b\<^sub>1) (bsimp b\<^sub>2)" |
"bsimp (Less a\<^sub>1 a\<^sub>2) = less (asimp a\<^sub>1) (asimp a\<^sub>2)"
text_raw{*}%endsnip*}

value "bsimp (And (Less (N 0) (N 1)) b)"

value "bsimp (And (Less (N 1) (N 0)) (Bc True))"

theorem "bval (bsimp b) s = bval b s"
apply(induction b)
apply simp_all
done

end
