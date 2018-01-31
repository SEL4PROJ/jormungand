chapter \<open>The Owicki-Gries Method\<close>

section \<open>Abstract Syntax\<close>

theory OG_Com imports Main begin

text \<open>Type abbreviations for boolean expressions and assertions:\<close>

type_synonym 'a bexp = "'a set"
type_synonym 'a assn = "'a set"

text \<open>The syntax of commands is defined by two mutually recursive
datatypes: \<open>'a ann_com\<close> for annotated commands and \<open>'a
com\<close> for non-annotated commands.\<close>

datatype 'a ann_com =
     AnnBasic "('a assn)"  "('a \<Rightarrow> 'a)"
   | AnnSeq "('a ann_com)"  "('a ann_com)"
   | AnnCond1 "('a assn)"  "('a bexp)"  "('a ann_com)"  "('a ann_com)"
   | AnnCond2 "('a assn)"  "('a bexp)"  "('a ann_com)"
   | AnnWhile "('a assn)"  "('a bexp)"  "('a assn)"  "('a ann_com)"
   | AnnAwait "('a assn)"  "('a bexp)"  "('a com)"
and 'a com =
     Parallel "('a ann_com option \<times> 'a assn) list"
   | Basic "('a \<Rightarrow> 'a)"
   | Seq "('a com)"  "('a com)"
   | Cond "('a bexp)"  "('a com)"  "('a com)"
   | While "('a bexp)"  "('a assn)"  "('a com)"

text \<open>The function \<open>pre\<close> extracts the precondition of an
annotated command:\<close>

primrec pre ::"'a ann_com \<Rightarrow> 'a assn"  where
  "pre (AnnBasic r f) = r"
| "pre (AnnSeq c1 c2) = pre c1"
| "pre (AnnCond1 r b c1 c2) = r"
| "pre (AnnCond2 r b c) = r"
| "pre (AnnWhile r b i c) = r"
| "pre (AnnAwait r b c) = r"

text \<open>Well-formedness predicate for atomic programs:\<close>

primrec atom_com :: "'a com \<Rightarrow> bool" where
  "atom_com (Parallel Ts) = False"
| "atom_com (Basic f) = True"
| "atom_com (Seq c1 c2) = (atom_com c1 \<and> atom_com c2)"
| "atom_com (Cond b c1 c2) = (atom_com c1 \<and> atom_com c2)"
| "atom_com (While b i c) = atom_com c"

end
