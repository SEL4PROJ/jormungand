(*  Title:      Sequents/Sequents.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge
*)

section \<open>Parsing and pretty-printing of sequences\<close>

theory Sequents
imports Pure
keywords "print_pack" :: diag
begin

setup Pure_Thy.old_appl_syntax_setup

declare [[unify_trace_bound = 20, unify_search_bound = 40]]

typedecl o


subsection \<open>Sequences\<close>

typedecl seq'
consts
 SeqO'         :: "[o,seq']\<Rightarrow>seq'"
 Seq1'         :: "o\<Rightarrow>seq'"


subsection \<open>Concrete syntax\<close>

nonterminal seq and seqobj and seqcont

syntax
 "_SeqEmp"         :: seq                                  ("")
 "_SeqApp"         :: "[seqobj,seqcont] \<Rightarrow> seq"            ("__")

 "_SeqContEmp"     :: seqcont                              ("")
 "_SeqContApp"     :: "[seqobj,seqcont] \<Rightarrow> seqcont"        (",/ __")

 "_SeqO"           :: "o \<Rightarrow> seqobj"                        ("_")
 "_SeqId"          :: "'a \<Rightarrow> seqobj"                       ("$_")

type_synonym single_seqe = "[seq,seqobj] \<Rightarrow> prop"
type_synonym single_seqi = "[seq'\<Rightarrow>seq',seq'\<Rightarrow>seq'] \<Rightarrow> prop"
type_synonym two_seqi = "[seq'\<Rightarrow>seq', seq'\<Rightarrow>seq'] \<Rightarrow> prop"
type_synonym two_seqe = "[seq, seq] \<Rightarrow> prop"
type_synonym three_seqi = "[seq'\<Rightarrow>seq', seq'\<Rightarrow>seq', seq'\<Rightarrow>seq'] \<Rightarrow> prop"
type_synonym three_seqe = "[seq, seq, seq] \<Rightarrow> prop"
type_synonym four_seqi = "[seq'\<Rightarrow>seq', seq'\<Rightarrow>seq', seq'\<Rightarrow>seq', seq'\<Rightarrow>seq'] \<Rightarrow> prop"
type_synonym four_seqe = "[seq, seq, seq, seq] \<Rightarrow> prop"
type_synonym sequence_name = "seq'\<Rightarrow>seq'"


syntax
  (*Constant to allow definitions of SEQUENCES of formulas*)
  "_Side"        :: "seq\<Rightarrow>(seq'\<Rightarrow>seq')"     ("<<(_)>>")

ML \<open>

(* parse translation for sequences *)

fun abs_seq' t = Abs ("s", Type (@{type_name seq'}, []), t);

fun seqobj_tr (Const (@{syntax_const "_SeqO"}, _) $ f) =
      Const (@{const_syntax SeqO'}, dummyT) $ f
  | seqobj_tr (_ $ i) = i;

fun seqcont_tr (Const (@{syntax_const "_SeqContEmp"}, _)) = Bound 0
  | seqcont_tr (Const (@{syntax_const "_SeqContApp"}, _) $ so $ sc) =
      seqobj_tr so $ seqcont_tr sc;

fun seq_tr (Const (@{syntax_const "_SeqEmp"}, _)) = abs_seq' (Bound 0)
  | seq_tr (Const (@{syntax_const "_SeqApp"}, _) $ so $ sc) =
      abs_seq'(seqobj_tr so $ seqcont_tr sc);

fun singlobj_tr (Const (@{syntax_const "_SeqO"},_) $ f) =
  abs_seq' ((Const (@{const_syntax SeqO'}, dummyT) $ f) $ Bound 0);


(* print translation for sequences *)

fun seqcont_tr' (Bound 0) =
      Const (@{syntax_const "_SeqContEmp"}, dummyT)
  | seqcont_tr' (Const (@{const_syntax SeqO'}, _) $ f $ s) =
      Const (@{syntax_const "_SeqContApp"}, dummyT) $
        (Const (@{syntax_const "_SeqO"}, dummyT) $ f) $ seqcont_tr' s
  | seqcont_tr' (i $ s) =
      Const (@{syntax_const "_SeqContApp"}, dummyT) $
        (Const (@{syntax_const "_SeqId"}, dummyT) $ i) $ seqcont_tr' s;

fun seq_tr' s =
  let
    fun seq_itr' (Bound 0) = Const (@{syntax_const "_SeqEmp"}, dummyT)
      | seq_itr' (Const (@{const_syntax SeqO'}, _) $ f $ s) =
          Const (@{syntax_const "_SeqApp"}, dummyT) $
            (Const (@{syntax_const "_SeqO"}, dummyT) $ f) $ seqcont_tr' s
      | seq_itr' (i $ s) =
          Const (@{syntax_const "_SeqApp"}, dummyT) $
            (Const (@{syntax_const "_SeqId"}, dummyT) $ i) $ seqcont_tr' s
  in
    case s of
      Abs (_, _, t) => seq_itr' t
    | _ => s $ Bound 0
  end;


fun single_tr c [s1, s2] =
  Const (c, dummyT) $ seq_tr s1 $ singlobj_tr s2;

fun two_seq_tr c [s1, s2] =
  Const (c, dummyT) $ seq_tr s1 $ seq_tr s2;

fun three_seq_tr c [s1, s2, s3] =
  Const (c, dummyT) $ seq_tr s1 $ seq_tr s2 $ seq_tr s3;

fun four_seq_tr c [s1, s2, s3, s4] =
  Const (c, dummyT) $ seq_tr s1 $ seq_tr s2 $ seq_tr s3 $ seq_tr s4;


fun singlobj_tr' (Const (@{const_syntax SeqO'},_) $ fm) = fm
  | singlobj_tr' id = Const (@{syntax_const "_SeqId"}, dummyT) $ id;


fun single_tr' c [s1, s2] =
  Const (c, dummyT) $ seq_tr' s1 $ seq_tr' s2;

fun two_seq_tr' c [s1, s2] =
  Const (c, dummyT) $ seq_tr' s1 $ seq_tr' s2;

fun three_seq_tr' c [s1, s2, s3] =
  Const (c, dummyT) $ seq_tr' s1 $ seq_tr' s2 $ seq_tr' s3;

fun four_seq_tr' c [s1, s2, s3, s4] =
  Const (c, dummyT) $ seq_tr' s1 $ seq_tr' s2 $ seq_tr' s3 $ seq_tr' s4;



(** for the <<...>> notation **)

fun side_tr [s1] = seq_tr s1;
\<close>

parse_translation \<open>[(@{syntax_const "_Side"}, K side_tr)]\<close>


subsection \<open>Proof tools\<close>

ML_file "prover.ML"

end
