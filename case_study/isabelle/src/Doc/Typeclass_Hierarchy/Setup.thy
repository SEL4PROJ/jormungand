theory Setup
imports Complex_Main "~~/src/HOL/Library/Multiset" "~~/src/HOL/Library/Lattice_Syntax"
begin

ML_file "../antiquote_setup.ML"
ML_file "../more_antiquote.ML"

attribute_setup all =
  \<open>Scan.succeed (Thm.rule_attribute [] (K Drule.forall_intr_vars))\<close>
  "quantified schematic vars"

setup \<open>Config.put_global Printer.show_type_emphasis false\<close>

setup \<open>
let
  fun strip_all t =
    if Logic.is_all t
    then
      case snd (dest_comb t) of Abs (w, T, t') =>
        strip_all t' |>> cons (w, T)
    else ([], t);
  fun frugal (w, T as TFree (v, sort)) visited =
        if member (op =) visited v
        then ((w, dummyT), visited) else ((w, T), v :: visited)
    | frugal (w, T) visited = ((w, dummyT), visited);
  fun frugal_sorts t =
    let
      val (vTs, body) = strip_all t
      val (vTs', _) = fold_map frugal vTs [];
    in Logic.list_all (vTs', map_types (K dummyT) body) end;
in
  Term_Style.setup @{binding frugal_sorts}
    (Scan.succeed (K frugal_sorts))
end
\<close>

declare [[show_sorts]]

end
