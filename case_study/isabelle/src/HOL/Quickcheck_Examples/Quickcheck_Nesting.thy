theory Quickcheck_Nesting
imports Main
begin

ML \<open>
let
  open BNF_FP_Def_Sugar
  open BNF_LFP_Compat

  val compat_plugin = Plugin_Name.declare_setup @{binding compat};

  fun compat fp_sugars =
    perhaps (try (datatype_compat (map (fst o dest_Type o #T) fp_sugars)));
in
  Theory.setup (fp_sugars_interpretation compat_plugin compat)
end
\<close>

end
