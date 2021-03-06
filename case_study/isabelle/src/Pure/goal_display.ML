(*  Title:      Pure/goal_display.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Author:     Makarius

Display tactical goal state.
*)

signature GOAL_DISPLAY =
sig
  val goals_limit_raw: Config.raw
  val goals_limit: int Config.T
  val show_main_goal_raw: Config.raw
  val show_main_goal: bool Config.T
  val pretty_goals: Proof.context -> thm -> Pretty.T list
  val pretty_goal: Proof.context -> thm -> Pretty.T
  val string_of_goal: Proof.context -> thm -> string

  val set_goal_print_cache_limit: int -> unit

  val quick_print_enabled: unit -> bool
end;

structure Goal_Display: GOAL_DISPLAY =
struct

val goals_limit_raw = Config.declare_option ("goals_limit", @{here});
val goals_limit = Config.int goals_limit_raw;

val show_main_goal_raw = Config.declare_option ("show_main_goal", @{here});
val show_main_goal = Config.bool show_main_goal_raw;

val print_cache_limit = Unsynchronized.ref (0 : int);
fun set_goal_print_cache_limit limit = print_cache_limit := limit;

fun quick_print_enabled () = Options.default_bool "quick_print";

(*print thm A1,...,An/B in "goal style" -- premises as numbered subgoals*)

local

fun ins_entry (x, y) =
  AList.default (op =) (x, []) #>
  AList.map_entry (op =) x (insert (op =) y);

val add_consts = Term.fold_aterms
  (fn Const (c, T) => ins_entry (T, (c, T))
    | _ => I);

val add_vars = Term.fold_aterms
  (fn Free (x, T) => ins_entry (T, (x, ~1))
    | Var (xi, T) => ins_entry (T, xi)
    | _ => I);

val add_varsT = Term.fold_atyps
  (fn TFree (x, S) => ins_entry (S, (x, ~1))
    | TVar (xi, S) => ins_entry (S, xi)
    | _ => I);

fun sort_idxs vs = map (apsnd (sort (prod_ord string_ord int_ord))) vs;
fun sort_cnsts cs = map (apsnd (sort_by fst)) cs;

fun consts_of t = sort_cnsts (add_consts t []);
fun vars_of t = sort_idxs (add_vars t []);
fun varsT_of t = rev (sort_idxs (Term.fold_types add_varsT t []));

val cache = Unsynchronized.ref ([] : (term * Pretty.T) list);

fun cache_eq (subgoal, subgoal') = subgoal = subgoal';

fun check_cache subgoal = AList.lookup cache_eq (take (!print_cache_limit) (!cache)) subgoal

fun add_cache subgoal pretty = if !print_cache_limit = 0 then () else
Unsynchronized.change cache (fn cache_val =>
  let
    val next_cache = (subgoal, pretty) :: cache_val
    val result = take (!print_cache_limit) next_cache;
  in result end)


in

fun pretty_goals ctxt0 state =
  let
    val ctxt = ctxt0
      |> Config.put show_types (Config.get ctxt0 show_types orelse Config.get ctxt0 show_sorts)
      |> Config.put show_sorts false;

    val show_sorts0 = Config.get ctxt0 show_sorts;
    val show_types = Config.get ctxt show_types;
    val show_consts = Config.get ctxt show_consts
    val show_main_goal = Config.get ctxt show_main_goal;
    val goals_limit = Config.get ctxt goals_limit;

    val prt_sort = Syntax.pretty_sort ctxt;
    val prt_typ = Syntax.pretty_typ ctxt;
    val prt_term =
      singleton (Syntax.uncheck_terms ctxt) #>
      Type_Annotation.ignore_free_types #>
      Syntax.unparse_term ctxt;

    fun prt_subgoal' t = case check_cache t of SOME pretty => pretty | NONE =>
      let
        val pretty = prt_term t
        val _ = add_cache t pretty;
      in pretty end;

    fun prt_subgoal t = if (quick_print_enabled ()) then prt_subgoal' (Const ("Pure.prop", dummyT) $ t) else prt_subgoal' t

    fun prt_atoms prt prtT (X, xs) = Pretty.block
      [Pretty.block (Pretty.commas (map prt xs)), Pretty.str " ::",
        Pretty.brk 1, prtT X];

    fun prt_var (x, ~1) = prt_term (Syntax.free x)
      | prt_var xi = prt_term (Syntax.var xi);

    fun prt_varT (x, ~1) = prt_typ (TFree (x, []))
      | prt_varT xi = prt_typ (TVar (xi, []));

    val prt_consts = prt_atoms (prt_term o Const) prt_typ;
    val prt_vars = prt_atoms prt_var prt_typ;
    val prt_varsT = prt_atoms prt_varT prt_sort;


    fun pretty_list _ _ [] = []
      | pretty_list name prt lst = [Pretty.big_list name (map prt lst)];

    fun pretty_subgoal s A =
      Pretty.markup (Markup.subgoal s) [Pretty.str (" " ^ s ^ ". "), prt_subgoal A];
    val pretty_subgoals = map_index (fn (i, A) => pretty_subgoal (string_of_int (i + 1)) A);

    val pretty_ffpairs = pretty_list "flex-flex pairs:" (Thm.pretty_flexpair ctxt);

    val pretty_consts = pretty_list "constants:" prt_consts o consts_of;
    val pretty_vars = pretty_list "variables:" prt_vars o vars_of;
    val pretty_varsT = pretty_list "type variables:" prt_varsT o varsT_of;


    val prop = Thm.prop_of state;
    val (As, B) = Logic.strip_horn prop;
    val ngoals = length As;
  in
    (if show_main_goal then [Pretty.mark Markup.goal (prt_subgoal B)] else []) @
     (if ngoals = 0 then [Pretty.str "No subgoals!"]
      else if ngoals > goals_limit then
        pretty_subgoals (take goals_limit As) @
        [Pretty.str ("A total of " ^ string_of_int ngoals ^ " subgoals...")]
      else pretty_subgoals As) @
    pretty_ffpairs (Thm.tpairs_of state) @
    (if show_consts then pretty_consts prop else []) @
    (if show_types then pretty_vars prop else []) @
    (if show_sorts0 then pretty_varsT prop else [])
  end;

val pretty_goal = Pretty.chunks oo pretty_goals;
val string_of_goal = Pretty.string_of oo pretty_goal;

end;

end;

