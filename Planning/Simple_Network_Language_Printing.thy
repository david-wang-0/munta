theory Simple_Network_Language_Printing
  imports Parsing.JSON_Printing
    Networks.Networks 
    Simple_Networks.Simple_Network_Language_Model_Checking
    TA_Library.Error_List_Monad
begin

fun showsp_sbexp::"(String.literal, String.literal, String.literal, int) sexp \<Rightarrow> string" where
"showsp_sbexp sexp.true = ''true''" |
"showsp_sbexp (sexp.not f) = ''(~'' @ showsp_sbexp f @ '')''" |
"showsp_sbexp (sexp.and f g) = ''('' @ showsp_sbexp f @ '' && '' @ showsp_sbexp g @ '')''" |
"showsp_sbexp (sexp.or f g) = ''('' @ showsp_sbexp f @ '' || '' @ showsp_sbexp g @ '')''" |
"showsp_sbexp (sexp.imply f g) = ''('' @ showsp_sbexp f @ '' -> '' @ showsp_sbexp g @ '')''" |
"showsp_sbexp (sexp.loc p s) = ''('' @ show p @ ''.'' @ show s @ '')''" |
"showsp_sbexp (sexp.eq c d) = ''('' @ show c @ '' = '' @ show d @ '')''" |
"showsp_sbexp (sexp.le c d) = ''('' @ show c @ '' <= '' @ show d @ '')''" |
"showsp_sbexp (sexp.lt c d) = ''('' @ show c @ '' < '' @ show d @ '')''" |
"showsp_sbexp (sexp.ge c d) = ''('' @ show c @ '' >= '' @ show d @ '')''" |
"showsp_sbexp (sexp.gt c d) = ''('' @ show c @ '' > '' @ show d @ '')''"

fun showsp_formula::"(String.literal, String.literal, String.literal, int) formula \<Rightarrow> string" where
"showsp_formula (formula.EX b) = ''(E<> '' @ showsp_sbexp b @ '')''" |
"showsp_formula (formula.EG b) = ''(E[] '' @ showsp_sbexp b @ '')''" |
"showsp_formula (formula.AX b) = ''(A<> '' @ showsp_sbexp b @ '')''" |
"showsp_formula (formula.AG b) = ''(A[] '' @ showsp_sbexp b @ '')''" |
"showsp_formula (formula.Leadsto a b) = ''('' @ showsp_sbexp a @ '' --> '' @ showsp_sbexp b @ '')''"

(* For the goal. To do: locations are not just strings. *)
definition formula_to_json::"(String.literal, String.literal, String.literal, int) formula \<Rightarrow> string \<times> JSON" where
"formula_to_json f =
  (''\"formula\"'', String (showsp_formula f))
"

fun print_var::"(String.literal \<times> int \<times> int) \<Rightarrow> string" where
"print_var (v, l, u) = show v @ ''['' @ show l @ '':'' @ show u @ '']''"

definition print_var_list::"(String.literal \<times> int \<times> int) list \<Rightarrow> string" where
"print_var_list vs = fold (\<lambda>l r. l @ '', '' @ r) (map print_var vs) ''''" 


(* variables are passed together with bounds *)
definition bounded_vars_to_vars_and_bounds::"(String.literal \<times> int \<times> int) list \<Rightarrow> string \<times> JSON" where
"bounded_vars_to_vars_and_bounds bv \<equiv> (''\"vars\"'', String (print_var_list bv))"


(* What do actions do? They synchronise channels, but they are always paired with another value
  in the semantics in Networks.thy. What is the other value? *)
fun label_to_str::"String.literal act \<Rightarrow> string" where
"label_to_str (Sil _) = ''''" |
"label_to_str (In v) = show ''?'' @ show v" |
"label_to_str (Out v) = show ''!'' @ show v"

datatype ('a, 'b) bexp =
  true |
  not "('a, 'b) bexp" |
  "and" "('a, 'b) bexp" "('a, 'b) bexp" |
  or "('a, 'b) bexp" "('a, 'b) bexp" |
  imply "('a, 'b) bexp" "('a, 'b) bexp" | \<comment> \<open>Boolean connectives\<close>
  eq "('a, 'b) exp" "('a, 'b) exp" |
  le "('a, 'b) exp" "('a, 'b) exp" |
  lt "('a, 'b) exp" "('a, 'b) exp" |
  ge "('a, 'b) exp" "('a, 'b) exp" |
  gt "('a, 'b) exp" "('a, 'b) exp"
and ('a, 'b) exp =
  const 'b | var 'a | if_then_else "('a, 'b) bexp" "('a, 'b) exp" "('a, 'b) exp" |
  add "('a, 'b) exp" "('a, 'b) exp" | mult "('a, 'b) exp" "('a, 'b) exp" (*| 
  neg "('a, 'b) exp" *)
(* There is a unary operator in the original abstract syntax. 
    I do not know where it is used. *)

(* Simple Network Language expressions use functions in the arguments. 
Better not use them. Instead, define own expression type. *)
fun exp_to_str::"(('a::show), ('b::show)) exp \<Rightarrow> string" and
  showsp_bexp::"('a, 'b::show) bexp \<Rightarrow> string" where
"exp_to_str (exp.mult a b) = show ''('' @ exp_to_str a @ show '') * ('' @ exp_to_str b @ show '')''" |
"exp_to_str (exp.add a b) = show ''('' @ exp_to_str a @ show '') + ('' @ exp_to_str b @ show '')''" |
"exp_to_str (exp.if_then_else b x y) = show ''('' @ showsp_bexp b @ show '') ? ('' @ exp_to_str x @ show '') : ('' @ exp_to_str y @ show '')''" |
"exp_to_str (exp.const c) = show c" |
"exp_to_str (exp.var v) = show v" |
"showsp_bexp bexp.true = show ''True''" |
"showsp_bexp (bexp.not b) = show ''~('' @ showsp_bexp b @ show '')''" |
"showsp_bexp (bexp.and a b) = show ''('' @ showsp_bexp a @ show '') && ('' @ showsp_bexp b @ show '')''" |
"showsp_bexp (bexp.or a b) = show ''('' @ showsp_bexp a @ show '') || ('' @ showsp_bexp b @ show '')''" |
"showsp_bexp (bexp.imply a b) = show ''('' @ showsp_bexp a @ show '') -> ('' @ showsp_bexp b @ show '')''" |
"showsp_bexp (bexp.eq x y) = show ''('' @ exp_to_str x @ show '') = ('' @ exp_to_str y @ show '')''" |
"showsp_bexp (bexp.le x y) = show ''('' @ exp_to_str x @ show '') <= ('' @ exp_to_str y @ show '')''" |
"showsp_bexp (bexp.lt x y) = show ''('' @ exp_to_str x @ show '') < ('' @ exp_to_str y @ show '')''" |
"showsp_bexp (bexp.ge x y) = show ''('' @ exp_to_str x @ show '') >= ('' @ exp_to_str y @ show '')''" |
"showsp_bexp (bexp.gt x y) = show ''('' @ exp_to_str x @ show '') > ('' @ exp_to_str y @ show '')''"

fun update_to_str::"String.literal \<times> (String.literal, int) exp \<Rightarrow> string" where
"update_to_str (v, e) = show v @ show '' := '' @ exp_to_str e"

fun reset_to_str::"String.literal \<Rightarrow> string" where
"reset_to_str r = show r @ show '' := '' @ show (0::int)"

fun showsp_acconstraint::"('c::show, 't::show) acconstraint \<Rightarrow> string" where
"showsp_acconstraint (acconstraint.LT c t) = show c @ show '' < '' @ show t" |
"showsp_acconstraint (acconstraint.LE c t) = show c @ show '' <= '' @ show t" |
"showsp_acconstraint (acconstraint.EQ c t) = show c @ show '' = '' @ show t" |
"showsp_acconstraint (acconstraint.GT c t) = show c @ show '' > '' @ show t" |
"showsp_acconstraint (acconstraint.GE c t) = show c @ show '' >= '' @ show t"


definition showsp_invariant::"(String.literal, int) acconstraint list 
  \<Rightarrow> (String.literal, int) bexp \<Rightarrow> string" where
"showsp_invariant guards invariants = (
  let 
    cconsts = fold (\<lambda>l r. l @ show '' && '' @ r) (map showsp_acconstraint guards) '''';
    invs = showsp_bexp invariants
  in
    show ''('' @ cconsts @ show '') && ('' @ invs @ show '')''
)"


(* Simple_Network_Language_Export_Code.convert_edge *)
definition edge_to_JSON::"
  (String.literal \<Rightarrow> int option)
  \<Rightarrow> String.literal \<times> (String.literal, int) bexp \<times>
     (String.literal, int) acconstraint list \<times> String.literal act \<times>
     (String.literal \<times> (String.literal, int) exp) list \<times>
     String.literal list \<times> String.literal 
  \<Rightarrow> JSON Error_List_Monad.result" where
"edge_to_JSON name_to_id e \<equiv> do {
  let (s, check, guard, label, upds, resets, t) = e;
  s_id \<leftarrow> (case (name_to_id s) of None \<Rightarrow> Error [''Unknown location: ''  @ (String.explode s) |> String.implode] | Some n \<Rightarrow> Result n);
  t_id \<leftarrow> (case (name_to_id t) of None \<Rightarrow> Error [''Unknown location: ''  @ (String.explode t) |> String.implode] | Some n \<Rightarrow> Result n);
  let source = (''\"source\"'', JSON.Int s_id);
  let target = (''\"target\"'', JSON.Int t_id);
  let label = (''\"label\"'', String (label_to_str label));
  let upds = map update_to_str upds;
  let resets = map reset_to_str resets;
  let guards = (''\"guard\"'', String (showsp_invariant guard check));
  let updates = (''\"update\"'', String (fold (\<lambda>l r. l @ '', '' @ r) (upds @ resets) ''''));
  Result (Object [source, label, target, guards, updates])
}"

definition nodes_to_JSON::"
  String.literal list \<times>
  String.literal list \<times>
  (nat \<times> (String.literal, int) acconstraint list) list \<Rightarrow> JSON Error_List_Monad.result" where
"nodes_to_JSON _ = undefined"

(* What do edges look like? (s, ..., label, , s')

- labels are In, Out, Sil
- resets are sets of clocks
-  *)

(* states are string literals. Edges are nta transitions. 
More or less inverse of Simple_Network_Language_Export_Code.convert_automaton *)
(* Invariants take clocks as string literals. *)
definition automaton_to_JSON::"
  String.literal \<times>
  String.literal list \<times>
  String.literal list \<times>
  (String.literal \<times>
     (String.literal, int) bexp \<times>
     (String.literal, int) acconstraint list \<times>
     String.literal act \<times>
     (String.literal \<times> (String.literal, int) exp) list \<times>
     String.literal list \<times> String.literal) list \<times>
  (String.literal \<times> (String.literal, int) acconstraint list) list \<Rightarrow> JSON Error_List_Monad.result" where
"automaton_to_JSON a \<equiv> do {
    let (name, committed, urgent, edges, invs) = a;
    let name = (''\"name\"'', JSON.String (''1234''));
    let id_asmt = map_of (snd (fold (\<lambda>x (n, xs). (n + 1, (x,n)#xs)) (committed @ urgent) (0, [])));
    edges \<leftarrow> combine_map (edge_to_JSON id_asmt) edges |> err_msg (STR ''Edges refer to undefined nodes'');
    let edges = (''\"edges\"'', JSON.Array edges);
    let nodes = undefined;
    Result (Object [name, edges])
  }"

definition automata_to_JSON::"(nat list \<times>
    nat list \<times>
    (nat \<times>
     (String.literal, int) Simple_Expressions.bexp \<times>
     (String.literal, int) acconstraint list \<times>
     String.literal act \<times>
     (String.literal \<times> (String.literal, int) exp) list \<times>
     String.literal list \<times> nat) list \<times>
    (nat \<times>
     (String.literal, int) acconstraint list) list) list \<Rightarrow> string \<times> JSON" where
"automata_to_JSON as = undefined"

definition to_muntax::"(nat \<Rightarrow> nat \<Rightarrow> String.literal) \<times>
  (String.literal \<Rightarrow> nat) \<times> 
  String.literal list \<times>
  (nat list \<times> nat list \<times>
   (String.literal act, nat, String.literal, int, String.literal, int) transition list
    \<times> (nat \<times> (String.literal, int) cconstraint) list) list \<times>
   (String.literal \<times> int \<times> int) list \<times>
   (String.literal, String.literal, String.literal, int) formula \<times> 
  nat list
  \<Rightarrow> JSON" where
"to_muntax a  \<equiv> 
  let (ids_to_names, process_names_to_index, broadcast, automata, vars, formula, init_locs) = a
  in (
    Object [formula_to_json formula, bounded_vars_to_vars_and_bounds vars]
  )
"

(* Initial locations are the locations.
   Initial variables are all declared variables.
   Broadcast is ...?
*)
end