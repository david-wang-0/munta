theory Simple_Network_Language_Printing
  imports Parsing.JSON_Printing
    Networks.Networks 
    Simple_Networks.Simple_Network_Language_Model_Checking
    TA_Library.Error_List_Monad
begin

fun show_sbexp::"(String.literal, String.literal, String.literal, int) sexp \<Rightarrow> string" where
"show_sbexp sexp.true = ''true''" |
"show_sbexp (sexp.not f) = ''(~'' @ show_sbexp f @ '')''" |
"show_sbexp (sexp.and f g) = ''('' @ show_sbexp f @ '' && '' @ show_sbexp g @ '')''" |
"show_sbexp (sexp.or f g) = ''('' @ show_sbexp f @ '' || '' @ show_sbexp g @ '')''" |
"show_sbexp (sexp.imply f g) = ''('' @ show_sbexp f @ '' -> '' @ show_sbexp g @ '')''" |
"show_sbexp (sexp.loc p s) = ''('' @ show p @ ''.'' @ show s @ '')''" |
"show_sbexp (sexp.eq c d) = ''('' @ show c @ '' = '' @ show d @ '')''" |
"show_sbexp (sexp.le c d) = ''('' @ show c @ '' <= '' @ show d @ '')''" |
"show_sbexp (sexp.lt c d) = ''('' @ show c @ '' < '' @ show d @ '')''" |
"show_sbexp (sexp.ge c d) = ''('' @ show c @ '' >= '' @ show d @ '')''" |
"show_sbexp (sexp.gt c d) = ''('' @ show c @ '' > '' @ show d @ '')''"

fun show_formula::"(String.literal, String.literal, String.literal, int) formula \<Rightarrow> string" where
"show_formula (formula.EX b) = ''(E<> '' @ show_sbexp b @ '')''" |
"show_formula (formula.EG b) = ''(E[] '' @ show_sbexp b @ '')''" |
"show_formula (formula.AX b) = ''(A<> '' @ show_sbexp b @ '')''" |
"show_formula (formula.AG b) = ''(A[] '' @ show_sbexp b @ '')''" |
"show_formula (formula.Leadsto a b) = ''('' @ show_sbexp a @ '' --> '' @ show_sbexp b @ '')''"

(* for the goal *)
definition formula_to_json::"(String.literal, String.literal, String.literal, int) formula \<Rightarrow> string \<times> JSON" where
"formula_to_json f =
  (''\"formula\"'', String (show_formula f))
"

fun print_var::"(String.literal \<times> int \<times> int) \<Rightarrow> string" where
"print_var (v, l, u) = show v @ ''['' @ show l @ '':'' @ show u @ '']''"

definition print_var_list::"(String.literal \<times> int \<times> int) list \<Rightarrow> string" where
"print_var_list vs = fold (\<lambda>l r. l @ '', '' @ r) (map print_var vs) ''''" 


(* variables are passed together with bounds *)
definition bounded_vars_to_vars_and_bounds::"(String.literal \<times> int \<times> int) list \<Rightarrow> string \<times> JSON" where
"bounded_vars_to_vars_and_bounds bv \<equiv> (''\"vars\"'', String (print_var_list bv))"


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
  add "('a, 'b) exp" "('a, 'b) exp" | mult "('a, 'b) exp" "('a, 'b) exp" | 
  neg "('a, 'b) exp"

(* Simple Network Language expressions use functions in the arguments. 
Better not use them. Instead, define own expression type. *)
fun exp_to_str::"(String.literal, int) exp \<Rightarrow> string" and
  bexp_to_str::"(String.literal, int) exp \<Rightarrow> string" where
"exp_to_str (exp.mult a b) = undefined" |
"exp_to_str (exp.add a b) = undefined" |

fun update_to_str::"String.literal \<times> (String.literal, int) exp \<Rightarrow> string" where
"update_to_str _ = undefined"

definition edge_to_JSON::"
  (String.literal \<Rightarrow> int)
  \<Rightarrow> String.literal \<times> (String.literal, int) Simple_Expressions.bexp \<times>
     (String.literal, int) acconstraint list \<times> String.literal act \<times>
     (String.literal \<times> (String.literal, int) exp) list \<times>
     String.literal list \<times> String.literal 
  \<Rightarrow> _" where
"edge_to_JSON name_to_id e \<equiv> 
let (s, check, guard, label, upds, resets, t) = e;
  source = (''\"source\"'', JSON.Int (name_to_id s));
  target = (''\"target\"'', JSON.Int (name_to_id s));
  label = (''\"label\"'', String (label_to_str label));
  update = 
in Object [source, label, target]"

(* states are string literals. Edges are nta transitions *)
definition automaton_to_JSON::"String.literal list \<times>
    String.literal list \<times>
    (String.literal \<times>
     (String.literal, int) Simple_Expressions.bexp \<times>
     (String.literal, int) acconstraint list \<times>
     String.literal act \<times>
     (String.literal \<times> (String.literal, int) exp) list \<times>
     String.literal list \<times> String.literal) list \<times>
    (nat \<times> (String.literal, int) acconstraint list) list \<Rightarrow> string" where
"automaton_to_JSON a \<equiv> 
  let (committed, urgent, edges, invs) = a
  
  in undefined"

(* What do edges look like? (s, ..., label, , s')

- labels are In, Out, Sil
- resets are sets of clocks
-  *)

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