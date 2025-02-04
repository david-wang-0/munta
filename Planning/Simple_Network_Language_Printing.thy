theory Simple_Network_Language_Printing
  imports (* Parsing.JSON_Printing *)
    Networks.Networks 
    TA_Code.Simple_Network_Language_Export_Code
    TA_Library.Error_List_Monad
begin

(* fun showsp_sbexp::"('n::show, 's::show, 'a::show, 'b::show) sexp \<Rightarrow> string \<Rightarrow> string" where
"showsp_sbexp sexp.true = (@) ''true''" |
"showsp_sbexp (sexp.not f) = shows ''(~'' o showsp_sbexp f o shows '')''" |
"showsp_sbexp (sexp.and f g) = shows ''('' o showsp_sbexp f o shows '' && '' o showsp_sbexp g o shows '')''" |
"showsp_sbexp (sexp.or f g) = shows ''('' o showsp_sbexp f o shows '' || '' o showsp_sbexp g o shows '')''" |
"showsp_sbexp (sexp.imply f g) = shows ''('' o showsp_sbexp f o shows '' -> '' o showsp_sbexp g o shows '')''" |
"showsp_sbexp (sexp.loc p s) = shows ''('' o shows p o shows ''.'' o shows s o shows '')''" |
"showsp_sbexp (sexp.eq c d) = shows ''('' o shows c o shows '' = '' o shows d o shows '')''" |
"showsp_sbexp (sexp.le c d) = shows ''('' o shows c o shows '' <= '' o shows d o shows '')''" |
"showsp_sbexp (sexp.lt c d) = shows ''('' o shows c o shows '' < '' o shows d o shows '')''" |
"showsp_sbexp (sexp.ge c d) = shows ''('' o shows c o shows '' >= '' o shows d o shows '')''" |
"showsp_sbexp (sexp.gt c d) = shows ''('' o shows c o shows '' > '' o shows d o shows '')''"

instantiation sexp::("show", "show", "show", "show") "show" begin
  definition "shows_prec_sexp (n::nat) e \<equiv> showsp_sbexp e"
 (*  definition "shows_list_sexp xs \<equiv> showsp_list (\<lambda>n x. showsp_sbexp x) 0 xs" *)
instance sorry
end *)
(* 
fun showsp_formula::"('n::show, 's::show, 'a::show, 'b::show) formula \<Rightarrow> string \<Rightarrow> string" where
"showsp_formula (formula.EX b) = shows ''(E<> '' o showsp_sbexp b o shows '')''" |
"showsp_formula (formula.EG b) = shows ''(E[] '' o showsp_sbexp b o shows '')''" |
"showsp_formula (formula.AX b) = shows ''(A<> '' o showsp_sbexp b o shows '')''" |
"showsp_formula (formula.AG b) = shows ''(A[] '' o showsp_sbexp b o shows '')''" |
"showsp_formula (formula.Leadsto a b) = shows ''('' o showsp_sbexp a o shows '' --> '' o showsp_sbexp b o shows '')''"

instantiation formula::("show", "show", "show", "show") "show" begin
  definition "shows_prec_formula (n::nat) f \<equiv> showsp_formula f"
 (*  definition "shows_list_formula xs \<equiv> showsp_list (\<lambda>n x. showsp_formula x) 0 xs" *)
instance sorry
end
 *)

(* For the goal. To do: locations are not just strings. *)
definition formula_to_json::"(String.literal, String.literal, String.literal, int) formula \<Rightarrow> string \<times> JSON" where
"formula_to_json f =
  (''formula'', String (show f))
"

fun print_var::"(String.literal \<times> int \<times> int) \<Rightarrow> string" where
"print_var (v, l, u) = show v @ ''['' @ show l @ '':'' @ show u @ '']''"

definition print_var_list::"(String.literal \<times> int \<times> int) list \<Rightarrow> string" where
"print_var_list vs = fold (\<lambda>l r. l @ '', '' @ r) (map print_var vs) ''''" 

(* variables are passed together with bounds *)
definition bounded_vars_to_vars_and_bounds::"(String.literal \<times> int \<times> int) list \<Rightarrow> string \<times> JSON" where
"bounded_vars_to_vars_and_bounds bv \<equiv> (''vars'', String (print_var_list bv))"


(* What do actions do? They synchronise channels, but they are always paired with another value
  in the semantics in Networks.thy. What is the other value? *)

fun showsp_act::"('a::show) act \<Rightarrow> string \<Rightarrow> string" where
"showsp_act (Sil v) = id" |
"showsp_act (In v) = (shows ''?'') o (shows v)" |
"showsp_act (Out v) = (shows ''!'') o (shows v)"

(*
instantiation act::("show") "show" begin
  
  definition shows_prec_act where
  "shows_prec_act (n::nat) a \<equiv> showsp_act a"
  
 (*  definition shows_list_act where
  "shows_list_act xs \<equiv> showsp_list (\<lambda>n x. showsp_act x) 0 xs" *)
instance sorry
end
 *)
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
I cannot think of a way to check whether the binary operator that is
used to construct a bexp is (+), for instance. *)
fun showsp_exp::"(('a::show), ('b::show)) exp \<Rightarrow> string \<Rightarrow> string" and
  showsp_bexp::"('a, 'b::show) bexp \<Rightarrow> string \<Rightarrow> string" where
"showsp_exp (exp.mult a b) = shows ''('' o showsp_exp a o shows '') * ('' o showsp_exp b o shows '')''" |
"showsp_exp (exp.add a b) = shows ''('' o showsp_exp a o shows '') + ('' o showsp_exp b o shows '')''" |
"showsp_exp (exp.if_then_else b x y) = shows ''('' o showsp_bexp b o shows '') ? ('' o showsp_exp x o shows '') : ('' o showsp_exp y o shows '')''" |
"showsp_exp (exp.const c) = shows c" |
"showsp_exp (exp.var v) = shows v" |
"showsp_bexp bexp.true = shows ''True''" |
"showsp_bexp (bexp.not b) = shows ''~('' o showsp_bexp b o shows '')''" |
"showsp_bexp (bexp.and a b) = shows ''('' o showsp_bexp a o shows '') && ('' o showsp_bexp b o shows '')''" |
"showsp_bexp (bexp.or a b) = shows ''('' o showsp_bexp a o shows '') || ('' o showsp_bexp b o shows '')''" |
"showsp_bexp (bexp.imply a b) = shows ''('' o showsp_bexp a o shows '') -> ('' o showsp_bexp b o shows '')''" |
"showsp_bexp (bexp.eq x y) = shows ''('' o showsp_exp x o shows '') = ('' o showsp_exp y o shows '')''" |
"showsp_bexp (bexp.le x y) = shows ''('' o showsp_exp x o shows '') <= ('' o showsp_exp y o shows '')''" |
"showsp_bexp (bexp.lt x y) = shows ''('' o showsp_exp x o shows '') < ('' o showsp_exp y o shows '')''" |
"showsp_bexp (bexp.ge x y) = shows ''('' o showsp_exp x o shows '') >= ('' o showsp_exp y o shows '')''" |
"showsp_bexp (bexp.gt x y) = shows ''('' o showsp_exp x o shows '') > ('' o showsp_exp y o shows '')''"

instantiation exp:: ("show", "show") "show" begin
  definition "shows_prec_exp (n::nat) e \<equiv> showsp_exp e"
  definition "shows_list_exp xs \<equiv> showsp_list (\<lambda>n x. showsp_exp x) 0 xs"
instance sorry
end

(* To do: properly implement shows_*) 

instantiation bexp:: ("show", "show") "show" begin
  definition "shows_prec_bexp (n::nat) e \<equiv> showsp_bexp e"
  definition "shows_list_bexp xs \<equiv> showsp_list (\<lambda>n x. showsp_bexp x) 0 xs"
instance sorry
end

fun update_to_str::"String.literal \<times> (String.literal, int) exp \<Rightarrow> string" where
"update_to_str (v, e) = show v @ show '' := '' @ show e"

fun reset_to_str::"String.literal \<Rightarrow> string" where
"reset_to_str r = show r @ show '' := '' @ show (0::int)"

(* fun showsp_acconstraint::"('c::show, 't::show) acconstraint \<Rightarrow> string \<Rightarrow> string" where
"showsp_acconstraint (acconstraint.LT c t) = shows c o shows '' < '' o shows t" |
"showsp_acconstraint (acconstraint.LE c t) = shows c o shows '' <= '' o shows t" |
"showsp_acconstraint (acconstraint.EQ c t) = shows c o shows '' = '' o shows t" |
"showsp_acconstraint (acconstraint.GT c t) = shows c o shows '' > '' o shows t" |
"showsp_acconstraint (acconstraint.GE c t) = shows c o shows '' >= '' o shows t"

instantiation acconstraint:: ("show", "show") "show" begin
  definition "shows_prec_acconstraint (n::nat) e \<equiv> showsp_acconstraint e"
 (*  definition "shows_list_acconstraint xs \<equiv> showsp_list (\<lambda>n x. showsp_acconstraint x) 0 xs" *)
instance sorry
end *)


fun sequence_list_opt::"'a option list \<Rightarrow> 'a list option" where
"sequence_list_opt [] = Some []" |
"sequence_list_opt (x#xs) = 
  do {
    x \<leftarrow> x;
    xs \<leftarrow> sequence_list_opt xs;
    Some (x # xs)
  }"

fun traverse

definition inv_to_str::"(String.literal, int) acconstraint list 
  \<Rightarrow> (String.literal, int) bexp \<Rightarrow> string" where
"inv_to_str guards invariants = (
  let 
    cconsts = fold (\<lambda>l r. l @ show '' && '' @ r) (map show guards) '''';
    invs = show invariants
  in
    cconsts @ show ''&& ('' @ invs @ show '')''
)"

(* Simple_Network_Language_Export_Code.convert_edge *)
definition edge_to_JSON::"
  (String.literal \<Rightarrow> int option)
  \<Rightarrow> String.literal \<times> 
    (String.literal, int) bexp \<times>
    (String.literal, int) acconstraint list \<times> 
    String.literal act \<times>
    (String.literal \<times> (String.literal, int) exp) list \<times>
    String.literal list \<times> 
    String.literal 
  \<Rightarrow> JSON Error_List_Monad.result" where
"edge_to_JSON name_to_id e \<equiv> 
  let (s, check, guard, label, upds, resets, t) = e
  in 
  do {
    s_id \<leftarrow> (case (name_to_id s) of None \<Rightarrow> Error [''Location has no id: ''  @ (String.explode s) |> String.implode] | Some n \<Rightarrow> Result n);
    t_id \<leftarrow> (case (name_to_id t) of None \<Rightarrow> Error [''Location has no id: ''  @ (String.explode t) |> String.implode] | Some n \<Rightarrow> Result n);
    let source = (''source'', JSON.Int s_id);
    let target = (''target'', JSON.Int t_id);
    let label = (''label'', String (showsp_act label ''''));
    let upds = map update_to_str upds;
    let resets = map reset_to_str resets;
    let guards = (''guard'', String (inv_to_str guard check));
    let updates = (''update'', String (fold (\<lambda>l r. l @ '', '' @ r) (upds @ resets) ''''));
    Result (Object [source, label, target, guards, updates])
  } |> err_msg (''Error while converting edge: '' @ show e |> String.implode)
"


definition edges_to_JSON::"
  (String.literal \<Rightarrow> int option)
  \<Rightarrow> (String.literal \<times> (String.literal, int) bexp \<times>
     (String.literal, int) acconstraint list \<times> String.literal act \<times>
     (String.literal \<times> (String.literal, int) exp) list \<times>
     String.literal list \<times> String.literal) list
  \<Rightarrow> JSON Error_List_Monad.result" where
"edges_to_JSON name_to_id edges \<equiv> do {
  edges \<leftarrow> combine_map (edge_to_JSON name_to_id) edges ;
  Result (JSON.Array edges)
} |> err_msg (STR ''Error while converting edges: '')"


fun get_or_default::"'a option \<Rightarrow> 'a \<Rightarrow> 'a" where
"get_or_default None d = d" |
"get_or_default (Some x) _ = x"

definition node_to_JSON::"
  (String.literal \<Rightarrow> int option) 
  \<Rightarrow> (String.literal \<Rightarrow> (String.literal, int) acconstraint list option)
  \<Rightarrow> String.literal
  \<Rightarrow> JSON Error_List_Monad.result" where
"node_to_JSON name_to_id name_to_invs n \<equiv> do {
  id \<leftarrow> (case (name_to_id n) of 
    None \<Rightarrow> Error [''Location has no ID: '' @ (String.explode n) |> String.implode] |
    Some n \<Rightarrow> Result (''id'', JSON.Int n));
  let f = (\<lambda>x. fold (\<lambda>l r. l @ show '' && '' @ r) (map show x) '''');
  let invs = default '''' (get (map_option f) (name_to_invs n));
  let inv = (''inv'', String invs);
  let name = (''name'', String (show n));
  Result (Object [id, name, inv])
}"

definition nodes_to_JSON::"
  (String.literal \<Rightarrow> int option) 
  \<Rightarrow> (String.literal \<Rightarrow> (String.literal, int) acconstraint list option)
  \<Rightarrow> String.literal list
  \<Rightarrow> JSON Error_List_Monad.result" where
"nodes_to_JSON name_to_id name_to_invs ns \<equiv> do {
  nodes \<leftarrow> combine_map (node_to_JSON name_to_id name_to_invs) ns;
  Result (JSON.Array nodes)
} |> err_msg (STR ''Error while converting locations'')"

(* What do edges look like? (s, ..., label, , s')

- labels are In, Out, Sil
- resets are sets of clocks
-  *)


(* states are string literals. Edges are nta transitions. 
More or less inverse of Simple_Network_Language_Export_Code.convert_automaton *)
(* Invariants take clocks as string literals. *)
definition automaton_to_JSON::"
  String.literal \<times>
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
"automaton_to_JSON a \<equiv> 
  let (name, init, committed, urgent, edges, invs) = a
  in 
  do {
    let name = (''name'', String (show name));

    let e_nodes = fold (@) (map (\<lambda>(s,_,_,_,_,_,t). [s,t]) edges) [];
    let all_nodes = sorted_list_of_set (set (init # e_nodes @ committed @ urgent));
  
    let name_to_id = map_of (snd (fold (\<lambda>x (n, xs). (n + 1, (x,n)#xs)) all_nodes (0, [])));
    let name_to_invs = map_of invs;
    
    init \<leftarrow> (case (name_to_id init) of 
      None \<Rightarrow> Error [''Location has no ID: '' @ (String.explode init) |> String.implode] |
      Some n \<Rightarrow> Result (''init'', JSON.Int n));
  
    edges \<leftarrow> edges_to_JSON name_to_id edges;
    let edges = (''edges'', edges);
    nodes \<leftarrow> nodes_to_JSON name_to_id name_to_invs all_nodes;
    let nodes = (''nodes'', nodes);
    Result (Object [name, init, edges, nodes])
  } |> err_msg (''Error while converting automaton with name: '' @ show name |> String.implode)"


definition automata_to_JSON::"(
    String.literal \<times>
    String.literal \<times>
    String.literal list \<times>
    String.literal list \<times>
    (String.literal \<times>
      (String.literal, int) bexp \<times>
      (String.literal, int) acconstraint list \<times>
      String.literal act \<times>
      (String.literal \<times> (String.literal, int) exp) list \<times>
      String.literal list \<times>
      String.literal) list \<times>
    (String.literal \<times>
     (String.literal, int) acconstraint list) list) list \<Rightarrow> JSON Error_List_Monad.result" where
"automata_to_JSON as = do {
  automata \<leftarrow> combine_map automaton_to_JSON as;
  Result (JSON.Array automata)
}"

definition to_muntax::"
  (String.literal \<times> 
    String.literal \<times> 
    String.literal list \<times> 
    String.literal list \<times>                                                           
    (String.literal \<times>
      (String.literal, int) bexp \<times>
      (String.literal, int) acconstraint list \<times>
      String.literal act \<times>
      (String.literal \<times> (String.literal, int) exp) list \<times>
        String.literal list \<times>
        String.literal) list \<times>
      (String.literal \<times> (String.literal, int) cconstraint) list) list \<times>
   (String.literal \<times> int \<times> int) list \<times>
   (String.literal, String.literal, String.literal, int) formula
  \<Rightarrow> JSON Error_List_Monad.result" where
"to_muntax a \<equiv>
  let (automata, vars, formula) = a
  in 
  do {
    automata \<leftarrow> automata_to_JSON automata;
    let automata = (''automata'', automata);
    Result (Object [automata, formula_to_json formula, bounded_vars_to_vars_and_bounds vars])
  }
" 
(* The convert function extracts more information that is necessary for printing. To do: Implement
    simpler convert function for these types? *)

definition test3 where "test3 \<equiv>
 STR ''{
    \"info\": \"Derived from the Uppaal benchmarks found at https://www.it.uu.se/research/group/darts/uppaal/benchmarks/\",
    \"automata\": [
        {
            \"name\": \"ST2\",
            \"initial\": 9,
            \"nodes\": [
                {
                    \"id\": 14,
                    \"name\": \"y_idle\",
                    \"x\": 458.2894592285156,
                    \"y\": 442.4790954589844,
                    \"invariant\": \"\"
                }
            ],
            \"edges\": [
                {
                    \"source\": 9,
                    \"target\": 12,
                    \"guard\": \"\",
                    \"label\": \"tt1?\",
                    \"update\": \"y2 := 0, x2 := 0\"
                }
            ]
        }
    ],
    \"clocks\": \"x0, x1, y1, z1, x2, y2, z2\",
    \"vars\": \"id[-1:2]\",
    \"formula\": \"E<> (&& (ST2.y_idle)  )\"
}''"

definition "parse_convert s \<equiv> do {
  parse json s \<bind> convert
}
"

value [code] "do {
  json \<leftarrow> parse json test2;
  convert json
}
"

ML \<open>
  fun do_parse_convert file =
  let
    val s = file_to_string file;
  in                                                    
    @{code parse_convert} s 
  end
\<close>

ML_val \<open>OS.FileSys.getDir()\<close>

ML_val \<open>
  do_parse_convert "work/temporal_planning_certification/munta/certificates/planning.muntax"
\<close>

definition test_automaton1 where
"test_automaton1 \<equiv> (
  STR ''main'', 
  STR ''start'',
  [],
  [],
  [(STR ''start'', 
    bexp.true, 
    [], 
    Sil (STR ''''), 
    [
      (STR ''lock'', const 1),
      (STR ''pf11'', const 1),
      (STR ''ef12'', const 1),
      (STR ''s1'', const 1)
    ],
    [],
    STR ''plan'')],
  []
)"

value [code]  "automaton_to_JSON test_automaton1"

definition test_to_muntax where
"test_to_muntax \<equiv> ([])"
end