theory Simple_Network_Language_Printing
  imports Parsing.JSON_Printing
    Networks.Networks 
    Simple_Networks.Simple_Network_Language_Model_Checking
    TA_Library.Error_List_Monad
begin

fun print_bexp::"(String.literal, String.literal, String.literal, int) sexp \<Rightarrow> string" where
"print_bexp sexp.true = ''true''" |
"print_bexp (sexp.not f) = ''(~'' @ print_bexp f @ '')''" |
"print_bexp (sexp.and f g) = ''('' @ print_bexp f @ '' && '' @ print_bexp g @ '')''" |
"print_bexp (sexp.or f g) = ''('' @ print_bexp f @ '' || '' @ print_bexp g @ '')''" |
"print_bexp (sexp.imply f g) = ''('' @ print_bexp f @ '' -> '' @ print_bexp g @ '')''" |
<<<<<<< Updated upstream
"print_bexp (sexp.loc p s) = undefined" |
=======
"print_bexp (sexp.loc p s) = ''('' @ show p @ ''.'' @ show s @ '')''" |
>>>>>>> Stashed changes
"print_bexp (sexp.eq c d) = ''('' @ show c @ '' = '' @ show d @ '')''" |
"print_bexp (sexp.le c d) = ''('' @ show c @ '' <= '' @ show d @ '')''" |
"print_bexp (sexp.lt c d) = ''('' @ show c @ '' < '' @ show d @ '')''" |
"print_bexp (sexp.ge c d) = ''('' @ show c @ '' >= '' @ show d @ '')''" |
"print_bexp (sexp.gt c d) = ''('' @ show c @ '' > '' @ show d @ '')''"

fun print_formula::"(String.literal, String.literal, String.literal, int) formula \<Rightarrow> string" where
<<<<<<< Updated upstream
"print_formula _ = undefined"

definition formula_to_json::"(String.literal, String.literal, String.literal, int) formula \<Rightarrow> string \<times> JSON" where
"formula_to_json f =
  (''\"formula\"'', String '''')
"

definition to_muntax::"(nat \<Rightarrow> nat \<Rightarrow> String.literal) \<times> 
=======
"print_formula (formula.EX b) = ''(E<> '' @ print_bexp b @ '')''" |
"print_formula (formula.EG b) = ''(E[] '' @ print_bexp b @ '')''" |
"print_formula (formula.AX b) = ''(A<> '' @ print_bexp b @ '')''" |
"print_formula (formula.AG b) = ''(A[] '' @ print_bexp b @ '')''" |
"print_formula (formula.Leadsto a b) = ''('' @ print_bexp a @ '' --> '' @ print_bexp b @ '')''"

definition formula_to_json::"(String.literal, String.literal, String.literal, int) formula \<Rightarrow> string \<times> JSON" where
"formula_to_json f =
  (''\"formula\"'', String (print_formula f))
"

definition convert_to_JSON::"(nat \<Rightarrow> nat \<Rightarrow> String.literal) \<times> 
>>>>>>> Stashed changes
  (String.literal \<Rightarrow> nat) \<times> 
  String.literal list \<times>
  (nat list \<times> nat list \<times>
   (String.literal act, nat, String.literal, int, String.literal, int) transition list
    \<times> (nat \<times> (String.literal, int) cconstraint) list) list \<times>
   (String.literal \<times> int \<times> int) list \<times>
   (nat, nat, String.literal, int) formula \<times> 
  nat list \<times> 
  (String.literal \<times> int) list
  \<Rightarrow> JSON" where
<<<<<<< Updated upstream
"to_muntax a \<equiv> 
=======
"convert_to_JSON a \<equiv> 
>>>>>>> Stashed changes
  let (ids_to_names, process_names_to_index, broadcast, automata, bounds, formula, init_locs, init_vars) = a
  in (
    undefined
  )
"

(* Initial locations are the locations.
   Initial variables are all declared variables.
   Broadcast is ...?
*)
end