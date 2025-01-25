theory JSON_Printing
  imports JSON_Parsing "Show.Show"
begin


(* fun showsp_JSON
  and showsp_list_JSON
  and showsp_kv_list_JSON where
"showsp_JSON (Object xs) = (\<lambda>x. ''{'' @ (showsp_kv_list_JSON xs '''') @ ''}'' @ x)" |
"showsp_JSON (Array js) = (\<lambda>x. ''{'' @ (showsp_list_JSON js '''')  @ '']'' @ x)" |
"showsp_JSON (String s) = (\<lambda>x. ''\"'' @ (shows s '''') @ ''\"'' @ x)" |
"showsp_JSON (JSON.Int i) = shows i" |
"showsp_JSON (Nat n) = shows n" |
"showsp_JSON (Rat (fract.Rat b n d)) = shows (Fract n d)" |
"showsp_JSON (Boolean b) = (case b of True \<Rightarrow> shows ''true'' | False \<Rightarrow> shows ''false'')" |
"showsp_JSON Null = shows ''null''" |
"showsp_list_JSON xs = (\<lambda>x. (fold (\<lambda>s s'. (s '''') @ '', '' @ s') (map (showsp_JSON) xs) '''') @ x)" |
"showsp_kv_list_JSON xs = (\<lambda>x. (fold (\<lambda>s s'. s  @ '', '' @ s') (map (\<lambda>(k, v). ''\"'' @ k @ ''\": '' @ (showsp_JSON v '''')) xs) '''') @ x)" 
 *)
fun showsp_JSON
  and showsp_list_JSON
  and showsp_kv_list_JSON where
"showsp_JSON (Object xs) = (shows_string ''{'') o (showsp_kv_list_JSON xs) o (shows_string ''}'')" |
"showsp_JSON (Array js) = (shows_string ''['') o (showsp_list_JSON js) o (shows_string '']'')" |
"showsp_JSON (String s) = (shows ''\"'') o (shows s) o (shows ''\"'')" |
"showsp_JSON (JSON.Int i) = shows i" |
"showsp_JSON (Nat n) = shows n" |
"showsp_JSON (Rat (fract.Rat b n d)) = shows (Fract n d)" |
"showsp_JSON (Boolean b) = (case b of True \<Rightarrow> shows ''true'' | False \<Rightarrow> shows ''false'')" |
"showsp_JSON Null = shows ''null''" |
"showsp_list_JSON [] = id" |
"showsp_list_JSON (x#[]) = showsp_JSON x" |
"showsp_list_JSON (x#xs) = (showsp_JSON x) o (shows '', '') o (showsp_list_JSON xs)" |
"showsp_kv_list_JSON [] = id" |
"showsp_kv_list_JSON ((k, v)#[]) = (shows k) o (shows '': '') o (showsp_JSON v)" |
"showsp_kv_list_JSON ((k, v)#kvs) = (shows k) o (shows '': '') o (showsp_JSON v) o (shows '', '') o (showsp_kv_list_JSON kvs)"

instantiation JSON :: "show" 
begin

definition shows_prec_JSON where
"shows_prec_JSON (n::nat) j \<equiv> showsp_JSON j"

definition shows_list_JSON where
"shows_list_JSON xs \<equiv> showsp_list (\<lambda>n x. showsp_JSON x) 0 xs"
instance sorry
    
end

value "show (0::nat)"
    
value [code] "case parse_all lx_ws json test2 of (Inr x) \<Rightarrow> x"

end