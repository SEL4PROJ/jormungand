theory SP
imports
"~~/src/HOL/Main"
"~~/src/HOL/Eisbach/Eisbach"
begin

text \<open>Rule collections for strongest postconditions\<close>
named_theorems sp
named_theorems sp_pre

text {* Strongest postcondition method setup *}
method sp declares sp = ((((rule sp)+), (rule sp_pre, rule sp, assumption?)?)  | (rule sp_pre, rule sp, assumption?))

end