theory Code_Python
  imports Main
begin

ML_file \<open>./code_python.ML\<close>

datatype 'a list =
  Nil
| Cons 'a "'a list"

fun concat :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "concat Nil ys = ys"
| "concat (Cons x xs) ys = Cons x (concat xs ys)"

export_code concat in Python

end