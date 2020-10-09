theory Code_Python
  imports Main
begin

section \<open>ML\<close>

ML_file \<open>./code_python.ML\<close>
ML_file \<open>~~/src/Tools/Code/code_symbol.ML\<close>
ML_file \<open>~~/src/Pure/thm.ML\<close>

section \<open>Examples\<close>

print_codesetup

subsection \<open>Queue\<close>

datatype 'a queue = AQueue "'a list" "'a list"

definition empty :: "'a queue" where
  "empty = AQueue [] []"

primrec enqueue :: "'a \<Rightarrow> 'a queue \<Rightarrow> 'a queue" where
  "enqueue x (AQueue xs ys) = AQueue (x # xs) ys"

fun dequeue :: "'a queue \<Rightarrow> 'a option \<times> 'a queue" where
  "dequeue (AQueue [] []) = (None, AQueue [] [])"
| "dequeue (AQueue xs (y # ys)) = (Some y, AQueue xs ys)"
| "dequeue (AQueue xs []) = (case rev xs of y # ys \<Rightarrow> (Some y, AQueue [] ys))"

code_thms dequeue
code_deps dequeue

subsection \<open>Monoid\<close>

class semigroup =
  fixes mult :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<otimes>" 70)
  assumes assoc: "(x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"

class monoid = semigroup +
  fixes neutral :: 'a ("\<one>")
  assumes neutl: "\<one> \<otimes> x = x"
      and neutr: "x \<otimes> \<one> = x"

instantiation nat :: monoid
begin

primrec mult_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "0 \<otimes> n = (0::nat)"
| "Suc m \<otimes> n = n + m \<otimes> n"

definition neutral_nat :: "nat" where
  "\<one> = Suc 0"

lemma add_mult_distrib:
  fixes x y z :: nat
  shows "(x + y) \<otimes> z = x \<otimes> z + y \<otimes> z"
  by (induction x) simp_all

instance proof
  fix x y z :: nat
  show "(x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"
    by (induction x) (simp_all add: add_mult_distrib)
  show "\<one> \<otimes> x = x"
    by (simp add: neutral_nat_def)
  show "x \<otimes> \<one> = x"
    by (induction x) (simp_all add: neutral_nat_def)
qed

end

primrec (in monoid) pow :: "nat \<Rightarrow> 'a \<Rightarrow> 'a" where
  "pow 0 a = \<one>"
| "pow (Suc n) a = a \<otimes> pow n a"

definition bexp :: "nat \<Rightarrow> nat" where
  "bexp n = pow n (Suc (Suc 0))"

subsection \<open>List\<close>

datatype 'a list =
  Nil
| Cons 'a "'a list"

fun concat :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "concat Nil ys = ys"
| "concat (Cons x xs) ys = Cons x (concat xs ys)"

export_code Nil in Python

end