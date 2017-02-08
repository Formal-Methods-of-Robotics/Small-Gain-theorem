(* A simple comment *)

theory Demo_1
imports Main
begin

text {* This is also a comment but it generates nice \LaTeX-text! *}

text {*
 Note that free variables (eg x) and constants (eg Suc) are displayed
 differently.  *}

term "x"
term "Suc x"
term "Succ x"

text{* To display types: menu Isabelle/Isar -> Settings -> Show Types *}

text {* Warning: 0 and + are overloaded: *}

term  "n + n = 0" 
term "(n::nat) + n = 0"
term "n + n = Suc m"

text {* A bound variable: *}
term "map (\<lambda>n. Suc n + 1) [0, 1] = [2, 3]"

(*
Try this:

term "Suc n = True"

Terms must be type correct!
*)

end