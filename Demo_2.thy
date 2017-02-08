theory Demo_2
imports Datatype
begin

text {*
 Note: to avoid name clashes with the existing type of lists we build
 on top of Datatype rather than Main. This is an exception!
*}

datatype 'a list = Nil | Cons 'a "'a list"

primrec app :: "'a list => 'a list => 'a list" where
"app Nil ys = ys" |
"app (Cons x xs) ys = Cons x (app xs ys)"

primrec rev :: "'a list => 'a list" where
"rev Nil = Nil" |
"rev (Cons x xs) = app (rev xs) (Cons x Nil)"


value "rev(Cons True (Cons False Nil))"

value "rev(Cons a (Cons b Nil))"


text {*
  Simple proofs:

  Command 'lemma' / 'theorem': state a proposition
  Attribute 'simp': use this theorem as a simplification rule in future proofs
  Method 'induct': structural induction
  Method 'auto':  automatic proof (mostly by simplification)
  Command 'done':  end of proof
*}

lemma app_Nil2[simp]: "app xs Nil = xs"
apply (induct xs)
apply auto
done

lemma app_assoc[simp]: "app (app xs ys) zs = app xs (app ys zs)"
apply (induct xs)
apply auto
done

lemma rev_app[simp]: "rev (app xs ys) = app (rev ys) (rev xs)"
apply (induct xs)
apply auto
done

theorem rev_rev[simp]: "rev (rev xs) = xs"
apply (induct xs)
apply auto
done

(* Hint for demo:
   do the proof top down, discovering the lemmas one by one,
   as described in LNCS2283.
*)

end