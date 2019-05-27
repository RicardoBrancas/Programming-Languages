Require Import String.
Require Import List.
Import ListNotations.

Inductive expr : Type :=
| Var (x:string)
| Abs (x:string) (e:expr)
| App (e1:expr) (e2:expr).

Fixpoint is_in (a:string) (l:list string) : bool :=
  match l with
    | [] => false
    | b :: m => orb (eqb a b) (is_in a m)
  end.

Fixpoint remove_duplicates (l:list string) (acc:list string) : list string :=
match l with
| [] => acc
| h :: t => if (is_in h acc) then remove_duplicates t acc else remove_duplicates t (h :: acc)
end.


Fixpoint bv (e:expr) : list string :=
  remove_duplicates (match e with
  | Var x => []
  | Abs x t => x :: (bv t)
  | App t1 t2 => (bv t1) ++ (bv t2)
  end) [].


Fixpoint subst (t:expr) (v:string) (s:expr) : expr :=
match t with
| Var x => if eqb x v then s else t
| Abs x t' => if eqb x v then t else Abs x (subst t' v s)
| App t1 t2 => App (subst t1 v s) (subst t2 v s)
end.

Compute subst (Var "x") "x" (Var "y").
Compute subst (Var "y") "x" (Var "y").
Compute subst (Abs "x" (App (Var "y") (Var "x"))) "x" (Var "y").
Compute subst (Abs "y" (App (Var "y") (Var "x"))) "x" (Var "y").
Compute subst (Abs "y" (Abs "x" (App (Var "w") (App (Var "x") (Var "y"))))) "w" (Var "y").
Compute subst (Abs "y" (Abs "x" (App (Var "w") (App (Var "x") (Var "y"))))) "w" (Var "x").