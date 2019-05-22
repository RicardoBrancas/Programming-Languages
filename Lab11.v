Require Import String.
Require Import List.
Import ListNotations.

Inductive expr : Type :=
| Var (x:string)
| Abs (x:string) (e:expr)
| App (e1:expr) (e2:expr).

Coercion Var : string >-> expr. 
Notation "'lamb' x '.' e" := (Abs x e) (at level 90).
Notation "t1 ' t2" := (App t1 t2) (at level 90).

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

Compute bv (App "x").

