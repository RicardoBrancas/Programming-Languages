Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.
  
Arguments nil {X}.
Arguments cons {X}.

Check nil.

Fixpoint repeat (X:Type) (x:X) (count:nat) : list X :=
  match count with
    | 0 => nil
    | S n => cons x (repeat X x n)
  end.

Fixpoint length {T:Type} (l:list T) : nat :=
  match l with
  | nil => 0
  | cons h t => 1 + length t
  end.

Require Import Coq.Lists.List.
Import ListNotations.

Check [1;2;3].

Fixpoint combine {X Y : Type} (l1: list X) (l2: list Y) : list (X * Y) :=
 match l1,l2 with
 | [], _                  => []
 | _, []                  => []
 | (h1 :: t1), (h2 :: t2) => (h1, h2) :: combine t1 t2
 end.

