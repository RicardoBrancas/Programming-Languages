Require Import Coq.Lists.List.
Import ListNotations.
Require Import TacticsL8.

Module tree.

Inductive tree (T:Type) :=
| nil : tree T
| root : T -> tree T -> tree T -> tree T.
Arguments nil {T}.
Arguments root {T}.

Fixpoint nodes {X:Type} (t:tree X) : nat :=
  match t with
  | nil => 0
  | root x T1 T2 => 1 + (nodes T1) + (nodes T2)
  end.

Definition a := (root 1 (root 2 (root 3 (nil) (nil)) (nil)) (root 4 (nil) (nil))).

Fixpoint leaves {X:Type} (t:tree X) : nat :=
  match t with
  | nil => 0
  | root x nil nil => 1
  | root x T1 T2 => (leaves T1) + (leaves T2)
  end.

Fixpoint flatten {X:Type} (t:tree X) : list X :=
  match t with
  | nil => []
  | root x T1 T2 => x :: (flatten T1) ++ (flatten T2)
  end.

Fixpoint height {X:Type} (t:tree X) : nat :=
  match t with
  | nil => 0
  | root x T1 T2 => 1 + (max (height T1) (height T2))
  end.

Theorem height_atmost_nodes: forall (X:Type) (t:tree X),
  height t <= nodes t.
Proof.
  intros X t.
  induction t.
  - simpl. reflexivity.
  - simpl. linear_arithmetic.
Qed.

Fixpoint max (t:tree nat) : nat :=
 match t with
 | nil => 0
 | root x nil nil => x
 | root x T1 T2 => Nat.max x (Nat.max (max T1) (max T2))
 end.

Fixpoint subTrees {X:Type} (t:tree X) : (list (tree X)) :=
  match t with
  | nil => []
  | root x T1 T2 => [T1;T2] ++ (subTrees T1) ++ (subTrees T2)
  end.

Fixpoint mapBTree {X Y:Type} (f:X->Y) (t:tree X) : tree Y :=
  match t with
  | nil => nil
  | root x T1 T2 => root (f x) (mapBTree f T1) (mapBTree f T2)
  end.

Definition foldBTree {X Y:Type} (f:X->Y->Y) (y:Y) (t:tree X) : Y :=
  fold_right f y (flatten t).

End tree.
