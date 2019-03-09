Require Import Coq.Lists.List.
Import ListNotations.

Fixpoint filter {X:Type} (test: X->bool) (l:list X) : (list X) :=
 match l with
 | [] => []
 | h :: t => if test h then h :: (filter test t)
    else filter test t
 end.

Fixpoint oddb (n:nat) : bool :=
  match n with
  | 0 => false
  | 1 => true
  | S (S n') => oddb n'
  end.

Require Import Coq.Arith.PeanoNat.

Definition remove_smaller_than (n:nat) (l:list nat) : list nat :=
  filter (fun x => n <=? x) l.

Fixpoint map {X Y: Type} (f:X->Y) (l:list X) : (list Y) :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.

Fixpoint fold {X Y:Type} (f: X -> Y -> Y) (l: list X) (b: Y) : Y :=
  match l with
  | [] => b
  | h :: t => f h (fold f t b)
  end.

Example efold1 : fold mult [1;2;3;4] 1 = 24.
Proof. auto. Qed.

Definition constfun {X:Type} (x:X) : nat -> X :=
  fun (k:nat) => x.

(* PLACEHOLDER *)

Theorem plus_0_n : forall n: nat, 0 + n = n.
Proof. intros n. simpl. reflexivity. Qed.

Theorem plus_id_ex : forall n m:nat, n = m -> n+n = m+m.
Proof. intros n m. intros H. rewrite -> H. reflexivity. Qed.

Theorem plus_id_ex2 : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof. intros n m o. intros H1 H2. rewrite H1. rewrite <- H2. reflexivity. Qed.
