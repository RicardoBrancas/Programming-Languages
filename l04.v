Require Import String.


Inductive arith : Type :=
  | Const (n : nat)
  | Var (x : string) 
  | Plus (e1 e2 : arith)
  | Times (e1 e2 : arith).

Fixpoint depth (ast:arith) :=
  match ast with
  | Const _ => 1
  | Var _ => 1
  | Plus e1 e2 => 1 + (max (depth e1) (depth e2))
  | Times e1 e2 => 1 + (max (depth e1) (depth e2))
  end.

Fixpoint size (ast:arith) :=
  match ast with
  | Const _ => 1
  | Var _ => 1
  | Plus e1 e2 => 1 + (plus (size e1) (size e2))
  | Times e1 e2 => 1 + (plus (size e1) (size e2))
  end.

Require Import TacticsL8.

Theorem depth_le_size : forall e, depth e <= size e.
Proof.
  intros. induction e.
  - simpl. linear_arithmetic.
  - simpl. linear_arithmetic.
  - simpl. linear_arithmetic.
  - simpl. linear_arithmetic.
Qed.

Fixpoint commuter (ast:arith) : arith :=
  match ast with
  | Const n => Const n
  | Var x => Var x
  | Plus e1 e2 => Plus (commuter e2) (commuter e1) 
  | Times e1 e2 => Times (commuter e2) (commuter e1)
  end.

Compute commuter (Plus (Const 1) (Times (Const 2) (Const 3))).

Theorem size_commuter : forall e, size (commuter e) = size e.
Proof.
  intros. induction e.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. rewrite IHe1. rewrite IHe2. linear_arithmetic.
  - simpl. rewrite IHe1. rewrite IHe2. linear_arithmetic.
Qed.

Theorem commuter_inverse : forall e, commuter (commuter e) = e.
Proof.
  intros. induction e.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. rewrite IHe1. rewrite IHe2. reflexivity.
  - simpl. rewrite IHe1. rewrite IHe2. reflexivity.
Qed.

Fixpoint substitute (e1:arith) (v:string) (e2:arith) : arith :=
  match e1 with
  | Const n => Const n
  | Var x => if x =? v then e2 else Var x
  | Plus p1 p2 => Plus (substitute p1 v e2) (substitute p2 v e2)
  | Times p1 p2 => Times (substitute p1 v e2) (substitute p2 v e2)
  end.

Theorem substitute_depth : forall replaceThis withThis inThis,
        depth (substitute inThis replaceThis withThis)
        <= depth inThis + depth withThis.
Proof.
  intros. induction inThis.
  - simpl. linear_arithmetic.
  - simpl. case_eq (x =? replaceThis).
   + intros. linear_arithmetic.
   + intros. simpl. linear_arithmetic.
  - simpl. linear_arithmetic.
  - simpl. linear_arithmetic.
Qed.

Theorem substitute_self : forall replaceThis inThis,
    substitute inThis replaceThis (Var replaceThis) = inThis.
Proof.
  induction inThis.
  - simpl. reflexivity.
  - simpl. case_eq (x =? replaceThis).
   + rewrite eqb_eq. intros. rewrite H. reflexivity.
   + easy.
  - simpl. rewrite IHinThis1. rewrite IHinThis2. reflexivity.
  - simpl. rewrite IHinThis1. rewrite IHinThis2. reflexivity.
Qed.

Theorem substitute_commuter : forall replaceThis withThis inThis,
    commuter (substitute inThis replaceThis withThis)
  = substitute (commuter inThis) replaceThis (commuter withThis).
Proof.
  induction inThis.
  - simpl. reflexivity.
  - simpl. case_eq (x =? replaceThis).
   + reflexivity.
   + simpl. reflexivity.
  - simpl. rewrite IHinThis1. rewrite IHinThis2. reflexivity.
  - simpl. rewrite IHinThis1. rewrite IHinThis2. reflexivity.
Qed.

Require Import Maps.

Definition valuation := partial_map nat.

Fixpoint eval (e:arith) (v:valuation) : nat :=
 match e with
 | Const n => n
 | Var x => match v x with
            | None => 0
            | Some p => p
            end
 | Plus e1 e2 => (eval e1 v) + (eval e2 v)
 | Times e1 e2 => (eval e1 v) * (eval e2 v)
 end.
