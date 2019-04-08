Require Import String.


Inductive arith : Type :=
  | Const (n : nat)
  | Var (x : string) 
  | Let (x : string) (e body : arith)
  | Plus (e1 e2 : arith)
  | Times (e1 e2 : arith).

Fixpoint depth (ast:arith) :=
  match ast with
  | Const _ => 1
  | Var _ => 1
  | Let _ e1 e2 => 1 + (depth e1) + (depth e2)
  | Plus e1 e2 => 1 + (max (depth e1) (depth e2))
  | Times e1 e2 => 1 + (max (depth e1) (depth e2))
  end.

Fixpoint size (ast:arith) :=
  match ast with
  | Const _ => 1
  | Var _ => 1
  | Let _ e1 e2 => 1 + (size e1) + (size e2)
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
  - simpl. linear_arithmetic.
Qed.

Fixpoint commuter (ast:arith) : arith :=
  match ast with
  | Const n => Const n
  | Var x => Var x
  | Let x e b => Let x (commuter e) (commuter b)
  | Plus e1 e2 => Plus (commuter e2) (commuter e1) 
  | Times e1 e2 => Times (commuter e2) (commuter e1)
  end.

Compute commuter (Plus (Const 1) (Times (Const 2) (Const 3))).

Theorem size_commuter : forall e, size (commuter e) = size e.
Proof.
  intros. induction e.
  - simpl. reflexivity.
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
  - simpl. reflexivity.
  - simpl. rewrite IHe1. rewrite IHe2. reflexivity.
  - simpl. rewrite IHe1. rewrite IHe2. reflexivity.
Qed.

Fixpoint substitute (e1:arith) (v:string) (e2:arith) : arith :=
  match e1 with
  | Const n => Const n
  | Var x => if x =? v then e2 else Var x
  | Let x e' e'' => if x =? v then (Let x e' e'') else (Let x e' (substitute e'' v e2))
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
  - simpl. case_eq (x =? replaceThis).
   + intros. simpl. linear_arithmetic.
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
  - simpl. case_eq (x =? replaceThis).
   + easy.
   + intros. rewrite IHinThis2. easy.
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
  - simpl. case_eq (x =? replaceThis).
   + simpl. easy.
   + intros. simpl. rewrite IHinThis2. easy.
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
 | Let x e1 e2 => eval e2 (v & {{x --> (eval e1 v)}})
 | Plus e1 e2 => (eval e1 v) + (eval e2 v)
 | Times e1 e2 => (eval e1 v) * (eval e2 v)
 end.

Example ex1 := Let "x" (Const 1)
               (Let "y" (Const 2)
                      (Plus (Var "x") (Var "y"))).
Example ex2 := Let "x" (Const 1)
               (Let "y" (Const 2)
                      (Plus (Var "x") (Times (Var "y") (Var "z")))).

Compute eval ex1 empty.
Compute eval ex2 empty.

