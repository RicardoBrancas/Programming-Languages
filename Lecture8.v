Inductive arith : Type :=
| Const (n:nat)
| Plus (e1 e2 : arith)
| Times (e1 e2 : arith).

Require Import TacticsL8.

Fixpoint size (ast:arith) : nat :=
  match ast with
  | Const n => 1
  | Plus e1 e2 => 1 + (size e1) + (size e2)
  | Times e1 e2 => 1 + (size e1) + (size e2)
  end.

Definition ex1 :=
  (Plus (Const 2) (Times (Const 1) (Const 3))).
Definition ex2 := Const 2.
Definition ex3 := Plus ex1 ex2.

Fixpoint depth (ast:arith) : nat :=
  match ast with
  | Const n => 1
  | Plus e1 e2 => 1 + (Nat.max (depth e1) (depth e2))
  | Times e1 e2 => 1 + (Nat.max (depth e1) (depth e2))
  end.

Theorem depth_le_size: forall (ast:arith),
  depth ast <= size ast.
Proof.
  intros ast.
  induction ast; simpl; linear_arithmetic.
Qed.

Fixpoint commuter (ast:arith) : arith :=
  match ast with
  | Const n => Const n
  | Plus e1 e2 => Plus (commuter e2) (commuter e1)
  | Times e1 e2 => Times (commuter e2) (commuter e1)
  end.

Theorem commuter_size: forall (ast:arith),
  depth (commuter ast) = depth ast.
Proof.
  intros ast.
  induction ast.
  - simpl. reflexivity.
  - simpl. linear_arithmetic.
  - simpl. linear_arithmetic.
Qed.

Require Import String.
Require Import TacticsL8.

Module ArithVariables.
Inductive arith : Type :=
| Const (n:nat)
| Var (v:string)
| Plus (e1 e2 : arith)
| Times (e1 e2 : arith).

Fixpoint size (ast:arith) : nat :=
  match ast with
  | Const n => 1
  | Var s => 1
  | Plus e1 e2 => 1 + (size e1) + (size e2)
  | Times e1 e2 => 1 + (size e1) + (size e2)
  end.

Definition ex1 :=
  (Plus (Const 2) (Times (Const 1) (Const 3))).
Definition ex2 := Const 2.
Definition ex3 := Plus ex1 ex2.
Definition ex4 := Times ex3 (Var "abc").

Fixpoint depth (ast:arith) : nat :=
  match ast with
  | Const n => 1
  | Var s => 1
  | Plus e1 e2 => 1 + (Nat.max (depth e1) (depth e2))
  | Times e1 e2 => 1 + (Nat.max (depth e1) (depth e2))
  end.

Fixpoint substitute (ast:arith) (s:string) (e:arith) : arith :=
  match ast with
  | Const n => Const n
  | Var v => if v =? s then e else Var v
  | Plus e1 e2 => Plus (substitute e1 s e) (substitute e2 s e)
  | Times e1 e2 => Times (substitute e1 s e) (substitute e2 s e)
  end.

Definition bindings := list (string * nat).

Definition b1 := [("x", 1);("y",2)].

Fixpoint getValue (v:string) (b:bindings) : nat :=
  match b with
  | [] => 0
  | (x, e) :: t => if x =? v then e else (getValue v t)
  end.

Fixpoint eval (b:bindings) (ast:arith) : nat :=
 match ast with
 | Const n => n
 | Var s => getValue s b 
 | Plus e1 e2 => (eval b e1) + (eval b e2)
 | Times e1 e2 => (eval b e1) * (eval b e2) 
 end.

End ArithVariables.
