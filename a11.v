Require Import Maps TacticsL8 String.

Notation var := string.
Definition valuation := partial_map nat.

Definition m1 := empty & {{ "x" --> 0}}.
(*
d = {}
d['x'] = 0
*)
Compute m1 "x".
Compute m1 "y".
Definition m2 := m1 & {{ "x" --> 1 }}.
Compute m2 "x".

Inductive arith : Type :=
  | Const (n : nat)
  | Var (x : var)
  | Plus (e1 e2: arith)
  | Minus (e1 e2: arith)
  | Times (e1 e2: arith).

Fixpoint interp (e:arith) (v:valuation) : nat :=
  match e with
  | Const n => n
  | Var x => match v x with
            | None => 0
            | Some n => n
            end
  | Plus e1 e2 => interp e1 v  +  interp e2 v
  | Minus e1 e2 => interp e1 v  -  interp e2 v
  | Times e1 e2 => interp e1 v  *  interp e2 v
  end.

Definition ex1 := Plus (Const 1) 
                    (Times (Const 2)  (Const 3)). (* 7 *)

Definition ex2 := Plus (Const 1) 
                    (Times (Const 2)  (Var "x")).
Compute interp ex2 m2.

Fixpoint doSomeArithmetic (e:arith) : arith :=
  match e with
  | Const _ => e
  | Var _ => e
  | Plus (Const n1) (Const n2) => Const (n1+n2)
  | Times (Const n1) (Const n2) => Const (n1*n2)
  | Plus e1 e2 => Plus (doSomeArithmetic e1)
                       (doSomeArithmetic e2)
  | Minus e1 e2 => Minus (doSomeArithmetic e1)
                         (doSomeArithmetic e2)
  | Times e1 e2 => Times (doSomeArithmetic e1)
                         (doSomeArithmetic e2)
  end.

Print ex1.
Compute doSomeArithmetic ex1.

Inductive instruction :=
 | PushConst (n : nat)
 | PushVar (x : var)
 | Add
 | Subtract
 | Multiply.

Definition run1 (i:instruction) (v:valuation) 
                (stack: list nat) : list nat :=
  match i with
  | PushConst n => n :: stack
  | PushVar x   => (match v x with
                   | None => 0 :: stack
                   | Some n => n :: stack
                   end) 
  | Add => match stack with
           | n1 :: n2 :: stack' => n1+n2 :: stack'
           | _                  => stack
          end
  | Subtract => match stack with
                | n1 :: n2 :: stack' => n1-n2 :: stack'
                | _                  => stack
                end
  | Multiply => match stack with
                | n1 :: n2 :: stack' => n1*n2 :: stack'
                | _                  => stack
                end
  end.

Definition i1 := [ PushConst 1; PushConst 2; Add ].
Definition valuation0 := empty & {{ "x" --> 1 }}.

Fixpoint run (lis: list instruction) (v: valuation) (stack:list nat) : list nat :=
  match lis with
  | nil => stack
  | i :: lis' => run lis' v (run1 i v stack)
  end.

Compute run i1 valuation0 [].

Fixpoint compile (e : arith) : list instruction :=
  match e with
  | Const n     => PushConst n :: nil
  | Var x       => PushVar x :: nil
  | Plus e1 e2  => compile e1 ++ compile e2 ++ Add :: nil
  | Minus e1 e2 => compile e1 ++ compile e2 ++ Subtract :: nil
  | Times e1 e2 => compile e1 ++ compile e2 ++ Multiply :: nil
  end.

  (*
Lemma compile_ok' : forall e v is stack,
    run (compile e ++ is) v stack = run is v (interp e v :: stack).
Proof.
  induction e; intros; simpl.
  - equality.
  - equality.
  - rewrite app_assoc_reverse. rewrite app_assoc_reverse.
    rewrite IHe1.
    rewrite IHe2. simpl. equality.
  - try repeat rewrite app_assoc_reverse.
    rewrite IHe1. rewrite IHe2. simpl. equality.
  - try repeat rewrite app_assoc_reverse.
    rewrite IHe1. rewrite IHe2. simpl. equality.
Qed.
*)

Inductive cmd : Type :=
| Skip
| Assign (x: var) (e: arith)
| Sequence (c1 c2: cmd)
| Repeat (e: arith) (body: cmd).

Fixpoint selfCompose {A} (f : A -> A) (n : nat) : A -> A :=
  match n with
  | O => fun x => x
  | S n' => fun x => selfCompose f n' (f x)
  end.


Fixpoint exec (c:cmd) (v:valuation) : valuation :=
  match c with
  | Skip => v
  | Assign x e => v & {{ x --> interp e v }}
  | Sequence c1 c2 => exec c2 (exec c1 v)
  | Repeat e body => selfCompose (exec body) (interp e v) v
  end.

Coercion Const : nat >-> arith.
Coercion Var : var >-> arith.
Infix "+" := Plus : arith_scope.
Infix "-" := Minus : arith_scope.
Infix "*" := Times : arith_scope.
Delimit Scope arith_scope with arith.
Notation "x <- e" := (Assign x e%arith) (at level 75).
Infix ";" := Sequence (at level 76).
Notation "'repeat' e 'doing' body 'done'" := (Repeat e%arith body) (at level 75).

Definition factorial :=
  "output" <- 1;
  repeat "input" doing
    "output" <- "output" * "input";
    "input" <- "input" - 1
  done.

