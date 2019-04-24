Require Import Maps TacticsL8 String.

Notation var := string.
Definition valuation := partial_map nat.

Example m1 := empty & {{ "x" --> 0}}.
(*
d = {}
d['x'] = 0
*)
Compute m1 "x".
Compute m1 "y".
Example m2 := m1 & {{ "x" --> 1 }}.
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

Example ex1 := Plus (Const 1) 
                    (Times (Const 2)  (Const 3)). (* 7 *)

Example ex2 := Plus (Const 1) 
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
                   | None => 0
                   | Some n => n
                   end) :: stack
  | Add => match stack with
           | n1 :: n2 :: stack' => n2+n1 :: stack'
           | _                  => stack
          end
  | Subtract => match stack with
                | n1 :: n2 :: stack' => n2-n1 :: stack'
                | _                  => stack
                end
  | Multiply => match stack with
                | n1 :: n2 :: stack' => n2*n1 :: stack'
                | _                  => stack
                end
  end.

Example i1 := [ PushConst 1; PushConst 2; Add ].
Example valuation0 := empty & {{ "x" --> 1 }}.

(** This is where we stopped in Lecture 10 *)
(** We will continue from here in Lecture 11 *)

(** TODO: define run *)
Fixpoint run (is : list instruction) (v: valuation) 
             (stack : list nat) : list nat :=
  match is with
  | []   => stack  (* no state changes *)
  | i::t => run t v (run1 i v stack)
  end.

Example i2 := [ PushConst 1; PushConst 2; Add; PushConst 4; Add ].

Compute run i2 valuation0 [].


(** TODO: define compile *)
Fixpoint compile (e:arith) : list instruction :=
  match e with
  | Const n    => [PushConst n]
  | Var x      => [PushVar x]
  | Plus e1 e2 => (compile e1)  ++ (compile e2) ++ [Add]
  | Minus e1 e2 => (compile e1) ++ (compile e2) ++ [Subtract]
  | Times e1 e2 => (compile e1) ++ (compile e2) ++ [Multiply]
  end.

Example exp1 := Times (Plus (Const 1) (Const 2)) (Minus (Const 3) (Var "x")).

Example exp2 := Times exp1 exp1.

Compute compile exp2.


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

(*
Theorem compile_ok : forall e v,
    run (compile e) v nil = interp e v :: nil.
Proof.
  intros. simpl.
  (* To match the form of our lemma, we need to replace [compile e] with
   * [compile e ++ nil], adding a "pointless" concatenation of the empty list.
   * [SearchRewrite] helps us find a library lemma. *)
  rewrite (app_nil_end (compile e)).
  (* Note that we can use [rewrite] with explicit values of the first few
   * quantified variables of a lemma.  Otherwise, [rewrite] picks an
   * unhelpful place to rewrite.  (Try it and see!) *)
  apply compile_ok'.
  (* Direct appeal to a previously proved lemma *)
Qed.
*)

Inductive logic : Type :=
| bTrue
| bFalse
| Not (l:logic)
| Conjuction (l1 l2:logic)
| Le (a1 a2:arith).

Fixpoint bInterp (e:logic) (v:valuation) : bool :=
match e with
| bTrue => true
| bFalse => false
| Not l => negb (bInterp l v)
| Conjuction l1 l2 => andb (bInterp l1 v) (bInterp l2 v)
| Le a1 a2 => leb (interp a1 v) (interp a2 v)
end.

Inductive cmd : Type :=
  | Skip   (* No op command *)
  | Assign (x : var) (e : arith)
  | Sequence (c1 c2 : cmd)
  | Repeat (e : arith) (body : cmd)
  | If (b : logic) (t e: cmd).

Example prog1 :=
  Sequence (Assign "x" (Const 1)) (Assign "y" (Const 2)).
(* This is the same as x <- 1; y <- 2 *)

(** The function selfCompose will be helpful when 
    defining evaluation for our tiny imperative
    language. This function corresponds to repeated
    application of a function. *)
Fixpoint selfCompose {A} (f : A -> A) (n : nat) : A -> A :=
  match n with
  | O => fun x => x
  | S n' => fun x => selfCompose f n' (f x)
  end.

Fixpoint exec (c:cmd) (v:valuation) : valuation :=
  match c with
  | Skip            =>  v
  | Assign x e      =>  v & {{ x --> interp e v }}
  | Sequence c1 c2  =>  exec c2 (exec c1 v)
  | Repeat e body   =>  selfCompose (exec body) (interp e v) v
  | If t b1 b2      => if (bInterp t v) then exec b1 v else exec b2 v
  end.

Definition bool2logic (b:bool) : logic :=
match b with
| true => bTrue
| false => bFalse
end.

(** The following notations will be helpful later *)
Coercion Const : nat >-> arith.
Coercion Var : var >-> arith.
Coercion bool2logic : bool >-> logic.
Infix "+" := Plus : arith_scope.
Infix "-" := Minus : arith_scope.
Infix "*" := Times : arith_scope.
Infix "&&" := Conjuction : logic_scope.
Delimit Scope arith_scope with arith.
Delimit Scope logic_scope with logic.
Notation "x <- e" := (Assign x e%arith) (at level 75).
Infix ";" := Sequence (at level 76).
Notation "'repeat' e 'doing' body 'done'" := (Repeat e%arith body) (at level 75).
Notation "'testing' t 'do' b1 'or' b2 'cond'" := (If t%logic b1 b2).
Notation "'not' b" := (Not b%logic) (at level 75).

Lemma ifTrue: forall t b1 b2 v,
  (bInterp t v) = true -> exec (If t b1 b2) v = exec b1 v.
Proof.
intros. simpl. rewrite H. easy. Qed.

Lemma ifFalse: forall t b1 b2 v,
  (bInterp t v) = false -> exec (If t b1 b2) v = exec b2 v.
Proof.
intros. simpl. rewrite H. easy. Qed.

Lemma ifOneOrOther: forall t b1 b2 v,
  exec (If t b1 b2) v = exec b1 v \/ exec (If t b1 b2) v = exec b2 v.
Proof.
intros. simpl. destruct bInterp.
 - left. easy.
 - right. easy.
Qed.

(** Properties *)

Lemma cmd_seq_assoc: forall c1 c2 c3 v,
    exec ((c1 ; c2 ) ; c3)  v = exec (c1 ; (c2 ; c3)) v.
Proof.
  intros; induction c1; simpl; reflexivity.
Qed.  

Lemma cmd_seq_skip_r: forall c v,
    exec (c ; Skip) v = exec c v.
Proof.
  reflexivity.
Qed.

Lemma cmd_seq_skip_l: forall c v,
    exec (Skip ; c) v = exec c v.
Proof.
  reflexivity.
Qed.


Lemma cmd_no_repeat: forall c v,
    exec (repeat 0 doing c done) v = exec Skip v.
Proof. 
  reflexivity. 
Qed.

Lemma cmd_seq: forall c1 c2 v,
    exec (c1 ; c2) v = exec c2 (exec c1 v).
Proof.
  reflexivity.
Qed.

Lemma selfCompose_n: forall A (f:A->A) n v,
    selfCompose f (n+1) v = selfCompose f n (f v).
Proof.
  induction n.
  - simpl. reflexivity.
  - intros. simpl. rewrite IHn. reflexivity.
Qed.

Lemma cmd_repeat_unroll: forall c1 v (n:nat),
          exec (repeat (n+1) doing c1 done) v
        = exec (c1; repeat n doing c1 done) v.
Proof.
  induction n.
  - simpl. reflexivity.
  - rewrite cmd_seq. simpl in *. apply selfCompose_n.
Qed.