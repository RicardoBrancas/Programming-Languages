Require Import TacticsL8 Maps Arith.
Open Scope nat_scope.


(* ================================================================= *)
(** ** Arithmetic and Boolean Expressions *)
(* We start by defining types for arithmetic and boolean
   expressions. Since we are interested in having
   expressions with variables, we also need the notion
   of state. *)

Definition state := total_map nat.

Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

(** Defining a few variable names as notational shorthands will make
    examples easier to read: *)

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.

Definition bool_to_bexp (b : bool) : bexp :=
  if b then BTrue else BFalse.
Coercion bool_to_bexp : bool >-> bexp.

Bind Scope imp_scope with aexp.
Bind Scope imp_scope with bexp.
Delimit Scope imp_scope with imp.

Notation "x + y" := (APlus x y) (at level 50, left associativity) : imp_scope.
Notation "x - y" := (AMinus x y) (at level 50, left associativity) : imp_scope.
Notation "x * y" := (AMult x y) (at level 40, left associativity) : imp_scope.
Notation "x <= y" := (BLe x y) (at level 70, no associativity) : imp_scope.
Notation "x = y" := (BEq x y) (at level 70, no associativity) : imp_scope.
Notation "x && y" := (BAnd x y) (at level 40, left associativity) : imp_scope.
Notation "'~' b" := (BNot b) (at level 75, right associativity) : imp_scope.

(** We can now write [3 + (X * 2)] instead  of [APlus 3 (AMult X 2)],
    and [true && ~(X <= 4)] instead of [BAnd true (BNot (BLe X 4))]. *)

Definition example_aexp := (3 + (X * 2))%imp : aexp.
Definition example_bexp := (true && ~(X <= 4))%imp : bexp.

(** One downside of these coercions is that they can make it a little
    harder for humans to calculate the types of expressions.  If you
    get confused, try doing [Set Printing Coercions] to see exactly
    what is going on. *)

Print example_bexp.
Set Printing Coercions. 
(* In CoqIDE, this might have to be set in the View menu *)

Print example_bexp.
(* ===> example_bexp = bool_to_bexp true && ~ (AId X <= ANum 4) *)

Unset Printing Coercions.

(* ================================================================= *)
(** ** Functional Evaluation *)

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2  => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => (aeval st a1) =? (aeval st a2)
  | BLe a1 a2   => (aeval st a1) <=? (aeval st a2)
  | BNot b1     => negb (beval st b1)
  | BAnd b1 b2  => andb (beval st b1) (beval st b2)
  end.

Definition empty_st := t_empty 0.

(** Now we can add a notation for a "singleton state" with just one
    variable bound to a value. *)
Notation "a '!->' x" := (t_update empty_st a x) (at level 100).

Example aexp1 :
    aeval (X !-> 5) (3 + (X * 2))%imp
  = 13.
Proof. reflexivity. Qed.

Example bexp1 :
    beval (X !-> 5) (true && ~(X <= 4))%imp
  = true.
Proof. reflexivity. Qed.

(* ================================================================= *)
(** ** Relational Evaluation *)

Reserved Notation "st '|-' e '\\' n"
                  (at level 90, left associativity).

Inductive aevalR : aexp -> state -> nat -> Prop :=
| E_ANum (n: nat) : forall st,
    st |- (ANum n) \\ n
| E_AId (x: string) : forall st v,
    st x = v ->
    st |- (AId x) \\ v
| E_APlus (a1 a2: aexp) : forall st n1 n2 n3,
    st |- a1 \\ n1 ->
    st |- a2 \\ n2 ->
    (n1 + n2)%nat = n3 ->
    st |- APlus a1 a2 \\ n3
| E_AMinus (a1 a2: aexp) : forall st n1 n2 n3,
    st |- a1 \\ n1 ->
    st |- a2 \\ n2 ->
    (n1 - n2)%nat = n3 ->
    st |- AMinus a1 a2 \\ n3
| E_AMult (a1 a2: aexp) : forall st n1 n2 n3,
    st |- a1 \\ n1 ->
    st |- a2 \\ n2 ->
    (n1 * n2)%nat = n3 ->
    st |- AMult a1 a2 \\ n3

where "st '|-' e '\\' n" := (aevalR e st n) : type_scope.


(* TODO: exercises 1.2 and 1.4 *)


(* ================================================================= *)
(** ** Imperative Programs *)

(* We now define a small imperative language with While loops *)

Module WhileLoops.
 Inductive com : Type :=
  | CSkip
  | CAss (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

(* We define some notation *)
Bind Scope imp_scope with com.
Notation "'SKIP'" :=
   CSkip : imp_scope.
Notation "x '::=' a" :=
  (CAss x a) (at level 60) : imp_scope.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity) : imp_scope.
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity) : imp_scope.
Notation "'TEST' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity) : imp_scope.

Open Scope imp_scope.

Example prog2 := WHILE (X <= 2) DO (Y ::= Y + 1 ;; X ::= X - 1) END.

Definition fact_in_coq : com :=
  (Z ::= X;;
  Y ::= 1;;
  WHILE ~(Z = 0) DO
    Y ::= Y * Z;;
    Z ::= Z - 1
  END)%imp.

Open Scope imp_scope.

Fixpoint exec (st : state) (c : com): state :=
  match c with
    | SKIP =>  st 
    | x ::= a1 => st & {x --> (aeval st a1)}
    | c1 ;; c2 => let st' := exec st c1
                 in   exec st' c2
    | TEST b THEN c1 ELSE c2 FI => if (beval st b)
                                  then exec st c1
                                  else exec st c2
    | WHILE b DO c END => st  (* DOES NOTHING!! *)
  end.
Close Scope imp_scope.

(* Defining the semantics of while loops functionally can cause
   some problems, so now we do it relationally *)

Reserved Notation "st '=[' c ']=>' st'"
                  (at level 40).


(* TODO: exercise 1.5 *)
Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      (*TODO*)
  | E_Ass  : forall st a1 n x,
      aeval st a1 = n ->
      (*TODO*)
  | E_Seq : forall c1 c2 st st' st'',
      (*TODO*)
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      (*TODO*)
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      (*TODO*)
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      (*TODO*)
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      (*TODO*)

  where "st =[ c ]=> st'" := (ceval c st st').
       
End WhileLoops.
