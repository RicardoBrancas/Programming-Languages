Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Init.Nat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
Import ListNotations.
Require Import Maps.
Require Import Imp.


Inductive tm : Type :=
  | C : nat -> tm         (* Constant *)
  | P : tm -> tm -> tm.   (* Plus *)

(** Exercise 1: implement an evaluation function for
this toy language *)


Module SSSNoValues.

(** Exercise 2: implement an evaluation relation for this 
toy language *)


Reserved Notation " t '==>' n " (at level 50, left associativity).

Inductive eval : tm -> nat -> Prop :=
  | E_Const : forall n,
     C n ==> n
  | E_Plus : forall t1 t2 n1 n2,
     t1 ==> n1 -> t2 ==> n2 -> P t1 t2 ==> (n1 + n2)
where " t '==>' n " := (eval t n).

(** Exercise 3: define a small-step semantics for this 
toy language *)

(** The rules are: 

    
                     -------------------------------        (ST_PlusConstConst)
                     P (C n1) (C n2) --> C (n1 + n2)

                              t1 --> t1'
                         --------------------                        (ST_Plus1)
                         P t1 t2 --> P t1' t2

                              t2 --> t2'
                      ----------------------------                   (ST_Plus2)
                      P (C n1) t2 --> P (C n1) t2'
*)

(** Solution: *)
Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_Plus2 : forall n1 t2 t2',
      t2 --> t2' ->
      P (C n1) t2 --> P (C n1) t2'
  where " t '-->' t' " := (step t t').


(** Exercise 4: prove the following examples *)

Example test_step_1 :
      P
        (P (C 0) (C 3))
        (P (C 2) (C 4))
      -->
      P
        (C (0 + 3))
        (P (C 2) (C 4)).
Proof.
  apply ST_Plus1. apply ST_PlusConstConst.
Qed.

Example test_step_2 :
      P
        (C 0)
        (P
          (C 2)
          (P (C 0) (C 3)))
      -->
      P
        (C 0)
        (P
          (C 2)
          (C (0 + 3))).
Proof.
  apply ST_Plus2. apply ST_Plus2. apply ST_PlusConstConst.
Qed.

End SSSNoValues.

Module SSSValues.

Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n).

(**  Exercise 5: encode the following rules: *)

(** 
                     -------------------------------        (ST_PlusConstConst)
                     P (C n1) (C n2) --> C (n1 + n2)

                              t1 --> t1'
                         --------------------                        (ST_Plus1)
                         P t1 t2 --> P t1' t2

                               value v1
                              t2 --> t2'
                         --------------------                        (ST_Plus2)
                         P v1 t2 --> P v1 t2'
*)

(**  Solution: *)

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' -> P t1 t2 --> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      value v1 -> t2 --> t2' -> P v1 t2 --> P v1 t2'

  where " t '-->' t' " := (step t t').

End SSSValues.






(** We will now define a small-step semantics
for the tiny imperative language Imp. We start with
arithmetic expressions and boolean expressions *)

Inductive aval : aexp -> Prop :=
  | av_num : forall n, aval (ANum n).

(** Exercise 6: complete the following definition. *)

Reserved Notation " t '/' st '-->a' t' "
                  (at level 40, st at level 39).

Inductive astep : state -> aexp -> aexp -> Prop :=
  | AS_Id : forall st i,
      AId i / st -->a ANum (st i)
  | AS_Plus1 : forall st a1 a1' a2,
      a1 / st -->a a1' ->
      (APlus a1 a2) / st -->a (APlus a1' a2)
  | AS_Plus2 : forall st v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      (APlus v1 a2) / st -->a (APlus v1 a2')
  | AS_Plus : forall st n1 n2,
      APlus (ANum n1) (ANum n2) / st -->a ANum (n1 + n2)
  | AS_Minus1 : forall st a1 a1' a2,
      a1 / st -->a a1' ->
      (AMinus a1 a2) / st -->a (AMinus a1' a2)
  | AS_Minus2 : forall st v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      (AMinus v1 a2) / st -->a (AMinus v1 a2')
  | AS_Minus : forall st n1 n2,
      (AMinus (ANum n1) (ANum n2)) / st -->a ANum (n1 - n2)
  | AS_Mult1 : forall st a1 a1' a2,
      a1 / st -->a a1' ->
      (AMult a1 a2) / st -->a (AMult a1' a2)
  | AS_Mult2 : forall st v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      (AMult v1 a2) / st -->a (AMult v1 a2')
  | AS_Mult : forall st n1 n2,
      (AMult (ANum n1) (ANum n2)) / st -->a ANum (n1 * n2)

    where " t '/' st '-->a' t' " := (astep st t t').


Example st1 := empty_st.
Example st2 := (X !-> 1).

(** Exercise 7: use this newly defined semantics to evaluate the
following example: *)
Example aexp1_eval1:
  APlus (APlus (ANum 1) (ANum 2)) (ANum 3) / empty_st
  -->a 
  APlus (ANum 3) (ANum 3).
Proof.
  apply AS_Plus1. apply AS_Plus.
Qed.


(** Exercise 8: do the same for boolean expressions. *)
Reserved Notation " t '/' st '-->b' t' "
                  (at level 40, st at level 39).

Inductive bstep : state -> bexp -> bexp -> Prop :=
| BS_Eq1 : forall st a1 a1' a2,
    a1 / st -->a a1' ->
    (BEq a1 a2) / st -->b (BEq a1' a2)
| BS_Eq2 : forall st v1 a2 a2',
    aval v1 ->
    a2 / st -->a a2' ->
    (BEq v1 a2) / st -->b (BEq v1 a2')
| BS_Eq : forall st n1 n2,
    (BEq (ANum n1) (ANum n2)) / st -->b
    (if (n1 =? n2) then BTrue else BFalse)
| BS_LtEq1 : forall st a1 a1' a2,
    a1 / st -->a a1' ->
    (BLe a1 a2) / st -->b (BLe a1' a2)
| BS_LtEq2 : forall st v1 a2 a2',
    aval v1 ->
    a2 / st -->a a2' ->
    (BLe v1 a2) / st -->b (BLe v1 a2')
| BS_LtEq : forall st n1 n2,
    (BLe (ANum n1) (ANum n2)) / st -->b
             (if (n1 <=? n2) then BTrue else BFalse)
| BS_NotStep : forall st b1 b1',
    b1 / st -->b b1' ->
    (BNot b1) / st -->b (BNot b1')
| BS_NotTrue : forall st,
    (BNot BTrue) / st -->b BFalse
| BS_NotFalse : forall st,
    (BNot BFalse) / st -->b BTrue
| BS_AndTrueStep : forall st b2 b2',
    b2 / st -->b b2' ->
    (BAnd BTrue b2) / st -->b b2
| BS_AndStep : forall st b1 b1' b2,
    b1 / st -->b b1' ->
    (BAnd b1 b2) / st -->b (BAnd b1' b2)
| BS_AndTrueTrue : forall st,
    (BAnd BTrue BTrue) / st -->b BTrue
| BS_AndTrueFalse : forall st,
    (BAnd BTrue BFalse) / st -->b BFalse
| BS_AndFalse : forall st b2,
    (BAnd BFalse b2) / st -->b BFalse

where " t '/' st '-->b' t' " := (bstep st t t').

(** Exercise 9: complete the small-step semantics for
commands. *)

Reserved Notation " t '/' st '-->' t' '/' st' "
                  (at level 40, st at level 39, t' at level 39).

Open Scope imp_scope.
Inductive cstep : (com * state) -> (com * state) -> Prop :=
  | CS_AssStep : forall st i a a',
      a / st -->a a' ->
      (i ::= a) / st --> (i ::= a') / st
  | CS_Ass : forall st i n,
      (i ::= (ANum n)) / st --> SKIP / (i !-> n; st)
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st --> c1' / st' ->
      (c1 ;; c2) / st --> (c1' ;; c2) / st'
  | CS_SeqFinish : forall st c2,
      (SKIP ;; c2) / st --> c2 / st
  | CS_IfStep : forall st b b' c1 c2,
      b / st -->b b' ->
      TEST b  THEN c1 ELSE c2 FI / st
      -->
    ( TEST b' THEN c1 ELSE c2 FI ) / st
  | CS_IfTrue : forall st c1 c2,
      TEST BTrue THEN c1 ELSE c2 FI / st --> c1 / st
  | CS_IfFalse : forall st c1 c2,
      TEST BFalse THEN c1 ELSE c2 FI / st --> c2 / st
  | CS_While : forall st b c1,
      WHILE b DO c1 END / st
      -->
    ( TEST b THEN c1 ;; (WHILE b DO c1 END) ELSE SKIP FI ) / st

  where " t '/' st '-->' t' '/' st' " := (cstep (t,st) (t',st')).

Close Scope imp_scope.


(* ################################################################# *)
(** * Concurrent Imp *)

(** Finally, to show the power of this definitional style, let's
    enrich Imp with a new form of command that runs two subcommands in
    parallel and terminates when both have terminated.  To reflect the
    unpredictability of scheduling, the actions of the subcommands may
    be interleaved in any order, but they share the same memory and
    can communicate by reading and writing the same variables. *)

Module CImp.

Inductive com : Type :=
  | CSkip : com
  | CAss : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CPar : com -> com -> com.         (* <--- NEW *)

Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'TEST' b 'THEN' c1 'ELSE' c2 'FI'" :=
  (CIf b c1 c2) (at level 80, right associativity).
Notation "'PAR' c1 'WITH' c2 'END'" :=
  (CPar c1 c2) (at level 80, right associativity).


(** Exercise 10: define the small-step semantics of Concurrent Imp *)
Inductive cstep : (com * state)  -> (com * state) -> Prop :=
    (* Old part *)
  | CS_AssStep : forall st i a a',
      a / st -->a a' ->
      (i ::= a) / st --> (i ::= a') / st
  | CS_Ass : forall st i n,
      (i ::= (ANum n)) / st --> SKIP / (i !-> n ; st)
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st --> c1' / st' ->
      (c1 ;; c2) / st --> (c1' ;; c2) / st'
  | CS_SeqFinish : forall st c2,
      (SKIP ;; c2) / st --> c2 / st
  | CS_IfStep : forall st b b' c1 c2,
      b /st -->b b' ->
          (TEST b THEN c1 ELSE c2 FI) / st 
      --> (TEST b' THEN c1 ELSE c2 FI) / st
  | CS_IfTrue : forall st c1 c2,
      (TEST BTrue THEN c1 ELSE c2 FI) / st --> c1 / st
  | CS_IfFalse : forall st c1 c2,
      (TEST BFalse THEN c1 ELSE c2 FI) / st --> c2 / st
  | CS_While : forall st b c1,
          (WHILE b DO c1 END) / st 
      --> (TEST b THEN (c1;; (WHILE b DO c1 END)) ELSE SKIP FI) / st
    (* New part: *)
  | CS_Par1 : forall st c1 c1' c2 st',
      c1 / st --> c1' / st' ->
      (PAR c1 WITH c2 END) / st --> (PAR c1' WITH c2 END) / st'
  | CS_Par2 : forall st c1 c2 c2' st',
      c2 / st --> c2' / st' ->
      (PAR c1 WITH c2 END) / st --> (PAR c1 WITH c2' END) / st'
  | CS_ParDone : forall st,
      (PAR SKIP WITH SKIP END) / st --> SKIP / st
  where " t '/' st '-->' t' '/' st' " := (cstep (t,st) (t',st')).



(** Here, we define something that will allow us to write some
interesting properties. See section "Multi-step relations"
for more details. *)
Definition relation (X : Type) := X -> X -> Prop.
Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.
Definition cmultistep := multi cstep.

Notation " t '/' st '-->*' t' '/' st' " :=
   (multi cstep  (t,st) (t',st'))
   (at level 40, st at level 39, t' at level 39).



(** Here's the example shown in the slides: *)
Definition par_ex1 : com :=
  PAR
    X ::= 1
  WITH
    X ::= 42
  END.
Example par_ex1_0:
  exists st',
       par_ex1 / empty_st  -->* SKIP / st'
    /\ st' X = 42.
Proof.
eapply ex_intro. split.
  unfold par_ex1.
  eapply multi_step. apply CS_Par1.
    apply CS_Ass.

  eapply multi_step. apply CS_Par2.
    apply CS_Ass.
  eapply multi_step. apply CS_ParDone.
eapply multi_refl.
  reflexivity.
Qed.

Example par_ex1_1:
  exists st',
       par_ex1 / empty_st  -->* SKIP / st'
    /\ st' X = 1.
Proof.
  eapply ex_intro. split.
  unfold par_ex1.
  eapply multi_step. apply CS_Par2.
  apply CS_Ass.

  eapply multi_step. apply CS_Par1.
  apply CS_Ass.
  
  eapply multi_step. apply CS_ParDone.
  eapply multi_refl.reflexivity.
Qed.
 

(** Among the (many) interesting properties of this language is the fact
    that the following program can terminate with the variable [X] set
    to any value. *)

Definition par_loop : com :=
  PAR
    Y ::= 1
  WITH
    WHILE Y = 0 DO
      X ::= X + 1
    END
  END.

(** In particular, it can terminate with [X] set to [0]: *)

Example par_loop_example_0:
  exists st',
       par_loop / empty_st  -->* SKIP / st'
    /\ st' X = 0.
Proof.
  eapply ex_intro. split.
  unfold par_loop.
  eapply multi_step. apply CS_Par1.
    apply CS_Ass.
  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfFalse.
  eapply multi_step. apply CS_ParDone.
  eapply multi_refl.
  reflexivity. Qed.

(** It can also terminate with [X] set to [2]: *)

Example par_loop_example_2:
  exists st',
       par_loop / empty_st -->* SKIP / st'
    /\ st' X = 2.
Proof.
  eapply ex_intro. split.
  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfTrue.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_Ass.
  eapply multi_step. apply CS_Par2. apply CS_SeqFinish.

  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfTrue.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_Ass.

  eapply multi_step. apply CS_Par1. apply CS_Ass.
  eapply multi_step. apply CS_Par2. apply CS_SeqFinish.
  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfFalse.
  eapply multi_step. apply CS_ParDone.
  eapply multi_refl.
  reflexivity. Qed.

End CImp.