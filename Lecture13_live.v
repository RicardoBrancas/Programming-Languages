Require Import String TacticsL8 Maps.


Module AExp.
Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus  a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult  a1 a2 => (aeval a1) * (aeval a2)
  end.

Example test_aeval1:
  aeval (APlus (ANum 2) (ANum 2)) = 4.
Proof. reflexivity. Qed.

Open Scope nat_scope.
Fixpoint beval (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => (aeval a1) =? (aeval a2)
  | BLe a1 a2   => (aeval a1) <=? (aeval a2)
  | BNot b1     => negb (beval b1)
  | BAnd b1 b2  => andb (beval b1) (beval b2)
  end.

Module aevalR_first_try.

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum n :
      aevalR (ANum n) n
  | E_APlus (e1 e2: aexp) (n1 n2: nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus (e1 e2: aexp) (n1 n2: nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult (e1 e2: aexp) (n1 n2: nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMult e1 e2) (n1 * n2).

Module TooHardToRead.

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum n :
      aevalR (ANum n) n
  | E_APlus (e1 e2: aexp) (n1 n2: nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus (e1 e2: aexp) (n1 n2: nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult (e1 e2: aexp) (n1 n2: nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (AMult e1 e2) (n1 * n2).
End TooHardToRead.

Notation "e '\\' n"
         := (aevalR e n)
            (at level 50, left associativity)
         : type_scope.

End aevalR_first_try.

Reserved Notation "e '\\' n" (at level 90, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      (ANum n) \\ n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 \\ n1) -> (e2 \\ n2) -> (APlus e1 e2) \\ (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 \\ n1) -> (e2 \\ n2) -> (AMinus e1 e2) \\ (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 \\ n1) -> (e2 \\ n2) -> (AMult e1 e2) \\ (n1 * n2)

  where "e '\\' n" := (aevalR e n) : type_scope.


Theorem aeval_iff_aevalR : forall a n,
  (a \\ n) <-> aeval a = n.
Proof.
 split.
 - (* -> *)
   intros H.
   induction H; simpl.
   + (* E_ANum *)
     reflexivity.
   + (* E_APlus *)
     rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
   + (* E_AMinus *)
     rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
   + (* E_AMult *)
     rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
 - (* <- *)
   generalize dependent n.
   induction a;
      simpl; intros; subst.
   + (* ANum *)
     apply E_ANum.
   + (* APlus *)
     apply E_APlus.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
   + (* AMinus *)
     apply E_AMinus.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
   + (* AMult *)
     apply E_AMult.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
Qed.

Theorem aeval_iff_aevalR' : forall a n,
  (a \\ n) <-> aeval a = n.
Proof.
  (* WORKED IN CLASS *)
  split.
  - (* -> *)
    intros H; induction H; subst; reflexivity.
  - (* <- *)
    generalize dependent n.
    induction a; simpl; intros; subst; constructor;
       try apply IHa1; try apply IHa2; reflexivity.
Qed.

Inductive bevalR: bexp -> bool -> Prop :=
(* FILL IN HERE *)
.

Lemma beval_iff_bevalR : forall b bv,
  bevalR b bv <-> beval b = bv.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

Module aevalR_division.

(** For example, suppose that we wanted to extend the arithmetic
    operations with division: *)

Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
  | ADiv (a1 a2 : aexp).         (* <--- NEW *)

(** Extending the definition of [aeval] to handle this new operation
    would not be straightforward (what should we return as the result
    of [ADiv (ANum 5) (ANum 0)]?).  But extending [aevalR] is
    straightforward. *)

Reserved Notation "e '\\' n"
                  (at level 90, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      (ANum n) \\ n
  | E_APlus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 \\ n1) -> (a2 \\ n2) -> (APlus a1 a2) \\ (n1 + n2)
  | E_AMinus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 \\ n1) -> (a2 \\ n2) -> (AMinus a1 a2) \\ (n1 - n2)
  | E_AMult (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 \\ n1) -> (a2 \\ n2) -> (AMult a1 a2) \\ (n1 * n2)
  | E_ADiv (a1 a2 : aexp) (n1 n2 n3 : nat) :
      (a1 \\ n1) -> (a2 \\ n2) -> (n2 > 0) ->
      (mult n2 n3 = n1) -> (ADiv a1 a2) \\ n3

where "a '\\' n" := (aevalR a n) : type_scope.

End aevalR_division.

Module aevalR_extended.

Reserved Notation "e '\\' n" (at level 90, left associativity).

Inductive aexp : Type :=
  | AAny                           (* <--- NEW *)
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

(** Again, extending [aeval] would be tricky, since now evaluation is
    _not_ a deterministic function from expressions to numbers, but
    extending [aevalR] is no problem... *)

Inductive aevalR : aexp -> nat -> Prop :=
  | E_Any (n : nat) :
      AAny \\ n                        (* <--- NEW *)
  | E_ANum (n : nat) :
      (ANum n) \\ n
  | E_APlus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 \\ n1) -> (a2 \\ n2) -> (APlus a1 a2) \\ (n1 + n2)
  | E_AMinus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 \\ n1) -> (a2 \\ n2) -> (AMinus a1 a2) \\ (n1 - n2)
  | E_AMult (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 \\ n1) -> (a2 \\ n2) -> (AMult a1 a2) \\ (n1 * n2)

where "a '\\' n" := (aevalR a n) : type_scope.

End aevalR_extended.

End AExp.

(* ======================================== *)
(* JFF *)

Definition state := total_map nat.

Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string)              (* <--- NEW *)
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

Set Printing Coercions.

Print example_bexp.
(* ===> example_bexp = bool_to_bexp true && ~ (AId X <= ANum 4) *)

Unset Printing Coercions.

(* ================================================================= *)
(** ** Evaluation *)

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x                                (* <--- NEW *)
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2  => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Open Scope nat_scope.
Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => (aeval st a1) =? (aeval st a2)
  | BLe a1 a2   => (aeval st a1) <=? (aeval st a2)
  | BNot b1     => negb (beval st b1)
  | BAnd b1 b2  => andb (beval st b1) (beval st b2)
  end.

(** We specialize our notation for total maps to the specific case of
    states, i.e. using [(_ !-> 0)] as empty state. *)

Definition empty_st := t_empty 0.
(*
Definition empty_st := (_ !-> 0).
*)
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



(* ======================================== *)
(* JFF *)


(** Lecture 13 *)

Module ComWithRepeat.

  Inductive com : Type :=
  | CSkip
  | CAss (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CRepeat (a : aexp) (c : com).

Fixpoint selfCompose {A} (f : A -> A) (n : nat) : A -> A :=
  match n with
  | O => fun x => x
  | S n' => fun x => selfCompose f n' (f x)
  end.

Bind Scope imp_scope with com.
Notation "'SKIP'" :=
   CSkip : imp_scope.
Notation "x '::=' a" :=
  (CAss x a) (at level 60) : imp_scope.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity) : imp_scope.
Notation "'REPEAT' a 'DO' c 'END'" :=
  (CRepeat a c) (at level 80, right associativity) : imp_scope.
Notation "'TEST' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity) : imp_scope.

Open Scope imp_scope.

Example prog1 := REPEAT X+1 DO (Y ::= Y + 1 ;; Z ::= Z + 2) END.

Fixpoint exec (c : com) (st : state) : state :=
  match c with
    | SKIP => st
    | x ::= a1 => st & {x --> (aeval st a1)}
    | c1 ;; c2 =>  let st' := exec c1 st
                 in exec c2 st'
    | TEST b THEN c1 ELSE c2 FI =>
        if (beval st b)
          then exec c1 st
          else exec c2 st
    | REPEAT a DO c END => selfCompose (exec c) (aeval st a) st
  end.

(** Example: run prog1 on initial state **)
Example initial_state := t_empty 0 & { X --> 1}.


End ComWithRepeat.



(** Lecture 13: while loops *)

Inductive com : Type :=
  | CSkip
  | CAss (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

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


Reserved Notation "st '=[' c ']=>' st'"
                  (at level 40).


Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ SKIP ]=> st
  | E_Ass  : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x ::= a1 ]=> st & {x --> n}
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ;; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ WHILE b DO c END ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ WHILE b DO c END ]=> st'' ->
      st  =[ WHILE b DO c END ]=> st''

  where "st =[ c ]=> st'" := (ceval c st st').

Example ceval_example1:
  empty_st =[
     X ::= 2;;
     TEST X <= 1
       THEN Y ::= 3
       ELSE Z ::= 4
     FI
  ]=> (X !-> 2) & { Z --> 4 }.
Proof.
  (* We must supply the intermediate state *)
  apply E_Seq with (X !-> 2).
  - (* assignment command *)
    apply E_Ass. reflexivity.
  - (* if command *)
    apply E_IfFalse.
    reflexivity.
    apply E_Ass. reflexivity.
Qed.

Theorem ceval_deterministic: forall c st st1 st2,
     st =[ c ]=> st1  ->
     st =[ c ]=> st2 ->
                 st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  induction E1;
           intros st2 E2; inversion E2; subst.
  - (* E_Skip *) reflexivity.
  - (* E_Ass *) reflexivity.
  - (* E_Seq *)
    assert (st' = st'0) as EQ1.
    { (* Proof of assertion *) apply IHE1_1; assumption. }
    subst st'0.
    apply IHE1_2. assumption.
  - (* E_IfTrue, b1 evaluates to true *)
      apply IHE1. assumption.
  - (* E_IfTrue,  b1 evaluates to false (contradiction) *)
      rewrite H in H5. discriminate H5.
  - (* E_IfFalse, b1 evaluates to true (contradiction) *)
      rewrite H in H5. discriminate H5.
  - (* E_IfFalse, b1 evaluates to false *)
      apply IHE1. assumption.
  - (* E_WhileFalse, b1 evaluates to false *)
    reflexivity.
  - (* E_WhileFalse, b1 evaluates to true (contradiction) *)
    rewrite H in H2. discriminate H2.
  - (* E_WhileTrue, b1 evaluates to false (contradiction) *)
    rewrite H in H4. discriminate H4.
  - (* E_WhileTrue, b1 evaluates to true *)
      assert (st' = st'0) as EQ1.
      { (* Proof of assertion *) apply IHE1_1; assumption. }
      subst st'0.
      apply IHE1_2. assumption.  Qed.



(** * Hoare: Hoare Logic *)
Set Warnings "-notation-overridden,-parsing".
Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import omega.Omega.
Require Import Imp.






Definition Assertion := state -> Prop.


Example as1 := fun st => st X <= st Y.
Example as2 := fun st => st X = 3 \/ st X <= st Y.


Module ExAssertions.
Definition as1 : Assertion := fun st => st X = 3.
Definition as2 : Assertion := fun st => st X <= st Y.
Definition as3 : Assertion :=
  fun st => st X = 3 \/ st X <= st Y.
Definition as4 : Assertion :=
  fun st => st Z * st Z <= st X /\
            ~ (((S (st Z)) * (S (st Z))) <= st X).
Definition as5 : Assertion := fun st => True.
Definition as6 : Assertion := fun st => False.

End ExAssertions.



Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Notation "P ->> Q" := (assert_implies P Q)
                      (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.

Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.


Definition hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
     st =[ c ]=> st'  ->
     P st  ->
     Q st'.

Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.

Theorem hoare_post_true : forall (P Q : Assertion) c,
  (forall st, Q st) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros st st' Heval HP.
  apply H.  Qed.

Theorem hoare_pre_false : forall (P Q : Assertion) c,
  (forall st, ~ (P st)) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros st st' Heval HP.
  unfold not in H. apply H in HP.
  inversion HP.  Qed.


(* SKIP *)
Theorem hoare_skip : forall P,
    {{P}} SKIP {{P}}.
Proof.
  intros P st st' H HP. inversion H. subst.
  assumption.  Qed.

Example spec1 :
  {{ fun st => st X = 2 }} SKIP {{ fun st => st X = 2 }}.
Proof. apply hoare_skip. Qed.

Definition assn_sub X a P : Assertion :=
  fun (st : state) =>
    P (st & {X --> aeval st a}).
    (*P (X !-> aeval st a ; st).*)

Notation "P [ X |-> a ]" := (assn_sub X a P)
  (at level 10, X at next level).


(* ASSIGNMENT *)
Theorem hoare_asgn : forall Q X a,
    {{Q [X |-> a]}} X ::= a {{Q}}.
Proof.
  unfold hoare_triple.
  intros Q X a st st' HE HQ.
  inversion HE. subst.
  unfold assn_sub in HQ. assumption.  Qed.

Example assn_sub_example :
  {{(fun st => st X < 5) [X |-> X + 1]}}
  X ::= X + 1
  {{fun st => st X < 5}}.
Proof.
  apply hoare_asgn.
Qed.


(** The following fails! *)
Example hoare_asgn_fails :
  {{fun st => True}}
  X ::= 1
  {{fun st => st X = 1}}.
Proof.
  apply hoare_asgn.
Qed.



(* Consequence *)
Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q c Hhoare Himp.
  intros st st' Hc HP. apply (Hhoare st st').
  assumption. apply Himp. assumption. Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P Q Q' c Hhoare Himp.
  intros st st' Hc HP.
  apply Himp.
  apply (Hhoare st st').
  assumption. assumption. Qed.

Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} ->
  P ->> P' ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q Q' c Hht HPP' HQ'Q.
  apply hoare_consequence_pre with (P' := P').
  apply hoare_consequence_post with (Q' := Q').
  assumption. assumption. assumption.  Qed.


(* Example: Consequence *)
Example hoare_asgn_example1' :
  {{fun st => True}}
  X ::= 1
  {{fun st => st X = 1}}.
Proof.
  eapply hoare_consequence_pre.
  apply hoare_asgn.
  intros st H.  reflexivity.  Qed.

Theorem hoare_seq : forall P Q R c1 c2,
     {{Q}} c2 {{R}} ->
     {{P}} c1 {{Q}} ->
     {{P}} c1;;c2 {{R}}.
Proof.
  intros P Q R c1 c2 H1 H2 st st' H12 Pre.
  inversion H12; subst.
  apply (H1 st'0 st'); try assumption.
  apply (H2 st st'0); assumption. Qed.

Example hoare_asgn_example3 : forall a n,
  {{fun st => aeval st a = n}}
  X ::= a;; SKIP
  {{fun st => st X = n}}.
Proof.
  intros a n. eapply hoare_seq.
  - (* right part of seq *) apply hoare_skip.
  - (* left part of seq *) eapply hoare_consequence_pre. apply hoare_asgn.
    intros st H. subst. reflexivity.
Qed.

Example hoare_asgn_example4 :
  {{fun st => True}}
  X ::= 1;; Y ::= 2
  {{fun st => st X = 1 /\ st Y = 2}}.
Proof.
  (* FILL IN HERE *) Admitted.

Definition swap_program : com :=
  Z ::= X;; X ::= Y;; Y ::= Z.

Theorem swap_exercise :
  {{fun st => st X <= st Y}}
  swap_program
  {{fun st => st Y <= st X}}.
Proof.
  eapply hoare_seq.
  -eapply hoare_seq; apply hoare_asgn.
  - admit.
 (*end hide*)
  (* FILL IN HERE *) Admitted.


Definition bassn b : Assertion :=
  fun st => (beval st b = true).

Lemma bexp_eval_true : forall b st,
  beval st b = true -> (bassn b) st.
Proof.
  intros b st Hbe.
  unfold bassn. assumption.  Qed.

Lemma bexp_eval_false : forall b st,
  beval st b = false -> ~ ((bassn b) st).
Proof.
  intros b st Hbe contra.
  unfold bassn in contra.
  rewrite -> contra in Hbe. inversion Hbe.  Qed.

Theorem hoare_if : forall P Q b c1 c2,
  {{fun st => P st /\ bassn b st}} c1 {{Q}} ->
  {{fun st => P st /\ ~ (bassn b st)}} c2 {{Q}} ->
  {{P}} TEST b THEN c1 ELSE c2 FI {{Q}}.
Proof.
  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  inversion HE; subst.
  - (* b is true *)
    apply (HTrue st st').
      assumption.
      split. assumption.
      apply bexp_eval_true. assumption.
  - (* b is false *)
    apply (HFalse st st').
      assumption.
      split. assumption.
      apply bexp_eval_false. assumption. Qed.

Theorem hoare_while : forall P b c,
  {{fun st => P st /\ bassn b st}} c {{P}} ->
  {{P}} WHILE b DO c END {{fun st => P st /\ ~ (bassn b st)}}.
Proof.
  intros P b c Hhoare st st' He HP.
  (* Like we've seen before, we need to reason by induction
     on [He], because, in the "keep looping" case, its hypotheses
     talk about the whole loop instead of just [c]. *)
  remember (WHILE b DO c END)%imp as wcom eqn:Heqwcom.
  induction He;
    try (inversion Heqwcom); subst; clear Heqwcom.
  - (* E_WhileFalse *) 
    split. assumption. apply bexp_eval_false. assumption.
  - (* E_WhileTrue *)
    apply IHHe2. reflexivity.
    apply (Hhoare st st'). assumption.
      split. assumption. apply bexp_eval_true. assumption.
Qed.


Example while_example :
    {{fun st => st X <= 3}}
  WHILE X <= 2
  DO X ::= X + 1 END
    {{fun st => st X = 3}}.
Proof.
  eapply hoare_consequence_post.
  apply hoare_while.
  eapply hoare_consequence_pre.
  apply hoare_asgn.
  unfold bassn, assn_sub, assert_implies, t_update. simpl.
    intros st [H1 H2]. apply leb_complete in H2. omega.
  unfold bassn, assert_implies. intros st [Hle Hb].
    simpl in Hb. destruct ((st X) <=? 2) eqn : Heqle.
    exfalso. apply Hb; reflexivity.
    apply leb_iff_conv in Heqle. omega.
Qed.

Theorem always_loop_hoare : forall P Q,
  {{P}} WHILE true DO SKIP END {{Q}}.
Proof.
  (* WORKED IN CLASS *)
  intros P Q.
  apply hoare_consequence_pre with (P' := fun st : state => True).
  eapply hoare_consequence_post.
  apply hoare_while.
  - (* Loop body preserves invariant *)
    apply hoare_post_true. intros st. apply I.
  - (* Loop invariant and negated guard imply postcondition *)
    simpl. intros st [Hinv Hguard].
    exfalso. apply Hguard. reflexivity.
  - (* Precondition implies invariant *)
    intros st H. constructor.  Qed.