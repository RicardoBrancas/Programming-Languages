Theorem plus_0_n : forall n: nat, 0 + n = n.
Proof. intros n. simpl. reflexivity. Qed.

Theorem mult_0_plus: forall n m:nat, (0+n)*m = n * m.
Proof.
  intros.
  rewrite -> plus_0_n.
  reflexivity.
Qed.

Require Import Coq.Arith.EqNat.

Theorem plus_1_neq_0 : forall n : nat,
  beq_nat (n+1) 0 = false.
Proof.
  intros n.
  destruct n as [| n'].
  - reflexivity.
  - simpl. reflexivity.
Qed.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c.
  destruct c.
  - reflexivity.
  - destruct b.
    + simpl. intros H. assumption.
    + simpl. intros H. assumption.
Qed.
