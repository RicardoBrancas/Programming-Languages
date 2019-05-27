Require Import Numbers.BinNums.
Require Import Coq.NArith.BinNat.
Require Import Coq.PArith.BinPosDef.
Require Import Omega.

Fixpoint n_ones (n: positive) : nat :=
match n with
| xI n' => 1 + (n_ones n')
| xO n' => (n_ones n')
| xH => 1
end.

Fixpoint diff (n1 n2: positive) : nat :=
match n1, n2 with
| xI n1', xI n2' => diff n1' n2'
| xO n1', xO n2' => diff n1' n2'
| xI n1', xO n2' => 1 + (diff n1' n2')
| xO n1', xI n2' => 1 + (diff n1' n2')
| xH, xH         => 0
| xI n1, xH         => Pos.size_nat n1
| xH, xI n2         => Pos.size_nat n2
| xO n1, xH         => Pos.size_nat n1 + 1
| xH, xO n2         => Pos.size_nat n2 + 1
end.

Compute diff 1~1~1~1 1~0.

Theorem diff_eq : forall n : positive,
  diff n n = 0.
Proof.
  induction n.
  - simpl. assumption.
  - simpl. assumption.
  - simpl. reflexivity.
Qed.

Theorem amortized_cost_2 : forall n : positive,
  (diff n (Pos.succ n)) + (n_ones (Pos.succ n)) - (n_ones n) = 2.
Proof.
  induction n.
  - simpl. assumption.
  - simpl. destruct n.
   + simpl. rewrite diff_eq. omega.
   + simpl. destruct (n_ones n).
    * rewrite diff_eq. reflexivity.
    * rewrite diff_eq. omega.
   + simpl. reflexivity.
  - simpl. reflexivity.
Qed.