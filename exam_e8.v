Require Import String.
Require Import List.
Require Import Arith.
Require Import Arith.Compare.
Import ListNotations.
Require Import TacticsL8.

Inductive RoboLang : Type :=
| Skip
| MoveRight (n: nat)
| MoveLeft (n: nat)
| Pick
| Drop
| Seq (e1 e2: RoboLang).

Fixpoint replace {X:Type} (n: nat) (l: list X) (x:X) : list X :=
match n, l with
| 0   , h :: t => x :: t
| _   , []     => []
| S n', h :: t => h :: (replace n' t x)
end.

Fixpoint eval (e: RoboLang) (st: ((nat*(option string))*(list (option string))))
                               : ((nat*(option string))*(list (option string))) :=
match st with
| ((pos, hold), env) => match e with
                        | Skip        => st
                        | MoveRight n => ((pos+n, hold), env)
                        | MoveLeft n  => if negb ((pos-1) <? 0) then
                                           ((pos-n, hold), env)
                                         else
                                           ((0, hold), env)
                        | Pick        => match hold with
                                         | None => ((pos, (nth pos env None)), (replace pos env None))
                                         | Some s => st
                                         end
                        | Drop        => match (nth pos env None) with
                                         | None => ((pos, None), (replace pos env hold))
                                         | Some s => st
                                         end
                        | Seq e1 e2   => eval e2 (eval e1 st)
                        end
end.

Theorem natPnMn : forall n, n - n = 0.
Proof.
  intros. induction n.
  - easy.
  - simpl. rewrite IHn. easy.
Qed.

Theorem natAPnMn : forall a n, a + n - n = a.
Proof.
  intros. cut ((n-n) = 0).
  - intros. induction a.
    + simpl. exact H.
    + rewrite <- IHa at 2. linear_arithmetic.
  - apply natPnMn.
Qed.

Theorem mvNRNL : forall n st, (eval (Seq (MoveRight n) (MoveLeft n)) st) = st.
Proof.
  intros. induction st. induction a. rename a into pos. rename b0 into hold. rename b into env.
  simpl. cut ((pos + n - n) = pos).
    + intros. rewrite H. easy.
    + apply natAPnMn.
Qed.

Fixpoint opt1 (e: RoboLang) : RoboLang :=
match e with
| Seq (MoveRight a) (MoveLeft b) => if beq_nat a b then Skip else Seq (MoveRight a) (MoveLeft b)
| Skip => Skip
| MoveRight n => MoveRight n
| MoveLeft n => MoveLeft n
| Pick => Pick
| Drop => Drop
| Seq a b => Seq (opt1 a) (opt1 b)
end.