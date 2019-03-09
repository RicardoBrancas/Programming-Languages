Definition two := 2.

Definition succ (n:nat) := n+1.

Check succ.

Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Definition day_wildcard (d:day) : nat :=
  match d with
  | saturday | sunday => 0
  | _ => 1
  end.

Example test_next_weekday: (next_weekday (next_weekday saturday)) = tuesday.
Proof. simpl. reflexivity. Qed.

Inductive bool : Type :=
| true
| false.

Definition andb (a b : bool) : bool :=
  match a, b with
  | true, true => true
  | _, _ => false
  end.
Notation "x && y" := (andb x y).

Definition orb (a b : bool) : bool :=
  match a, b with
  | false, false => false
  | _, _ => true
  end.
Notation "x || y" := (orb x y).

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

Check (S (S (S (S O)))).

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

