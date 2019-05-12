(*e01*)

Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

Definition weekday_to_nat d :=
  match d with
    | sunday => 1
    | monday => 2
    | tuesday => 3
    | wednesday => 4
    | thursday => 5
    | friday => 6
    | saturday => 7
  end.

Definition is_weekend d :=
  match d with
    | saturday | sunday => true
    | _ => false
  end.

Compute is_weekend tuesday.

(*e02*)

Definition negb b :=
  match b with
    | true => false
    | false => true
  end.

Definition andb b1 b2 :=
  match b1, b2 with
    | true, true => true
    | _, _ => false
  end.

Definition orb b1 b2 :=
  match b1, b2 with
    | false, false => false
    | _, _ => true
  end.

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb false true) = true.
Proof. simpl. reflexivity. Qed.

Notation "~ x" := (negb x).
Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Compute true && false.

Definition xor b1 b2 :=
  match b1, b2 with
    | true, false => true
    | false, true => true
    | _, _ => false
  end.

(*e03*)

Module NatPlayground.

Inductive natural : Type :=
  | O : natural
  | S : natural -> natural.

Definition pred (n : natural) : natural :=
  match n with
    | O => O
    | S n' => n'
  end.

Definition minustwo (n: natural) : natural :=
  (pred (pred n)).

End NatPlayground.

Fixpoint oddb (n: nat) :=
  match n with
    | O => false
    | S O => true
    | S (S n') => oddb n'
  end.

Definition evenb (n: nat) :=
  negb (oddb n).

Fixpoint plus a b :=
  match b with
    | 0 => a
    | S n' => S (plus a n')
  end.

Fixpoint mult a b :=
  match b with
    | 0 => 0
    | S n' => plus (mult a n') a
  end.

Fixpoint exp a b :=
  match b with
    | 0 => 1
    | S n' => mult (exp a n') a
  end.



Fixpoint minus a b :=
  if (Nat.leb a b) then 0 else
  match b with
    | 0 => a
    | S n' => pred (minus a n')
  end.

Fixpoint factorial n :=
  match n with
    | 0 => 1
    | S n' => n * (factorial n')
  end.




