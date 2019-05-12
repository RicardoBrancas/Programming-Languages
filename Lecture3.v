Fixpoint leb (n m : nat) : bool :=
  match n with
    | 0    => true
    | S n' => match m with
      | 0 => false
      | S m' => leb n' m'
      end
  end.

Compute leb 0 1.

Inductive natprod : Type :=
  | pair : nat -> nat -> natprod.

Definition first (p: natprod) : nat :=
  match p with
    | pair a b => a
  end.
  

(*e05*)
Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.
  
Check (cons 1(cons 2 nil)).