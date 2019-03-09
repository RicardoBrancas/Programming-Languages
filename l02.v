Require Import Coq.Lists.List.
Import ListNotations.

Fixpoint tl {X:Type} (l: list X) : (list X) :=
  match l with
  | [] => []
  | h :: t => t
  end.

Fixpoint removelast {X:Type} (l: list X) : (list X) :=
  match l with
  | [] => []
  | [x] => []
  | h :: t => h :: (removelast t)
  end.

Fixpoint firstn {X:Type} (n: nat) (l:list X) : (list X) :=
  match n, l with
  | _, [] => []
  | 0, _ => []
  | S n', h :: t => h :: (firstn n' t)
  end.

Fixpoint skipn {X:Type} (n: nat) (l:list X) : (list X) :=
  match n, l with
  | _, [] => []
  | 0, L => L
  | S n', h :: t => skipn n' t
  end.

Fixpoint last {X:Type} (l:list X) : (option X) :=
  match l with
  | [] => None
  | [x] => Some x
  | h :: t => last t
  end.

Fixpoint seq (start:nat) (len:nat) : (list nat) :=
  match len with
  | 0 => []
  | S n' => start :: (seq (S start) n')
  end.

Definition split {X Y:Type} (l:list (X*Y)) : ((list X)*(list Y)) :=
  match l with
  | [] => ([],[])
  | h :: t => ( (fst h) :: (fst (split t)) , (snd h) :: (snd (split t)) )
  end.

Fixpoint append {X:Type} (l1:list X) (l2:list X) : (list X) :=
  match l1 with
  | [] => l2
  | h :: t => h :: (append t l2)
  end.

Fixpoint rev {X:Type} (l:list X) : (list X) :=
  match l with
  | [] => []
  | h :: t => (append (rev t) [h])
  end.

Fixpoint existsb {X:Type} (f: X->bool) (l:list X) : bool :=
  match l with
  | [] => false
  | h :: t => orb (f h) (existsb f t)
  end.

Fixpoint forallb {X:Type} (f: X->bool) (l:list X) : bool :=
  match l with
  | [] => false
  | h :: t => andb (f h) (existsb f t)
  end.

Fixpoint find {X:Type} (f: X->bool) (l:list X) : option X :=
  match l with
  | [] => None
  | h :: t => if f h then Some h else find f t
  end.

