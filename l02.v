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

(* ex 02 *)

Require Import Coq.Arith.PeanoNat.

Definition partition {X: Type} (p: X -> bool) (l:list X) : (list X) * (list X) :=
  ((filter p l), (filter (fun x => negb (p x)) l)).

Definition list_prod {X Y : Type} (l1: list X) (l2: list Y) : list (X*Y) :=
  concat (map (fun x:X => map (fun y:Y => (x,y)) l2) l1).

Definition length {X:Type} (l:list X) : nat := 
  fold_right (fun (x:X) (acc:nat) => acc+1) 0 l.

Definition map {X Y : Type} (f : X -> Y) (l:list X) : list Y :=
  fold_right (fun (x:X) (l1:list Y) => (f x) :: l1) [] l.

Definition forallbc {X:Type} (f : X -> bool) (l:list X) : bool :=
  fold_right andb true (map f l).

(* ex 03 *)

Theorem thm_simpl1: forall a b c:nat,
    a = 0 -> b*(a+b) = b*b.
Proof.
  intros a b c.
  intros H.
  rewrite H.
  simpl.
  reflexivity.
Qed.

Theorem thm_simpl2: forall (a b c d:nat) (f: nat -> nat -> nat),
    a=b -> c=d -> (forall x y, f x y = f y x) -> f a c = f d b.
Proof.
  intros a b c d f.
  intros H1.
  intros H2.
  intros H3.
  rewrite -> H1.
  rewrite <- H2.
  rewrite H3.
  reflexivity.
Qed.

Theorem identity_fn_applied_twice : forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f.
  intros H.
  intros b.
  rewrite H. rewrite H.
  reflexivity.
Qed.

Theorem negation_fn_applied_twice : forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f.
  intros H.
  intros b.
  rewrite H. rewrite H.
  destruct b.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

