Require Import Maps.
Require Import Coq.Lists.List.
Require Import String.
Import ListNotations.

Definition fake_map (X:Type) := list (string * X).

Fixpoint fake_to_partial {X:Type} (fake: fake_map X) : partial_map X :=
  match fake with
  | [] => empty
  | (s, x) :: t => (fake_to_partial t) & {{s --> x}}
  end.

