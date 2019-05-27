Require Import String.

Inductive ty : Type :=
| Bool
| Nat
| Arrow : ty -> ty -> ty.

Inductive tm : Type :=
  | tru : tm 
  | fls : tm
  | test : tm -> tm -> tm -> tm
  | zro : tm
  | scc : tm -> tm
  | prd : tm -> tm
  | iszro : tm -> tm
  | var : string -> tm
  | app : tm -> tm -> tm 
  | abs : string -> ty -> tm -> tm.

