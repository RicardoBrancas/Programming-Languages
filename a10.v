Require Import String.
Require Import Maps.
Require Import TacticsL8.

Notation var := string.
Definition valuation := partial_map nat.

Inductive arith : Set :=
| Const (n : nat)
| Var (x : var)
| Plus (e1 e2 : arith)
| Minus (e1 e2 : arith)
| Times (e1 e2 : arith).

Definition ex1 := Const 42.
Definition ex2 := Plus (Var "y") (Times (Var "x") (Const 3)).

Fixpoint interp (e:arith) (v:valuation) : nat :=
  match e with
  | Const n => n
  | Var x =>
      match v x with
      | None => 0
      | Some n => n
      end
  | Plus e1 e2 => interp e1 v + interp e2 v
  | Minus e1 e2 => interp e1 v - interp e2 v
  | Times e1 e2 => interp e1 v * interp e2 v
  end.

Definition valuation0 : valuation :=
  empty & {{ "x" --> 17 ; "y" --> 3}}.

Compute interp ex1 valuation0.
Compute interp ex2 valuation0.

Fixpoint substitute (inThis : arith) (replaceThis : var) (withThis : arith) : arith :=
  match inThis with
  | Const _ => inThis
  | Var x => if x =? replaceThis then withThis else inThis
  | Plus e1 e2 => Plus (substitute e1 replaceThis withThis) (substitute e2 replaceThis withThis)
  | Minus e1 e2 => Minus (substitute e1 replaceThis withThis) (substitute e2 replaceThis withThis)
  | Times e1 e2 => Times (substitute e1 replaceThis withThis) (substitute e2 replaceThis withThis)
  end.

Fixpoint doSomeArithmetic (e : arith) : arith :=
  match e with
  | Const _ => e
  | Var _ => e
  | Plus (Const n1) (Const n2) => Const (n1 + n2)
  | Plus e1 e2 => Plus (doSomeArithmetic e1) (doSomeArithmetic e2)
  | Minus e1 e2 => Minus (doSomeArithmetic e1) (doSomeArithmetic e2)
  | Times (Const n1) (Const n2) => Const (n1 * n2)
  | Times e1 e2 => Times (doSomeArithmetic e1) (doSomeArithmetic e2)
  end.


