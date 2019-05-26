(** * Stlc: The Simply Typed Lambda-Calculus *)
(** This was extracted from the Software Foundations book (vol 2). *)

Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
Require Import Maps.
Require Import Smallstep.


Module STLC.

(* ================================================================= *)
(** ** Types *)

(** Exercise: define a datatype for base types (ty). Our base types
are Booleans and the "Arrow" type (functions) *)

Inductive ty : Type :=
| Bool : ty
| Arrow : ty -> ty -> ty.

(* ================================================================= *)
(** ** Terms *)


(** Exercise: To define the terms of STLC, we need to 
encode variables, application, and (typed) abstraction. 
Moreover, for convenience we introduce boolean terms tru, 
fls, and test (as before) *)

Inductive tm : Type :=
| var  : string -> tm
| abs  : string -> ty -> tm -> tm
| app  : tm -> tm -> tm
(* boolean part of the language *)
| tru  : tm
| fls  : tm
| test : tm -> tm -> tm -> tm.

(** Some examples... *)

Open Scope string_scope.

Definition x := "x".
Definition y := "y".
Definition z := "z".

Hint Unfold x.
Hint Unfold y.
Hint Unfold z.


(** Exercise: Encode the following terms. *)

(** [idB = \x:Bool. x] *)

Notation idB :=
  (abs x Bool (var x)).

(** [idBB = \x:Bool->Bool. x] *)

Notation idBB :=
  (abs x (Arrow Bool Bool) (var x)).

(** [idBBBB = \x:(Bool->Bool) -> (Bool->Bool). x] *)

Notation idBBBB :=
    (abs x (Arrow (Arrow Bool Bool) (Arrow Bool Bool)) (var x)).

(** [k = \x:Bool. \y:Bool. x] *)

Notation k := (abs x Bool (abs y Bool (var x))).

(** [notB = \x:Bool. test x then fls else tru] *)

Notation notB := (abs x Bool (test (var x) fls tru)).

(* ################################################################# *)
(** * Operational Semantics *)

(** To define the small-step semantics of STLC terms, we begin,
    as always, by defining the set of values.  Next, we define the
    critical notions of _free variables_ and _substitution_, which are
    used in the reduction rule for application expressions.  And
    finally we give the small-step relation itself. *)

(* ================================================================= *)
(** ** Values *)

(** Exercise: What are the values of the STLC? Note that
to define the values of the STLC, we have a few cases to consider:

    1. The boolean part of the language
    2. Application
    3. Abstraction (there are two main options here, but let's consider
       abstractions as values)

*)

Inductive value : tm -> Prop :=
  | v_abs : forall x T t,
      value (abs x T t)
  | v_tru :
      value tru
  | v_fls :
      value fls.




Hint Constructors value.

(** Finally, we must consider what constitutes a _complete_ program.

    Intuitively, a "complete program" must not refer to any undefined
    variables. A complete program is _closed_ -- that is, it
    contains no free variables.

    (Conversely, a term with free variables is often called an _open
    term_.) *)

(** Having made the choice not to reduce under abstractions, we don't
    need to worry about whether variables are values, since we'll
    always be reducing programs "from the outside in," and that means
    the [step] relation will always be working with closed terms.  *)












(* ================================================================= *)
(** ** Substitution *)

(** Now we come to the heart of the STLC: the operation of
    substituting one term for a variable in another term.  This
    operation is used below to define the operational semantics of
    function application, where we will need to substitute the
    argument term for the function parameter in the function's body.
    For example, we reduce

       (\x:Bool. test x then tru else x) fls

    to

       test fls then tru else fls

    by substituting [fls] for the parameter [x] in the body of the
    function.

    In general, we need to be able to substitute some given term [s]
    for occurrences of some variable [x] in another term [t].  In
    informal discussions, this is usually written [ [x:=s]t ] and
    pronounced "substitute [s] for [x] in [t]." *)

(** Here are some examples:

      - [[x:=tru] (test x then x else fls)]
           yields [test tru then tru else fls]

      - [[x:=tru] x] yields [tru]

      - [[x:=tru] (test x then x else y)] yields [test tru then tru else y]

      - [[x:=tru] y] yields [y]

      - [[x:=tru] fls] yields [fls] (vacuous substitution)

      - [[x:=tru] (\y:Bool. test y then x else fls)]
           yields [\y:Bool. test y then tru else fls]

      - [[x:=tru] (\y:Bool. x)] yields [\y:Bool. tru]

      - [[x:=tru] (\y:Bool. y)] yields [\y:Bool. y]

      - [[x:=tru] (\x:Bool. x)] yields [\x:Bool. x]

    The last example is very important: substituting [x] with [tru] in
    [\x:Bool. x] does _not_ yield [\x:Bool. tru]!  The reason for
    this is that the [x] in the body of [\x:Bool. x] is _bound_ by the
    abstraction: it is a new, local name that just happens to be
    spelled the same as some global name [x]. *)

(** Here is the definition, informally...

       [x:=s]x               = s
       [x:=s]y               = y                     if x <> y
       [x:=s](\x:T11. t12)   = \x:T11. t12
       [x:=s](\y:T11. t12)   = \y:T11. [x:=s]t12     if x <> y
       [x:=s](t1 t2)         = ([x:=s]t1) ([x:=s]t2)
       [x:=s]tru             = tru
       [x:=s]fls             = fls
       [x:=s](test t1 then t2 else t3) =
              test [x:=s]t1 then [x:=s]t2 else [x:=s]t3
*)

(** ... and formally: *)

(** Exercise: complete the definition of substitution below. *)

Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | var x' =>
      if eqb_string x x' then s else t
  | abs x' T t1 =>
      abs x' T (if eqb_string x x' then t1 else (subst x s t1))
  | app t1 t2 =>
        app (subst x s t1) (subst x s t2)
  | tru =>
        tru
  | fls =>
        fls
  | test t1 t2 t3 =>
        test (subst x s t1) (subst x s t2) (subst x s t3)
  end

where "'[' x ':=' s ']' t" := (subst x s t).


(** Exercise: illustrate substitution with one or two examples. *)

Example ex1 := (abs "x" Bool (var "y")).
Compute subst "y" tru ex1.



(** _Technical note_: Substitution becomes trickier to define if we
    consider the case where [s], the term being substituted for a
    variable in some other term, may itself contain free variables.
    Since we are only interested here in defining the [step] relation
    on _closed_ terms (i.e., terms like [\x:Bool. x] that include
    binders for all of the variables they mention), we can sidestep this
    extra complexity, but it must be dealt with when formalizing
    richer languages. *)

(** For example, using the definition of substitution above to
    substitute the _open_ term [s = \x:Bool. r], where [r] is a _free_
    reference to some global resource, for the variable [z] in the
    term [t = \r:Bool. z], where [r] is a bound variable, we would get
    [\r:Bool. \x:Bool. r], where the free reference to [r] in [s] has
    been "captured" by the binder at the beginning of [t].

    Why would this be bad?  Because it violates the principle that the
    names of bound variables do not matter.  For example, if we rename
    the bound variable in [t], e.g., let [t' = \w:Bool. z], then
    [[x:=s]t'] is [\w:Bool. \x:Bool. r], which does not behave the
    same as [[x:=s]t = \r:Bool. \x:Bool. r].  That is, renaming a
    bound variable changes how [t] behaves under substitution. *)










(* ================================================================= *)
(** ** Reduction *)

(** The small-step reduction relation for STLC now follows the
    same pattern as the ones we have seen before.  Intuitively, to
    reduce a function application, we first reduce its left-hand
    side (the function) until it becomes an abstraction; then we
    reduce its right-hand side (the argument) until it is also a
    value; and finally we substitute the argument for the bound
    variable in the body of the abstraction.  This last rule, written
    informally as

      (\x:T.t12) v2 --> [x:=v2]t12

    is traditionally called _beta-reduction_. *)


(** Exercise: Write the inference rules that define the small-step reduction
relation for STLC. *)


(** Exercise: Encode the inference rules formally: *)

Reserved Notation "t1 '-->' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t12 v2,
         value v2 ->
         (app (abs x T t12) v2) --> (subst x v2 t12)
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         app t1 t2 --> app t1' t2
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         app v1 t2 --> app v1 t2'
  | ST_TestTru : forall t1 t2,
      (test tru t1 t2) --> t1
  | ST_TestFls : forall t1 t2,
      (test fls t1 t2) --> t2
  | ST_Test : forall t1 t1' t2 t3,
      t1 --> t1' ->
      (test t1 t2 t3) --> (test t1' t2 t3)

where "t1 '-->' t2" := (step t1 t2).

Hint Constructors step.

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

(* ================================================================= *)
(** ** Examples *)

(** Exercise: For each of the examples below, write on paper the
reduction steps taken. Then, go through the Coq proof and compare. *)

(** Example:

      (\x:Bool->Bool. x) (\x:Bool. x) -->* \x:Bool. x

    i.e.,

      idBB idB -->* idB
*)

Lemma step_example1 :
  (app idBB idB) -->* idB.
Proof.
  eapply multi_step.
    apply ST_AppAbs.
    apply v_abs.
  simpl.
  apply multi_refl.  Qed.

(** Example:

      (\x:Bool->Bool. x) ((\x:Bool->Bool. x) (\x:Bool. x))
            -->* \x:Bool. x

    i.e.,

      (idBB (idBB idB)) -->* idB.
*)

Lemma step_example2 :
  (app idBB (app idBB idB)) -->* idB.
Proof.
  eapply multi_step.
    apply ST_App2. auto.
    apply ST_AppAbs. auto.
  eapply multi_step.
    apply ST_AppAbs. simpl. auto.
  simpl. apply multi_refl.  Qed.

(** Example:

      (\x:Bool->Bool. x)
         (\x:Bool. test x then fls else tru)
         tru
            -->* fls

    i.e.,

       (idBB notB) tru -->* fls.
*)

Lemma step_example3 :
  app (app idBB notB) tru -->* fls.
Proof.
  eapply multi_step.
    apply ST_App1. apply ST_AppAbs. auto. simpl.
  eapply multi_step.
    apply ST_AppAbs. auto. simpl.
  eapply multi_step.
    apply ST_TestTru. apply multi_refl.  Qed.

(** Example:

      (\x:Bool -> Bool. x)
         ((\x:Bool. test x then fls else tru) tru)
            -->* fls

    i.e.,

      idBB (notB tru) -->* fls.

    (Note that this term doesn't actually typecheck; even so, we can
    ask how it reduces.)
*)

Lemma step_example4 :
  app idBB (app notB tru) -->* fls.
Proof.
  eapply multi_step.
    apply ST_App2. auto.
    apply ST_AppAbs. auto. simpl.
  eapply multi_step.
    apply ST_App2. auto.
    apply ST_TestTru.
  eapply multi_step.
    apply ST_AppAbs. auto. simpl.
  apply multi_refl.  Qed.

(** Just a side note: we can use the [normalize] tactic defined in the [Smallstep] chapter
    to simplify these proofs. *)

Lemma step_example1' :
  app idBB idB -->* idB.
Proof. normalize.  Qed.

Lemma step_example2' :
  app idBB (app idBB idB) -->* idB.
Proof. normalize. Qed.

Lemma step_example3' :
  app (app idBB notB) tru -->* fls.
Proof. normalize.  Qed.

Lemma step_example4' :
  app idBB (app notB tru) -->* fls.
Proof. normalize.  Qed.


(** **** Homework: Try to do this one both with and without [normalize]. *)

Lemma step_example5 :
       app (app idBBBB idBB) idB
  -->* idB.
Proof.
  eapply multi_step.
    apply ST_App1. auto.
    unfold subst. simpl.
  eapply multi_step.
    apply ST_AppAbs. auto.
    unfold subst. simpl.
  apply multi_refl.
Qed.

Lemma step_example5_with_normalize :
       app (app idBBBB idBB) idB
  -->* idB.
Proof.
  normalize.
Qed.





(* ################################################################# *)
(** * Typing *)

(** Next we consider the typing relation of the STLC. *)

(* ================================================================= *)
(** ** Contexts *)

(** _Question_: What is the type of the term "[x y]"?

    _Answer_: It depends on the types of [x] and [y]!

    I.e., in order to assign a type to a term, we need to know
    what assumptions we should make about the types of its free
    variables.

    This leads us to a three-place _typing judgment_, informally
    written [Gamma |- t \in T], where [Gamma] is a
    "typing context" -- a mapping from variables to their types. *)

(** Following the usual notation for partial maps, we write [(X |->
    T11, Gamma)] for "update the partial function [Gamma] so that it
    maps [x] to [T]." *)

Definition context := partial_map ty.

(* ================================================================= *)
(** ** Typing Relation *)


(** Exercise: Write the typing relation for the STLC. First, on paper
(as a set of inference rules); then, formally in Coq. *)

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      Gamma |- var x \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      (x |-> T11 ; Gamma) |- t12 \in T12 ->
      Gamma |- abs x T11 t12 \in Arrow T11 T12
  | T_App : forall T11 T12 Gamma t1 t2,
      Gamma |- t1 \in Arrow T11 T12 ->
      Gamma |- t2 \in T11 ->
      Gamma |- app t1 t2 \in T12
  | T_Tru : forall Gamma,
       Gamma |- tru \in Bool
  | T_Fls : forall Gamma,
       Gamma |- fls \in Bool
  | T_Test : forall t1 t2 t3 T Gamma,
       Gamma |- t1 \in Bool ->
       Gamma |- t2 \in T ->
       Gamma |- t3 \in T ->
       Gamma |- test t1 t2 t3 \in T

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type.

(* ================================================================= *)
(** ** Examples *)

(** Exercise: Use the typing rules above to prove that
the following terms are well typed. Write the proof trees on paper
and then go through the Coq proofs. *)

Example typing_example_1 :
  empty |- abs x Bool (var x) \in Arrow Bool Bool.
Proof.
  apply T_Abs. apply T_Var. reflexivity.  Qed.

(** Note that, since we added the [has_type] constructors to the hints
    database, [auto] can actually solve this one immediately. *)

Example typing_example_1' :
  empty |- abs x Bool (var x) \in Arrow Bool Bool.
Proof. auto.  Qed.

(** Example 2:

       empty |- \x:A. \y:A->A. y (y x)
             \in A -> (A->A) -> A.
*)

Example typing_example_2 :
  empty |-
    (abs x Bool
       (abs y (Arrow Bool Bool)
          (app (var y) (app (var y) (var x))))) \in
    (Arrow Bool (Arrow (Arrow Bool Bool) Bool)).
Proof with auto using update_eq.
  apply T_Abs.
  apply T_Abs.
  eapply T_App. apply T_Var...
  eapply T_App. apply T_Var...
  apply T_Var...
Qed.

End STLC.
