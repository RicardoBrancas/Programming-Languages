(** * Hoare: Hoare Logic, Part I *)

Set Warnings "-notation-overridden,-parsing".
Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import omega.Omega.
Require Import Imp.

(* ################################################################# *)
(** * Assertions *)

(** To talk about specifications of programs, the first thing we
    need is a way of making _assertions_ about properties that hold at
    particular points during a program's execution -- i.e., claims
    about the current state of the memory when execution reaches that
    point.  Formally, an assertion is just a family of propositions
    indexed by a [state]. *)

Definition Assertion := state -> Prop.

(** **** Exercise 1: 1 star, standard, optional (assertions)  

    Paraphrase the following assertions in English (or your favorite
    natural language). *)

Module ExAssertions.
Definition as1 : Assertion := fun st => st X = 3.
(* In this state the value of X is 3. *)
Definition as2 : Assertion := fun st => st X <= st Y.
(* In this state the value of X is at most the value of Y. *)
Definition as3 : Assertion :=
  fun st => st X = 3 \/ st X <= st Y.
(* In this state, either the value of X is 3, or the value of X is at most the value of Y. *)
Definition as4 : Assertion :=
  fun st => st Z * st Z <= st X /\
            ~ (((S (st Z)) * (S (st Z))) <= st X).
(* In this state, the value of Z squared is at most the value of X AND
   the value of Z, plus 1, squared is less greater than the value of X. *)
Definition as5 : Assertion := fun st => True.
(* All states satisfy this assertion. *)
Definition as6 : Assertion := fun st => False.
(* No states satisfy this assertion. *)

End ExAssertions.

(** Given two assertions [P] and [Q], we say that [P] _implies_ [Q],
    written [P ->> Q], if, whenever [P] holds in some state [st], [Q]
    also holds. *)

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Notation "P ->> Q" := (assert_implies P Q)
                      (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.

(** (The [hoare_spec_scope] annotation here tells Coq that this
    notation is not global but is intended to be used in particular
    contexts.  The [Open Scope] tells Coq that this file is one such
    context.) *)

(** We'll also want the "iff" variant of implication between
    assertions: *)

Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.

(* ################################################################# *)
(** * Hoare Triples *)

(** Next, we need a way of making formal claims about the
    behavior of commands. *)

(** In general, the behavior of a command is to transform one state to
    another, so it is natural to express claims about commands in
    terms of assertions that are true before and after the command
    executes:

      - "If command [c] is started in a state satisfying assertion
        [P], and if [c] eventually terminates in some final state,
        then this final state will satisfy the assertion [Q]."

    Such a claim is called a _Hoare Triple_.  The assertion [P] is
    called the _precondition_ of [c], while [Q] is the
    _postcondition_.  *)

(** Formally: *)

Definition hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
     st =[ c ]=> st'  ->
     P st  ->
     Q st'.

(** Since we'll be working a lot with Hoare triples, it's useful to
    have a compact notation:

       {{P}} c {{Q}}.

    (The traditional notation is [{P} c {Q}], but single braces
    are already used for other things in Coq.)  *)

Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.

(** **** Exercise 2: 1 star, standard, optional (triples)  

    Paraphrase the following Hoare triples in English.

   1) {{True}} c {{X = 5}}
      
      Starting from any state, after executing c, the value of X should be 5.

   2) {{X = m}} c {{X = m + 5)}}
   
      Given that the value of X is m, after executing c, the value of X should be m+5.

   3) {{X <= Y}} c {{Y <= X}}
   
      Given that the value of X is at most the value of Y, after executing c,
      the value of Y should be at most the value of X.

   4) {{True}} c {{False}}
   
      Starting from any state, executing c, there should be no state we can end up in.

   5) {{X = m}}
      c
      {{Y = real_fact m}}
      
      Given that the value of X is m, after executing c, the value of Y
      should be (real_fact m).

   6) {{X = m}}
      c
      {{(Z * Z) <= m /\ ~ (((S Z) * (S Z)) <= m)}}
      
      Given that the value of X is m, after executing C, the value of Z squared
      should be at most m AND the value of Z, plus 1, squared should be greater than m.
*)

(** **** Exercise 3: 1 star, standard, optional (valid_triples)  

    Which of the following Hoare triples are _valid_ -- i.e., the
    claimed relation between [P], [c], and [Q] is true?

   1) {{True}} X ::= 5 {{X = 5}}
      true

   2) {{X = 2}} X ::= X + 1 {{X = 3}}
      true

   3) {{True}} X ::= 5;; Y ::= 0 {{X = 5}}
      true

   4) {{X = 2 /\ X = 3}} X ::= 5 {{X = 0}}
      false

   5) {{True}} SKIP {{False}}
      false

   6) {{False}} SKIP {{True}}
      true

   7) {{True}} WHILE true DO SKIP END {{False}}
      true

   8) {{X = 0}}
        WHILE X = 0 DO X ::= X + 1 END
      {{X = 1}}
      true

   9) {{X = 1}}
        WHILE ~(X = 0) DO X ::= X + 1 END
      {{X = 100}}
      true
*)

(** To get us warmed up for what's coming, here are two simple facts
    about Hoare triples.  (Make sure you understand what they mean.) *)

Theorem hoare_post_true : forall (P Q : Assertion) c,
  (forall st, Q st) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros st st' Heval HP.
  apply H.  Qed.

Theorem hoare_pre_false : forall (P Q : Assertion) c,
  (forall st, ~ (P st)) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros st st' Heval HP.
  unfold not in H. apply H in HP.
  inversion HP.  Qed.

(* ################################################################# *)
(** * Proof Rules *)

(** The goal of Hoare logic is to provide a _compositional_
    method for proving the validity of specific Hoare triples.  That
    is, we want the structure of a program's correctness proof to
    mirror the structure of the program itself.  To this end, in the
    sections below, we'll introduce a rule for reasoning about each of
    the different syntactic forms of commands in Imp -- one for
    assignment, one for sequencing, one for conditionals, etc. -- plus
    a couple of "structural" rules for gluing things together.  We
    will then be able to prove programs correct using these proof
    rules, without ever unfolding the definition of [hoare_triple]. *)

(* ================================================================= *)
(** ** Assignment *)

(** The rule for assignment is the most fundamental of the Hoare logic
    proof rules.  Here's how it works.

    Consider this valid Hoare triple:

       {{ Y = 1 }}  X ::= Y  {{ X = 1 }}

    In English: if we start out in a state where the value of [Y]
    is [1] and we assign [Y] to [X], then we'll finish in a
    state where [X] is [1]. 
    That is, the property of being equal to [1] gets transferred
    from [Y] to [X]. *)

(** Similarly, in

       {{ Y + Z = 1 }}  X ::= Y + Z  {{ X = 1 }}

    the same property (being equal to one) gets transferred to
    [X] from the expression [Y + Z] on the right-hand side of
    the assignment. *)

(** More generally, if [a] is _any_ arithmetic expression, then

       {{ a = 1 }}  X ::= a  {{ X = 1 }}

    is a valid Hoare triple. *)

(** Even more generally, to conclude that an arbitrary assertion [Q]
    holds after [X ::= a], we need to assume that [Q] holds before [X
    ::= a], but _with all occurrences of_ [X] replaced by [a] in
    [Q]. This leads to the Hoare rule for assignment

      {{ Q [X |-> a] }} X ::= a {{ Q }}

    where "[Q [X |-> a]]" is pronounced "[Q] where [a] is substituted
    for [X]". *)

(** For example, these are valid applications of the assignment
    rule:

      {{ (X <= 5) [X |-> X + 1]
         i.e., X + 1 <= 5 }}
      X ::= X + 1
      {{ X <= 5 }}

      {{ (X = 3) [X |-> 3]
         i.e., 3 = 3 }}
      X ::= 3
      {{ X = 3 }}

      {{ (0 <= X /\ X <= 5) [X |-> 3]
         i.e., (0 <= 3 /\ 3 <= 5) }}
      X ::= 3
      {{ 0 <= X /\ X <= 5 }}
*)

(** To formalize the rule, we must first formalize the idea of
    "substituting an expression for an Imp variable in an assertion",
    which we refer to as assertion substitution, or [assn_sub].  That
    is, given a proposition [P], a variable [X], and an arithmetic
    expression [a], we want to derive another proposition [P'] that is
    just the same as [P] except that [P'] should mention [a] wherever
    [P] mentions [X]. *)

(** Since [P] is an arbitrary Coq assertion, we can't directly "edit"
    its text.  However, we can achieve the same effect by evaluating
    [P] in an updated state: *)

Definition assn_sub X a P : Assertion :=
  fun (st : state) =>
    P (X !-> aeval st a ; st).

Notation "P [ X |-> a ]" := (assn_sub X a P)
  (at level 10, X at next level).

(** That is, [P [X |-> a]] stands for an assertion -- let's call it [P'] --
    that is just like [P] except that, wherever [P] looks up the
    variable [X] in the current state, [P'] instead uses the value
    of the expression [a]. *)


(** Now, using the concept of substitution, we can give the precise
    proof rule for assignment:

      ------------------------------ (hoare_asgn)
      {{Q [X |-> a]}} X ::= a {{Q}}
*)

(** We can prove formally that this rule is indeed valid. *)

Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} X ::= a {{Q}}.
Proof.
  unfold hoare_triple.
  intros Q X a st st' HE HQ.
  inversion HE. subst.
  unfold assn_sub in HQ. assumption.  Qed.

(** Here's a first formal proof using this rule. *)

Example assn_sub_example :
  {{(fun st => st X < 5) [X |-> X + 1]}}
  X ::= X + 1
  {{fun st => st X < 5}}.
Proof.
  apply hoare_asgn.
Qed.

(** **** Exercise 5: 2 stars, standard (hoare_asgn_examples)  

    Translate these informal Hoare triples...

    1) {{ (X <= 10) [X |-> 2 * X] }}
       X ::= 2 * X
       {{ X <= 10 }}

    2) {{ (0 <= X /\ X <= 5) [X |-> 3] }}
       X ::= 3
       {{ 0 <= X /\ X <= 5 }}

   ...into formal statements (use the names [assn_sub_ex1]
   and [assn_sub_ex2]) and use [hoare_asgn] to prove them. *)

Example assn_sub_ex1 :
  {{(fun st => st X <= 10) [X |-> 2* X]}}
  X ::= 2 * X
  {{fun st => st X <= 10}}.
Proof. apply hoare_asgn. Qed.

Example assn_sub_ex2 :
  {{(fun st => 0 < st X /\ st X < 5) [X |-> 3]}}
  X ::= 3
  {{(fun st => 0 < st X /\ st X < 5)}}.
Proof. apply hoare_asgn. Qed.


(** **** Exercise 6: 2 stars, standard, recommended (hoare_asgn_wrong)  

    The assignment rule looks backward to almost everyone the first
    time they see it.  If it still seems puzzling, it may help
    to think a little about alternative "forward" rules.  Here is a
    seemingly natural one:

      ------------------------------ (hoare_asgn_wrong)
      {{ True }} X ::= a {{ X = a }}

    Give a counterexample showing that this rule is incorrect and
    argue informally that it is really a counterexample.  (Hint:
    The rule universally quantifies over the arithmetic expression
    [a], and your counterexample needs to exhibit an [a] for which
    the rule doesn't work.)
    
    a = X - 1
    *)


(* ================================================================= *)
(** ** Consequence *)

(** Sometimes the preconditions and postconditions we get from the
    Hoare rules won't quite be the ones we want in the particular
    situation at hand -- they may be logically equivalent but have a
    different syntactic form that fails to unify with the goal we are
    trying to prove, or they actually may be logically weaker (for
    preconditions) or stronger (for postconditions) than what we need.

    For instance, while

      {{(X = 3) [X |-> 3]}} X ::= 3 {{X = 3}},

    follows directly from the assignment rule,

      {{True}} X ::= 3 {{X = 3}}

    does not.  This triple is valid, but it is not an instance of
    [hoare_asgn] because [True] and [(X = 3) [X |-> 3]] are not
    syntactically equal assertions.  However, they are logically
    _equivalent_, so if one triple is valid, then the other must
    certainly be as well.  We can capture this observation with the
    following rule:

                {{P'}} c {{Q}}
                  P <<->> P'
         -----------------------------   (hoare_consequence_pre_equiv)
                {{P}} c {{Q}}
*)

(** Taking this line of thought a bit further, we can see that
    strengthening the precondition or weakening the postcondition of a
    valid triple always produces another valid triple. This
    observation is captured by two _Rules of Consequence_.

                {{P'}} c {{Q}}
                   P ->> P'
         -----------------------------   (hoare_consequence_pre)
                {{P}} c {{Q}}

                {{P}} c {{Q'}}
                  Q' ->> Q
         -----------------------------    (hoare_consequence_post)
                {{P}} c {{Q}}
*)

(** Exercise 7: compare ht1 with ht2 *)

Example ht1:
  {{ (fun st => st X = 3) [X |-> 3] }} 
    X ::= 3 
  {{ (fun st => st X = 3) }}.
Proof. apply hoare_asgn. Qed.

Example ht2: 
  {{ (fun st => True) }} 
    X ::= 3 
  {{ (fun st => st X = 3) }}.
Proof. try apply hoare_asgn. Abort.

(** Here are the formal versions: *)

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q c Hhoare Himp.
  intros st st' Hc HP. apply (Hhoare st st').
  assumption. apply Himp. assumption. Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P Q Q' c Hhoare Himp.
  intros st st' Hc HP.
  apply Himp.
  apply (Hhoare st st').
  assumption. assumption. Qed.

(** For example, we can use the first consequence rule like this:

      {{ True }} ->>
      {{ 1 = 1 }}
    X ::= 1
      {{ X = 1 }}

    Or, formally... *)

Example hoare_asgn_example1 :
  {{fun st => True}} X ::= 1 {{fun st => st X = 1}}.
Proof.
  (* WORKED IN CLASS *)
  apply hoare_consequence_pre
    with (P' := (fun st => st X = 1) [X |-> 1]).
  apply hoare_asgn.
  intros st H. unfold assn_sub, t_update. simpl. reflexivity.
Qed.

(** We can also use it to prove the example mentioned earlier.

      {{ X < 4 }} ->>
      {{ (X < 5)[X |-> X + 1] }}
    X ::= X + 1
      {{ X < 5 }}

   Or, formally ... *)

Example assn_sub_example2 :
  {{(fun st => st X < 4)}}
  X ::= X + 1
  {{fun st => st X < 5}}.
Proof.
  (* WORKED IN CLASS *)
  apply hoare_consequence_pre
    with (P' := (fun st => st X < 5) [X |-> X + 1]).
  apply hoare_asgn.
  intros st H. unfold assn_sub, t_update. simpl. omega.
Qed.

(** Exercise 8: we can also prove the example we saw above. *)

Ltac hsimpl :=
  intros st P; unfold assn_sub; simpl; unfold t_update; simpl;
  try omega; try reflexivity; try assumption.

Example ht2: 
  {{ (fun st => True) }} 
    X ::= 3 
  {{ (fun st => st X = 3) }}.
Proof.
  eapply hoare_consequence_pre.
  apply hoare_asgn.
  hsimpl.
Qed.

(** Finally, for convenience in proofs, here is a combined rule of
    consequence that allows us to vary both the precondition and the
    postcondition in one go.

                {{P'}} c {{Q'}}
                   P ->> P'
                   Q' ->> Q
         -----------------------------   (hoare_consequence)
                {{P}} c {{Q}}
*)

Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} ->
  P ->> P' ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q Q' c Hht HPP' HQ'Q.
  apply hoare_consequence_pre with (P' := P').
  apply hoare_consequence_post with (Q' := Q').
  assumption. assumption. assumption.  Qed.


(* ================================================================= *)
(** ** Digression: The [eapply] Tactic *)

(** This is a good moment to take another look at the [eapply] tactic,
    which we introduced briefly in the [Auto] chapter of
    _Logical Foundations_.

    We had to write "[with (P' := ...)]" explicitly in the proof of
    [hoare_asgn_example1] and [hoare_consequence] above, to make sure
    that all of the metavariables in the premises to the
    [hoare_consequence_pre] rule would be set to specific
    values.  (Since [P'] doesn't appear in the conclusion of
    [hoare_consequence_pre], the process of unifying the conclusion
    with the current goal doesn't constrain [P'] to a specific
    assertion.)

    This is annoying, both because the assertion is a bit long and
    also because, in [hoare_asgn_example1], the very next thing we are
    going to do -- applying the [hoare_asgn] rule -- will tell us
    exactly what it should be!  We can use [eapply] instead of [apply]
    to tell Coq, essentially, "Be patient: The missing part is going
    to be filled in later in the proof." *)

Example hoare_asgn_example1' :
  {{fun st => True}}
  X ::= 1
  {{fun st => st X = 1}}.
Proof.
  eapply hoare_consequence_pre.
  apply hoare_asgn.
  intros st H.  reflexivity.  Qed.

(** In general, the [eapply H] tactic works just like [apply H] except
    that, instead of failing if unifying the goal with the conclusion
    of [H] does not determine how to instantiate all of the variables
    appearing in the premises of [H], [eapply H] will replace these
    variables with _existential variables_ (written [?nnn]), which
    function as placeholders for expressions that will be
    determined (by further unification) later in the proof. *)



(** **** Exercise 9: 2 stars, standard (hoare_asgn_examples_2)  

    Translate these informal Hoare triples...

       {{ X + 1 <= 5 }}  X ::= X + 1  {{ X <= 5 }}
       {{ 0 <= 3 /\ 3 <= 5 }}  X ::= 3  {{ 0 <= X /\ X <= 5 }}

   ...into formal statements (name them [assn_sub_ex1'] and
   [assn_sub_ex2']) and use [hoare_asgn] and [hoare_consequence_pre]
   to prove them. *)

Example assn_sub_ex1' :
  {{fun st => st X + 1 <= 5}}
  X ::= X +1
  {{fun st => st X <= 5}}.
Proof.
  eapply hoare_consequence_pre.
  apply hoare_asgn. hsimpl.
Qed.

Example assn_sub_ex2' :
  {{fun st => 0 <= 3 /\ 3 <= 5}}
  X ::= 3
  {{fun st => 0 <= st X /\ st X <= 5}}.
Proof.
  eapply hoare_consequence_pre.
  apply hoare_asgn. hsimpl.
Qed.


(* ================================================================= *)
(** ** Skip *)

(** Since [SKIP] doesn't change the state, it preserves any
    assertion [P]:

      --------------------  (hoare_skip)
      {{ P }} SKIP {{ P }}
*)

Theorem hoare_skip : forall P,
     {{P}} SKIP {{P}}.
Proof.
  intros P st st' H HP. inversion H. subst.
  assumption.  Qed.


(* ================================================================= *)
(** ** Sequencing *)

(** More interestingly, if the command [c1] takes any state where
    [P] holds to a state where [Q] holds, and if [c2] takes any
    state where [Q] holds to one where [R] holds, then doing [c1]
    followed by [c2] will take any state where [P] holds to one
    where [R] holds:

        {{ P }} c1 {{ Q }}
        {{ Q }} c2 {{ R }}
       ----------------------  (hoare_seq)
       {{ P }} c1;;c2 {{ R }}
*)

Theorem hoare_seq : forall P Q R c1 c2,
     {{Q}} c2 {{R}} ->
     {{P}} c1 {{Q}} ->
     {{P}} c1;;c2 {{R}}.
Proof.
  intros P Q R c1 c2 H1 H2 st st' H12 Pre.
  inversion H12; subst.
  apply (H1 st'0 st'); try assumption.
  apply (H2 st st'0); assumption. Qed.

(** Note that, in the formal rule [hoare_seq], the premises are
    given in backwards order ([c2] before [c1]).  This matches the
    natural flow of information in many of the situations where we'll
    use the rule, since the natural way to construct a Hoare-logic
    proof is to begin at the end of the program (with the final
    postcondition) and push postconditions backwards through commands
    until we reach the beginning. *)

(** Informally, a nice way of displaying a proof using the sequencing
    rule is as a "decorated program" where the intermediate assertion
    [Q] is written between [c1] and [c2]:

      {{ a = n }}
    X ::= a;;
      {{ X = n }}    <--- decoration for Q
    SKIP
      {{ X = n }}
*)

(** Here's an example of a program involving both assignment and
    sequencing. *)

Example hoare_asgn_example3 : forall a n,
  {{fun st => aeval st a = n}}
  X ::= a;; SKIP
  {{fun st => st X = n}}.
Proof.
  intros a n. eapply hoare_seq.
  - (* right part of seq *)
    apply hoare_skip.
  - (* left part of seq *)
    eapply hoare_consequence_pre. apply hoare_asgn.
    intros st H. subst. reflexivity.
Qed.

(** We typically use [hoare_seq] in conjunction with
    [hoare_consequence_pre] and the [eapply] tactic, as in this
    example. *)

(** **** Exercise 10: 2 stars, standard, recommended (hoare_asgn_example4)  

    Translate this "decorated program" into a formal proof:

                   {{ True }} ->>
                   {{ 1 = 1 }}
    X ::= 1;;
                   {{ X = 1 }} ->>
                   {{ X = 1 /\ 2 = 2 }}
    Y ::= 2
                   {{ X = 1 /\ Y = 2 }}

   (Note the use of "[->>]" decorations, each marking a use of
   [hoare_consequence_pre].) *)

Example hoare_asgn_example4 :
  {{fun st => True}}
  X ::= 1;; Y ::= 2
  {{fun st => st X = 1 /\ st Y = 2}}.
Proof.
  apply hoare_seq with (Q := (fun st => st X = 1)).
  eapply hoare_consequence_pre. apply hoare_asgn. hsimpl.
  eapply hoare_consequence_pre. apply hoare_asgn. hsimpl.
Qed.


(** **** Exercise 11: 3 stars, standard (swap_exercise)  

    Write an Imp program [c] that swaps the values of [X] and [Y] and
    show that it satisfies the following specification:

      {{X <= Y}} c {{Y <= X}}

    Your proof should not need to use [unfold hoare_triple].  (Hint:
    Remember that the assignment rule works best when it's applied
    "back to front," from the postcondition to the precondition.  So
    your proof will want to start at the end and work back to the
    beginning of your program.)  *)


Example swap_exercise :
  {{fun st => st X <= st Y}}
  Z ::= X;;
  X ::= Y;;
  Y ::= Z
  {{fun st => st Y <= st X}}.
Proof.
  eapply hoare_seq with (Q := fun st => st Z <= st Y).
  eapply hoare_seq with (Q := fun st => st Z <= st X).
  - eapply hoare_consequence_pre. apply hoare_asgn. hsimpl.
  - eapply hoare_consequence_pre. apply hoare_asgn. hsimpl.
  - eapply hoare_consequence_pre. apply hoare_asgn. hsimpl.
Qed.




(** The following tactic can make proofs shorter *)
Ltac hoare_simp := 
  intros st H; 
  unfold assn_sub, t_update; 
  simpl; try omega; try assumption; try reflexivity.
  

(** **** Exercise 12: 3 stars, standard (hoarestate1)  

    Explain why the following proposition can't be proven:

      forall (a : aexp) (n : nat),
         {{fun st => aeval st a = n}}
           X ::= 3;; Y ::= a
         {{fun st => st Y = n}}.
         
    It can't be proven because expression a can depend on the value of X
    which is changes in the program.
*)



(* ================================================================= *)
(** ** Conditionals *)

(** What sort of rule do we want for reasoning about conditional
    commands? 

    Certainly, if the same assertion [Q] holds after executing
    either of the branches, then it holds after the whole conditional. 
    So we might be tempted to write:

              {{P}} c1 {{Q}}
              {{P}} c2 {{Q}}
      ---------------------------------
      {{P}} TEST b THEN c1 ELSE c2 {{Q}}
*)

(** However, this is rather weak. For example, using this rule,
   we cannot show

     {{ True }}
     TEST X = 0
       THEN Y ::= 2
       ELSE Y ::= X + 1
     FI
     {{ X <= Y }}

   since the rule tells us nothing about the state in which the
   assignments take place in the "then" and "else" branches. *)

(** Fortunately, we can say something more precise.  In the
    "then" branch, we know that the boolean expression [b] evaluates to
    [true], and in the "else" branch, we know it evaluates to [false].
    Making this information available in the premises of the rule gives
    us more information to work with when reasoning about the behavior
    of [c1] and [c2] (i.e., the reasons why they establish the
    postcondition [Q]). 

              {{P /\   b}} c1 {{Q}}
              {{P /\ ~ b}} c2 {{Q}}
      ------------------------------------  (hoare_if)
      {{P}} TEST b THEN c1 ELSE c2 FI {{Q}}
*)

(** To interpret this rule formally, we need to do a little work.
    Strictly speaking, the assertion we've written, [P /\ b], is the
    conjunction of an assertion and a boolean expression -- i.e., it
    doesn't typecheck.  To fix this, we need a way of formally
    "lifting" any bexp [b] to an assertion.  We'll write [bassn b] for
    the assertion "the boolean expression [b] evaluates to [true] (in
    the given state)." *)

Definition bassn b : Assertion :=
  fun st => (beval st b = true).

(** A couple of useful facts about [bassn]: *)

Lemma bexp_eval_true : forall b st,
  beval st b = true -> (bassn b) st.
Proof.
  intros b st Hbe.
  unfold bassn. assumption.  Qed.

Lemma bexp_eval_false : forall b st,
  beval st b = false -> ~ ((bassn b) st).
Proof.
  intros b st Hbe contra.
  unfold bassn in contra.
  rewrite -> contra in Hbe. inversion Hbe.  Qed.

(** Now we can formalize the Hoare proof rule for conditionals
    and prove it correct. *)

Theorem hoare_if : forall P Q b c1 c2,
  {{fun st => P st /\ bassn b st}} c1 {{Q}} ->
  {{fun st => P st /\ ~ (bassn b st)}} c2 {{Q}} ->
  {{P}} TEST b THEN c1 ELSE c2 FI {{Q}}.
Proof.
  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  inversion HE; subst.
  - (* b is true *)
    apply (HTrue st st').
      assumption.
      split. assumption.
      apply bexp_eval_true. assumption.
  - (* b is false *)
    apply (HFalse st st').
      assumption.
      split. assumption.
      apply bexp_eval_false. assumption. Qed.

(* ----------------------------------------------------------------- *)
(** *** Example *)

(** Here is a formal proof that the program we used to motivate the
    rule satisfies the specification we gave. *)

Example if_example :
    {{fun st => True}}
  TEST X = 0
    THEN Y ::= 2
    ELSE Y ::= X + 1
  FI
    {{fun st => st X <= st Y}}.
Proof.
  (* WORKED IN CLASS *)
  apply hoare_if.
  - (* Then *)
    eapply hoare_consequence_pre. apply hoare_asgn.
    unfold bassn, assn_sub, t_update, assert_implies.
    simpl. intros st [_ H].
    apply eqb_eq in H.
    rewrite H. omega.
  - (* Else *)
    eapply hoare_consequence_pre. apply hoare_asgn.
    unfold assn_sub, t_update, assert_implies.
    simpl; intros st _. omega.
Qed.

(** JFF: As before, we can automate simplifications for the
examples shown here *)
Ltac hoare_simp2 :=
  unfold bassn, assn_sub, t_update, assert_implies;
    simpl; intros st [_ H];
    try apply eqb_eq in H; try apply leb_le in H;
    try rewrite H; try omega; try assumption; try reflexivity.

(** **** Exercise 13: 2 stars, standard (if_minus_plus)  

    Prove the following hoare triple using [hoare_if].  Do not
    use [unfold hoare_triple].  *)

Theorem if_minus_plus :
  {{fun st => True}}
  TEST X <= Y
    THEN Z ::= Y - X
    ELSE Y ::= X + Z
  FI
  {{fun st => st Y = st X + st Z}}.
Proof.
  apply hoare_if.
  - eapply hoare_consequence_pre.
    apply hoare_asgn. hoare_simp2.
  - eapply hoare_consequence_pre.
    apply hoare_asgn. hoare_simp2.
Qed.


(* ================================================================= *)
(** ** Loops *)

(** Finally, we need a rule for reasoning about while loops. *)

(** Suppose we have a loop

      WHILE b DO c END

    and we want to find a precondition [P] and a postcondition
    [Q] such that

      {{P}} WHILE b DO c END {{Q}}

    is a valid triple. *)

(** First of all, let's think about the case where [b] is false at the
    beginning -- i.e., let's assume that the loop body never executes
    at all.  In this case, the loop behaves like [SKIP], so we might
    be tempted to write: *)

(**

      {{P}} WHILE b DO c END {{P}}.
*)

(** But, as we remarked above for the conditional, we know a
    little more at the end -- not just [P], but also the fact
    that [b] is false in the current state.  So we can enrich the
    postcondition a little: 

      {{P}} WHILE b DO c END {{P /\ ~ b}}
*)

(** What about the case where the loop body _does_ get executed?
    In order to ensure that [P] holds when the loop finally
    exits, we certainly need to make sure that the command [c]
    guarantees that [P] holds whenever [c] is finished.
    Moreover, since [P] holds at the beginning of the first
    execution of [c], and since each execution of [c]
    re-establishes [P] when it finishes, we can always assume
    that [P] holds at the beginning of [c].  This leads us to the
    following rule: 

                   {{P}} c {{P}}
        -----------------------------------
        {{P}} WHILE b DO c END {{P /\ ~ b}}

    This is almost the rule we want, but again it can be improved a
    little: at the beginning of the loop body, we know not only that
    [P] holds, but also that the guard [b] is true in the current
    state. *)

(** This gives us a little more information to use in reasoning
    about [c] (showing that it establishes the invariant by the time
    it finishes).  

    And this leads us to the final version of the rule: 

               {{P /\ b}} c {{P}}
        ----------------------------------  (hoare_while)
        {{P}} WHILE b DO c END {{P /\ ~ b}}

    The proposition [P] is called an _invariant_ of the loop.
*)

Theorem hoare_while : forall P b c,
  {{fun st => P st /\ bassn b st}} c {{P}} ->
  {{P}} WHILE b DO c END {{fun st => P st /\ ~ (bassn b st)}}.
Proof.
  intros P b c Hhoare st st' He HP.
  (* Like we've seen before, we need to reason by induction
     on [He], because, in the "keep looping" case, its hypotheses
     talk about the whole loop instead of just [c]. *)
  remember (WHILE b DO c END)%imp as wcom eqn:Heqwcom.
  induction He;
    try (inversion Heqwcom); subst; clear Heqwcom.
  - (* E_WhileFalse *) 
    split. assumption. apply bexp_eval_false. assumption.
  - (* E_WhileTrue *)
    apply IHHe2. reflexivity.
    apply (Hhoare st st'). assumption.
      split. assumption. apply bexp_eval_true. assumption.
Qed.

(** One subtlety in the terminology is that calling some assertion [P]
    a "loop invariant" doesn't just mean that it is preserved by the
    body of the loop in question (i.e., [{{P}} c {{P}}], where [c] is
    the loop body), but rather that [P] _together with the fact that
    the loop's guard is true_ is a sufficient precondition for [c] to
    ensure [P] as a postcondition.

    This is a slightly (but importantly) weaker requirement.  For
    example, if [P] is the assertion [X = 0], then [P] _is_ an
    invariant of the loop

      WHILE X = 2 DO X := 1 END

    although it is clearly _not_ preserved by the body of the
    loop. *)

Example while_example :
    {{fun st => st X <= 3}}
  WHILE X <= 2
  DO X ::= X + 1 END
    {{fun st => st X = 3}}.
Proof.
  eapply hoare_consequence_post.
  apply hoare_while.
  eapply hoare_consequence_pre.
  apply hoare_asgn.
  unfold bassn, assn_sub, assert_implies, t_update. simpl.
    intros st [H1 H2]. apply leb_complete in H2. omega.
  unfold bassn, assert_implies. intros st [Hle Hb].
    simpl in Hb. destruct ((st X) <=? 2) eqn : Heqle.
    exfalso. apply Hb; reflexivity.
    apply leb_iff_conv in Heqle. omega.
Qed.
(** We can use the WHILE rule to prove the following Hoare triple... *)

Theorem always_loop_hoare : forall P Q,
  {{P}} WHILE true DO SKIP END {{Q}}.
Proof.
  (* WORKED IN CLASS *)
  intros P Q.
  apply hoare_consequence_pre with (P' := fun st : state => True).
  eapply hoare_consequence_post.
  apply hoare_while.
  - (* Loop body preserves invariant *)
    apply hoare_post_true. intros st. apply I.
  - (* Loop invariant and negated guard imply postcondition *)
    simpl. intros st [Hinv Hguard].
    exfalso. apply Hguard. reflexivity.
  - (* Precondition implies invariant *)
    intros st H. constructor.  Qed.

(** Of course, this result is not surprising if we remember that
    the definition of [hoare_triple] asserts that the postcondition
    must hold _only_ when the command terminates.  If the command
    doesn't terminate, we can prove anything we like about the
    postcondition. *)

(** Hoare rules that only talk about what happens when commands
    terminate (without proving that they do) are often said to
    describe a logic of "partial" correctness.  It is also possible to
    give Hoare rules for "total" correctness, which build in the fact
    that the commands terminate. However, in this course we will only
    talk about partial correctness. *)


(* ################################################################# *)
(** * Summary *)

(** So far, we've introduced Hoare Logic as a tool for reasoning about
    Imp programs. The rules of Hoare Logic are:

             --------------------------- (hoare_asgn)
             {{Q [X |-> a]}} X::=a {{Q}}

             --------------------  (hoare_skip)
             {{ P }} SKIP {{ P }}

               {{ P }} c1 {{ Q }}
               {{ Q }} c2 {{ R }}
              ----------------------  (hoare_seq)
              {{ P }} c1;;c2 {{ R }}

              {{P /\   b}} c1 {{Q}}
              {{P /\ ~ b}} c2 {{Q}}
      ------------------------------------  (hoare_if)
      {{P}} TEST b THEN c1 ELSE c2 FI {{Q}}

               {{P /\ b}} c {{P}}
        -----------------------------------  (hoare_while)
        {{P}} WHILE b DO c END {{P /\ ~ b}}

                {{P'}} c {{Q'}}
                   P ->> P'
                   Q' ->> Q
         -----------------------------   (hoare_consequence)
                {{P}} c {{Q}}
*)

(* ################################################################# *)

(** Exercise 14: Consider [prog1] below. What is the program doing?
Write down a specification as a Hoare triple and prove it correct. *)

Definition prog1 : com :=
  X ::= X + Y;;
  Y ::= X - Y;;
  X ::= X - Y.
  
Definition prog1_spec : forall a b : nat,
  {{fun st => st X = a /\ st Y = b}}
  prog1
  {{fun st => st X = b /\ st Y = a}}.
Proof.
  intros a b.
  eapply hoare_seq. eapply hoare_seq.
  - apply hoare_asgn.
  - apply hoare_asgn.
  - eapply hoare_consequence_pre. apply hoare_asgn. hsimpl.
Qed.
