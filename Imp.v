(** * Imp: Simple Imperative Programs *)

(** In this chapter, we begin a new direction that will continue for
    the rest of the course.  Up to now most of our attention has been
    focused on various aspects of Coq itself, while from now on we'll
    mostly be using Coq to formalize other things.  (We'll continue to
    pause from time to time to introduce a few additional aspects of
    Coq.)

    Our first case study is a _simple imperative programming language_
    called Imp, embodying a tiny core fragment of conventional
    mainstream languages such as C and Java.  Here is a familiar
    mathematical function written in Imp.

     Z ::= X;;
     Y ::= 1;;
     WHILE not (Z = 0) DO
       Y ::= Y * Z;;
       Z ::= Z - 1
     END
*)

(** This chapter looks at how to define the _syntax_ and _semantics_
    of Imp; the chapters that follow develop a theory of _program
    equivalence_ and introduce _Hoare Logic_, a widely used logic for
    reasoning about imperative programs. *)

(* IMPORTS *)
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Maps.
(* /IMPORTS *)

(* ################################################################# *)
(** * Arithmetic and Boolean Expressions *)

(** We'll present Imp in three parts: first a core language of
    _arithmetic and boolean expressions_, then an extension of these
    expressions with _variables_, and finally a language of _commands_
    including assignment, conditions, sequencing, and loops. *)

(* ================================================================= *)
(** ** Syntax *)

Module AExp.

(** These two definitions specify the _abstract syntax_ of
    arithmetic and boolean expressions. *)

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

(** In this chapter, we'll elide the translation from the
    concrete syntax that a programmer would actually write to these
    abstract syntax trees -- the process that, for example, would
    translate the string ["1+2*3"] to the AST

      APlus (ANum 1) (AMult (ANum 2) (ANum 3)).

    The optional chapter [ImpParser] develops a simple
    implementation of a lexical analyzer and parser that can perform
    this translation.  You do _not_ need to understand that chapter to
    understand this one, but if you haven't taken a course where these
    techniques are covered (e.g., a compilers course) you may want to
    skim it. *)

(** For comparison, here's a conventional BNF (Backus-Naur Form)
    grammar defining the same abstract syntax:

    a ::= nat
        | a + a
        | a - a
        | a * a

    b ::= true
        | false
        | a = a
        | a <= a
        | not b
        | b and b
*)

(** Compared to the Coq version above...

       - The BNF is more informal -- for example, it gives some
         suggestions about the surface syntax of expressions (like the
         fact that the addition operation is written [+] and is an
         infix symbol) while leaving other aspects of lexical analysis
         and parsing (like the relative precedence of [+], [-], and
         [*], the use of parens to explicitly group subexpressions,
         etc.) unspecified.  Some additional information (and human
         intelligence) would be required to turn this description into
         a formal definition, for example when implementing a
         compiler.

         The Coq version consistently omits all this information and
         concentrates on the abstract syntax only.

       - On the other hand, the BNF version is lighter and easier to
         read.  Its informality makes it flexible, a big advantage in
         situations like discussions at the blackboard, where
         conveying general ideas is more important than getting every
         detail nailed down precisely.

         Indeed, there are dozens of BNF-like notations and people
         switch freely among them, usually without bothering to say
         which form of BNF they're using because there is no need to:
         a rough-and-ready informal understanding is all that's
         important.

    It's good to be comfortable with both sorts of notations: informal
    ones for communicating between humans and formal ones for carrying
    out implementations and proofs. *)

(* ================================================================= *)
(** ** Evaluation *)

(** _Evaluating_ an arithmetic expression produces a number. *)

Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2  => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.

Example test_aeval1:
  aeval (APlus (ANum 2) (ANum 2)) = 4.
Proof. reflexivity. Qed.

(** Similarly, evaluating a boolean expression yields a boolean. *)

Fixpoint beval (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => beq_nat (aeval a1) (aeval a2)
  | BLe a1 a2   => leb (aeval a1) (aeval a2)
  | BNot b1     => negb (beval b1)
  | BAnd b1 b2  => andb (beval b1) (beval b2)
  end.

(* ================================================================= *)
(** ** Optimization *)

(** We haven't defined very much yet, but we can already get
    some mileage out of the definitions.  Suppose we define a function
    that takes an arithmetic expression and slightly simplifies it,
    changing every occurrence of [0+e] (i.e., [(APlus (ANum 0) e])
    into just [e]. *)

Fixpoint optimize_0plus (a:aexp) : aexp :=
  match a with
  | ANum n =>
      ANum n
  | APlus (ANum 0) e2 =>
      optimize_0plus e2
  | APlus e1 e2 =>
      APlus (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 =>
      AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult e1 e2 =>
      AMult (optimize_0plus e1) (optimize_0plus e2)
  end.

(** To make sure our optimization is doing the right thing we
    can test it on some examples and see if the output looks OK. *)

Example test_optimize_0plus:
  optimize_0plus (APlus (ANum 2)
                        (APlus (ANum 0)
                               (APlus (ANum 0) (ANum 1))))
  = APlus (ANum 2) (ANum 1).
Proof. reflexivity. Qed.

(** But if we want to be sure the optimization is correct --
    i.e., that evaluating an optimized expression gives the same
    result as the original -- we should prove it. *)

Theorem optimize_0plus_sound: forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a. induction a.
  - (* ANum *) reflexivity.
  - (* APlus *) destruct a1.
    + (* a1 = ANum n *) destruct n.
      * (* n = 0 *)  simpl. apply IHa2.
      * (* n <> 0 *) simpl. rewrite IHa2. reflexivity.
    + (* a1 = APlus a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + (* a1 = AMinus a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + (* a1 = AMult a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
  - (* AMinus *)
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  - (* AMult *)
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.  Qed.

(* ################################################################# *)
(** * Coq Automation *)

(** The amount of repetition in this last proof is a little
    annoying.  And if either the language of arithmetic expressions or
    the optimization being proved sound were significantly more
    complex, it would start to be a real problem.

    So far, we've been doing all our proofs using just a small handful
    of Coq's tactics and completely ignoring its powerful facilities
    for constructing parts of proofs automatically.  This section
    introduces some of these facilities, and we will see more over the
    next several chapters.  Getting used to them will take some
    energy -- Coq's automation is a power tool -- but it will allow us
    to scale up our efforts to more complex definitions and more
    interesting properties without becoming overwhelmed by boring,
    repetitive, low-level details. *)

(* ================================================================= *)
(** ** Tacticals *)

(** _Tacticals_ is Coq's term for tactics that take other tactics as
    arguments -- "higher-order tactics," if you will.  *)

(* ----------------------------------------------------------------- *)
(** *** The [try] Tactical *)

(** If [T] is a tactic, then [try T] is a tactic that is just like [T]
    except that, if [T] fails, [try T] _successfully_ does nothing at
    all (instead of failing). *)

Theorem silly1 : forall ae, aeval ae = aeval ae.
Proof. try reflexivity. (* this just does [reflexivity] *) Qed.

Theorem silly2 : forall (P : Prop), P -> P.
Proof.
  intros P HP.
  try reflexivity. (* just [reflexivity] would have failed *)
  apply HP. (* we can still finish the proof in some other way *)
Qed.

(** There is no real reason to use [try] in completely manual
    proofs like these, but it is very useful for doing automated
    proofs in conjunction with the [;] tactical, which we show
    next. *)

(* ----------------------------------------------------------------- *)
(** *** The [;] Tactical (Simple Form) *)

(** In its most common form, the [;] tactical takes two tactics as
    arguments.  The compound tactic [T;T'] first performs [T] and then
    performs [T'] on _each subgoal_ generated by [T]. *)

(** For example, consider the following trivial lemma: *)

Lemma foo : forall n, leb 0 n = true.
Proof.
  intros.
  destruct n.
    (* Leaves two subgoals, which are discharged identically...  *)
    - (* n=0 *) simpl. reflexivity.
    - (* n=Sn' *) simpl. reflexivity.
Qed.

(** We can simplify this proof using the [;] tactical: *)

Lemma foo' : forall n, leb 0 n = true.
Proof.
  intros.
  (* [destruct] the current goal *)
  destruct n;
  (* then [simpl] each resulting subgoal *)
  simpl;
  (* and do [reflexivity] on each resulting subgoal *)
  reflexivity.
Qed.

(** Using [try] and [;] together, we can get rid of the repetition in
    the proof that was bothering us a little while ago. *)

Theorem optimize_0plus_sound': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    (* Most cases follow directly by the IH... *)
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity).
    (* ... but the remaining cases -- ANum and APlus --
       are different: *)
  - (* ANum *) reflexivity.
  - (* APlus *)
    destruct a1;
      (* Again, most cases follow directly by the IH: *)
      try (simpl; simpl in IHa1; rewrite IHa1;
           rewrite IHa2; reflexivity).
    (* The interesting case, on which the [try...]
       does nothing, is when [e1 = ANum n]. In this
       case, we have to destruct [n] (to see whether
       the optimization applies) and rewrite with the
       induction hypothesis. *)
    + (* a1 = ANum n *) destruct n;
      simpl; rewrite IHa2; reflexivity.   Qed.

(** Coq experts often use this "[...; try... ]" idiom after a tactic
    like [induction] to take care of many similar cases all at once.
    Naturally, this practice has an analog in informal proofs.  For
    example, here is an informal proof of the optimization theorem
    that matches the structure of the formal one:

    _Theorem_: For all arithmetic expressions [a],

       aeval (optimize_0plus a) = aeval a.

    _Proof_: By induction on [a].  Most cases follow directly from the
    IH.  The remaining cases are as follows:

      - Suppose [a = ANum n] for some [n].  We must show

          aeval (optimize_0plus (ANum n)) = aeval (ANum n).

        This is immediate from the definition of [optimize_0plus].

      - Suppose [a = APlus a1 a2] for some [a1] and [a2].  We must
        show

          aeval (optimize_0plus (APlus a1 a2)) = aeval (APlus a1 a2).

        Consider the possible forms of [a1].  For most of them,
        [optimize_0plus] simply calls itself recursively for the
        subexpressions and rebuilds a new expression of the same form
        as [a1]; in these cases, the result follows directly from the
        IH.

        The interesting case is when [a1 = ANum n] for some [n].  If
        [n = ANum 0], then

          optimize_0plus (APlus a1 a2) = optimize_0plus a2

        and the IH for [a2] is exactly what we need.  On the other
        hand, if [n = S n'] for some [n'], then again [optimize_0plus]
        simply calls itself recursively, and the result follows from
        the IH.  [] *)

(** However, this proof can still be improved: the first case (for
    [a = ANum n]) is very trivial -- even more trivial than the cases
    that we said simply followed from the IH -- yet we have chosen to
    write it out in full.  It would be better and clearer to drop it
    and just say, at the top, "Most cases are either immediate or
    direct from the IH.  The only interesting case is the one for
    [APlus]..."  We can make the same improvement in our formal proof
    too.  Here's how it looks: *)

Theorem optimize_0plus_sound'': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    (* Most cases follow directly by the IH *)
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity);
    (* ... or are immediate by definition *)
    try reflexivity.
  (* The interesting case is when a = APlus a1 a2. *)
  - (* APlus *)
    destruct a1; try (simpl; simpl in IHa1; rewrite IHa1;
                      rewrite IHa2; reflexivity).
    + (* a1 = ANum n *) destruct n;
      simpl; rewrite IHa2; reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(** *** The [;] Tactical (General Form) *)

(** The [;] tactical also has a more general form than the simple
    [T;T'] we've seen above.  If [T], [T1], ..., [Tn] are tactics,
    then

      T; [T1 | T2 | ... | Tn]

   is a tactic that first performs [T] and then performs [T1] on the
   first subgoal generated by [T], performs [T2] on the second
   subgoal, etc.

   So [T;T'] is just special notation for the case when all of the
   [Ti]'s are the same tactic; i.e., [T;T'] is shorthand for:

      T; [T' | T' | ... | T']
*)

(* ----------------------------------------------------------------- *)
(** *** The [repeat] Tactical *)

(** The [repeat] tactical takes another tactic and keeps applying this
    tactic until it fails. Here is an example showing that [10] is in
    a long list using repeat. *)

Theorem In10 : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (try (left; reflexivity); right).
Qed.

(** The tactic [repeat T] never fails: if the tactic [T] doesn't apply
    to the original goal, then repeat still succeeds without changing
    the original goal (i.e., it repeats zero times). *)

Theorem In10' : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (left; reflexivity).
  repeat (right; try (left; reflexivity)).
Qed.

(** The tactic [repeat T] also does not have any upper bound on the
    number of times it applies [T].  If [T] is a tactic that always
    succeeds, then repeat [T] will loop forever (e.g., [repeat simpl]
    loops forever, since [simpl] always succeeds).  While evaluation
    in Coq's term language, Gallina, is guaranteed to terminate,
    tactic evaluation is not!  This does not affect Coq's logical
    consistency, however, since the job of [repeat] and other tactics
    is to guide Coq in constructing proofs; if the construction
    process diverges, this simply means that we have failed to
    construct a proof, not that we have constructed a wrong one. *)

(** **** Exercise: 3 stars (optimize_0plus_b)  *)
(** Since the [optimize_0plus] transformation doesn't change the value
    of [aexp]s, we should be able to apply it to all the [aexp]s that
    appear in a [bexp] without changing the [bexp]'s value.  Write a
    function which performs that transformation on [bexp]s, and prove
    it is sound.  Use the tacticals we've just seen to make the proof
    as elegant as possible. *)

Fixpoint optimize_0plus_b (b : bexp) : bexp :=
  match b with
    | BTrue       => BTrue
    | BFalse      => BFalse
    | BEq a1 a2   => BEq (optimize_0plus a1) (optimize_0plus a2)
    | BLe a1 a2   => BLe (optimize_0plus a1) (optimize_0plus a2)
    | BNot b1     => BNot (optimize_0plus_b b1)
    | BAnd b1 b2  => BAnd (optimize_0plus_b b1) (optimize_0plus_b b2)
  end.

Theorem optimize_0plus_b_sound : forall b,
  beval (optimize_0plus_b b) = beval b.
Proof.
  intros.
  induction b;
    try (simpl; reflexivity);
    try (simpl; rewrite IHb1; rewrite IHb2; reflexivity);
    try (simpl; rewrite optimize_0plus_sound; rewrite optimize_0plus_sound; reflexivity).
  - simpl. rewrite IHb. reflexivity.
Qed.  
(** [] *)

(** **** Exercise: 4 stars, optional (optimizer)  *)
(** _Design exercise_: The optimization implemented by our
    [optimize_0plus] function is only one of many possible
    optimizations on arithmetic and boolean expressions.  Write a more
    sophisticated optimizer and prove it correct.  (You will probably
    find it easiest to start small -- add just a single, simple
    optimization and prove it correct -- and build up to something
    more interesting incrementially.*)
Fixpoint optimize_0mult (a:aexp) : aexp :=
  match a with
  | ANum n =>
      ANum n
  | APlus e1 e2 =>
      APlus (optimize_0mult e1) (optimize_0mult e2)
  | AMinus e1 e2 =>
      AMinus (optimize_0mult e1) (optimize_0mult e2)
  | AMult (ANum 0) e2 =>
      ANum 0
  | AMult e1 e2 =>
      AMult (optimize_0mult e1) (optimize_0mult e2)
end.

Theorem optimize_0mult_sound : forall a,
  aeval (optimize_0mult a) = aeval a.
Proof.
  intros.
  induction a;
    try (simpl; reflexivity);
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity).
  - simpl. destruct a1;
    try (simpl; simpl in IHa1; rewrite IHa1; rewrite IHa2; reflexivity).
    + destruct n.
      -- simpl. reflexivity.
      -- simpl. rewrite IHa2. reflexivity.
Qed.

(** Combination of two optimziation *)
Definition optimize_aexp (a : aexp) := optimize_0mult (optimize_0plus a).

Theorem optimized_sound : forall a,
  aeval (optimize_aexp a) = aeval a.
Proof.
  intros.
  unfold optimize_aexp.
  rewrite (optimize_0mult_sound (optimize_0plus a)).
  apply optimize_0plus_sound.
Qed.
(** [] *)

(* ================================================================= *)
(** ** Defining New Tactic Notations *)

(** Coq also provides several ways of "programming" tactic scripts.

    - The [Tactic Notation] idiom illustrated below gives a handy way to
      define "shorthand tactics" that bundle several tactics into a
      single command.

    - For more sophisticated programming, Coq offers a built-in
      programming language called [Ltac] with primitives that can
      examine and modify the proof state.  The details are a bit too
      complicated to get into here (and it is generally agreed that
      [Ltac] is not the most beautiful part of Coq's design!), but they
      can be found in the reference manual and other books on Coq, and
      there are many examples of [Ltac] definitions in the Coq standard
      library that you can use as examples.

    - There is also an OCaml API, which can be used to build tactics
      that access Coq's internal structures at a lower level, but this
      is seldom worth the trouble for ordinary Coq users.

    The [Tactic Notation] mechanism is the easiest to come to grips with,
    and it offers plenty of power for many purposes.  Here's an example. *)

Tactic Notation "simpl_and_try" tactic(c) :=
  simpl;
  try c.

(** This defines a new tactical called [simpl_and_try] that takes one
    tactic [c] as an argument and is defined to be equivalent to the
    tactic [simpl; try c].  Now writing "[simpl_and_try reflexivity.]"
    in a proof will be the same as writing "[simpl; try
    reflexivity.]" *)

(* ================================================================= *)
(** ** The [omega] Tactic *)

(** The [omega] tactic implements a decision procedure for a subset of
    first-order logic called _Presburger arithmetic_.  It is based on
    the Omega algorithm invented in 1991 by William Pugh [Pugh 1991].

    If the goal is a universally quantified formula made out of

      - numeric constants, addition ([+] and [S]), subtraction ([-]
        and [pred]), and multiplication by constants (this is what
        makes it Presburger arithmetic),

      - equality ([=] and [<>]) and inequality ([<=]), and

      - the logical connectives [/\], [\/], [~], and [->],

    then invoking [omega] will either solve the goal or tell you that
    it is actually false. *)

Require Import Coq.micromega.Lia.

Example silly_presburger_example : forall m n o p,
  m + n <= n + o /\ o + 3 = p + 3 ->
  m <= p.
Proof.
  intros. lia.
Qed.

(* ================================================================= *)
(** ** A Few More Handy Tactics *)

(** Finally, here are some miscellaneous tactics that you may find
    convenient.

     - [clear H]: Delete hypothesis [H] from the context.

     - [subst x]: Find an assumption [x = e] or [e = x] in the
       context, replace [x] with [e] throughout the context and
       current goal, and clear the assumption.

     - [subst]: Substitute away _all_ assumptions of the form [x = e]
       or [e = x].

     - [rename... into...]: Change the name of a hypothesis in the
       proof context.  For example, if the context includes a variable
       named [x], then [rename x into y] will change all occurrences
       of [x] to [y].

     - [assumption]: Try to find a hypothesis [H] in the context that
       exactly matches the goal; if one is found, behave like [apply
       H].

     - [contradiction]: Try to find a hypothesis [H] in the current
       context that is logically equivalent to [False].  If one is
       found, solve the goal.

     - [constructor]: Try to find a constructor [c] (from some
       [Inductive] definition in the current environment) that can be
       applied to solve the current goal.  If one is found, behave
       like [apply c].

    We'll see examples below. *)

(* ################################################################# *)
(** * Evaluation as a Relation *)

(** We have presented [aeval] and [beval] as functions defined by
    [Fixpoint]s.  Another way to think about evaluation -- one that we
    will see is often more flexible -- is as a _relation_ between
    expressions and their values.  This leads naturally to [Inductive]
    definitions like the following one for arithmetic expressions... *)

Module aevalR_first_try.

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum  : forall (n: nat),
      aevalR (ANum n) n
  | E_APlus : forall (e1 e2: aexp) (n1 n2: nat),
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus: forall (e1 e2: aexp) (n1 n2: nat),
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult : forall (e1 e2: aexp) (n1 n2: nat),
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMult e1 e2) (n1 * n2).

(** It will be convenient to have an infix notation for
    [aevalR].  We'll write [e \\ n] to mean that arithmetic expression
    [e] evaluates to value [n].  (This notation is one place where the
    limitation to ASCII symbols becomes a little bothersome.  The
    standard notation for the evaluation relation is a double
    down-arrow.  We'll typeset it like this in the HTML version of the
    notes and use a double slash as the closest approximation in [.v]
    files.)  *)

Notation "e '\\' n"
         := (aevalR e n)
            (at level 50, left associativity)
         : type_scope.

End aevalR_first_try.

(** In fact, Coq provides a way to use this notation in the
    definition of [aevalR] itself.  This reduces confusion by avoiding
    situations where we're working on a proof involving statements in
    the form [e \\ n] but we have to refer back to a definition
    written using the form [aevalR e n].

    We do this by first "reserving" the notation, then giving the
    definition together with a declaration of what the notation
    means. *)

Reserved Notation "e '\\' n" (at level 50, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum : forall (n:nat),
      (ANum n) \\ n
  | E_APlus : forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 \\ n1) -> (e2 \\ n2) -> (APlus e1 e2) \\ (n1 + n2)
  | E_AMinus : forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 \\ n1) -> (e2 \\ n2) -> (AMinus e1 e2) \\ (n1 - n2)
  | E_AMult :  forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 \\ n1) -> (e2 \\ n2) -> (AMult e1 e2) \\ (n1 * n2)

  where "e '\\' n" := (aevalR e n) : type_scope.

(* ================================================================= *)
(** ** Inference Rule Notation *)

(** In informal discussions, it is convenient to write the rules for
    [aevalR] and similar relations in the more readable graphical form
    of _inference rules_, where the premises above the line justify
    the conclusion below the line (we have already seen them in the
    [Prop] chapter). *)

(** For example, the constructor [E_APlus]...

      | E_APlus : forall (e1 e2: aexp) (n1 n2: nat),
          aevalR e1 n1 ->
          aevalR e2 n2 ->
          aevalR (APlus e1 e2) (n1 + n2)

    ...would be written like this as an inference rule:

                               e1 \\ n1
                               e2 \\ n2
                         --------------------                         (E_APlus)
                         APlus e1 e2 \\ n1+n2
*)

(** Formally, there is nothing deep about inference rules: they
    are just implications.  You can read the rule name on the right as
    the name of the constructor and read each of the linebreaks
    between the premises above the line (as well as the line itself)
    as [->].  All the variables mentioned in the rule ([e1], [n1],
    etc.) are implicitly bound by universal quantifiers at the
    beginning. (Such variables are often called _metavariables_ to
    distinguish them from the variables of the language we are
    defining.  At the moment, our arithmetic expressions don't include
    variables, but we'll soon be adding them.)  The whole collection
    of rules is understood as being wrapped in an [Inductive]
    declaration.  In informal prose, this is either elided or else
    indicated by saying something like "Let [aevalR] be the smallest
    relation closed under the following rules...". *)

(** For example, [\\] is the smallest relation closed under these
    rules:

                             -----------                               (E_ANum)
                             ANum n \\ n

                               e1 \\ n1
                               e2 \\ n2
                         --------------------                         (E_APlus)
                         APlus e1 e2 \\ n1+n2

                               e1 \\ n1
                               e2 \\ n2
                        ---------------------                        (E_AMinus)
                        AMinus e1 e2 \\ n1-n2

                               e1 \\ n1
                               e2 \\ n2
                         --------------------                         (E_AMult)
                         AMult e1 e2 \\ n1*n2
*)

(* ================================================================= *)
(** ** Equivalence of the Definitions *)

(** It is straightforward to prove that the relational and functional
    definitions of evaluation agree: *)

Theorem aeval_iff_aevalR : forall a n,
  (a \\ n) <-> aeval a = n.
Proof.
 split.
 - (* -> *)
   intros H.
   induction H; simpl.
   + (* E_ANum *)
     reflexivity.
   + (* E_APlus *)
     rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
   + (* E_AMinus *)
     rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
   + (* E_AMult *)
     rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
 - (* <- *)
   generalize dependent n.
   induction a;
      simpl; intros; subst.
   + (* ANum *)
     apply E_ANum.
   + (* APlus *)
     apply E_APlus.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
   + (* AMinus *)
     apply E_AMinus.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
   + (* AMult *)
     apply E_AMult.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
Qed.

(** We can make the proof quite a bit shorter by making more
    use of tacticals. *)

Theorem aeval_iff_aevalR' : forall a n,
  (a \\ n) <-> aeval a = n.
Proof.
  (* WORKED IN CLASS *)
  split.
  - (* -> *)
    intros H; induction H; subst; reflexivity.
  - (* <- *)
    generalize dependent n.
    induction a; simpl; intros; subst; constructor;
       try apply IHa1; try apply IHa2; reflexivity.
Qed.

(** **** Exercise: 3 stars  (bevalR)  *)
(** Write a relation [bevalR] in the same style as
    [aevalR], and prove that it is equivalent to [beval].*)

Inductive bevalR: bexp -> bool -> Prop :=
  | E_BTrue : bevalR BTrue true
  | E_BFalse : bevalR BFalse false
  | E_BEq : forall (a1 a2 : aexp) (n1 n2 : nat),
            a1 \\ n1 -> a2 \\ n2 -> bevalR (BEq a1 a2) (n1 =? n2)
  | E_BLe : forall (a1 a2 : aexp) (n1 n2 : nat),
            a1 \\ n1 -> a2 \\ n2 -> bevalR (BLe a1 a2) (n1 <=? n2)
  | E_BNot : forall (b : bexp) (b1 : bool),
            bevalR b b1 -> bevalR (BNot b) (negb b1)
  | E_BAnd : forall (b1 b2 : bexp) (n1 n2 : bool),
            bevalR b1 n1 -> bevalR b2 n2 -> bevalR (BAnd b1 b2) (n1 && n2). 

Lemma beval_iff_bevalR : forall b bv,
  bevalR b bv <-> beval b = bv.
Proof.
  intros.
  split.
  - intros.
    induction H.
    + simpl. reflexivity.
    + simpl. reflexivity.
    + simpl. apply aeval_iff_aevalR in H. apply aeval_iff_aevalR in H0.
      rewrite H. rewrite H0. reflexivity.
    + simpl. apply aeval_iff_aevalR in H. apply aeval_iff_aevalR in H0.
      rewrite H. rewrite H0. reflexivity.
    + simpl. rewrite IHbevalR. reflexivity.
    + simpl. rewrite IHbevalR1. rewrite IHbevalR2. reflexivity.
  - generalize dependent bv.
    induction b;
    try (intros; simpl in H; rewrite <- H).
    + apply E_BTrue.
    + apply E_BFalse.
    + apply E_BEq;
      (apply aeval_iff_aevalR; reflexivity).
    + apply E_BLe;
      (apply aeval_iff_aevalR; reflexivity).
    + apply E_BNot.
      specialize (IHb (negb bv)). 
      assert (beval b = negb bv). {
        rewrite <- H.
        rewrite negb_involutive.
         reflexivity.
      }
      apply IHb in H0. rewrite <- H in H0. rewrite negb_involutive in H0. apply H0.
    + apply E_BAnd.
      -- specialize (IHb1 (beval b1)). assert (beval b1 = beval b1). { reflexivity. }
         apply IHb1 in H0. apply H0.
      -- specialize (IHb2 (beval b2)). assert (beval b2 = beval b2). { reflexivity. }
         apply IHb2 in H0. apply H0.
Qed.


(** [] *)

End AExp.

(* ================================================================= *)
(** ** Computational vs. Relational Definitions *)

(** For the definitions of evaluation for arithmetic and boolean
    expressions, the choice of whether to use functional or relational
    definitions is mainly a matter of taste: either way works.

    However, there are circumstances where relational definitions of
    evaluation work much better than functional ones.  *)

Module aevalR_division.

(** For example, suppose that we wanted to extend the arithmetic
    operations by considering also a division operation:*)

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp
  | ADiv : aexp -> aexp -> aexp.   (* <--- new *)

(** Extending the definition of [aeval] to handle this new operation
    would not be straightforward (what should we return as the result
    of [ADiv (ANum 5) (ANum 0)]?).  But extending [aevalR] is
    straightforward. *)

Reserved Notation "e '\\' n"
                  (at level 50, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum : forall (n:nat),
      (ANum n) \\ n
  | E_APlus : forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 \\ n1) -> (a2 \\ n2) -> (APlus a1 a2) \\ (n1 + n2)
  | E_AMinus : forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 \\ n1) -> (a2 \\ n2) -> (AMinus a1 a2) \\ (n1 - n2)
  | E_AMult :  forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 \\ n1) -> (a2 \\ n2) -> (AMult a1 a2) \\ (n1 * n2)
  | E_ADiv :  forall (a1 a2: aexp) (n1 n2 n3: nat),
      (a1 \\ n1) -> (a2 \\ n2) -> (n2 > 0) ->
      (mult n2 n3 = n1) -> (ADiv a1 a2) \\ n3

where "a '\\' n" := (aevalR a n) : type_scope.

End aevalR_division.

Module aevalR_extended.

(** Suppose, instead, that we want to extend the arithmetic operations
    by a nondeterministic number generator [any] that, when evaluated,
    may yield any number.  (Note that this is not the same as making a
    _probabilistic_ choice among all possible numbers -- we're not
    specifying any particular distribution of results, but just saying
    what results are _possible_.) *)

Reserved Notation "e '\\' n" (at level 50, left associativity).

Inductive aexp : Type :=
  | AAny  : aexp                   (* <--- NEW *)
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

(** Again, extending [aeval] would be tricky, since now evaluation is
    _not_ a deterministic function from expressions to numbers, but
    extending [aevalR] is no problem: *)

Inductive aevalR : aexp -> nat -> Prop :=
  | E_Any : forall (n:nat),
      AAny \\ n                 (* <--- new *)
  | E_ANum : forall (n:nat),
      (ANum n) \\ n
  | E_APlus : forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 \\ n1) -> (a2 \\ n2) -> (APlus a1 a2) \\ (n1 + n2)
  | E_AMinus : forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 \\ n1) -> (a2 \\ n2) -> (AMinus a1 a2) \\ (n1 - n2)
  | E_AMult :  forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 \\ n1) -> (a2 \\ n2) -> (AMult a1 a2) \\ (n1 * n2)

where "a '\\' n" := (aevalR a n) : type_scope.

End aevalR_extended.

(** At this point you maybe wondering: which style should I use by
    default?  The examples above show that relational definitions are
    fundamentally more powerful than functional ones.  For situations
    like these, where the thing being defined is not easy to express
    as a function, or indeed where it is _not_ a function, there is no
    choice.  But what about when both styles are workable?

    One point in favor of relational definitions is that some people
    feel they are more elegant and easier to understand.  Another is
    that Coq automatically generates nice inversion and induction
    principles from [Inductive] definitions.

    On the other hand, functional definitions can often be more
    convenient:
     - Functions are by definition deterministic and defined on all
       arguments; for a relation we have to show these properties
       explicitly if we need them.
     - With functions we can also take advantage of Coq's computation
       mechanism to simplify expressions during proofs.

    Furthermore, functions can be directly "extracted" to executable
    code in OCaml or Haskell.

    Ultimately, the choice often comes down to either the specifics of
    a particular situation or simply a question of taste.  Indeed, in
    large Coq developments it is common to see a definition given in
    _both_ functional and relational styles, plus a lemma stating that
    the two coincide, allowing further proofs to switch from one point
    of view to the other at will.*)

(* ################################################################# *)
(** * Expressions With Variables *)

(** Let's turn our attention back to defining Imp.  The next thing we
    need to do is to enrich our arithmetic and boolean expressions
    with variables.  To keep things simple, we'll assume that all
    variables are global and that they only hold numbers. *)

(* ================================================================= *)
(** ** States *)

(** Since we'll want to look variables up to find out their current
    values, we'll reuse the type [id] from the [Maps] chapter for the
    type of variables in Imp.

    A _machine state_ (or just _state_) represents the current values
    of _all_ variables at some point in the execution of a program. *)

(** For simplicity, we assume that the state is defined for
    _all_ variables, even though any given program is only going to
    mention a finite number of them.  The state captures all of the
    information stored in memory.  For Imp programs, because each
    variable stores a natural number, we can represent the state as a
    mapping from identifiers to [nat].  For more complex programming
    languages, the state might have more structure. *)

Definition state := total_map nat.

Definition empty_state : state :=
  t_empty 0.

(* ================================================================= *)
(** ** Syntax  *)

(** We can add variables to the arithmetic expressions we had before by
    simply adding one more constructor: *)

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | AId : id -> aexp                (* <----- NEW *)
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

(** Defining a few variable names as notational shorthands will make
    examples easier to read: *)
Require Import String.
Definition W : id := Id "W".
Definition X : id := Id "X".
Definition Y : id := Id "Y".
Definition Z : id := Id "Z".

(** (This convention for naming program variables ([X], [Y],
    [Z]) clashes a bit with our earlier use of uppercase letters for
    types.  Since we're not using polymorphism heavily in the chapters
    devoped to Imp, this overloading should not cause confusion.) *)

(** The definition of [bexp]s is unchanged (except for using the new
    [aexp]s): *)

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

(* ================================================================= *)
(** ** Evaluation *)

(** The arith and boolean evaluators are extended to handle
    variables in the obvious way, taking a state as an extra
    argument: *)

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x                                (* <----- NEW *)
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2  => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => (aeval st a1) =? (aeval st a2)
  | BLe a1 a2   => (aeval st a1) <=? (aeval st a2)
  | BNot b1     => negb (beval st b1)
  | BAnd b1 b2  => andb (beval st b1) (beval st b2)
  end.

Example aexp1 :
  aeval (t_update empty_state X 5)
        (APlus (ANum 3) (AMult (AId X) (ANum 2)))
  = 13.
Proof. reflexivity. Qed.

Example bexp1 :
  beval (t_update empty_state X 5)
        (BAnd BTrue (BNot (BLe (AId X) (ANum 4))))
  = true.
Proof. reflexivity. Qed.

(* ################################################################# *)
(** * Commands *)

(** Now we are ready define the syntax and behavior of Imp
    _commands_ (sometimes called _statements_). *)

(* ================================================================= *)
(** ** Syntax *)

(** Informally, commands [c] are described by the following BNF
    grammar.  (We choose this slightly awkward concrete syntax for the
    sake of being able to define Imp syntax using Coq's Notation
    mechanism.  In particular, we use [IFB] to avoid conflicting with
    the [if] notation from the standard library.)

     c ::= SKIP | x ::= a | c ;; c | IFB b THEN c ELSE c FI
         | WHILE b DO c END
*)
(**
    For example, here's factorial in Imp:

     Z ::= X;;
     Y ::= 1;;
     WHILE not (Z = 0) DO
       Y ::= Y * Z;;
       Z ::= Z - 1
     END

   When this command terminates, the variable [Y] will contain the
   factorial of the initial value of [X]. *)

(** Here is the formal definition of the abstract syntax of
    commands: *)

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.

(** As usual, we can use a few [Notation] declarations to make things
    more readable.  To avoid conflicts with Coq's built-in notations,
    we keep this light -- in particular, we don't introduce any
    notations for [aexps] and [bexps] to avoid confusion with the
    numeric and boolean operators we've already defined. *)

Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).

(** For example, here is the factorial function again, written as a
    formal definition to Coq: *)

Definition fact_in_coq : com :=
  Z ::= AId X;;
  Y ::= ANum 1;;
  WHILE BNot (BEq (AId Z) (ANum 0)) DO
    Y ::= AMult (AId Y) (AId Z);;
    Z ::= AMinus (AId Z) (ANum 1)
  END.

(* ================================================================= *)
(** ** More Examples *)

(** Assignment: *)

Definition plus2 : com :=
  X ::= (APlus (AId X) (ANum 2)).

Definition XtimesYinZ : com :=
  Z ::= (AMult (AId X) (AId Y)).

Definition subtract_slowly_body : com :=
  Z ::= AMinus (AId Z) (ANum 1) ;;
  X ::= AMinus (AId X) (ANum 1).

(* ----------------------------------------------------------------- *)
(** *** Loops *)

Definition subtract_slowly : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    subtract_slowly_body
  END.

Definition subtract_3_from_5_slowly : com :=
  X ::= ANum 3 ;;
  Z ::= ANum 5 ;;
  subtract_slowly.

(* ----------------------------------------------------------------- *)
(** *** An infinite loop: *)

Definition loop : com :=
  WHILE BTrue DO
    SKIP
  END.

(* ################################################################# *)
(** * Evaluating Commands *)

(** Next we need to define what it means to evaluate an Imp command.
    The fact that [WHILE] loops don't necessarily terminate makes defining
    an evaluation function tricky... *)

(* ================================================================= *)
(** ** Evaluation as a Function (Failed Attempt) *)

(** Here's an attempt at defining an evaluation function for commands,
    omitting the [WHILE] case. *)

Fixpoint ceval_fun_no_while (st : state) (c : com)
                          : state :=
  match c with
    | SKIP =>
        st
    | x ::= a1 =>
        t_update st x (aeval st a1)
    | c1 ;; c2 =>
        let st' := ceval_fun_no_while st c1 in
        ceval_fun_no_while st' c2
    | IFB b THEN c1 ELSE c2 FI =>
        if (beval st b)
          then ceval_fun_no_while st c1
          else ceval_fun_no_while st c2
    | WHILE b DO c END =>
        st  (* bogus *)
  end.

(** In a traditional functional programming language like OCaml or
    Haskell we could add the [WHILE] case as follows:

  Fixpoint ceval_fun (st : state) (c : com) : state :=
    match c with
      ...
      | WHILE b DO c END =>
          if (beval st b)
            then ceval_fun st (c; WHILE b DO c END)
            else st
    end.

    Coq doesn't accept such a definition ("Error: Cannot guess
    decreasing argument of fix") because the function we want to
    define is not guaranteed to terminate. Indeed, it _doesn't_ always
    terminate: for example, the full version of the [ceval_fun]
    function applied to the [loop] program above would never
    terminate. Since Coq is not just a functional programming
    language but also a consistent logic, any potentially
    non-terminating function needs to be rejected. Here is
    an (invalid!) program showing what would go wrong if Coq
    allowed non-terminating recursive functions:

         Fixpoint loop_false (n : nat) : False := loop_false n.

    That is, propositions like [False] would become provable
    ([loop_false 0] would be a proof of [False]), which
    would be a disaster for Coq's logical consistency.

    Thus, because it doesn't terminate on all inputs,
    of [ceval_fun] cannot be written in Coq -- at least not without
    additional tricks and workarounds (see chapter [ImpCEvalFun]
    if you're curious about what those might be). *)

(* ================================================================= *)
(** ** Evaluation as a Relation *)

(** Here's a better way: define [ceval] as a _relation_ rather than a
    _function_ -- i.e., define it in [Prop] instead of [Type], as we
    did for [aevalR] above. *)

(** This is an important change.  Besides freeing us from awkward
    workarounds, it gives us a lot more flexibility in the definition.
    For example, if we add nondeterministic features like [any] to the
    language, we want the definition of evaluation to be
    nondeterministic -- i.e., not only will it not be total, it will
    not even be a function! *)

(** We'll use the notation [c / st \\ st'] for the [ceval] relation:
    [c / st \\ st'] means that executing program [c] in a starting
    state [st] results in an ending state [st'].  This can be
    pronounced "[c] takes state [st] to [st']". *)

(* ----------------------------------------------------------------- *)
(** *** Operational Semantics *)

(** Here is an informal definition of evaluation, presented as inference
    rules for readability:

                           ----------------                            (E_Skip)
                           SKIP / st \\ st

                           aeval st a1 = n
                   --------------------------------                     (E_Ass)
                   x := a1 / st \\ (t_update st x n)

                           c1 / st \\ st'
                          c2 / st' \\ st''
                         -------------------                            (E_Seq)
                         c1;;c2 / st \\ st''

                          beval st b1 = true
                           c1 / st \\ st'
                -------------------------------------                (E_IfTrue)
                IF b1 THEN c1 ELSE c2 FI / st \\ st'

                         beval st b1 = false
                           c2 / st \\ st'
                -------------------------------------               (E_IfFalse)
                IF b1 THEN c1 ELSE c2 FI / st \\ st'

                         beval st b = false
                    ------------------------------                 (E_WhileEnd)
                    WHILE b DO c END / st \\ st

                          beval st b = true
                           c / st \\ st'
                  WHILE b DO c END / st' \\ st''
                  ---------------------------------               (E_WhileLoop)
                    WHILE b DO c END / st \\ st''
*)

(** Here is the formal definition.  Make sure you understand
    how it corresponds to the inference rules. *)

Reserved Notation "c1 '/' st '\\' st'"
                  (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      SKIP / st \\ st
  | E_Ass  : forall st a1 n x,
      aeval st a1 = n ->
      (x ::= a1) / st \\ (t_update st x n)
  | E_Seq : forall c1 c2 st st' st'',
      c1 / st  \\ st' ->
      c2 / st' \\ st'' ->
      (c1 ;; c2) / st \\ st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      c1 / st \\ st' ->
      (IFB b THEN c1 ELSE c2 FI) / st \\ st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      c2 / st \\ st' ->
      (IFB b THEN c1 ELSE c2 FI) / st \\ st'
  | E_WhileEnd : forall b st c,
      beval st b = false ->
      (WHILE b DO c END) / st \\ st
  | E_WhileLoop : forall st st' st'' b c,
      beval st b = true ->
      c / st \\ st' ->
      (WHILE b DO c END) / st' \\ st'' ->
      (WHILE b DO c END) / st \\ st''

  where "c1 '/' st '\\' st'" := (ceval c1 st st').

(** The cost of defining evaluation as a relation instead of a
    function is that we now need to construct _proofs_ that some
    program evaluates to some result state, rather than just letting
    Coq's computation mechanism do it for us. *)

Example ceval_example1:
    (X ::= ANum 2;;
     IFB BLe (AId X) (ANum 1)
       THEN Y ::= ANum 3
       ELSE Z ::= ANum 4
     FI)
   / empty_state
   \\ (t_update (t_update empty_state X 2) Z 4).
Proof.
  (* We must supply the intermediate state *)
  apply E_Seq with (t_update empty_state X 2).
  - (* assignment command *)
    apply E_Ass. reflexivity.
  - (* if command *)
    apply E_IfFalse.
      reflexivity.
      apply E_Ass. reflexivity.  Qed.

(** **** Exercise: 2 stars (ceval_example2)  *)
Example ceval_example2:
    (X ::= ANum 0;; Y ::= ANum 1;; Z ::= ANum 2) / empty_state \\
    (t_update (t_update (t_update empty_state X 0) Y 1) Z 2).
Proof.
  apply E_Seq with (t_update empty_state X 0).
  - apply E_Ass. simpl. reflexivity.
  - apply E_Seq with (t_update (t_update empty_state X 0) Y 1).
    + apply E_Ass. simpl. reflexivity.
    + apply E_Ass. simpl. reflexivity.
Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced (pup_to_n)  *)
(** Write an Imp program that sums the numbers from [1] to
   [X] (inclusive: [1 + 2 + ... + X]) in the variable [Y].
   Prove that this program executes as intended for [X] = [2]
   (this is trickier than you might expect). *)

Definition pup_to_n : com :=
  Y ::= ANum 0;;
  WHILE (BLe (ANum 1) (AId X)) DO
    Y ::= APlus (AId X) (AId Y);;
    X ::= AMinus (AId X) (ANum 1)
  END.

Theorem pup_to_2_ceval :
  pup_to_n / (t_update empty_state X 2) \\
    t_update (t_update (t_update (t_update (t_update (t_update empty_state
      X 2) Y 0) Y 2) X 1) Y 3) X 0.
Proof.
  apply E_Seq with (t_update (t_update empty_state X 2) Y 0).
  - apply E_Ass. simpl. reflexivity.
  - apply E_WhileLoop with (t_update (t_update (t_update (t_update empty_state X 2) Y 0) Y 2) X 1).
    + simpl. reflexivity.
    + apply E_Seq with (t_update (t_update (t_update empty_state X 2) Y 0) Y 2).
      -- apply E_Ass. simpl. reflexivity.
      -- apply E_Ass. simpl. reflexivity.
    + apply E_WhileLoop with (t_update (t_update (t_update (t_update (t_update (t_update empty_state X 2) Y 0) Y 2) X 1) Y 3) X 0).
      -- simpl. reflexivity.
      -- apply E_Seq with (t_update (t_update (t_update (t_update (t_update empty_state X 2) Y 0) Y 2) X 1) Y 3).
        ++ apply E_Ass. simpl. reflexivity.
        ++ apply E_Ass. simpl. reflexivity.
      -- apply E_WhileEnd.
         simpl. reflexivity.
Qed. 
(** [] *)

(* ================================================================= *)
(** ** Determinism of Evaluation *)

(** Changing from a computational to a relational definition of
    evaluation is a good move because it frees us from the artificial
    requirement that evaluation should be a total function.  But it
    also raises a question: Is the second definition of evaluation
    really a partial function?  Or is it possible that, beginning from
    the same state [st], we could evaluate some command [c] in
    different ways to reach two different output states [st'] and
    [st'']?

    In fact, this cannot happen: [ceval] _is_ a partial function: *)

Theorem ceval_deterministic: forall c st st1 st2,
     c / st \\ st1  ->
     c / st \\ st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  induction E1;
           intros st2 E2; inversion E2; subst.
  - (* E_Skip *) reflexivity.
  - (* E_Ass *) reflexivity.
  - (* E_Seq *)
    assert (st' = st'0) as EQ1.
    { (* Proof of assertion *) apply IHE1_1; assumption. }
    subst st'0.
    apply IHE1_2. assumption.
  - (* E_IfTrue, b1 evaluates to true *)
      apply IHE1. assumption.
  - (* E_IfTrue,  b1 evaluates to false (contradiction) *)
      rewrite H in H5. inversion H5.
  - (* E_IfFalse, b1 evaluates to true (contradiction) *)
    rewrite H in H5. inversion H5.
  - (* E_IfFalse, b1 evaluates to false *)
      apply IHE1. assumption.
  - (* E_WhileEnd, b1 evaluates to false *)
    reflexivity.
  - (* E_WhileEnd, b1 evaluates to true (contradiction) *)
    rewrite H in H2. inversion H2.
  - (* E_WhileLoop, b1 evaluates to false (contradiction) *)
    rewrite H in H4. inversion H4.
  - (* E_WhileLoop, b1 evaluates to true *)
      assert (st' = st'0) as EQ1.
      { (* Proof of assertion *) apply IHE1_1; assumption. }
      subst st'0.
      apply IHE1_2. assumption.  Qed.

(* ################################################################# *)
(** * Reasoning About Imp Programs *)

(** We'll get deeper into systematic techniques for reasoning about
    Imp programs in the following chapters, but we can do quite a bit
    just working with the bare definitions.  This section explores
    some examples. *)

Theorem plus2_spec : forall st n st',
  st X = n ->
  plus2 / st \\ st' ->
  st' X = n + 2.
Proof.
  intros st n st' HX Heval.

  (** Inverting [Heval] essentially forces Coq to expand one step of
      the [ceval] computation -- in this case revealing that [st']
      must be [st] extended with the new value of [X], since [plus2]
      is an assignment *)

  inversion Heval. subst. clear Heval. simpl.
  apply t_update_eq.  Qed.

(** **** Exercise: 3 stars, recommended (XtimesYinZ_spec)  *)
(** State and prove a specification of [XtimesYinZ]. *)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 3 stars, recommended (loop_never_stops)  *)
Theorem loop_never_stops : forall st st',
  ~(loop / st \\ st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember (WHILE BTrue DO SKIP END) as loopdef
           eqn:Heqloopdef.

  (** Proceed by induction on the assumed derivation showing that
      [loopdef] terminates.  Most of the cases are immediately
      contradictory (and so can be solved in one step with
      [inversion]). *)
  induction contra;
    try (inversion Heqloopdef).
  - rewrite -> H1 in H. inversion H.
  - apply IHcontra2 in Heqloopdef. inversion Heqloopdef.
Qed.
  
(** [] *)

(** **** Exercise: 3 stars (no_whilesR)  *)
(** Consider the following function: *)

Fixpoint no_whiles (c : com) : bool :=
  match c with
  | SKIP =>
      true
  | _ ::= _ =>
      true
  | c1 ;; c2 =>
      andb (no_whiles c1) (no_whiles c2)
  | IFB _ THEN ct ELSE cf FI =>
      andb (no_whiles ct) (no_whiles cf)
  | WHILE _ DO _ END  =>
      false
  end.

(** This predicate yields [true] just on programs that have no while
    loops.  Using [Inductive], write a property [no_whilesR] such that
    [no_whilesR c] is provable exactly when [c] is a program with no
    while loops.  Then prove its equivalence with [no_whiles]. *)

Inductive no_whilesR: com -> Prop :=
 | NW_SKIP : no_whilesR SKIP
 | NW_ASS : forall a b, no_whilesR (a ::= b)
 | NW_IF : forall a b c, no_whilesR b -> no_whilesR c -> no_whilesR (IFB a THEN b ELSE c FI)
 | NW_SEQ : forall a b, no_whilesR a -> no_whilesR b -> no_whilesR (a ;; b).

Theorem no_whiles_eqv:
   forall c, no_whiles c = true <-> no_whilesR c.
Proof.
  split.
  - intros. induction c.
    + apply NW_SKIP.
    + apply NW_ASS.
    + apply NW_SEQ.
      -- inversion H. assert (no_whiles c1 = true). {
          destruct (no_whiles c1).
          - reflexivity.
          - simpl in H1. inversion H1.
         }
         apply IHc1 in H0. apply H0.
      -- inversion H. assert (no_whiles c2 = true). {
            destruct (no_whiles c1).
            - simpl in H1. apply H1.
            - simpl in H1. inversion H1.
         }
         apply IHc2 in H0. apply H0.
    + apply NW_IF.  inversion H.
      -- assert (no_whiles c1 = true). {
          destruct (no_whiles c1).
          - reflexivity.
          - simpl in H1. inversion H1.
        }
        apply IHc1 in H0. apply H0.
      -- inversion H. assert (no_whiles c2 = true). {
          destruct (no_whiles c1).
          - simpl in H1. apply H1.
          - simpl in H1. inversion H1.
        }
        apply IHc2 in H0. apply H0.
    + inversion H.
  - intros. induction c;
      try (simpl; reflexivity).
    + inversion H. apply IHc1 in H2. apply IHc2 in H3.
      simpl. rewrite -> H2. rewrite -> H3. reflexivity.
    + inversion H. simpl.
      assert (no_whiles c1 = true). {
        apply IHc1 in H2. apply H2.
      }
      assert (no_whiles c2 = true). {
        apply IHc2 in H4. apply H4.
      }
      rewrite -> H5. rewrite -> H6.
      reflexivity.
    + inversion H.
Qed. 
(** [] *)

(** **** Exercise: 4 stars (no_whiles_terminating)  *)
(** Imp programs that don't involve while loops always terminate.
    State and prove a theorem [no_whiles_terminating] that says this. *)
(** Use either [no_whiles] or [no_whilesR], as you prefer. *)

Theorem no_whiles_terminating : forall (c : com) (st : state),
  no_whilesR c -> (exists (ed :state), c / st \\ ed).
Proof.
  intros c.
  induction c.
  - intros. exists st. apply E_Skip.
  - intros. exists (t_update st i (aeval st a)). apply E_Ass. reflexivity.
  - intros. specialize (IHc1 st). inversion H.
    apply IHc1 in H2. inversion H2. specialize (IHc2 x).
    apply IHc2 in H3. inversion H3. exists x0.
    apply (E_Seq c1 c2 st x x0).
    + apply H4.
    + apply H5.
  - intros. inversion H.
    specialize (IHc1 st). apply IHc1 in H2.
    specialize (IHc2 st). apply IHc2 in H4.
    inversion H2. inversion H4. remember (beval st b) as B.
    destruct B.
    + exists x. apply E_IfTrue.
      -- rewrite <- HeqB. reflexivity.
      -- apply H5.
    + exists x0. apply E_IfFalse.
      -- rewrite <- HeqB. reflexivity.
      -- apply H6.
  - intros. inversion H.
Qed.
(** [] *)

(* ################################################################# *)
(** * Additional Exercises *)

(** **** Exercise: 3 stars (stack_compiler)  *)
(** HP Calculators, programming languages like Forth and Postscript
    and abstract machines like the Java Virtual Machine all evaluate
    arithmetic expressions using a stack. For instance, the expression

      (2*3)+(3*(4-2))

   would be entered as

      2 3 * 3 4 2 - * +

   and evaluated like this (where we show the program being evaluated
   on the right and the contents of the stack on the left):

      []            |    2 3 * 3 4 2 - * +
      [2]           |    3 * 3 4 2 - * +
      [3, 2]        |    * 3 4 2 - * +
      [6]           |    3 4 2 - * +
      [3, 6]        |    4 2 - * +
      [4, 3, 6]     |    2 - * +
      [2, 4, 3, 6]  |    - * +
      [2, 3, 6]     |    * +
      [6, 6]        |    +
      [12]          |

  The task of this exercise is to write a small compiler that
  translates [aexp]s into stack machine instructions.

  The instruction set for our stack language will consist of the
  following instructions:
     - [SPush n]: Push the number [n] on the stack.
     - [SLoad x]: Load the identifier [x] from the store and push it
                  on the stack
     - [SPlus]:   Pop the two top numbers from the stack, add them, and
                  push the result onto the stack.
     - [SMinus]:  Similar, but subtract.
     - [SMult]:   Similar, but multiply. *)

Inductive sinstr : Type :=
| SPush : nat -> sinstr
| SLoad : id -> sinstr
| SPlus : sinstr
| SMinus : sinstr
| SMult : sinstr.

(** Write a function to evaluate programs in the stack language. It
    should take as input a state, a stack represented as a list of
    numbers (top stack item is the head of the list), and a program
    represented as a list of instructions, and it should return the
    stack after executing the program.  Test your function on the
    examples below.

    Note that the specification leaves unspecified what to do when
    encountering an [SPlus], [SMinus], or [SMult] instruction if the
    stack contains less than two elements.  In a sense, it is
    immaterial what we do, since our compiler will never emit such a
    malformed program. *)

Fixpoint s_execute (st : state) (stack : list nat)
                   (prog : list sinstr)
                 : list nat :=
match prog with
  | [] => stack
  | h :: t => match h with
    | SPush n => s_execute st (n :: stack) t
    | SLoad x => s_execute st ((st x) :: stack) t
    | SPlus => match stack with
                | h1 :: h2 :: t1 => s_execute st ((h1 + h2) :: t1) t
                | _ => []
               end
    | SMinus => match stack with
                  | h1 :: h2 :: t1 => s_execute st ((h2 - h1) :: t1) t
                  | _ => []
                end
    | SMult => match stack with
                  | h1 :: h2 :: t1 => s_execute st ((h2 * h1) :: t1) t
                  | _ => []
                end
  end
end.

Example s_execute1 :
     s_execute empty_state []
       [SPush 5; SPush 3; SPush 1; SMinus]
   = [2; 5].
Proof.
  simpl. reflexivity.
Qed.

Example s_execute2 :
     s_execute (t_update empty_state X 3) [3;4]
       [SPush 4; SLoad X; SMult; SPlus]
   = [15; 4].
Proof.
  simpl. reflexivity.
Qed.

(** Next, write a function that compiles an [aexp] into a stack
    machine program. The effect of running the program should be the
    same as pushing the value of the expression on the stack. *)

Fixpoint s_compile (e : aexp) : list sinstr :=
  match e with
  | ANum n => [SPush n]
  | AId n => [SLoad n]
  | APlus a b => s_compile a ++ s_compile b ++ [SPlus]
  | AMinus a b => s_compile a ++ s_compile b ++ [SMinus]
  | AMult a b => s_compile a ++ s_compile b ++ [SMult]
  end.


(** After you've defined [s_compile], prove the following to test
    that it works. *)

Example s_compile1 :
    s_compile (AMinus (AId X) (AMult (ANum 2) (AId Y)))
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
Proof.
  simpl. reflexivity.
Qed.
(** [] *)

(** **** Exercise: 4 stars, advanced (stack_compiler_correct)  *)
(** Now we'll prove the correctness of the compiler implemented in the
    previous exercise.  Remember that the specification left
    unspecified what to do when encountering an [SPlus], [SMinus], or
    [SMult] instruction if the stack contains less than two
    elements.  (In order to make your correctness proof easier you
    might find it helpful to go back and change your implementation!)

    Prove the following theorem.  You will need to start by stating a
    more general lemma to get a usable induction hypothesis; the main
    theorem will then be a simple corollary of this lemma. *)

Theorem s_execute_stack: forall (st : state) (s : list nat) (l : list sinstr) (e : aexp),
  s_execute st s (s_compile e ++ l) = s_execute st ((aeval st e) :: s) l.
Proof.
  intros.
  generalize dependent l.
  generalize dependent s.
  induction e.
  - intros. simpl. reflexivity.
  - intros. simpl. reflexivity.
  - intros. simpl. rewrite <- app_assoc. rewrite <- app_assoc.
    rewrite (IHe1 s (s_compile e2 ++ [SPlus] ++ l)).
    rewrite (IHe2 (aeval st e1 :: s) ([SPlus] ++ l)).
    simpl. rewrite -> plus_comm. reflexivity.
  - intros. simpl. rewrite <- app_assoc. rewrite <- app_assoc.
    rewrite (IHe1 s (s_compile e2 ++ [SMinus] ++ l)).
    rewrite (IHe2 (aeval st e1 :: s) ([SMinus] ++ l)).
    simpl. reflexivity.
  - intros. simpl. rewrite <- app_assoc. rewrite <- app_assoc.
    rewrite (IHe1 s (s_compile e2 ++ [SMult] ++ l)).
    rewrite (IHe2 (aeval st e1 :: s) ([SMult] ++ l)).
    simpl. reflexivity.
Qed.

Theorem s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].
Proof.
  intros.
  induction e;
    try (simpl; reflexivity);
    try (simpl; rewrite s_execute_stack; rewrite s_execute_stack; simpl).
  - rewrite plus_comm. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.
(** [] *)

(** **** Exercise: 3 stars, optional (short_circuit)  *)
(** Most modern programming languages use a "short-circuit" evaluation
    rule for boolean [and]: to evaluate [BAnd b1 b2], first evaluate
    [b1].  If it evaluates to [false], then the entire [BAnd]
    expression evaluates to [false] immediately, without evaluating
    [b2].  Otherwise, [b2] is evaluated to determine the result of the
    [BAnd] expression.

    Write an alternate version of [beval] that performs short-circuit
    evaluation of [BAnd] in this manner, and prove that it is
    equivalent to [beval]. *)

Fixpoint beval' (st : state) (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => (aeval st a1) =? (aeval st a2)
  | BLe a1 a2   => (aeval st a1) <=? (aeval st a2)
  | BNot b1     => negb (beval' st b1)
  | BAnd b1 b2  => if (beval' st b1) then (beval' st b2) else false
  end.

Theorem beval'_correct : forall (st : state) (b : bexp),
  beval' st b = beval st b.
Proof.
  intros.
  induction b; try (simpl; reflexivity).
Qed.
(** [] *)

(** **** Exercise: 4 stars, advanced (break_imp)  *)
Module BreakImp.

(** Imperative languages like C and Java often include a [break] or
    similar statement for interrupting the execution of loops. In this
    exercise we consider how to add [break] to Imp.  First, we need to
    enrich the language of commands with an additional case. *)

Inductive com : Type :=
  | CSkip : com
  | CBreak : com               (* <-- new *)
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.

Notation "'SKIP'" :=
  CSkip.
Notation "'BREAK'" :=
  CBreak.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).

(** Next, we need to define the behavior of [BREAK].  Informally,
    whenever [BREAK] is executed in a sequence of commands, it stops
    the execution of that sequence and signals that the innermost
    enclosing loop should terminate.  (If there aren't any
    enclosing loops, then the whole program simply terminates.)  The
    final state should be the same as the one in which the [BREAK]
    statement was executed.

    One important point is what to do when there are multiple loops
    enclosing a given [BREAK]. In those cases, [BREAK] should only
    terminate the _innermost_ loop. Thus, after executing the
    following...

       X ::= 0;;
       Y ::= 1;;
       WHILE 0 <> Y DO
         WHILE TRUE DO
           BREAK
         END;;
         X ::= 1;;
         Y ::= Y - 1
       END

    ... the value of [X] should be [1], and not [0].

    One way of expressing this behavior is to add another parameter to
    the evaluation relation that specifies whether evaluation of a
    command executes a [BREAK] statement: *)

Inductive result : Type :=
  | SContinue : result
  | SBreak : result.

Reserved Notation "c1 '/' st '\\' s '/' st'"
                  (at level 40, st, s at level 39).

(** Intuitively, [c / st \\ s / st'] means that, if [c] is started in
    state [st], then it terminates in state [st'] and either signals
    that the innermost surrounding loop (or the whole program) should
    exit immediately ([s = SBreak]) or that execution should continue
    normally ([s = SContinue]).

    The definition of the "[c / st \\ s / st']" relation is very
    similar to the one we gave above for the regular evaluation
    relation ([c / st \\ st']) -- we just need to handle the
    termination signals appropriately:

    - If the command is [SKIP], then the state doesn't change and
      execution of any enclosing loop can continue normally.

    - If the command is [BREAK], the state stays unchanged but we
      signal a [SBreak].

    - If the command is an assignment, then we update the binding for
      that variable in the state accordingly and signal that execution
      can continue normally.

    - If the command is of the form [IFB b THEN c1 ELSE c2 FI], then
      the state is updated as in the original semantics of Imp, except
      that we also propagate the signal from the execution of
      whichever branch was taken.

    - If the command is a sequence [c1 ;; c2], we first execute
      [c1].  If this yields a [SBreak], we skip the execution of [c2]
      and propagate the [SBreak] signal to the surrounding context;
      the resulting state is the same as the one obtained by
      executing [c1] alone. Otherwise, we execute [c2] on the state
      obtained after executing [c1], and propagate the signal
      generated there.

    - Finally, for a loop of the form [WHILE b DO c END], the
      semantics is almost the same as before. The only difference is
      that, when [b] evaluates to true, we execute [c] and check the
      signal that it raises.  If that signal is [SContinue], then the
      execution proceeds as in the original semantics. Otherwise, we
      stop the execution of the loop, and the resulting state is the
      same as the one resulting from the execution of the current
      iteration.  In either case, since [BREAK] only terminates the
      innermost loop, [WHILE] signals [SContinue]. *)

(** Based on the above description, complete the definition of the
    [ceval] relation. *)

Inductive ceval : com -> state -> result -> state -> Prop :=
  | E_Skip : forall st,
      CSkip / st \\ SContinue / st
  | E_Break : forall st,
      CBreak / st \\ SBreak / st
  | E_Ass : forall x a st,
      (x ::= a) / st \\ SContinue / (t_update st x (aeval st a))
  | E_Seq_c : forall st c1 c2 st1 st2 State,
      (c1 / st \\ SContinue / st1) -> (c2 / st1 \\ State / st2) -> ((c1;;c2) / st \\ State / st2)
  | E_Seq_b : forall st c1 c2 st1,
      (c1 / st \\ SBreak / st1) -> ((c1;;c2) / st \\ SBreak / st1)
  | E_If_true : forall st c1 c2 st1 b State,
      (beval st b = true) -> (c1 / st \\ State / st1) -> ((IFB b THEN c1 ELSE c2 FI) / st \\ State / st1)
  | E_If_false : forall st c1 c2 st1 b State,
      (beval st b = false) -> (c2 / st \\ State / st1) -> ((IFB b THEN c1 ELSE c2 FI) / st \\ State / st1) 
  | E_WhileEnd : forall b c st,
      (beval st b = false) -> ((WHILE b DO c END) / st \\ SContinue / st)
  | E_WhileLoop_c : forall st st' st'' b c,
      beval st b = true ->
      (c / st \\ SContinue / st') ->
      ((WHILE b DO c END) / st' \\ SContinue / st'') ->
      ((WHILE b DO c END) / st \\ SContinue / st'')
  | E_WhileLoop_b : forall st st' b c,
      beval st b = true ->
      (c / st \\ SBreak / st') ->
      ((WHILE b DO c END) / st \\ SContinue / st')
    where "c1 '/' st '\\' s '/' st'" := (ceval c1 st s st').

(** Now prove the following properties of your definition of [ceval]: *)

Theorem break_ignore : forall c st st' s,
     (BREAK;; c) / st \\ s / st' ->
     st = st'.
Proof.
  intros.
  inversion H.
  - inversion H2.
  - inversion H5. reflexivity.
Qed.

Theorem while_continue : forall b c st st' s,
  (WHILE b DO c END) / st \\ s / st' ->
  s = SContinue.
Proof.
  intros.
  inversion H.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.
  

Theorem while_stops_on_break : forall b c st st',
  beval st b = true ->
  c / st \\ SBreak / st' ->
  (WHILE b DO c END) / st \\ SContinue / st'.
Proof.
  intros.
  apply E_WhileLoop_b.
  - apply H.
  - apply H0.
Qed.
(** [] *)
(** **** Exercise: 3 stars, advanced, optional (while_break_true)  *)
Theorem while_break_true : forall b c st st',
  (WHILE b DO c END) / st \\ SContinue / st' ->
  beval st' b = true ->
  exists st'', c / st'' \\ SBreak / st'.
Proof.
  intros.
  assert ((WHILE b DO c END) / st \\ SContinue / st'). { apply H. }
  remember (WHILE b DO c END) as loop.
  induction H; try (inversion Heqloop).
  - rewrite H3 in H. rewrite H in H0. inversion H0.
  - assert ((WHILE b0 DO c0 END) = (WHILE b DO c END)). {
      rewrite H5. rewrite H6. reflexivity.
    }
    apply IHceval2.
    + apply H4.
    + apply H0.
    + apply H3.
  - exists st. rewrite <- H5. apply H2.
Qed.
 
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (ceval_deterministic)  *)
Theorem ceval_deterministic: forall (c:com) st st1 st2 s1 s2,
     c / st \\ s1 / st1  ->
     c / st \\ s2 / st2 ->
     st1 = st2 /\ s1 = s2.
Proof.
  intros c.
  induction c.
  - intros. inversion H. inversion H0. split.
    + rewrite <- H7. rewrite H4. reflexivity.
    + reflexivity.
  - intros. inversion H. inversion H0. split.
    + rewrite <- H7. rewrite H4. reflexivity.
    + reflexivity.
  - intros. inversion H. inversion H0. split.
    + reflexivity.
    + reflexivity.
  - intros. inversion H. inversion H0.
    + assert (st3 = st6). {
        specialize (IHc1 st st3 st6 SContinue SContinue).
        apply IHc1 in H3.
        - apply proj1 in H3. apply H3.
        - apply H10.
      }
      rewrite <- H15 in H14.
      specialize (IHc2 st3 st1 st2 s1 s2).
      apply IHc2 in H7.
      -- apply H7.
      -- apply H14.
    + assert (SContinue = SBreak). {
        specialize (IHc1 st st3 st6 SContinue SBreak).
        apply IHc1 in H3.
        - apply proj2 in H3. apply H3.
        - rewrite H12. apply H13.
      }
      inversion H14.
    + inversion H0.
      -- specialize (IHc1 st st1 st5 SBreak SContinue).
         apply IHc1 in H6. apply proj2 in H6. inversion H6. apply H9.
      -- specialize (IHc1 st st1 st2 SBreak SBreak).
         apply IHc1 in H6. apply H6. apply H12.
  - intros. inversion H. inversion H0.
    + specialize (IHc1 st st1 st2 s1 s2). apply IHc1 in H8. apply H8. apply H16.
    + rewrite H7 in H15. inversion H15.
    + inversion H0.
      -- rewrite H15 in H7. inversion H7.
      -- specialize (IHc2 st st1 st2 s1 s2). apply IHc2 in H8. apply H8. apply H16.
  - intros.
    assert ((WHILE b DO c END) / st \\ s2 / st2). { apply H0. } 
    remember (WHILE b DO c END) as loop.
    induction H; try (inversion Heqloop).
    + inversion H0.
      -- split. reflexivity. reflexivity.
      -- rewrite H6 in H. inversion H.
      -- rewrite H6 in H. inversion H.
    + inversion H0.
      -- rewrite H10 in H. rewrite H in H11. inversion H11.
      -- rewrite H6 in H2. rewrite H6 in H9. specialize (IHc st st' st'0 SContinue SContinue).
         assert (st' = st'0). {
           apply IHc.
           apply H2. apply H9.
         }
         rewrite <- H14 in H13. rewrite <- H11 in IHceval2.
         apply IHceval2.
         ++ rewrite H5. rewrite H6. reflexivity.
         ++ apply H13.
         ++ apply H13.
      -- rewrite H6 in H2. rewrite H6 in H12. specialize (IHc st st' st2 SContinue SBreak).
         assert (st' = st2 /\ SContinue = SBreak). {
           apply IHc.
           - apply H2.
           - apply H12.
         }
         apply proj2 in H13. inversion H13.
    + inversion H0.
      -- rewrite H9 in H. rewrite H in H10. inversion H10.
      -- rewrite H5 in H2. rewrite H5 in H8. specialize (IHc st st' st'0 SBreak SContinue).
         assert (st' = st'0 /\ SBreak = SContinue). {
           apply IHc.
           - apply H2.
           - apply H8.
         }
         apply proj2 in H13. inversion H13.
      -- rewrite H5 in H2. rewrite H5 in H11. specialize (IHc st st' st2 SBreak SBreak).
        assert (st' = st2 /\ SBreak = SBreak). {
          apply IHc.
          - apply H2.
          - apply H11.
        }
        apply proj1 in H12. split. rewrite H12. reflexivity. reflexivity.
Qed.

(** [] *)

(** **** Exercise: 4 stars, optional (add_for_loop)  *)
(** Add C-style [for] loops to the language of commands, update the
    [ceval] definition to define the semantics of [for] loops, and add
    cases for [for] loops as needed so that all the proofs in this file
    are accepted by Coq.

    A [for] loop should be parameterized by (a) a statement executed
    initially, (b) a test that is run on each iteration of the loop to
    determine whether the loop should continue, (c) a statement
    executed at the end of each loop iteration, and (d) a statement
    that makes up the body of the loop.  (You don't need to worry
    about making up a concrete Notation for [for] loops, but feel free
    to play with this too if you like.) *)


Definition FORLOOP (init : com) (b : bexp) (c : com) (d : com) :=
  (init);;(WHILE b DO (c;;d) END).

Example forloop_test : 
  (FORLOOP (X ::= (ANum) 0) (BLe (AId X) (ANum 2)) (X ::= APlus (AId X) (ANum 1)) (CSkip)) / empty_state \\ SContinue / (t_update (t_update (t_update (t_update empty_state X 0) X 1) X 2) X 3).
Proof.
  unfold FORLOOP.
  apply E_Seq_c with (t_update empty_state X 0).
  - apply E_Ass.
  - apply E_WhileLoop_c with (t_update (t_update empty_state X 0) X 1).
    + simpl. reflexivity.
    + apply E_Seq_c with (t_update (t_update empty_state X 0) X 1).
      -- apply E_Ass.
      -- apply E_Skip.
    + apply E_WhileLoop_c with (t_update (t_update (t_update empty_state X 0) X 1) X 2).
      -- simpl. reflexivity.
      -- apply E_Seq_c with (t_update (t_update (t_update empty_state X 0) X 1) X 2).
        ++ apply E_Ass.
        ++ apply E_Skip.
      -- apply E_WhileLoop_c with (t_update (t_update (t_update (t_update empty_state X 0) X 1) X 2) X 3).
        ++ simpl. reflexivity.
        ++ apply E_Seq_c with (t_update (t_update (t_update (t_update empty_state X 0) X 1) X 2) X 3).
          --- apply E_Ass.
          --- apply E_Skip.
        ++ apply E_WhileEnd. simpl. reflexivity.
Qed.

End BreakImp.
  
(* $Date: 2016-11-16 06:03:33 -0500 (Wed, 16 Nov 2016) $ *)
