(** * Equiv: Program Equivalence *)

(* IMPORTS *)
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Import ListNotations.
Require Import Maps.
Require Import Imp.
(* /IMPORTS *)

(** *** Some Advice for Working on Exercises:

    - Most of the Coq proofs we ask you to do are similar to proofs
      that we've provided.  Before starting to work on exercises
      problems, take the time to work through our proofs (both
      informally, on paper, and in Coq) and make sure you understand
      them in detail.  This will save you a lot of time.

    - The Coq proofs we're doing now are sufficiently complicated that
      it is more or less impossible to complete them simply by random
      experimentation or "following your nose."  You need to start
      with an idea about why the property is true and how the proof is
      going to go.  The best way to do this is to write out at least a
      sketch of an informal proof on paper -- one that intuitively
      convinces you of the truth of the theorem -- before starting to
      work on the formal one.  Alternately, grab a friend and try to
      convince them that the theorem is true; then try to formalize
      your explanation.

    - Use automation to save work!  The proofs in this chapter's
      exercises can get pretty long if you try to write out all the
      cases explicitly. *)

(* ################################################################# *)
(** * Behavioral Equivalence *)

(** In an earlier chapter, we investigated the correctness of a very
    simple program transformation: the [optimize_0plus] function.  The
    programming language we were considering was the first version of
    the language of arithmetic expressions -- with no variables -- so
    in that setting it was very easy to define what it means for a
    program transformation to be correct: it should always yield a
    program that evaluates to the same number as the original.

    To talk about the correctness of program transformations for the
    full Imp language, including assignment and other commands, we
    need to consider the role of variables and state. *)

(* ================================================================= *)
(** ** Definitions *)

(** For [aexp]s and [bexp]s with variables, the definition we want is
    clear.  We say that two [aexp]s or [bexp]s are _behaviorally
    equivalent_ if they evaluate to the same result in every state. *)

Definition aequiv (a1 a2 : aexp) : Prop :=
  forall (st:state),
    aeval st a1 = aeval st a2.

Definition bequiv (b1 b2 : bexp) : Prop :=
  forall (st:state),
    beval st b1 = beval st b2.

(** Here are some simple examples of equivalences of arithmetic
    and boolean expressions. *)

Theorem aequiv_example:
  aequiv (AMinus (AId X) (AId X)) (ANum 0).
Proof.
  intros st. simpl. lia.
Qed.

Theorem bequiv_example:
  bequiv (BEq (AMinus (AId X) (AId X)) (ANum 0)) BTrue.
Proof.
  intros st. unfold beval.
  rewrite aequiv_example. reflexivity.
Qed.

(** For commands, the situation is a little more subtle.  We can't
    simply say "two commands are behaviorally equivalent if they
    evaluate to the same ending state whenever they are started in the
    same initial state," because some commands, when run in some
    starting states, don't terminate in any final state at all!  What
    we need instead is this: two commands are behaviorally equivalent
    if, for any given starting state, they either (1) both diverge
    or (2) both terminate in the same final state.  A compact way to
    express this is "if the first one terminates in a particular state
    then so does the second, and vice versa." *)

Definition cequiv (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (c1 / st \\ st') <-> (c2 / st \\ st').

(* ================================================================= *)
(** ** Simple Examples *)

(** For examples of command equivalence, let's start by looking at
    some trivial program transformations involving [SKIP]: *)

Theorem skip_left: forall c,
  cequiv
     (SKIP;; c)
     c.
Proof.
  (* WORKED IN CLASS *)
  intros c st st'.
  split; intros H.
  - (* -> *)
    inversion H. subst.
    inversion H2. subst.
    assumption.
  - (* <- *)
    apply E_Seq with st.
    apply E_Skip.
    assumption.
Qed.

(** **** Exercise: 2 stars (skip_right)  *)
(** Prove that adding a [SKIP] after a command results in an
    equivalent program *)

Theorem skip_right: forall c,
  cequiv
    (c ;; SKIP)
    c.
Proof.
  intros.
  split; intros.
  - inversion H. inversion H5. subst. apply H2.
  - apply E_Seq with st'. apply H. apply E_Skip.
Qed. 
(** [] *)

(** Similarly, here is a simple transformation that optimizes [IFB]
    commands: *)

Theorem IFB_true_simple: forall c1 c2,
  cequiv
    (IFB BTrue THEN c1 ELSE c2 FI)
    c1.
Proof.
  intros c1 c2.
  split; intros H.
  - (* -> *)
    inversion H; subst. assumption. inversion H5.
  - (* <- *)
    apply E_IfTrue. reflexivity. assumption.  Qed.

(** Of course, few programmers would be tempted to write a conditional
    whose guard is literally [BTrue].  A more interesting case is when
    the guard is _equivalent_ to true: *)
(** _Theorem_: If [b] is equivalent to [BTrue], then [IFB b THEN c1
    ELSE c2 FI] is equivalent to [c1]. *)
(**
   _Proof_:

     - ([->]) We must show, for all [st] and [st'], that if [IFB b
       THEN c1 ELSE c2 FI / st \\ st'] then [c1 / st \\ st'].

       Proceed by cases on the rules that could possibly have been
       used to show [IFB b THEN c1 ELSE c2 FI / st \\ st'], namely
       [E_IfTrue] and [E_IfFalse].

       - Suppose the final rule rule in the derivation of [IFB b THEN
         c1 ELSE c2 FI / st \\ st'] was [E_IfTrue].  We then have, by
         the premises of [E_IfTrue], that [c1 / st \\ st'].  This is
         exactly what we set out to prove.

       - On the other hand, suppose the final rule in the derivation
         of [IFB b THEN c1 ELSE c2 FI / st \\ st'] was [E_IfFalse].
         We then know that [beval st b = false] and [c2 / st \\ st'].

         Recall that [b] is equivalent to [BTrue], i.e., forall [st],
         [beval st b = beval st BTrue].  In particular, this means
         that [beval st b = true], since [beval st BTrue = true].  But
         this is a contradiction, since [E_IfFalse] requires that
         [beval st b = false].  Thus, the final rule could not have
         been [E_IfFalse].

     - ([<-]) We must show, for all [st] and [st'], that if [c1 / st
       \\ st'] then [IFB b THEN c1 ELSE c2 FI / st \\ st'].

       Since [b] is equivalent to [BTrue], we know that [beval st b] =
       [beval st BTrue] = [true].  Together with the assumption that
       [c1 / st \\ st'], we can apply [E_IfTrue] to derive [IFB b THEN
       c1 ELSE c2 FI / st \\ st'].  []

   Here is the formal version of this proof: *)

Theorem IFB_true: forall b c1 c2,
     bequiv b BTrue  ->
     cequiv
       (IFB b THEN c1 ELSE c2 FI)
       c1.
Proof.
  intros b c1 c2 Hb.
  split; intros H.
  - (* -> *)
    inversion H; subst.
    + (* b evaluates to true *)
      assumption.
    + (* b evaluates to false (contradiction) *)
      unfold bequiv in Hb. simpl in Hb.
      rewrite Hb in H5.
      inversion H5.
  - (* <- *)
    apply E_IfTrue; try assumption.
    unfold bequiv in Hb. simpl in Hb.
    rewrite Hb. reflexivity.  Qed.

(** **** Exercise: 2 stars, recommended (IFB_false)  *)
Theorem IFB_false: forall b c1 c2,
  bequiv b BFalse  ->
  cequiv
    (IFB b THEN c1 ELSE c2 FI)
    c2.
Proof.
  intros.
  split; intros.
  - inversion H0; subst.
    + unfold bequiv in H. simpl in H.
      rewrite H in H6. inversion H6.
    + apply H7.
  - apply E_IfFalse.
    + unfold bequiv in H. apply H.
    + apply H0.
Qed.
(** [] *)

(** **** Exercise: 3 stars (swap_if_branches)  *)
(** Show that we can swap the branches of an IF if we also negate its
    guard. *)

Theorem swap_if_branches: forall b e1 e2,
  cequiv
    (IFB b THEN e1 ELSE e2 FI)
    (IFB BNot b THEN e2 ELSE e1 FI).
Proof.
  intros. split; intros.
  - inversion H; subst.
    + assert (beval st (BNot b) = false). {
        simpl. rewrite H5. reflexivity.
      }
      apply E_IfFalse.
      -- apply H0.
      -- apply H6.
    + assert (beval st (BNot b) = true). {
        simpl. rewrite H5. reflexivity.
      }
      apply E_IfTrue.
      apply H0. apply H6.
  - inversion H; subst.
    + assert (beval st b = false). {
        inversion H5. destruct (beval st b).
        inversion H1. reflexivity.
      }
      apply E_IfFalse.
      apply H0. apply H6.
    + assert (beval st b = true). {
        inversion H5. destruct (beval st b).
        reflexivity. inversion H1.
      }
      apply E_IfTrue.
      apply H0. apply H6.
Qed.
(** [] *)

(** For [WHILE] loops, we can give a similar pair of theorems.  A loop
    whose guard is equivalent to [BFalse] is equivalent to [SKIP],
    while a loop whose guard is equivalent to [BTrue] is equivalent to
    [WHILE BTrue DO SKIP END] (or any other non-terminating program).
    The first of these facts is easy. *)

Theorem WHILE_false : forall b c,
  bequiv b BFalse ->
  cequiv
    (WHILE b DO c END)
    SKIP.
Proof.
  intros b c Hb. split; intros H.
  - (* -> *)
    inversion H; subst.
    + (* E_WhileEnd *)
      apply E_Skip.
    + (* E_WhileLoop *)
      rewrite Hb in H2. inversion H2.
  - (* <- *)
    inversion H; subst.
    apply E_WhileEnd.
    rewrite Hb.
    reflexivity.  Qed.

(** **** Exercise: 2 stars, advanced, optional (WHILE_false_informal)  *)
(** Write an informal proof of [WHILE_false].

(* ............Not entering the loop, so it's equivalent to skip *)
[]
*)

(** To prove the second fact, we need an auxiliary lemma stating that
    [WHILE] loops whose guards are equivalent to [BTrue] never
    terminate. *)

(** _Lemma_: If [b] is equivalent to [BTrue], then it cannot be the
    case that [(WHILE b DO c END) / st \\ st'].

    _Proof_: Suppose that [(WHILE b DO c END) / st \\ st'].  We show,
    by induction on a derivation of [(WHILE b DO c END) / st \\ st'],
    that this assumption leads to a contradiction.

      - Suppose [(WHILE b DO c END) / st \\ st'] is proved using rule
        [E_WhileEnd].  Then by assumption [beval st b = false].  But
        this contradicts the assumption that [b] is equivalent to
        [BTrue].

      - Suppose [(WHILE b DO c END) / st \\ st'] is proved using rule
        [E_WhileLoop].  Then we are given the induction hypothesis
        that [(WHILE b DO c END) / st \\ st'] is contradictory, which
        is exactly what we are trying to prove!

      - Since these are the only rules that could have been used to
        prove [(WHILE b DO c END) / st \\ st'], the other cases of
        the induction are immediately contradictory. [] *)

Lemma WHILE_true_nonterm : forall b c st st',
  bequiv b BTrue ->
  ~( (WHILE b DO c END) / st \\ st' ).
Proof.
  (* WORKED IN CLASS *)
  intros b c st st' Hb.
  intros H.
  remember (WHILE b DO c END) as cw eqn:Heqcw.
  induction H;
    (* Most rules don't apply, and we can rule them out
       by inversion *)
    inversion Heqcw; subst; clear Heqcw.
  (* The two interesting cases are the ones for WHILE loops: *)
  - (* E_WhileEnd *) (* contradictory -- b is always true! *)
    unfold bequiv in Hb.
    (* [rewrite] is able to instantiate the quantifier in [st] *)
    rewrite Hb in H. inversion H.
  - (* E_WhileLoop *) (* immediate from the IH *)
    apply IHceval2. reflexivity.  Qed.

(** **** Exercise: 2 stars, optional (WHILE_true_nonterm_informal)  *)
(** Explain what the lemma [WHILE_true_nonterm] means in English.

(* The loop won't terminate. *)
*)
(** [] *)

(** **** Exercise: 2 stars, recommended (WHILE_true)  *)
(** Prove the following theorem. _Hint_: You'll want to use
    [WHILE_true_nonterm] here. *)

Theorem WHILE_true: forall b c,
  bequiv b BTrue  ->
  cequiv
    (WHILE b DO c END)
    (WHILE BTrue DO SKIP END).
Proof.
  intros.
  assert (forall st st', ~((WHILE b DO c END) / st \\ st')). {
      intros.
      apply (WHILE_true_nonterm b c st st'). apply H.
  }
  assert (forall st st', ~((WHILE BTrue DO SKIP END) / st \\ st')). {
      intros.
      apply (WHILE_true_nonterm BTrue SKIP st st'). 
      unfold bequiv.
      simpl. reflexivity.
  }
  unfold cequiv. intros. split.
  - intros. apply H0 in H2. inversion H2.
  - intros. apply H1 in H2. inversion H2.
Qed.
(** [] *)

(** A more interesting fact about [WHILE] commands is that any finite
    number of copies of the body can be "unrolled" without changing
    meaning.  Unrolling is a common transformation in real compilers. *)

Theorem loop_unrolling: forall b c,
  cequiv
    (WHILE b DO c END)
    (IFB b THEN (c ;; WHILE b DO c END) ELSE SKIP FI).
Proof.
  (* WORKED IN CLASS *)
  intros b c st st'.
  split; intros Hce.
  - (* -> *)
    inversion Hce; subst.
    + (* loop doesn't run *)
      apply E_IfFalse. assumption. apply E_Skip.
    + (* loop runs *)
      apply E_IfTrue. assumption.
      apply E_Seq with (st' := st'0). assumption. assumption.
  - (* <- *)
    inversion Hce; subst.
    + (* loop runs *)
      inversion H5; subst.
      apply E_WhileLoop with (st' := st'0).
      assumption. assumption. assumption.
    + (* loop doesn't run *)
      inversion H5; subst. apply E_WhileEnd. assumption.  Qed.

(** **** Exercise: 2 stars, optional (seq_assoc)  *)
Theorem seq_assoc : forall c1 c2 c3,
  cequiv ((c1;;c2);;c3) (c1;;(c2;;c3)).
Proof.
  intros.
  unfold cequiv.
  intros. split; intros.
  - inversion H. subst. inversion H2. subst.
    apply E_Seq with st'1. apply H3. apply E_Seq with st'0. apply H7. apply H5.
  - inversion H. subst. inversion H5. subst.
    apply E_Seq with st'1. apply E_Seq with st'0. apply H2. apply H3. apply H7.
Qed.
(** [] *)

(** Proving program properties involving assignments is one place
    where the Functional Extensionality axiom often comes in handy. *)

Theorem identity_assignment : forall (X:id),
  cequiv
    (X ::= AId X)
    SKIP.
Proof.
   intros. split; intro H.
     - (* -> *)
       inversion H; subst. simpl.
       replace (t_update st X (st X)) with st.
       + constructor.
       + apply functional_extensionality. intro.
         rewrite t_update_same; reflexivity.
     - (* <- *)
       replace st' with (t_update st' X (aeval st' (AId X))).
       + inversion H. subst. apply E_Ass. reflexivity.
       + apply functional_extensionality. intro.
         rewrite t_update_same. reflexivity.
Qed.

(** **** Exercise: 2 stars, recommended (assign_aequiv)  *)
Theorem assign_aequiv : forall X e,
  aequiv (AId X) e ->
  cequiv SKIP (X ::= e).
Proof.
  intros.
  unfold cequiv. intros; split; intros.
  - inversion H0. subst. assert (t_update st' X (aeval st' e) = st'). {
        apply functional_extensionality.
        intros. unfold t_update.
        remember (beq_id X x) as b. destruct b.
        - unfold aequiv in H. simpl in H. specialize (H st'). rewrite <- H.
          assert (beq_id X x = true). { rewrite Heqb. reflexivity. } 
          apply beq_id_true_iff in H1.
          rewrite H1. reflexivity.
        - reflexivity.
    }
    assert ((X ::= e) / st' \\ (t_update st' X (aeval st' e))). {
        apply E_Ass. reflexivity.
    }
    rewrite H1 in H2. apply H2.
  - inversion H0. subst. assert (st = t_update st X (aeval st e)). {
        apply functional_extensionality.
        intros.
        unfold aequiv in H.
        specialize (H st).
        unfold t_update.
        remember (beq_id X x) as b. destruct b.
        - simpl in H. rewrite <- H. assert (beq_id X x = true). { rewrite Heqb. reflexivity. }
          apply beq_id_true_iff in H1. rewrite H1. reflexivity.
        - reflexivity.
    }
    rewrite <- H1. apply E_Skip.
Qed.
(** [] *)

(** **** Exercise: 2 stars (equiv_classes)  *)

(** Given the following programs, group together those that are
    equivalent in Imp. Your answer should be given as a list of lists,
    where each sub-list represents a group of equivalent programs. For
    example, if you think programs (a) through (h) are all equivalent
    to each other, but not to (i), your answer should look like this:

       [ [prog_a;prog_b;prog_c;prog_d;prog_e;prog_f;prog_g;prog_h] ;
         [prog_i] ]

    Write down your answer below in the definition of
    [equiv_classes]. *)

Definition prog_a : com :=
  WHILE BNot (BLe (AId X) (ANum 0)) DO
    X ::= APlus (AId X) (ANum 1)
  END.

Definition prog_b : com :=
  IFB BEq (AId X) (ANum 0) THEN
    X ::= APlus (AId X) (ANum 1);;
    Y ::= ANum 1
  ELSE
    Y ::= ANum 0
  FI;;
  X ::= AMinus (AId X) (AId Y);;
  Y ::= ANum 0.

Definition prog_c : com :=
  SKIP.

Definition prog_d : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    X ::= APlus (AMult (AId X) (AId Y)) (ANum 1)
  END.

Definition prog_e : com :=
  Y ::= ANum 0.

Definition prog_f : com :=
  Y ::= APlus (AId X) (ANum 1);;
  WHILE BNot (BEq (AId X) (AId Y)) DO
    Y ::= APlus (AId X) (ANum 1)
  END.

Definition prog_g : com :=
  WHILE BTrue DO
    SKIP
  END.

Definition prog_h : com :=
  WHILE BNot (BEq (AId X) (AId X)) DO
    X ::= APlus (AId X) (ANum 1)
  END.

Definition prog_i : com :=
  WHILE BNot (BEq (AId X) (AId Y)) DO
    X ::= APlus (AId Y) (ANum 1)
  END.

Definition equiv_classes : list (list com) :=
  [[prog_a; prog_d; prog_g]; [prog_b; prog_c; prog_e; prog_h; prog_i]; [prog_f]].
(** I haven't checked yet...So it's probabily wrong somewhere*)

(** [] *)

(* ################################################################# *)
(** * Properties of Behavioral Equivalence *)

(** We next consider some fundamental properties of the program
    equivalence relations. *)

(* ================================================================= *)
(** ** Behavioral Equivalence Is an Equivalence *)

(** First, we verify that the equivalences on [aexps], [bexps], and
    [com]s really are _equivalences_ -- i.e., that they are reflexive,
    symmetric, and transitive.  The proofs are all easy. *)

Lemma refl_aequiv : forall (a : aexp), aequiv a a.
Proof.
  intros a st. reflexivity.  Qed.

Lemma sym_aequiv : forall (a1 a2 : aexp),
  aequiv a1 a2 -> aequiv a2 a1.
Proof.
  intros a1 a2 H. intros st. symmetry. apply H.  Qed.

Lemma trans_aequiv : forall (a1 a2 a3 : aexp),
  aequiv a1 a2 -> aequiv a2 a3 -> aequiv a1 a3.
Proof.
  unfold aequiv. intros a1 a2 a3 H12 H23 st.
  rewrite (H12 st). rewrite (H23 st). reflexivity.  Qed.

Lemma refl_bequiv : forall (b : bexp), bequiv b b.
Proof.
  unfold bequiv. intros b st. reflexivity.  Qed.

Lemma sym_bequiv : forall (b1 b2 : bexp),
  bequiv b1 b2 -> bequiv b2 b1.
Proof.
  unfold bequiv. intros b1 b2 H. intros st. symmetry. apply H.  Qed.

Lemma trans_bequiv : forall (b1 b2 b3 : bexp),
  bequiv b1 b2 -> bequiv b2 b3 -> bequiv b1 b3.
Proof.
  unfold bequiv. intros b1 b2 b3 H12 H23 st.
  rewrite (H12 st). rewrite (H23 st). reflexivity.  Qed.

Lemma refl_cequiv : forall (c : com), cequiv c c.
Proof.
  unfold cequiv. intros c st st'. apply iff_refl.  Qed.

Lemma sym_cequiv : forall (c1 c2 : com),
  cequiv c1 c2 -> cequiv c2 c1.
Proof.
  unfold cequiv. intros c1 c2 H st st'.
  assert (c1 / st \\ st' <-> c2 / st \\ st') as H'.
  { (* Proof of assertion *) apply H. }
  apply iff_sym. assumption.
Qed.

Lemma iff_trans : forall (P1 P2 P3 : Prop),
  (P1 <-> P2) -> (P2 <-> P3) -> (P1 <-> P3).
Proof.
  intros P1 P2 P3 H12 H23.
  inversion H12. inversion H23.
  split; intros A.
    apply H1. apply H. apply A.
    apply H0. apply H2. apply A.  Qed.

Lemma trans_cequiv : forall (c1 c2 c3 : com),
  cequiv c1 c2 -> cequiv c2 c3 -> cequiv c1 c3.
Proof.
  unfold cequiv. intros c1 c2 c3 H12 H23 st st'.
  apply iff_trans with (c2 / st \\ st'). apply H12. apply H23.  Qed.

(* ================================================================= *)
(** ** Behavioral Equivalence Is a Congruence *)

(** Less obviously, behavioral equivalence is also a _congruence_.
    That is, the equivalence of two subprograms implies the
    equivalence of the larger programs in which they are embedded:

              aequiv a1 a1'
      -----------------------------
      cequiv (i ::= a1) (i ::= a1')

              cequiv c1 c1'
              cequiv c2 c2'
         ------------------------
         cequiv (c1;;c2) (c1';;c2')

    ...and so on for the other forms of commands. *)

(** (Note that we are using the inference rule notation here not
    as part of a definition, but simply to write down some valid
    implications in a readable format. We prove these implications
    below.) *)

(** We will see a concrete example of why these congruence
    properties are important in the following section (in the proof of
    [fold_constants_com_sound]), but the main idea is that they allow
    us to replace a small part of a large program with an equivalent
    small part and know that the whole large programs are equivalent
    _without_ doing an explicit proof about the non-varying parts --
    i.e., the "proof burden" of a small change to a large program is
    proportional to the size of the change, not the program. *)

Theorem CAss_congruence : forall i a1 a1',
  aequiv a1 a1' ->
  cequiv (CAss i a1) (CAss i a1').
Proof.
  intros i a1 a2 Heqv st st'.
  split; intros Hceval.
  - (* -> *)
    inversion Hceval. subst. apply E_Ass.
    rewrite Heqv. reflexivity.
  - (* <- *)
    inversion Hceval. subst. apply E_Ass.
    rewrite Heqv. reflexivity.  Qed.

(** The congruence property for loops is a little more interesting,
    since it requires induction.

    _Theorem_: Equivalence is a congruence for [WHILE] -- that is, if
    [b1] is equivalent to [b1'] and [c1] is equivalent to [c1'], then
    [WHILE b1 DO c1 END] is equivalent to [WHILE b1' DO c1' END].

    _Proof_: Suppose [b1] is equivalent to [b1'] and [c1] is
    equivalent to [c1'].  We must show, for every [st] and [st'], that
    [WHILE b1 DO c1 END / st \\ st'] iff [WHILE b1' DO c1' END / st
    \\ st'].  We consider the two directions separately.

      - ([->]) We show that [WHILE b1 DO c1 END / st \\ st'] implies
        [WHILE b1' DO c1' END / st \\ st'], by induction on a
        derivation of [WHILE b1 DO c1 END / st \\ st'].  The only
        nontrivial cases are when the final rule in the derivation is
        [E_WhileEnd] or [E_WhileLoop].

          - [E_WhileEnd]: In this case, the form of the rule gives us
            [beval st b1 = false] and [st = st'].  But then, since
            [b1] and [b1'] are equivalent, we have [beval st b1' =
            false], and [E-WhileEnd] applies, giving us [WHILE b1' DO
            c1' END / st \\ st'], as required.

          - [E_WhileLoop]: The form of the rule now gives us [beval st
            b1 = true], with [c1 / st \\ st'0] and [WHILE b1 DO c1
            END / st'0 \\ st'] for some state [st'0], with the
            induction hypothesis [WHILE b1' DO c1' END / st'0 \\
            st'].

            Since [c1] and [c1'] are equivalent, we know that [c1' /
            st \\ st'0].  And since [b1] and [b1'] are equivalent, we
            have [beval st b1' = true].  Now [E-WhileLoop] applies,
            giving us [WHILE b1' DO c1' END / st \\ st'], as
            required.

      - ([<-]) Similar. [] *)

Theorem CWhile_congruence : forall b1 b1' c1 c1',
  bequiv b1 b1' -> cequiv c1 c1' ->
  cequiv (WHILE b1 DO c1 END) (WHILE b1' DO c1' END).
Proof.
  (* WORKED IN CLASS *)
  unfold bequiv,cequiv.
  intros b1 b1' c1 c1' Hb1e Hc1e st st'.
  split; intros Hce.
  - (* -> *)
    remember (WHILE b1 DO c1 END) as cwhile
      eqn:Heqcwhile.
    induction Hce; inversion Heqcwhile; subst.
    + (* E_WhileEnd *)
      apply E_WhileEnd. rewrite <- Hb1e. apply H.
    + (* E_WhileLoop *)
      apply E_WhileLoop with (st' := st').
      * (* show loop runs *) rewrite <- Hb1e. apply H.
      * (* body execution *)
        apply (Hc1e st st').  apply Hce1.
      * (* subsequent loop execution *)
        apply IHHce2. reflexivity.
  - (* <- *)
    remember (WHILE b1' DO c1' END) as c'while
      eqn:Heqc'while.
    induction Hce; inversion Heqc'while; subst.
    + (* E_WhileEnd *)
      apply E_WhileEnd. rewrite -> Hb1e. apply H.
    + (* E_WhileLoop *)
      apply E_WhileLoop with (st' := st').
      * (* show loop runs *) rewrite -> Hb1e. apply H.
      * (* body execution *)
        apply (Hc1e st st').  apply Hce1.
      * (* subsequent loop execution *)
        apply IHHce2. reflexivity.  Qed.

(** **** Exercise: 3 stars, optional (CSeq_congruence)  *)
Theorem CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (c1;;c2) (c1';;c2').
Proof.
  unfold cequiv.
  intros.
  split; intros.
  - inversion H1. subst. apply H in H4. apply H0 in H7.
    apply E_Seq with (st'0). apply H4. apply H7.
  - inversion H1. subst. apply H in H4. apply H0 in H7.
    apply E_Seq with (st'0). apply H4. apply H7.
Qed.
(** [] *)

(** **** Exercise: 3 stars (CIf_congruence)  *)
Theorem CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (IFB b THEN c1 ELSE c2 FI)
         (IFB b' THEN c1' ELSE c2' FI).
Proof.
  intros. unfold cequiv.
  split; intros.
  - unfold bequiv in H. remember (beval st b) as B. destruct B.
    + assert (beval st b' = true). {
       specialize (H st). rewrite <- H. rewrite HeqB. reflexivity.
      }
      apply E_IfTrue. apply H3. 
      inversion H2. subst.
      -- unfold cequiv in H0. apply H0 in H10. apply H10.
      -- subst. rewrite <- HeqB in H9. inversion H9.
   + assert (beval st b' = false). {
      specialize (H st). rewrite <- H. rewrite HeqB. reflexivity.
     }
     apply E_IfFalse. apply H3.
     inversion H2. subst.
     -- rewrite H9 in HeqB. inversion HeqB.
     -- subst. apply H1 in H10. apply H10.
 - unfold bequiv in H. remember (beval st b) as B. destruct B.
    + assert (beval st b' = true). {
        specialize (H st). rewrite <- H. rewrite HeqB. reflexivity.
    }
    apply E_IfTrue. rewrite HeqB. reflexivity. 
    inversion H2. subst.
    -- unfold cequiv in H0. apply H0 in H10. apply H10.
    -- subst. rewrite H3 in H9. inversion H9.
    + assert (beval st b' = false). {
    specialize (H st). rewrite <- H. rewrite HeqB. reflexivity.
    }
    apply E_IfFalse. rewrite HeqB. reflexivity.
    inversion H2. subst.
    -- rewrite H9 in H3. inversion H3.
    -- subst. apply H1 in H10. apply H10.
Qed.
(** [] *)

(** For example, here are two equivalent programs and a proof of their
    equivalence... *)

Example congruence_example:
  cequiv
    (* Program 1: *)
    (X ::= ANum 0;;
     IFB (BEq (AId X) (ANum 0))
     THEN
       Y ::= ANum 0
     ELSE
       Y ::= ANum 42
     FI)
    (* Program 2: *)
    (X ::= ANum 0;;
     IFB (BEq (AId X) (ANum 0))
     THEN
       Y ::= AMinus (AId X) (AId X)   (* <--- changed here *)
     ELSE
       Y ::= ANum 42
     FI).
Proof.
  apply CSeq_congruence.
    apply refl_cequiv.
    apply CIf_congruence.
      apply refl_bequiv.
      apply CAss_congruence. unfold aequiv. simpl.
        symmetry. apply minus_diag.
      apply refl_cequiv.
Qed.

(** **** Exercise: 3 stars, advanced, optional (not_congr)  *)
(** We've shown that the [cequiv] relation is both an equivalence and
    a congruence on commands.  Can you think of a relation on commands
    that is an equivalence but _not_ a congruence? *)

(*  R(c1,c2) = (ceval st c1) X <= (ceval st c2) X
    ??????????????????????????????????????????????????????
    R(c1,c2) /\ R(c3,c4) -> R(c1;;c2, c3;;c4)
*)
(** [] *)

(* ################################################################# *)
(** * Program Transformations *)

(** A _program transformation_ is a function that takes a program as
    input and produces some variant of the program as output.
    Compiler optimizations such as constant folding are a canonical
    example, but there are many others. *)

(** A program transformation is _sound_ if it preserves the
    behavior of the original program. *)

Definition atrans_sound (atrans : aexp -> aexp) : Prop :=
  forall (a : aexp),
    aequiv a (atrans a).

Definition btrans_sound (btrans : bexp -> bexp) : Prop :=
  forall (b : bexp),
    bequiv b (btrans b).

Definition ctrans_sound (ctrans : com -> com) : Prop :=
  forall (c : com),
    cequiv c (ctrans c).

(* ================================================================= *)
(** ** The Constant-Folding Transformation *)

(** An expression is _constant_ when it contains no variable
    references.

    Constant folding is an optimization that finds constant
    expressions and replaces them by their values. *)

Fixpoint fold_constants_aexp (a : aexp) : aexp :=
  match a with
  | ANum n       => ANum n
  | AId i        => AId i
  | APlus a1 a2  =>
    match (fold_constants_aexp a1, fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 + n2)
    | (a1', a2') => APlus a1' a2'
    end
  | AMinus a1 a2 =>
    match (fold_constants_aexp a1, fold_constants_aexp a2) with
    | (ANum n1, ANum n2) => ANum (n1 - n2)
    | (a1', a2') => AMinus a1' a2'
    end
  | AMult a1 a2  =>
    match (fold_constants_aexp a1, fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 * n2)
    | (a1', a2') => AMult a1' a2'
    end
  end.

Example fold_aexp_ex1 :
    fold_constants_aexp
      (AMult (APlus (ANum 1) (ANum 2)) (AId X))
  = AMult (ANum 3) (AId X).
Proof. reflexivity. Qed.

(** Note that this version of constant folding doesn't eliminate
    trivial additions, etc. -- we are focusing attention on a single
    optimization for the sake of simplicity.  It is not hard to
    incorporate other ways of simplifying expressions; the definitions
    and proofs just get longer. *)

Example fold_aexp_ex2 :
    fold_constants_aexp
      (AMinus (AId X) (APlus (AMult (ANum 0) (ANum 6))
                             (AId Y)))
  = AMinus (AId X) (APlus (ANum 0) (AId Y)).
Proof. reflexivity. Qed.

(** Not`* only can we lift [fold_constants_aexp] to [bexp]s (in the
    [BEq] and [BLe] cases); we can also look for constant _boolean_
    expressions and evaluate them in-place. *)

Fixpoint fold_constants_bexp (b : bexp) : bexp :=
  match b with
  | BTrue        => BTrue
  | BFalse       => BFalse
  | BEq a1 a2  =>
      match (fold_constants_aexp a1, fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if beq_nat n1 n2 then BTrue else BFalse
      | (a1', a2') =>
          BEq a1' a2'
      end
  | BLe a1 a2  =>
      match (fold_constants_aexp a1, fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if leb n1 n2 then BTrue else BFalse
      | (a1', a2') =>
          BLe a1' a2'
      end
  | BNot b1  =>
      match (fold_constants_bexp b1) with
      | BTrue => BFalse
      | BFalse => BTrue
      | b1' => BNot b1'
      end
  | BAnd b1 b2  =>
      match (fold_constants_bexp b1, fold_constants_bexp b2) with
      | (BTrue, BTrue) => BTrue
      | (BTrue, BFalse) => BFalse
      | (BFalse, BTrue) => BFalse
      | (BFalse, BFalse) => BFalse
      | (b1', b2') => BAnd b1' b2'
      end
  end.

Example fold_bexp_ex1 :
    fold_constants_bexp (BAnd BTrue (BNot (BAnd BFalse BTrue)))
  = BTrue.
Proof. reflexivity. Qed.

Example fold_bexp_ex2 :
    fold_constants_bexp
      (BAnd (BEq (AId X) (AId Y))
            (BEq (ANum 0)
                 (AMinus (ANum 2) (APlus (ANum 1)
                                         (ANum 1)))))
  = BAnd (BEq (AId X) (AId Y)) BTrue.
Proof. reflexivity. Qed.

(** To fold constants in a command, we apply the appropriate folding
    functions on all embedded expressions. *)

Fixpoint fold_constants_com (c : com) : com :=
  match c with
  | SKIP      =>
      SKIP
  | i ::= a  =>
      CAss i (fold_constants_aexp a)
  | c1 ;; c2  =>
      (fold_constants_com c1) ;; (fold_constants_com c2)
  | IFB b THEN c1 ELSE c2 FI =>
      match fold_constants_bexp b with
      | BTrue => fold_constants_com c1
      | BFalse => fold_constants_com c2
      | b' => IFB b' THEN fold_constants_com c1
                     ELSE fold_constants_com c2 FI
      end
  | WHILE b DO c END =>
      match fold_constants_bexp b with
      | BTrue => WHILE BTrue DO SKIP END
      | BFalse => SKIP
      | b' => WHILE b' DO (fold_constants_com c) END
      end
  end.

Example fold_com_ex1 :
  fold_constants_com
    (* Original program: *)
    (X ::= APlus (ANum 4) (ANum 5);;
     Y ::= AMinus (AId X) (ANum 3);;
     IFB BEq (AMinus (AId X) (AId Y))
             (APlus (ANum 2) (ANum 4)) THEN
       SKIP
     ELSE
       Y ::= ANum 0
     FI;;
     IFB BLe (ANum 0)
             (AMinus (ANum 4) (APlus (ANum 2) (ANum 1)))
     THEN
       Y ::= ANum 0
     ELSE
       SKIP
     FI;;
     WHILE BEq (AId Y) (ANum 0) DO
       X ::= APlus (AId X) (ANum 1)
     END)
  = (* After constant folding: *)
    (X ::= ANum 9;;
     Y ::= AMinus (AId X) (ANum 3);;
     IFB BEq (AMinus (AId X) (AId Y)) (ANum 6) THEN
       SKIP
     ELSE
       (Y ::= ANum 0)
     FI;;
     Y ::= ANum 0;;
     WHILE BEq (AId Y) (ANum 0) DO
       X ::= APlus (AId X) (ANum 1)
     END).
Proof. reflexivity. Qed.

(* ================================================================= *)
(** ** Soundness of Constant Folding *)

(** Now we need to show that what we've done is correct. *)

(** Here's the proof for arithmetic expressions: *)

Theorem fold_constants_aexp_sound :
  atrans_sound fold_constants_aexp.
Proof.
  unfold atrans_sound. intros a. unfold aequiv. intros st.
  induction a; simpl;
    (* ANum and AId follow immediately *)
    try reflexivity;
    (* APlus, AMinus, and AMult follow from the IH
       and the observation that
              aeval st (APlus a1 a2)
            = ANum ((aeval st a1) + (aeval st a2))
            = aeval st (ANum ((aeval st a1) + (aeval st a2)))
       (and similarly for AMinus/minus and AMult/mult) *)
    try (destruct (fold_constants_aexp a1);
         destruct (fold_constants_aexp a2);
         rewrite IHa1; rewrite IHa2; reflexivity). Qed.

(** **** Exercise: 3 stars, optional (fold_bexp_Eq_informal)  *)
(** Here is an informal proof of the [BEq] case of the soundness
    argument for boolean expression constant folding.  Read it
    carefully and compare it to the formal proof that follows.  Then
    fill in the [BLe] case of the formal proof (without looking at the
    [BEq] case, if possible).

   _Theorem_: The constant folding function for booleans,
   [fold_constants_bexp], is sound.

   _Proof_: We must show that [b] is equivalent to [fold_constants_bexp],
   for all boolean expressions [b].  Proceed by induction on [b].  We
   show just the case where [b] has the form [BEq a1 a2].

   In this case, we must show

       beval st (BEq a1 a2)
     = beval st (fold_constants_bexp (BEq a1 a2)).

   There are two cases to consider:

     - First, suppose [fold_constants_aexp a1 = ANum n1] and
       [fold_constants_aexp a2 = ANum n2] for some [n1] and [n2].

       In this case, we have

           fold_constants_bexp (BEq a1 a2)
         = if beq_nat n1 n2 then BTrue else BFalse

       and

           beval st (BEq a1 a2)
         = beq_nat (aeval st a1) (aeval st a2).

       By the soundness of constant folding for arithmetic
       expressions (Lemma [fold_constants_aexp_sound]), we know

           aeval st a1
         = aeval st (fold_constants_aexp a1)
         = aeval st (ANum n1)
         = n1

       and

           aeval st a2
         = aeval st (fold_constants_aexp a2)
         = aeval st (ANum n2)
         = n2,

       so

           beval st (BEq a1 a2)
         = beq_nat (aeval a1) (aeval a2)
         = beq_nat n1 n2.

       Also, it is easy to see (by considering the cases [n1 = n2] and
       [n1 <> n2] separately) that

           beval st (if beq_nat n1 n2 then BTrue else BFalse)
         = if beq_nat n1 n2 then beval st BTrue else beval st BFalse
         = if beq_nat n1 n2 then true else false
         = beq_nat n1 n2.

       So

           beval st (BEq a1 a2)
         = beq_nat n1 n2.
         = beval st (if beq_nat n1 n2 then BTrue else BFalse),

       as required.

     - Otherwise, one of [fold_constants_aexp a1] and
       [fold_constants_aexp a2] is not a constant.  In this case, we
       must show

           beval st (BEq a1 a2)
         = beval st (BEq (fold_constants_aexp a1)
                         (fold_constants_aexp a2)),

       which, by the definition of [beval], is the same as showing

           beq_nat (aeval st a1) (aeval st a2)
         = beq_nat (aeval st (fold_constants_aexp a1))
                   (aeval st (fold_constants_aexp a2)).

       But the soundness of constant folding for arithmetic
       expressions ([fold_constants_aexp_sound]) gives us

         aeval st a1 = aeval st (fold_constants_aexp a1)
         aeval st a2 = aeval st (fold_constants_aexp a2),

       completing the case.  []
*)

Theorem fold_constants_bexp_sound:
  btrans_sound fold_constants_bexp.
Proof.
  unfold btrans_sound. intros b. unfold bequiv. intros st.
  induction b;
    (* BTrue and BFalse are immediate *)
    try reflexivity.
  - (* BEq *)
    rename a into a1. rename a0 into a2. simpl.

(** (Doing induction when there are a lot of constructors makes
    specifying variable names a chore, but Coq doesn't always
    choose nice variable names.  We can rename entries in the
    context with the [rename] tactic: [rename a into a1] will
    change [a] to [a1] in the current goal and context.) *)

    remember (fold_constants_aexp a1) as a1' eqn:Heqa1'.
    remember (fold_constants_aexp a2) as a2' eqn:Heqa2'.
    replace (aeval st a1) with (aeval st a1') by
       (subst a1'; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a2) with (aeval st a2') by
       (subst a2'; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1'; destruct a2'; try reflexivity.

    (* The only interesting case is when both a1 and a2
       become constants after folding *)
      simpl. destruct (beq_nat n n0); reflexivity.
  - (*BLe*)
    unfold fold_constants_bexp.
    remember (fold_constants_aexp a0) as A0.
    remember (fold_constants_aexp a) as A.
    destruct A0;
    try (destruct A;
    try (rewrite HeqA0; rewrite HeqA; simpl; rewrite <- fold_constants_aexp_sound; rewrite <- fold_constants_aexp_sound; reflexivity)).
    -- simpl. assert (aeval st a = n0). {
            assert (aeval st (ANum n0) = aeval st (fold_constants_aexp a)). {
                rewrite HeqA. reflexivity.
            }
            simpl in H. rewrite <- fold_constants_aexp_sound in H. rewrite H.
            reflexivity.
        }
        assert (aeval st a0 = n). {
            assert (aeval st (ANum n) = aeval st (fold_constants_aexp a0)). {
                rewrite HeqA0. reflexivity.
            }
            simpl in H0. rewrite <- fold_constants_aexp_sound in H0. rewrite H0.
            reflexivity.
        }
        rewrite H. rewrite H0. destruct (n0 <=? n). reflexivity. reflexivity.
  - (* BNot *)
    simpl. remember (fold_constants_bexp b) as b' eqn:Heqb'.
    rewrite IHb.
    destruct b'; reflexivity.
  - (* BAnd *)
    simpl.
    remember (fold_constants_bexp b1) as b1' eqn:Heqb1'.
    remember (fold_constants_bexp b2) as b2' eqn:Heqb2'.
    rewrite IHb1. rewrite IHb2.
    destruct b1'; destruct b2'; reflexivity.
Qed.

(** [] *)

(** **** Exercise: 3 stars (fold_constants_com_sound)  *)
(** Complete the [WHILE] case of the following proof. *)

Theorem fold_constants_com_sound :
  ctrans_sound fold_constants_com.
Proof.
  unfold ctrans_sound. intros c.
  induction c; simpl.
  - (* SKIP *) apply refl_cequiv.
  - (* ::= *) apply CAss_congruence.
              apply fold_constants_aexp_sound.
  - (* ;; *) apply CSeq_congruence; assumption.
  - (* IFB *)
    assert (bequiv b (fold_constants_bexp b)). {
      apply fold_constants_bexp_sound. }
    destruct (fold_constants_bexp b) eqn:Heqb;
      try (apply CIf_congruence; assumption).
      (* (If the optimization doesn't eliminate the if, then the
          result is easy to prove from the IH and
          [fold_constants_bexp_sound].) *)
    + (* b always true *)
      apply trans_cequiv with c1; try assumption.
      apply IFB_true; assumption.
    + (* b always false *)
      apply trans_cequiv with c2; try assumption.
      apply IFB_false; assumption.
  - (* WHILE *)
    remember (fold_constants_bexp b) as b' eqn:Heqb'.
    destruct b'; 
    try (rewrite Heqb';  
    apply (CWhile_congruence b (fold_constants_bexp b) c (fold_constants_com c));
    apply fold_constants_bexp_sound; apply IHc).
    + assert (bequiv b BTrue). {
        unfold bequiv. intros.
        rewrite Heqb'.
        rewrite fold_constants_bexp_sound.
        reflexivity.
     }
     apply (WHILE_true b c). apply H.
    + assert (bequiv b BFalse). {
        unfold bequiv. intros.
        rewrite Heqb'.
        rewrite fold_constants_bexp_sound.
        reflexivity.
     }
     apply (WHILE_false b c). apply H.
    + rewrite Heqb'. apply (CWhile_congruence b (fold_constants_bexp b) c (fold_constants_com c)).
    apply fold_constants_bexp_sound. apply IHc.
    + rewrite Heqb'. apply (CWhile_congruence b (fold_constants_bexp b) c (fold_constants_com c)).
    apply fold_constants_bexp_sound. apply IHc.
    + rewrite Heqb'. apply (CWhile_congruence b (fold_constants_bexp b) c (fold_constants_com c)).
    apply fold_constants_bexp_sound. apply IHc.
    + rewrite Heqb'. apply (CWhile_congruence b (fold_constants_bexp b) c (fold_constants_com c)).
    apply fold_constants_bexp_sound. apply IHc.
Qed. 
(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Soundness of (0 + n) Elimination, Redux *)

(** **** Exercise: 4 stars, advanced, optional (optimize_0plus)  *)
(** Recall the definition [optimize_0plus] from the [Imp] chapter:

    Fixpoint optimize_0plus (e:aexp) : aexp :=
      match e with
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

   Note that this function is defined over the old [aexp]s,
   without states.

   Write a new version of this function that accounts for variables,
   plus analogous ones for [bexp]s and commands:

     optimize_0plus_aexp
     optimize_0plus_bexp
     optimize_0plus_com

   Prove that these three functions are sound, as we did for
   [fold_constants_*].  Make sure you use the congruence lemmas in
   the proof of [optimize_0plus_com] -- otherwise it will be _long_!

   Then define an optimizer on commands that first folds
   constants (using [fold_constants_com]) and then eliminates [0 + n]
   terms (using [optimize_0plus_com]).

   - Give a meaningful example of this optimizer's output.

   - Prove that the optimizer is sound.  (This part should be _very_
     easy.)  *)
Fixpoint optimize_0plus_aexp (st : state) (e:aexp) : aexp :=
  match e with
  | ANum n =>
      ANum n
  | APlus (ANum 0) e2 =>
      optimize_0plus_aexp st e2
  | AId X => if (st X =? 0) then (ANum 0) else (AId X)
  | APlus e1 e2 =>
      APlus (optimize_0plus_aexp st e1) (optimize_0plus_aexp st e2)
  | AMinus e1 e2 =>
      AMinus (optimize_0plus_aexp st e1) (optimize_0plus_aexp st e2)
  | AMult e1 e2 =>
      AMult (optimize_0plus_aexp st e1) (optimize_0plus_aexp st e2)
end.

Fixpoint optimize_0plus_bexp (st : state) (b : bexp) : bexp :=
  match b with
    | BTrue       => BTrue
    | BFalse      => BFalse
    | BEq a1 a2   => BEq (optimize_0plus_aexp st a1) (optimize_0plus_aexp st a2)
    | BLe a1 a2   => BLe (optimize_0plus_aexp st a1) (optimize_0plus_aexp st a2)
    | BNot b1     => BNot (optimize_0plus_bexp st b1)
    | BAnd b1 b2  => BAnd (optimize_0plus_bexp st b1) (optimize_0plus_bexp st b2)
end.

Fixpoint optimize_0plus_com (st : state) (c : com) : com :=
  match c with
    | CSkip => CSkip
    | CAss X a => CAss X (optimize_0plus_aexp st a)
    | CSeq c1 c2 => CSeq (optimize_0plus_com st c1) c2
    | CIf b c1 c2 => CIf (optimize_0plus_bexp st b) (optimize_0plus_com st c1) (optimize_0plus_com st c2)
    | CWhile b c => CWhile b c
end.

Theorem optimize_0plus_aexp_sound : forall (a : aexp) (st : state),
  aeval st a = aeval st (optimize_0plus_aexp st a).
Proof.
  induction a; try (intros).
  - simpl. reflexivity.
  - simpl. destruct (st i =? 0) eqn: rua.
    + simpl. rewrite beq_nat_true_iff in rua. apply rua.
    + simpl. reflexivity.
  - (* APlus *) destruct a1.
    + (* a1 = ANum n *) destruct n.
      * (* n = 0 *)  simpl. apply IHa2.
      * (* n <> 0 *) simpl. rewrite IHa2. reflexivity.
    + simpl. simpl in IHa1. rewrite <- IHa1.
      rewrite IHa2. reflexivity.
    + (* a1 = APlus a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite <- IHa1.
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
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.  
Qed.

Theorem optimize_0plus_bexp_sound : forall (b : bexp) (st : state),
 beval st b = beval st (optimize_0plus_bexp st b).
Proof.
  induction b.
  - intros. simpl. reflexivity.
  - intros. simpl. reflexivity.
  - intros. simpl. rewrite <- optimize_0plus_aexp_sound. rewrite <- optimize_0plus_aexp_sound. reflexivity.
  - intros. simpl. rewrite <- optimize_0plus_aexp_sound. rewrite <- optimize_0plus_aexp_sound. reflexivity.
  - intros. simpl. rewrite <- IHb. reflexivity.
  - intros. simpl. rewrite <- IHb1. rewrite <- IHb2. reflexivity.
Qed.


Theorem optimize_0plus_com_sound : forall (c : com) (st ed ed1 : state),
  ceval c st ed -> ceval (optimize_0plus_com st c) st ed1 -> ed = ed1.
Proof.
  induction c.
  - intros. simpl in H0. inversion H. inversion H0. subst. reflexivity.
  - intros. simpl in H0. inversion H. inversion H0. subst. rewrite optimize_0plus_aexp_sound. reflexivity.
  - intros. simpl in H0. inversion H. inversion H0. subst.
    assert (st' = st'0). {
       specialize (IHc1 st st' st'0).
       apply IHc1.
       assumption. assumption.
    } 
    subst.
    apply (ceval_deterministic c2 st'0 ed ed1).
    assumption. assumption.
  - intros. simpl in H0. inversion H.
    + inversion H0. 
      -- subst. specialize (IHc1 st ed ed1). apply IHc1. assumption. assumption.
      -- rewrite <- (optimize_0plus_bexp_sound) in H13. rewrite H13 in H6. inversion H6.
    + inversion H0.
      -- subst. rewrite <- optimize_0plus_bexp_sound in H13. rewrite H13 in H6. inversion H6.
      -- subst. specialize (IHc2 st ed ed1). apply IHc2. assumption. assumption.
  - intros. simpl in H0. apply (ceval_deterministic (WHILE b DO c END) st ed ed1).
    assumption. assumption. 
Qed.

(** I'm too lazy to write about folding constants.... *)
(** It's noticeworthy that CWhile b c => CWhile (optimize_0plus_bexp st b) (optimze_0plus_com st c)
    is wrong in that as the loop goes on, the state will change and will result in the
    error since X + Y is 0 at first and can be changed. So it's wrong to optimize it as 0.
*)

(* ################################################################# *)
(** * Proving That Programs Are _Not_ Equivalent *)

(** Suppose that [c1] is a command of the form [X ::= a1;; Y ::= a2]
    and [c2] is the command [X ::= a1;; Y ::= a2'], where [a2'] is
    formed by substituting [a1] for all occurrences of [X] in [a2].
    For example, [c1] and [c2] might be:

       c1  =  (X ::= 42 + 53;;
               Y ::= Y + X)
       c2  =  (X ::= 42 + 53;;
               Y ::= Y + (42 + 53))

    Clearly, this _particular_ [c1] and [c2] are equivalent.  Is this
    true in general? *)

(** We will see in a moment that it is not, but it is worthwhile
    to pause, now, and see if you can find a counter-example on your
    own. *)

(** More formally, here is the function that substitutes an arithmetic
    expression for each occurrence of a given variable in another
    expression: *)

Fixpoint subst_aexp (i : id) (u : aexp) (a : aexp) : aexp :=
  match a with
  | ANum n       =>
      ANum n
  | AId i'       =>
      if beq_id i i' then u else AId i'
  | APlus a1 a2  =>
      APlus (subst_aexp i u a1) (subst_aexp i u a2)
  | AMinus a1 a2 =>
      AMinus (subst_aexp i u a1) (subst_aexp i u a2)
  | AMult a1 a2  =>
      AMult (subst_aexp i u a1) (subst_aexp i u a2)
  end.

Example subst_aexp_ex :
  subst_aexp X (APlus (ANum 42) (ANum 53))
             (APlus (AId Y) (AId X))
= (APlus (AId Y) (APlus (ANum 42) (ANum 53))).
Proof. reflexivity.  Qed.

(** And here is the property we are interested in, expressing the
    claim that commands [c1] and [c2] as described above are
    always equivalent.  *)

Definition subst_equiv_property := forall i1 i2 a1 a2,
  cequiv (i1 ::= a1;; i2 ::= a2)
         (i1 ::= a1;; i2 ::= subst_aexp i1 a1 a2).

(** Sadly, the property does _not_ always hold -- i.e., it is not the
    case that, for all [i1], [i2], [a1], and [a2],

      cequiv (i1 ::= a1;; i2 ::= a2)
             (i1 ::= a1;; i2 ::= subst_aexp i1 a1 a2).

    To see this, suppose (for a contradiction) that for all [i1], [i2],
    [a1], and [a2], we have

      cequiv (i1 ::= a1;; i2 ::= a2)
             (i1 ::= a1;; i2 ::= subst_aexp i1 a1 a2).

    Consider the following program:

       X ::= APlus (AId X) (ANum 1);; Y ::= AId X

    Note that

       (X ::= APlus (AId X) (ANum 1);; Y ::= AId X)
       / empty_state \\ st1,

    where [st1 = { X |-> 1, Y |-> 1 }].

    By assumption, we know that

      cequiv (X ::= APlus (AId X) (ANum 1);;
              Y ::= AId X)
             (X ::= APlus (AId X) (ANum 1);;
              Y ::= APlus (AId X) (ANum 1))

    so, by the definition of [cequiv], we have

      (X ::= APlus (AId X) (ANum 1);; Y ::= APlus (AId X) (ANum 1))
      / empty_state \\ st1.

    But we can also derive

      (X ::= APlus (AId X) (ANum 1);; Y ::= APlus (AId X) (ANum 1))
      / empty_state \\ st2,

    where [st2 = { X |-> 1, Y |-> 2 }].  But [st1 <> st2], which is a
    contradiction, since [ceval] is deterministic!  [] *)

Theorem subst_inequiv :
  ~ subst_equiv_property.
Proof.
  unfold subst_equiv_property.
  intros Contra.

  (* Here is the counterexample: assuming that [subst_equiv_property]
     holds allows us to prove that these two programs are
     equivalent... *)
  remember (X ::= APlus (AId X) (ANum 1);;
            Y ::= AId X)
      as c1.
  remember (X ::= APlus (AId X) (ANum 1);;
            Y ::= APlus (AId X) (ANum 1))
      as c2.
  assert (cequiv c1 c2) by (subst; apply Contra).

  (* ... allows us to show that the command [c2] can terminate
     in two different final states:
        st1 = {X |-> 1, Y |-> 1}
        st2 = {X |-> 1, Y |-> 2}. *)
  remember (t_update (t_update empty_state X 1) Y 1) as st1.
  remember (t_update (t_update empty_state X 1) Y 2) as st2.
  assert (H1: c1 / empty_state \\ st1);
  assert (H2: c2 / empty_state \\ st2);
  try (subst;
       apply E_Seq with (st' := (t_update empty_state X 1));
       apply E_Ass; reflexivity).
  apply H in H1.

  (* Finally, we use the fact that evaluation is deterministic
     to obtain a contradiction. *)
  assert (Hcontra: st1 = st2)
    by (apply (ceval_deterministic c2 empty_state); assumption).
  assert (Hcontra': st1 Y = st2 Y)
    by (rewrite Hcontra; reflexivity).
  subst. inversion Hcontra'.  Qed.

(** **** Exercise: 4 stars, optional (better_subst_equiv)  *)
(** The equivalence we had in mind above was not complete nonsense --
    it was actually almost right.  To make it correct, we just need to
    exclude the case where the variable [X] occurs in the
    right-hand-side of the first assignment statement. *)

Inductive var_not_used_in_aexp (X:id) : aexp -> Prop :=
  | VNUNum: forall n, var_not_used_in_aexp X (ANum n)
  | VNUId: forall Y, X <> Y -> var_not_used_in_aexp X (AId Y)
  | VNUPlus: forall a1 a2,
      var_not_used_in_aexp X a1 ->
      var_not_used_in_aexp X a2 ->
      var_not_used_in_aexp X (APlus a1 a2)
  | VNUMinus: forall a1 a2,
      var_not_used_in_aexp X a1 ->
      var_not_used_in_aexp X a2 ->
      var_not_used_in_aexp X (AMinus a1 a2)
  | VNUMult: forall a1 a2,
      var_not_used_in_aexp X a1 ->
      var_not_used_in_aexp X a2 ->
      var_not_used_in_aexp X (AMult a1 a2).

Lemma aeval_weakening : forall i st a ni,
  var_not_used_in_aexp i a ->
  aeval (t_update st i ni) a = aeval st a.
Proof.
  induction a.
  - intros. simpl. reflexivity.
  - intros. simpl. inversion H. unfold t_update.
    assert (beq_id i i0 = false). {
      rewrite beq_id_false_iff. apply H1.
    }
    rewrite H2. reflexivity.
  - intros. simpl. inversion H. subst.
    specialize (IHa1 ni). apply IHa1 in H2.
    specialize (IHa2 ni). apply IHa2 in H3. rewrite H2. rewrite H3. reflexivity.
  - intros. simpl. inversion H. subst.
    specialize (IHa1 ni). apply IHa1 in H2.
    specialize (IHa2 ni). apply IHa2 in H3. rewrite H2. rewrite H3. reflexivity.
  - intros. simpl. inversion H. subst.
    specialize (IHa1 ni). apply IHa1 in H2.
    specialize (IHa2 ni). apply IHa2 in H3. rewrite H2. rewrite H3. reflexivity.
Qed.
(** Using [var_not_used_in_aexp], formalize and prove a correct verson
    of [subst_equiv_property]. *)

Theorem subst_equiv_aeval : forall st i a1 a2,
var_not_used_in_aexp i a2 ->
  aeval st a2 = aeval st (subst_aexp i a1 a2).
Proof.
  induction a2.
  - intros. simpl. reflexivity.
  - intros. simpl. inversion H.  rewrite <- beq_id_false_iff in H1. rewrite H1.
    simpl. reflexivity.
  - intros. simpl. inversion H. subst. apply IHa2_1 in H2. apply IHa2_2 in H3.
    rewrite H2. rewrite H3. reflexivity.
  - intros. simpl. inversion H. subst. apply IHa2_1 in H2. apply IHa2_2 in H3.
    rewrite H2. rewrite H3. reflexivity.
  - intros. simpl. inversion H. subst. apply IHa2_1 in H2. apply IHa2_2 in H3.
    rewrite H2. rewrite H3. reflexivity.
Qed.

Theorem subst_equiv_property_correct : forall i1 i2 a1 a2,
  var_not_used_in_aexp i1 a2 ->
  cequiv (i1 ::= a1;; i2 ::= a2)
          (i1 ::= a1;; i2 ::= subst_aexp i1 a1 a2).
Proof.
  intros. split.
  - intros. inversion H0. subst. apply E_Seq with (st'0).
    assumption. assert (st' = t_update st'0 i2 (aeval st'0 (subst_aexp i1 a1 a2))). {
      inversion H6. subst. 
      assert (aeval st'0 a2 = aeval st'0 (subst_aexp i1 a1 a2)). {
        apply subst_equiv_aeval.
        assumption.
      }
      rewrite H1.
      reflexivity. 
    }
    rewrite H1.
    apply E_Ass. reflexivity.
  - intros. inversion H0. subst. apply E_Seq with (st'0).
    assumption. 
    inversion H6. subst.
    assert (aeval st'0 a2 = aeval st'0 (subst_aexp i1 a1 a2)). {
      apply subst_equiv_aeval.
      assumption.
    }
    rewrite <- H1.
    apply E_Ass.
    reflexivity.
Qed. 
    
    
(** [] *)

(** **** Exercise: 3 stars (inequiv_exercise)  *)
(** Prove that an infinite loop is not equivalent to [SKIP] *)

Theorem inequiv_exercise:
  ~ cequiv (WHILE BTrue DO SKIP END) SKIP.
Proof.
  unfold cequiv.
  unfold not.
  intros. 
  assert (SKIP / empty_state \\ empty_state). { apply E_Skip. }
  apply H in H0.
  apply loop_never_stops in H0. inversion H0.
Qed.
(** [] *)

(* ################################################################# *)
(** * Extended Exercise: Nondeterministic Imp *)

(** As we have seen (in theorem [ceval_deterministic] in the [Imp]
    chapter), Imp's evaluation relation is deterministic.  However,
    _non_-determinism is an important part of the definition of many
    real programming languages. For example, in many imperative
    languages (such as C and its relatives), the order in which
    function arguments are evaluated is unspecified.  The program
    fragment

      x = 0;;
      f(++x, x)

    might call [f] with arguments [(1, 0)] or [(1, 1)], depending how
    the compiler chooses to order things.  This can be a little
    confusing for programmers, but it gives the compiler writer useful
    freedom.

    In this exercise, we will extend Imp with a simple
    nondeterministic command and study how this change affects
    program equivalence.  The new command has the syntax [HAVOC X],
    where [X] is an identifier. The effect of executing [HAVOC X] is
    to assign an _arbitrary_ number to the variable [X],
    nondeterministically. For example, after executing the program:

      HAVOC Y;;
      Z ::= Y * 2

    the value of [Y] can be any number, while the value of [Z] is
    twice that of [Y] (so [Z] is always even). Note that we are not
    saying anything about the _probabilities_ of the outcomes -- just
    that there are (infinitely) many different outcomes that can
    possibly happen after executing this nondeterministic code.

    In a sense, a variable on which we do [HAVOC] roughly corresponds
    to an unitialized variable in a low-level language like C.  After
    the [HAVOC], the variable holds a fixed but arbitrary number.  Most
    sources of nondeterminism in language definitions are there
    precisely because programmers don't care which choice is made (and
    so it is good to leave it open to the compiler to choose whichever
    will run faster).

    We call this new language _Himp_ (``Imp extended with [HAVOC]''). *)

Module Himp.

(** To formalize Himp, we first add a clause to the definition of
    commands. *)

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CHavoc : id -> com.                (* <---- new *)

Notation "'SKIP'" :=
  CSkip.
Notation "X '::=' a" :=
  (CAss X a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'HAVOC' l" := (CHavoc l) (at level 60).

(** **** Exercise: 2 stars (himp_ceval)  *)
(** Now, we must extend the operational semantics. We have provided
   a template for the [ceval] relation below, specifying the big-step
   semantics. What rule(s) must be added to the definition of [ceval]
   to formalize the behavior of the [HAVOC] command? *)

Reserved Notation "c1 '/' st '\\' st'"
                  (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st : state, SKIP / st \\ st
  | E_Ass : forall (st : state) (a1 : aexp) (n : nat) (X : id),
      aeval st a1 = n ->
      (X ::= a1) / st \\ t_update st X n
  | E_Seq : forall (c1 c2 : com) (st st' st'' : state),
      c1 / st \\ st' ->
      c2 / st' \\ st'' ->
      (c1 ;; c2) / st \\ st''
  | E_IfTrue : forall (st st' : state) (b1 : bexp) (c1 c2 : com),
      beval st b1 = true ->
      c1 / st \\ st' ->
      (IFB b1 THEN c1 ELSE c2 FI) / st \\ st'
  | E_IfFalse : forall (st st' : state) (b1 : bexp) (c1 c2 : com),
      beval st b1 = false ->
      c2 / st \\ st' ->
      (IFB b1 THEN c1 ELSE c2 FI) / st \\ st'
  | E_WhileEnd : forall (b1 : bexp) (st : state) (c1 : com),
      beval st b1 = false ->
      (WHILE b1 DO c1 END) / st \\ st
  | E_WhileLoop : forall (st st' st'' : state) (b1 : bexp) (c1 : com),
      beval st b1 = true ->
      c1 / st \\ st' ->
      (WHILE b1 DO c1 END) / st' \\ st'' ->
      (WHILE b1 DO c1 END) / st \\ st''
  | E_Havoc : forall (st : state) (X : id) (n : nat),
       (HAVOC X) / st \\ (t_update st X n) 

  where "c1 '/' st '\\' st'" := (ceval c1 st st').

(** As a sanity check, the following claims should be provable for
    your definition: *)

Example havoc_example1 : (HAVOC X) / empty_state \\ t_update empty_state X 0.
Proof.
 apply E_Havoc.
Qed.

Example havoc_example2 :
  (SKIP;; HAVOC Z) / empty_state \\ t_update empty_state Z 42.
Proof.
 apply E_Seq with empty_state.
 apply E_Skip.
 apply E_Havoc.
Qed.
(** [] *)

(** Finally, we repeat the definition of command equivalence from above: *)

Definition cequiv (c1 c2 : com) : Prop := forall st st' : state,
  c1 / st \\ st' <-> c2 / st \\ st'.

(** Let's apply this definition to prove some nondeterministic
    programs equivalent / inequivalent. *)

(** **** Exercise: 3 stars (havoc_swap)  *)
(** Are the following two programs equivalent? *)

Definition pXY :=
  HAVOC X;; HAVOC Y.

Definition pYX :=
  HAVOC Y;; HAVOC X.

(** If you think they are equivalent, prove it. If you think they are
    not, prove that. *)


Theorem pXY_cequiv_pYX :
  cequiv pXY pYX \/ ~cequiv pXY pYX.
Proof.
  left.
  unfold cequiv.
  intros. split.
  - intros. inversion H. subst.
    inversion H2. inversion H5. subst.
    assert (t_update (t_update st X n) Y n0 = t_update (t_update st Y n0) X n). {
      apply functional_extensionality.
      intros. unfold t_update.
      destruct (beq_id Y x) eqn: Yx.
      - destruct (beq_id X x) eqn: Xx.
        + rewrite beq_id_true_iff in Yx. rewrite beq_id_true_iff in Xx. rewrite <- Xx in Yx.
          inversion Yx.
        + reflexivity.
      - reflexivity. 
    }
    rewrite -> H0.
    apply E_Seq with (t_update st Y n0).
    apply E_Havoc. apply E_Havoc.
  - intros. inversion H. subst.
    inversion H2. inversion H5. subst.
    assert (t_update (t_update st X n0) Y n = t_update (t_update st Y n) X n0). {
      apply functional_extensionality.
      intros. unfold t_update.
      destruct (beq_id Y x) eqn: Yx.
      - destruct (beq_id X x) eqn: Xx.
        + rewrite beq_id_true_iff in Yx. rewrite beq_id_true_iff in Xx. rewrite <- Xx in Yx.
          inversion Yx.
        + reflexivity.
      - reflexivity. 
    }
    rewrite <- H0.
    apply E_Seq with (t_update st X n0).
    apply E_Havoc. apply E_Havoc.
Qed.
(** [] *)

(** **** Exercise: 4 stars, optional (havoc_copy)  *)
(** Are the following two programs equivalent? *)

Definition ptwice :=
  HAVOC X;; HAVOC Y.

Definition pcopy :=
  HAVOC X;; Y ::= AId X.

(** If you think they are equivalent, then prove it. If you think they
    are not, then prove that.  (Hint: You may find the [assert] tactic
    useful.) *)

Theorem ptwice_cequiv_pcopy :
  cequiv ptwice pcopy \/ ~cequiv ptwice pcopy.
Proof. 
  right.
  unfold not. unfold cequiv. unfold ptwice. unfold pcopy.
  intros.
  specialize (H empty_state (t_update (t_update empty_state X 0) Y 1)).
  assert ((HAVOC X;;HAVOC Y) / empty_state \\ (t_update (t_update empty_state X 0) Y 1 )). {
    apply E_Seq with (t_update empty_state X 0).
    apply E_Havoc. apply E_Havoc.
  }
  apply H in H0.
  inversion H0. subst.
  inversion H3. subst.
  inversion H6. subst.
  simpl in H7. assert (t_update empty_state X n X = n). {
    unfold t_update.
    assert (beq_id X X = true). {
      apply beq_id_true_iff. reflexivity.
    }
    rewrite H1.
     reflexivity.
  }
  rewrite H1 in H7.
  assert (n = 1). {
    assert (t_update (t_update empty_state X n) Y n Y = t_update (t_update empty_state X 0) Y 1 Y). {
      rewrite H7. reflexivity.
    }
    unfold t_update in H2.
    assert (beq_id Y Y = true). { apply beq_id_true_iff. reflexivity. }
    rewrite H4 in H2.
    apply H2.
  }
  assert (n = 0). {
    assert (t_update (t_update empty_state X n) Y n X = t_update (t_update empty_state X 0) Y 1 X). {
      rewrite H7. reflexivity.
    }
    unfold t_update in H4.
    assert (beq_id Y X = false). { apply beq_id_false_iff. unfold not. intros. inversion H5. }
    rewrite H5 in H4.
    assert (beq_id X X = true). { apply beq_id_true_iff. reflexivity. }
    rewrite H8 in H4.
    apply H4. 
  }
  rewrite H4 in H2.
  inversion H2.
Qed.


(** [] *)

(** The definition of program equivalence we are using here has some
    subtle consequences on programs that may loop forever.  What
    [cequiv] says is that the set of possible _terminating_ outcomes
    of two equivalent programs is the same. However, in a language
    with nondeterminism, like Himp, some programs always terminate,
    some programs always diverge, and some programs can
    nondeterministically terminate in some runs and diverge in
    others. The final part of the following exercise illustrates this
    phenomenon.
*)

(** **** Exercise: 4 stars, advanced (p1_p2_term)  *)
(** Consider the following commands: *)

Definition p1 : com :=
  WHILE (BNot (BEq (AId X) (ANum 0))) DO
    HAVOC Y;;
    X ::= APlus (AId X) (ANum 1)
  END.

Definition p2 : com :=
  WHILE (BNot (BEq (AId X) (ANum 0))) DO
    SKIP
  END.

(** Intuitively, [p1] and [p2] have the same termination behavior:
    either they loop forever, or they terminate in the same state they
    started in.  We can capture the termination behavior of [p1] and
    [p2] individually with these lemmas: *)

Lemma p1_may_diverge : forall st st', st X <> 0 ->
  ~ p1 / st \\ st'.
Proof. 
  unfold not. 
  intros.
  unfold p1 in H0.
  remember ((WHILE BNot (BEq (AId X) (ANum 0))
  DO HAVOC Y;; X ::= APlus (AId X) (ANum 1) END)) as loop eqn: loopeq.
  induction H0; try (inversion loopeq).
  - rewrite H2 in H0. simpl in H0. assert (st X =0). {
      assert (negb (negb (st X =? 0)) = negb (false)). { rewrite H0. reflexivity. }
      rewrite negb_involutive in H1. simpl in H1.
      apply beq_nat_true_iff in H1.
      apply H1.
    }
    apply H in H1. inversion H1.
  - subst. inversion H0_. subst. inversion H3. subst. inversion H6. subst.
    apply IHceval2.
    + simpl. intros.
      unfold t_update in H1.
      assert (beq_id X X = true). {
        apply beq_id_true_iff. reflexivity.
      }
      assert (beq_id Y X = false). {
        apply beq_id_false_iff. unfold not. intros. inversion H4.
      }
      rewrite H2 in H1. rewrite H4 in H1.
      destruct (st X).
      inversion H1. inversion H1.
    + reflexivity.
Qed.

Lemma p2_may_diverge : forall st st', st X <> 0 ->
  ~ p2 / st \\ st'.
Proof.
  unfold not. 
  intros.
  unfold p2 in H0.
  remember ((WHILE BNot (BEq (AId X) (ANum 0)) DO SKIP END)) as loop eqn: loopeq.
  induction H0; try (inversion loopeq).
  - rewrite H2 in H0. simpl in H0. assert (st X = 0). {
      assert (negb (negb (st X =? 0)) = negb false). { rewrite H0. reflexivity. }
      rewrite negb_involutive in H1. simpl in H1. apply beq_nat_true_iff in H1. apply H1.
    }
    apply H in H1. inversion H1.
  - subst. apply IHceval2.
    + inversion H0_. subst. apply H.
    + reflexivity.
Qed.
(** [] *)

(** **** Exercise: 4 stars, advanced (p1_p2_equiv)  *)
(** Use these two lemmas to prove that [p1] and [p2] are actually
    equivalent. *)

Lemma id_exluded_middle : forall (st : state) (x : id),
  st x = 0 \/ st x <> 0.
Proof.
  intros.
  destruct (st x).
  - left. reflexivity.
  - right. unfold not. intros. inversion H.
Qed.

Theorem p1_p2_equiv : cequiv p1 p2.
Proof.  
 unfold cequiv. intros.
 assert (st X = 0 \/ st X <> 0). { apply id_exluded_middle. }
 destruct H.
 - unfold p1. unfold p2. split.
  + intros. remember (WHILE BNot (BEq (AId X) (ANum 0))
      DO HAVOC Y;; X ::= APlus (AId X) (ANum 1) END) as loop eqn: loopeq.
      induction H0; try (intros; inversion loopeq).
      -- rewrite <- H2. apply E_WhileEnd. apply H0.
      -- rewrite H2 in H0. simpl in H0. assert (st X <> 0). {
          assert (negb (negb (st X =? 0)) = negb (true)). {
            rewrite H0. reflexivity.
          }
          rewrite negb_involutive in H1. simpl in H1.
          apply beq_nat_false_iff in H1. apply H1.
         }
         unfold not in H1. apply H1 in H. inversion H.
  + intros. remember (WHILE BNot (BEq (AId X) (ANum 0)) DO SKIP END) as loop eqn: loopeq.
    induction H0; try (intros; inversion loopeq).
    -- rewrite <- H2. apply E_WhileEnd. apply H0.
    -- rewrite H2 in H0. simpl in H0. assert (st X <> 0). {
        assert (negb (negb (st X =? 0)) = negb (true)). {
          rewrite H0. reflexivity.
        }
        rewrite negb_involutive in H1. simpl in H1.
        apply beq_nat_false_iff in H1. apply H1.
      }
      unfold not in H1. apply H1 in H. inversion H.
- split.
  + intros. assert (~(p1 / st \\ st')). {
      apply p1_may_diverge. assumption.
    }
    unfold not in H1.
    apply H1 in H0. inversion H0.
  + intros. assert (~(p2 / st \\ st')). {
    apply p2_may_diverge. assumption.
  }
    unfold not in H1.
    apply H1 in H0.
    inversion H0.
Qed.


(** **** Exercise: 4 stars, advanced (p3_p4_inequiv)  *)
(** Prove that the following programs are _not_ equivalent.  (Hint:
    What should the value of [Z] be when [p3] terminates?  What about
    [p4]?) *)

Definition p3 : com :=
  Z ::= ANum 1;;
  WHILE (BNot (BEq (AId X) (ANum 0))) DO
    HAVOC X;;
    HAVOC Z
  END.

Definition p4 : com :=
  X ::= (ANum 0);;
  Z ::= (ANum 1).


Theorem p3_p4_inequiv : ~ cequiv p3 p4.
Proof. 
  unfold not. unfold cequiv.
  intros.
  assert (p3 /
  (t_update empty_state X 1) \\
  (t_update (t_update (t_update (t_update empty_state X 1) Z 1) X 0) Z 2)
  ). {
    unfold p3.
    apply E_Seq with (t_update (t_update empty_state X 1) Z 1).
    apply E_Ass. simpl. reflexivity.
    apply E_WhileLoop with (t_update
    (t_update (t_update (t_update empty_state X 1) Z 1) X
       0) Z 2).
       - simpl. reflexivity.
       - apply E_Seq with (t_update (t_update (t_update empty_state X 1) Z 1) X 0).
         apply E_Havoc. apply E_Havoc.
       - apply E_WhileEnd. simpl. reflexivity.
  }
  apply H in H0.
  inversion H0. subst.
  inversion H3. subst. simpl in H3. simpl in H6.
  inversion H6. subst. simpl in H7.
  assert ((t_update (t_update (t_update empty_state X 1) X 0) Z 1) Z = 
  (t_update (t_update (t_update (t_update empty_state X 1) Z 1) X 0) Z 2) Z). {
    rewrite H7. reflexivity.
  }
  unfold t_update in H1.
  assert (beq_id Z Z = true). {
    assert (Z = Z). { reflexivity. }
    apply beq_id_true_iff in H2. apply H2.
  }
  assert (beq_id X Z = false). {
    apply beq_id_false_iff. unfold not. intros. inversion H4.
  }
  rewrite H2 in H1.
  inversion H1.
Qed.
(** [] *)

(** **** Exercise: 5 stars, advanced, optional (p5_p6_equiv)  *)
(** Prove that the following commands are equivalent.  (Hint: As
    mentioned above, our definition of [cequiv] for Himp only takes
    into account the sets of possible terminating configurations: two
    programs are equivalent if and only if when given a same starting
    state [st], the set of possible terminating states is the same for
    both programs. If [p5] terminates, what should the final state be?
    Conversely, is it always possible to make [p5] terminate?) *)

Definition p5 : com :=
  WHILE (BNot (BEq (AId X) (ANum 1))) DO
    HAVOC X
  END.

Definition p6 : com :=
  X ::= ANum 1.


Theorem p5_p6_equiv : cequiv p5 p6.
Proof.
  unfold cequiv. unfold p5. unfold p6. split.
  - intros. 
    remember (WHILE (BNot (BEq (AId X) (ANum 1))) DO HAVOC X END) as loop eqn: loopeq.
    induction H; try (inversion loopeq).
    + assert (st = t_update st X 1). {
        apply functional_extensionality. intros.
        destruct (beq_id X x) eqn: eq.
        - rewrite beq_id_true_iff in eq. subst. simpl in H. unfold t_update.
          assert (beq_id X X = true). { apply beq_id_true_iff. reflexivity. }
          rewrite H0.
          assert (negb (negb (st X =? 1)) = negb false). {
            rewrite H. reflexivity.
          }
          rewrite negb_involutive in H1. simpl in H1.
          rewrite beq_nat_true_iff in H1. apply H1.
        - unfold t_update. rewrite eq. reflexivity. 
      }
      assert ((X ::= ANum 1) / st \\ t_update st X 1). { apply E_Ass. simpl. reflexivity. }
      rewrite <- H0 in H3.
      apply H3.
    + subst. simpl in H. assert ((WHILE BNot (BEq (AId X) (ANum 1)) DO HAVOC X END) =
      (WHILE BNot (BEq (AId X) (ANum 1)) DO HAVOC X END)). { reflexivity. }
      apply IHceval2 in H2.
      inversion H0. subst. inversion H2. subst.
      simpl.
      assert (t_update st X 1 = t_update (t_update st X n) X 1). {
        apply functional_extensionality. intros.
        destruct (beq_id X x) eqn: eq.
        - unfold t_update. rewrite eq. reflexivity.
        - unfold t_update. rewrite eq. reflexivity. 
      }
      rewrite <- H3.
      apply E_Ass.
      reflexivity.
    - intros. inversion H. subst. simpl in H. simpl.
      (** I think the theorem is false here...*)
      Admitted.
      
      



End Himp.

(* ################################################################# *)
(** * Additional Exercises *)

(** **** Exercise: 4 stars, optional (for_while_equiv)  *)
(** This exercise extends the optional [add_for_loop] exercise from
    the [Imp] chapter, where you were asked to extend the language
    of commands with C-style [for] loops.  Prove that the command:

      for (c1 ; b ; c2) {
          c3
      }

    is equivalent to:

       c1 ;
       WHILE b DO
         c3 ;
         c2
       END
*)
(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 3 stars, optional (swap_noninterfering_assignments)  *)
(** (Hint: You'll need [functional_extensionality] for this one.) *)

Theorem swap_noninterfering_assignments: forall l1 l2 a1 a2,
  l1 <> l2 ->
  var_not_used_in_aexp l1 a2 ->
  var_not_used_in_aexp l2 a1 ->
  cequiv
    (l1 ::= a1;; l2 ::= a2)
    (l2 ::= a2;; l1 ::= a1).
Proof.
  intros.
  unfold cequiv. split.
  - intros. inversion H2. subst. inversion H5. inversion H8. subst.
    rewrite aeval_weakening. 
    + assert (t_update (t_update st l1 (aeval st a1)) l2 (aeval st a2) =
    t_update (t_update st l2 (aeval st a2)) l1 (aeval st a1)). {
      apply functional_extensionality.
      intros. unfold t_update.
      destruct (beq_id l2 x) eqn: eq.
      - apply beq_id_true_iff in eq. rewrite <- eq. 
        assert (beq_id l1 l2 = false). {
          apply beq_id_false_iff. apply H.
        }
        rewrite H3. reflexivity.
      - reflexivity.
    }
    rewrite H3.
    apply E_Seq with (t_update st l2 (aeval st a2)).
    apply E_Ass. reflexivity. apply E_Ass. rewrite aeval_weakening. reflexivity. assumption.
    + assumption.
  - intros. inversion H2. subst. inversion H5. inversion H8. subst.
    rewrite aeval_weakening. 
    + assert (t_update (t_update st l1 (aeval st a1)) l2 (aeval st a2) =
    t_update (t_update st l2 (aeval st a2)) l1 (aeval st a1)). {
      apply functional_extensionality.
      intros. unfold t_update.
      destruct (beq_id l2 x) eqn: eq.
      - apply beq_id_true_iff in eq. rewrite <- eq. 
        assert (beq_id l1 l2 = false). {
          apply beq_id_false_iff. apply H.
        }
        rewrite H3. reflexivity.
      - reflexivity.
    }
    rewrite <- H3.
    apply E_Seq with (t_update st l1 (aeval st a1)).
    apply E_Ass. reflexivity. apply E_Ass. rewrite aeval_weakening. reflexivity. assumption.
    + assumption.
Qed.

(** [] *)

(** **** Exercise: 4 stars, advanced, optional (capprox)  *)
(** In this exercise we define an asymmetric variant of program
    equivalence we call _program approximation_. We say that a
    program [c1] _approximates_ a program [c2] when, for each of
    the initial states for which [c1] terminates, [c2] also terminates
    and produces the same final state. Formally, program approximation
    is defined as follows: *)

Definition capprox (c1 c2 : com) : Prop := forall (st st' : state),
  c1 / st \\ st' -> c2 / st \\ st'.


(** For example, the program [c1 = WHILE X <> 1 DO X ::= X - 1 END]
    approximates [c2 = X ::= 1], but [c2] does not approximate [c1]
    since [c1] does not terminate when [X = 0] but [c2] does.  If two
    programs approximate each other in both directions, then they are
    equivalent. *)

(** Find two programs [c3] and [c4] such that neither approximates
    the other. *)

Definition c3 : com := X ::= ANum 1.
Definition c4 : com := X ::= ANum 2.

Theorem c3_c4_different : ~ capprox c3 c4 /\ ~ capprox c4 c3.
Proof. 
  split.
  - unfold not. unfold capprox. intros. specialize (H empty_state (t_update empty_state X 1)).
    unfold c3 in H. unfold c4 in H.
    assert ((X ::= ANum 1) / empty_state \\ t_update empty_state X 1). {
      apply E_Ass. reflexivity.
    }
    apply H in H0.
    inversion H0. subst.
    simpl in H5.
    assert (t_update empty_state X 2 X = t_update empty_state X 1 X). {
      rewrite H5. reflexivity.
    }
    unfold t_update in H1.
    assert (beq_id X X = true). { apply beq_id_true_iff. reflexivity. }
    rewrite H2 in H1. inversion H1.
  - unfold not. unfold capprox. intros. specialize (H empty_state (t_update empty_state X 2)).
  unfold c3 in H. unfold c4 in H.
  assert ((X ::= ANum 2) / empty_state \\ t_update empty_state X 2). {
    apply E_Ass. reflexivity.
  }
  apply H in H0.
  inversion H0. subst.
  simpl in H5.
  assert (t_update empty_state X 2 X = t_update empty_state X 1 X). {
    rewrite H5. reflexivity.
  }
  unfold t_update in H1.
  assert (beq_id X X = true). { apply beq_id_true_iff. reflexivity. }
  rewrite H2 in H1. inversion H1.
Qed.

(** Find a program [cmin] that approximates every other program. *)

Definition cmin : com := WHILE BTrue DO SKIP END.

Theorem cmin_minimal : forall c, capprox cmin c.
Proof.
  intros. unfold capprox. unfold cmin.
  intros.
  apply loop_never_stops in H. inversion H.
Qed.

(** Finally, find a non-trivial property which is preserved by
    program approximation (when going from left to right). *)

Definition zprop (c : com) : Prop :=
  forall st, (exists ed, c / st \\ ed).
(** The property seems trivial...which means that the program always terminates *)

Theorem zprop_preserving : forall c c',
  zprop c -> capprox c c' -> zprop c'.
Proof.
  intros.
  unfold zprop in H.
  unfold capprox in H0.
  unfold zprop.
  intros.
  specialize (H st).
  inversion H. 
  apply H0 in H1.
  exists x. apply H1.
Qed.
(** [] *)

(** $Date: 2016-10-25 11:37:34 -0400 (Tue, 25 Oct 2016) $ *)
