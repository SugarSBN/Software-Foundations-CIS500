(** * IndProp: Inductively Defined Propositions *)

Require Export Logic.

(* ################################################################# *)
(** * Inductively Defined Propositions *)

(** In the [Logic] chapter, we looked at several ways of writing
    propositions, including conjunction, disjunction, and quantifiers.
    In this chapter, we bring a new tool  into the mix: _inductive
    definitions_.

    Recall that we have seen two ways of stating that a number [n] is
    even: We can say (1) [evenb n = true], or (2) [exists k, n =
    double k].  Yet another possibility is to say that [n] is even if
    we can establish its evenness from the following rules:

       - Rule [ev_0]:  The number [0] is even.
       - Rule [ev_SS]: If [n] is even, then [S (S n)] is even. *)

(** To illustrate how this definition of evenness works, let's
    imagine using it to show that [4] is even. By rule [ev_SS], it
    suffices to show that [2] is even. This, in turn, is again
    guaranteed by rule [ev_SS], as long as we can show that [0] is
    even. But this last fact follows directly from the [ev_0] rule. *)

(** We will see many definitions like this one during the rest
    of the course.  For purposes of informal discussions, it is
    helpful to have a lightweight notation that makes them easy to
    read and write.  _Inference rules_ are one such notation: *)
(**

                              ------------                        (ev_0)
                                 ev 0

                                  ev n
                             --------------                      (ev_SS)
                              ev (S (S n))
*)

(** Each of the textual rules above is reformatted here as an
    inference rule; the intended reading is that, if the _premises_
    above the line all hold, then the _conclusion_ below the line
    follows.  For example, the rule [ev_SS] says that, if [n]
    satisfies [ev], then [S (S n)] also does.  If a rule has no
    premises above the line, then its conclusion holds
    unconditionally.

    We can represent a proof using these rules by combining rule
    applications into a _proof tree_. Here's how we might transcribe
    the above proof that [4] is even: *)
(**

                             ------  (ev_0)
                              ev 0
                             ------ (ev_SS)
                              ev 2
                             ------ (ev_SS)
                              ev 4
*)

(** Why call this a "tree" (rather than a "stack", for example)?
    Because, in general, inference rules can have multiple premises.
    We will see examples of this below. *)

(** Putting all of this together, we can translate the definition of
    evenness into a formal Coq definition using an [Inductive]
    declaration, where each constructor corresponds to an inference
    rule: *)

Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS : forall n : nat, ev n -> ev (S (S n)).

(** This definition is different in one crucial respect from
    previous uses of [Inductive]: its result is not a [Type], but
    rather a function from [nat] to [Prop] -- that is, a property of
    numbers.  Note that we've already seen other inductive definitions
    that result in functions, such as [list], whose type is [Type ->
    Type].  What is new here is that, because the [nat] argument of
    [ev] appears _unnamed_, to the _right_ of the colon, it is allowed
    to take different values in the types of different constructors:
    [0] in the type of [ev_0] and [S (S n)] in the type of [ev_SS].

    In contrast, the definition of [list] names the [X] parameter
    _globally_, to the _left_ of the colon, forcing the result of
    [nil] and [cons] to be the same ([list X]).  Had we tried to bring
    [nat] to the left in defining [ev], we would have seen an error: *)

Fail Inductive wrong_ev (n : nat) : Prop :=
| wrong_ev_0 : wrong_ev 0
| wrong_ev_SS : forall n, wrong_ev n -> wrong_ev (S (S n)).
(* ===> Error: A parameter of an inductive type n is not
        allowed to be used as a bound variable in the type
        of its constructor. *)

(** ("Parameter" here is Coq jargon for an argument on the left of the
    colon in an [Inductive] definition; "index" is used to refer to
    arguments on the right of the colon.) *)

(** We can think of the definition of [ev] as defining a Coq property
    [ev : nat -> Prop], together with theorems [ev_0 : ev 0] and
    [ev_SS : forall n, ev n -> ev (S (S n))].  Such "constructor
    theorems" have the same status as proven theorems.  In particular,
    we can use Coq's [apply] tactic with the rule names to prove [ev]
    for particular numbers... *)

Theorem ev_4 : ev 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

(** ... or we can use function application syntax: *)

Theorem ev_4' : ev 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

(** We can also prove theorems that have hypotheses involving [ev]. *)

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n. simpl. intros Hn.
  apply ev_SS. apply ev_SS. apply Hn.
Qed.

(** More generally, we can show that any number multiplied by 2 is even: *)

(** **** Exercise: 1 star (ev_double)  *)
Theorem ev_double : forall n,
  ev (double n).
Proof.
    intros n.
    induction n.
    - simpl. apply ev_0.
    - simpl. apply ev_SS. apply IHn.
Qed.
(** [] *)

(* ################################################################# *)
(** * Using Evidence in Proofs *)

(** Besides _constructing_ evidence that numbers are even, we can also
    _reason about_ such evidence.

    Introducing [ev] with an [Inductive] declaration tells Coq not
    only that the constructors [ev_0] and [ev_SS] are valid ways to
    build evidence that some number is even, but also that these two
    constructors are the _only_ ways to build evidence that numbers
    are even (in the sense of [ev]). *)

(** In other words, if someone gives us evidence [E] for the assertion
    [ev n], then we know that [E] must have one of two shapes:

      - [E] is [ev_0] (and [n] is [O]), or
      - [E] is [ev_SS n' E'] (and [n] is [S (S n')], where [E'] is
        evidence for [ev n']). *)

(** This suggests that it should be possible to analyze a hypothesis
    of the form [ev n] much as we do inductively defined data
    structures; in particular, it should be possible to argue by
    _induction_ and _case analysis_ on such evidence.  Let's look at a
    few examples to see what this means in practice. *)

(* ================================================================= *)
(** ** Inversion on Evidence *)

(** Suppose we are proving some fact involving a number [n], and we
    are given [ev n] as a hypothesis.  We already know how to perform
    case analysis on [n] using the [inversion] tactic, generating
    separate subgoals for the case where [n = O] and the case where [n
    = S n'] for some [n'].  But for some proofs we may instead want to
    analyze the evidence that [ev n] _directly_.

    By the definition of [ev], there are two cases to consider:

    - If the evidence is of the form [ev_0], we know that [n = 0].

    - Otherwise, the evidence must have the form [ev_SS n' E'], where
      [n = S (S n')] and [E'] is evidence for [ev n']. *)

(** We can perform this kind of reasoning in Coq, again using
    the [inversion] tactic.  Besides allowing us to reason about
    equalities involving constructors, [inversion] provides a
    case-analysis principle for inductively defined propositions.
    When used in this way, its syntax is similar to [destruct]: We
    pass it a list of identifiers separated by [|] characters to name
    the arguments to each of the possible constructors.  *)

Theorem ev_minus2 : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  inversion E as [| n' E'].
  - (* E = ev_0 *) simpl. apply ev_0.
  - (* E = ev_SS n' E' *) simpl. apply E'.  Qed.

(** In words, here is how the inversion reasoning works in this proof:

    - If the evidence is of the form [ev_0], we know that [n = 0].
      Therefore, it suffices to show that [ev (pred (pred 0))] holds.
      By the definition of [pred], this is equivalent to showing that
      [ev 0] holds, which directly follows from [ev_0].

    - Otherwise, the evidence must have the form [ev_SS n' E'], where
      [n = S (S n')] and [E'] is evidence for [ev n'].  We must then
      show that [ev (pred (pred (S (S n'))))] holds, which, after
      simplification, follows directly from [E']. *)

(** This particular proof also works if we replace [inversion] by
    [destruct]: *)

Theorem ev_minus2' : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  destruct E as [| n' E'].
  - (* E = ev_0 *) simpl. apply ev_0.
  - (* E = ev_SS n' E' *) simpl. apply E'.  Qed.

(** The difference between the two forms is that [inversion] is more
    convenient when used on a hypothesis that consists of an inductive
    property applied to a complex expression (as opposed to a single
    variable).  Here's is a concrete example.  Suppose that we wanted
    to prove the following variation of [ev_minus2]: *)

Theorem evSS_ev : forall n,
  ev (S (S n)) -> ev n.

(** Intuitively, we know that evidence for the hypothesis cannot
    consist just of the [ev_0] constructor, since [O] and [S] are
    different constructors of the type [nat]; hence, [ev_SS] is the
    only case that applies.  Unfortunately, [destruct] is not smart
    enough to realize this, and it still generates two subgoals.  Even
    worse, in doing so, it keeps the final goal unchanged, failing to
    provide any useful information for completing the proof.  *)

Proof.
  intros n E.
  destruct E as [| n' E'].
  - (* E = ev_0. *)
    (* We must prove that [n] is even from no assumptions! *)
Abort.

(** What happened, exactly?  Calling [destruct] has the effect of
    replacing all occurrences of the property argument by the values
    that correspond to each constructor.  This is enough in the case
    of [ev_minus2'] because that argument, [n], is mentioned directly
    in the final goal. However, it doesn't help in the case of
    [evSS_ev] since the term that gets replaced ([S (S n)]) is not
    mentioned anywhere. *)

(** The [inversion] tactic, on the other hand, can detect (1) that the
    first case does not apply, and (2) that the [n'] that appears on
    the [ev_SS] case must be the same as [n].  This allows us to
    complete the proof: *)

Theorem evSS_ev : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.
  inversion E as [| n' E'].
  (* We are in the [E = ev_SS n' E'] case now. *)
  apply E'.
Qed.

(** By using [inversion], we can also apply the principle of explosion
    to "obviously contradictory" hypotheses involving inductive
    properties. For example: *)

Theorem one_not_even : ~ ev 1.
Proof.
  intros H. inversion H. Qed.

(** **** Exercise: 1 star (inversion_practice)  *)
(** Prove the following results using [inversion]. *)

Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n E.
  inversion E as [| n' E'].
  inversion E' as [| n'' E''].
  apply E''.
Qed.

Theorem even5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  intros E.
  inversion E as [| n' E'].
  inversion E' as [| n'' E''].
  inversion E''.
Qed.
(** [] *)

(** The way we've used [inversion] here may seem a bit
    mysterious at first.  Until now, we've only used [inversion] on
    equality propositions, to utilize injectivity of constructors or
    to discriminate between different constructors.  But we see here
    that [inversion] can also be applied to analyzing evidence for
    inductively defined propositions.

    Here's how [inversion] works in general.  Suppose the name [I]
    refers to an assumption [P] in the current context, where [P] has
    been defined by an [Inductive] declaration.  Then, for each of the
    constructors of [P], [inversion I] generates a subgoal in which
    [I] has been replaced by the exact, specific conditions under
    which this constructor could have been used to prove [P].  Some of
    these subgoals will be self-contradictory; [inversion] throws
    these away.  The ones that are left represent the cases that must
    be proved to establish the original goal.  For those, [inversion]
    adds all equations into the proof context that must hold of the
    arguments given to [P] (e.g., [S (S n') = n] in the proof of
    [evSS_ev]). *)

(** The [ev_double] exercise above shows that our new notion of
    evenness is implied by the two earlier ones (since, by
    [even_bool_prop] in chapter [Logic], we already know that
    those are equivalent to each other). To show that all three
    coincide, we just need the following lemma: *)

Lemma ev_even_firsttry : forall n,
  ev n -> exists k, n = double k.
Proof.
(* WORKED IN CLASS *)

(** We could try to proceed by case analysis or induction on [n].  But
    since [ev] is mentioned in a premise, this strategy would probably
    lead to a dead end, as in the previous section.  Thus, it seems
    better to first try inversion on the evidence for [ev].  Indeed,
    the first case can be solved trivially. *)

  intros n E. inversion E as [| n' E'].
  - (* E = ev_0 *)
    exists 0. reflexivity.
  - (* E = ev_SS n' E' *) simpl.

(** Unfortunately, the second case is harder.  We need to show [exists
    k, S (S n') = double k], but the only available assumption is
    [E'], which states that [ev n'] holds.  Since this isn't directly
    useful, it seems that we are stuck and that performing case
    analysis on [E] was a waste of time.

    If we look more closely at our second goal, however, we can see
    that something interesting happened: By performing case analysis
    on [E], we were able to reduce the original result to an similar
    one that involves a _different_ piece of evidence for [ev]: [E'].
    More formally, we can finish our proof by showing that

        exists k', n' = double k',

    which is the same as the original statement, but with [n'] instead
    of [n].  Indeed, it is not difficult to convince Coq that this
    intermediate result suffices. *)

    assert (I : (exists k', n' = double k') ->
                (exists k, S (S n') = double k)).
    { intros [k' Hk']. rewrite Hk'. exists (S k'). reflexivity. }
    apply I. (* reduce the original goal to the new one *)

Admitted.

(* ================================================================= *)
(** ** Induction on Evidence *)

(** If this looks familiar, it is no coincidence: We've encountered
    similar problems in the [Induction] chapter, when trying to use
    case analysis to prove results that required induction.  And once
    again the solution is... induction!

    The behavior of [induction] on evidence is the same as its
    behavior on data: It causes Coq to generate one subgoal for each
    constructor that could have used to build that evidence, while
    providing an induction hypotheses for each recursive occurrence of
    the property in question. *)

(** Let's try our current lemma again: *)

Lemma ev_even : forall n,
  ev n -> exists k, n = double k.
Proof.
  intros n E.
  induction E as [|n' E' IH].
  - (* E = ev_0 *)
    exists 0. reflexivity.
  - (* E = ev_SS n' E'
       with IH : exists k', n' = double k' *)
    destruct IH as [k' Hk'].
    rewrite Hk'. exists (S k'). reflexivity.
Qed.

(** Here, we can see that Coq produced an [IH] that corresponds to
    [E'], the single recursive occurrence of [ev] in its own
    definition.  Since [E'] mentions [n'], the induction hypothesis
    talks about [n'], as opposed to [n] or some other number. *)

(** The equivalence between the second and third definitions of
    evenness now follows. *)

Theorem ev_even_iff : forall n,
  ev n <-> exists k, n = double k.
Proof.
  intros n. split.
  - (* -> *) apply ev_even.
  - (* <- *) intros [k Hk]. rewrite Hk. apply ev_double.
Qed.

(** As we will see in later chapters, induction on evidence is a
    recurring technique across many areas, and in particular when
    formalizing the semantics of programming languages, where many
    properties of interest are defined inductively. *)

(** The following exercises provide simple examples of this
    technique, to help you familiarize yourself with it. *)

(** **** Exercise: 2 stars (ev_sum)  *)
Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros n m E1 E2.
  induction E1.
  - simpl. apply E2.
  - simpl. apply ev_SS. apply IHE1.
Qed.
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (ev_alternate)  *)
(** In general, there may be multiple ways of defining a
    property inductively.  For example, here's a (slightly contrived)
    alternative definition for [ev]: *)

Inductive ev' : nat -> Prop :=
| ev'_0 : ev' 0
| ev'_2 : ev' 2
| ev'_sum : forall n m, ev' n -> ev' m -> ev' (n + m).

(** Prove that this definition is logically equivalent to the old
    one.  (You may want to look at the previous theorem when you get
    to the induction step.) *)

Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
    intros n.
    split.
    - intros E. 
      induction E.
      -- apply ev_0.
      -- apply ev_SS. apply ev_0.
      -- apply (ev_sum n m).
        + apply IHE1.
        + apply IHE2.
    - intros E.
      induction E.
      -- apply ev'_0.
      -- assert (H: S (S n) = 2 + n). {
          reflexivity.
         }
         rewrite -> H.
         apply ev'_sum.
         + apply ev'_2.
         + apply IHE.
Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced, recommended (ev_ev__ev)  *)
(** Finding the appropriate thing to do induction on is a
    bit tricky here: *)

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  intros n m.
  intros E E1.
  induction E1.
  - simpl in E. apply E.
  - simpl in E. inversion E. apply IHE1 in H0. apply H0.
Qed.
(** [] *)

(** **** Exercise: 3 stars, optional (ev_plus_plus)  *)
(** This exercise just requires applying existing lemmas.  No
    induction or even case analysis is needed, though some of the
    rewriting may be tedious. *)

Lemma double_eq_plus: forall (p : nat), 
    p + p = double p.
Proof.
    induction p.
    - simpl. reflexivity.
    - simpl. rewrite -> plus_comm. simpl. rewrite -> IHp. reflexivity.
Qed.

Lemma ev_add_double: forall (n m : nat),
    ev n -> ev (n + double m).
Proof.
    intros n m E.
    induction m.
    - simpl. rewrite -> plus_0_r. apply E.
    - simpl. rewrite <- plus_n_Sm. rewrite <- plus_n_Sm.
      apply ev_SS. apply IHm.
Qed.

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros n m p E1 E2.
  assert (E3: ev (n + p + m + p)). {
      assert (n + p + m = n + (p + m)). {
          rewrite -> plus_assoc.
          reflexivity.
      }
      rewrite -> H.
      assert (p + m = m + p). { rewrite -> plus_comm. reflexivity. }
      rewrite -> H0.
      assert (n + (m + p) + p = n + m + p + p). { rewrite plus_assoc. reflexivity. }
      rewrite -> H1.
      assert (n + m + p + p = n + m + (p + p)). { rewrite plus_assoc. reflexivity. }
      rewrite -> H2.
      rewrite -> double_eq_plus.
      apply (ev_add_double (n+m) p E1).
  }
  assert (n + p + m + p = n + p + (m + p)). {
      rewrite -> plus_assoc.
      reflexivity.
  }
  rewrite -> H in E3.
  apply (ev_ev__ev (n+p) (m+p) E3 E2).
Qed.
(** The proof above is so ugly! *)

(* ################################################################# *)
(** * Inductive Relations *)

(** A proposition parameterized by a number (such as [ev])
    can be thought of as a _property_ -- i.e., it defines
    a subset of [nat], namely those numbers for which the proposition
    is provable.  In the same way, a two-argument proposition can be
    thought of as a _relation_ -- i.e., it defines a set of pairs for
    which the proposition is provable. *)

Module Playground.

(** One useful example is the "less than or equal to" relation on
    numbers. *)

(** The following definition should be fairly intuitive.  It
    says that there are two ways to give evidence that one number is
    less than or equal to another: either observe that they are the
    same number, or give evidence that the first is less than or equal
    to the predecessor of the second. *)

Inductive le : nat -> nat -> Prop :=
  | le_n : forall n, le n n
  | le_S : forall n m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).

(** Proofs of facts about [<=] using the constructors [le_n] and
    [le_S] follow the same patterns as proofs about properties, like
    [ev] above. We can [apply] the constructors to prove [<=]
    goals (e.g., to show that [3<=3] or [3<=6]), and we can use
    tactics like [inversion] to extract information from [<=]
    hypotheses in the context (e.g., to prove that [(2 <= 1) ->
    2+2=5].) *)

(** Here are some sanity checks on the definition.  (Notice that,
    although these are the same kind of simple "unit tests" as we gave
    for the testing functions we wrote in the first few lectures, we
    must construct their proofs explicitly -- [simpl] and
    [reflexivity] don't do the job, because the proofs aren't just a
    matter of simplifying computations.) *)

Theorem test_le1 :
  3 <= 3.
Proof.
  (* WORKED IN CLASS *)
  apply le_n.  Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  (* WORKED IN CLASS *)
  apply le_S. apply le_S. apply le_S. apply le_n.  Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof.
  (* WORKED IN CLASS *)
  intros H. inversion H. inversion H2.  Qed.

(** The "strictly less than" relation [n < m] can now be defined
    in terms of [le]. *)

End Playground.

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

(** Here are a few more simple relations on numbers: *)

Inductive square_of : nat -> nat -> Prop :=
  sq : forall n:nat, square_of n (n * n).

Inductive next_nat : nat -> nat -> Prop :=
  | nn : forall n:nat, next_nat n (S n).

Inductive next_even : nat -> nat -> Prop :=
  | ne_1 : forall n, ev (S n) -> next_even n (S n)
  | ne_2 : forall n, ev (S (S n)) -> next_even n (S (S n)).

(** **** Exercise: 2 stars, optional (total_relation)  *)
(** Define an inductive binary relation [total_relation] that holds
    between every pair of natural numbers. *)

Inductive total_relation : nat -> nat -> Prop :=
  | tot_le1 : forall n m, le n m -> total_relation n m
  | tot_le2 : forall n m, le m n -> total_relation n m.

Lemma le_pass : forall n m : nat,
  le (S n) m -> le n m.
Proof.
  intros n m E.
  induction E.
  - apply le_S. apply le_n.
  - apply le_S. apply IHE.
Qed.

Lemma le_prev_S : forall n m : nat,
  le n m <-> le (S n) (S m).
Proof.
  intros n m.
  split.
  - intros E.
    induction E.
    -- apply le_n.
    -- apply le_S. apply IHE.
  - intros E.
    inversion E.
    -- apply le_n.
    -- apply le_pass in H0. apply H0. 
Qed.

Theorem test_tot : forall n m : nat,
    total_relation n m.
Proof.
    intros n m.
    induction m.
    - apply tot_le2. induction n.
        -- apply le_n.
        -- apply le_S. apply IHn.
    - destruct IHm.
        -- apply tot_le1. apply le_S. apply H.
        -- inversion H. 
            + apply tot_le1. apply le_S. apply le_n.
            + apply tot_le2. 
              assert (m <= m0 <-> S m <= S m0). {
                  apply le_prev_S.
              }
              apply proj1 in H2.
              apply H2 in H0. apply H0.
Qed.

(** [] *)

(** **** Exercise: 2 stars, optional (empty_relation)  *)
(** Define an inductive binary relation [empty_relation] (on numbers)
    that never holds. *)

Lemma always_false : forall n : nat, S n = n -> False.
Proof.
    induction n.
    - intros H. inversion H.
    - intros H. inversion H.
     apply IHn in H1. apply H1.
Qed.

Lemma always_false1 : forall n : nat, S n <= n -> False.
Proof.
    induction n.
    - intros H. inversion H.
    - intros H. inversion H.
     + apply always_false in H1. apply H1.
     + assert (H2: S n <= n <-> S (S n) <= S n). {
         apply le_prev_S.
     }
     apply proj2 in H2.
     apply H2 in H.
     apply IHn in H.
     apply H.
Qed.

Inductive empty_relation : nat -> nat -> Prop :=
    | emp_le : forall n, le (S n) n -> empty_relation n n.
Theorem test_empty_relation : forall (n m : nat),
    empty_relation n m -> False.
Proof.
    intros n m E.
    inversion E.
    inversion H.
    - apply (always_false m) in H2.
      apply H2.
    - apply always_false1 in H.
      apply H.
Qed.
    
(** [] *)

(** **** Exercise: 3 stars, optional (le_exercises)  *)
(** Here are a number of facts about the [<=] and [<] relations that
    we are going to need later in the course.  The proofs make good
    practice exercises. *)

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros m n o E1 E2.
  induction E1.
  - apply E2.
  - apply le_pass in E2. apply IHE1 in E2. apply E2.
Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros n.
  induction n.
  - apply le_n.
  - apply le_S. apply IHn.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros n m.
  assert (n <= m <-> S n <= S m). { apply le_prev_S. }
  apply proj1 in H.
  apply H.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros n m.
  assert (n <= m <-> S n <= S m). { apply le_prev_S. }
  apply proj2 in H.
  apply H.
Qed.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  induction b.
  - assert (H: a + 0 = a). {
      apply plus_0_r.
    }
    rewrite -> H.
    apply le_n.
  - rewrite <- plus_n_Sm.
    apply le_S.
    apply IHb.
Qed.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
 unfold lt.
 intros n1 n2 m E.
 split.
 - induction E.
    + assert (H1: n1 <= n1 + n2). {
        apply le_plus_l.
    }
    apply n_le_m__Sn_le_Sm in H1. apply H1.
    + apply le_pass in IHE. apply n_le_m__Sn_le_Sm in IHE. apply IHE.
 - induction E.
    + assert (H1: n2 <= n1 + n2). {
        rewrite -> plus_comm.
        apply le_plus_l.
    }
    apply n_le_m__Sn_le_Sm in H1. apply H1.
    + apply le_pass in IHE. apply n_le_m__Sn_le_Sm in IHE. apply IHE.
Qed.

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  unfold lt.
  intros n m E.
  inversion E.
  - apply le_S. apply le_n.
  - apply le_pass in E. rewrite -> H0.
    apply n_le_m__Sn_le_Sm in E. apply E.
Qed.

Theorem leb_complete : forall n m,
  leb n m = true -> n <= m.
Proof.
  intros n m.
  generalize dependent n.
  induction m.
  - destruct n.
    + intros E. apply le_n.
    + intros E. simpl in E. inversion E.
  - intros n E. 
    destruct n.
    + assert (H: S m = 0 + S m). {
        rewrite plus_comm.
        rewrite plus_0_r.
        reflexivity.
     }
     rewrite -> H.
     apply le_plus_l.
    + simpl in E. 
      apply n_le_m__Sn_le_Sm.
      apply IHm in E.
      apply E.
Qed.

(** Hint: The next one may be easiest to prove by induction on [m]. *)

Theorem leb_correct : forall n m,
  n <= m ->
  leb n m = true.
Proof.
  intros n m E.
  generalize dependent n.
  induction m.
  - intros n E. inversion E.
    + simpl. reflexivity.
  - intros n E. inversion E.
    + simpl. assert (H1: m <= m). { apply le_n. }
      apply IHm in H1. apply H1.
    + destruct n.
     -- simpl. reflexivity.
     -- simpl. apply Sn_le_Sm__n_le_m in E. apply IHm in E. apply E.
Qed.

(** Hint: This theorem can easily be proved without using [induction]. *)

Theorem leb_true_trans : forall n m o,
  leb n m = true -> leb m o = true -> leb n o = true.
Proof.
    intros n m o E E1.
    apply leb_complete in E.
    apply leb_complete in E1.
    assert (H: n <= o). {
        apply (le_trans n m o).
        - apply E.
        - apply E1.
    }
    apply leb_correct.
    apply H.
Qed.
  

(** **** Exercise: 2 stars, optional (leb_iff)  *)
Theorem leb_iff : forall n m,
  leb n m = true <-> n <= m.
Proof.
  intros n m.
  split.
  - intros E. apply leb_complete. apply E.
  - intros E. apply leb_correct. apply E.
Qed.
(** [] *)

Module R.

(** **** Exercise: 3 stars, recommendedM (R_provability)  *)
(** We can define three-place relations, four-place relations,
    etc., in just the same way as binary relations.  For example,
    consider the following three-place relation on numbers: *)

Inductive R : nat -> nat -> nat -> Prop :=
   | c1 : R 0 0 0
   | c2 : forall m n o, R m n o -> R (S m) n (S o)
   | c3 : forall m n o, R m n o -> R m (S n) (S o)
   | c4 : forall m n o, R (S m) (S n) (S (S o)) -> R m n o
   | c5 : forall m n o, R m n o -> R n m o.

(** m + n = o *)
(** - Which of the following propositions are provable?
      - [R 1 1 2]
      - [R 2 2 6]

    - If we dropped constructor [c5] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.

    - If we dropped constructor [c4] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.

Answer:
    - both
    - I think not
    - I'm not sure
[]
*)

(** **** Exercise: 3 stars, optional (R_fact)  *)
(** The relation [R] above actually encodes a familiar function.
    Figure out which function; then state and prove this equivalence
    in Coq? *)

Definition fR : nat -> nat -> nat :=
    fun (n m : nat) => n + m.

Theorem R_equiv_fR : forall m n o, R m n o <-> fR m n = o.
Proof.
 intros m n o.
 split.
 - intros E.
   induction E.
   -- simpl. reflexivity.
   -- simpl. rewrite -> IHE. reflexivity.
   -- rewrite <- plus_n_Sm. unfold fR in IHE. rewrite -> IHE. reflexivity.
   -- simpl in IHE. rewrite <- plus_n_Sm in IHE. inversion IHE. reflexivity.
   -- rewrite -> plus_comm in IHE. apply IHE.
 - generalize dependent o.
   induction m.
   -- induction n.
    + intros o E. rewrite <- E. simpl. apply c1.
    + intros o E. destruct o. 
        ++ inversion E.
        ++ apply c3. rewrite <- plus_n_Sm in E. inversion E. 
           assert (H: R 0 n o). { apply IHn in H0. apply H0. }
           rewrite -> H0 in H. apply H.
   -- induction n.
    + intros o E. simpl in E. destruct o.
        ++ inversion E.
        ++ inversion E. apply c2. rewrite -> H0. apply IHm in H0. apply H0.
    + intros o E. simpl in E. destruct o.
        ++ inversion E.
        ++ inversion E. apply IHm in H0. apply c2.
           inversion E. rewrite -> H1. apply H0.
Qed.
(** [] *)

End R.

(** **** Exercise: 4 stars, advanced (subsequence)  *)
(** A list is a _subsequence_ of another list if all of the elements
    in the first list occur in the same order in the second list,
    possibly with some extra elements in between. For example,

      [1;2;3]

    is a subsequence of each of the lists

      [1;2;3]
      [1;1;1;2;2;3]
      [1;2;7;3]
      [5;6;1;9;9;2;7;3;8]

    but it is _not_ a subsequence of any of the lists

      [1;2]
      [1;3]
      [5;6;2;1;7;3;8].

    - Define an inductive proposition [subseq] on [list nat] that
      captures what it means to be a subsequence. (Hint: You'll need
      three cases.)

    - Prove [subseq_refl] that subsequence is reflexive, that is,
      any list is a subsequence of itself.

    - Prove [subseq_app] that for any lists [l1], [l2], and [l3],
      if [l1] is a subsequence of [l2], then [l1] is also a subsequence
      of [l2 ++ l3].

    - (Optional, harder) Prove [subseq_trans] that subsequence is
      transitive -- that is, if [l1] is a subsequence of [l2] and [l2]
      is a subsequence of [l3], then [l1] is a subsequence of [l3].
      Hint: choose your induction carefully! *)

Inductive subseq : list nat -> list nat -> Prop :=
    | emp : forall (l : list nat), subseq [] l
    | con : forall (n : nat) (l1 l2 : list nat), subseq l1 l2 -> subseq (n :: l1) (n :: l2)
    | ncon : forall (n : nat) (l1 l2 : list nat), subseq l1 l2 -> subseq l1 (n :: l2).

Theorem subseq_refl : forall (l : list nat),
    subseq l l.
Proof.
    intros l.
    induction l.
    - apply emp.
    - apply (con x). apply IHl.
Qed.

Theorem subseq_app : forall (l1 l2 l3 : list nat),
    subseq l1 l2 -> subseq l1 (l2 ++ l3).
Proof.
    intros l1 l2 l3 E.
    induction E.
    - apply emp.
    - simpl. apply con. apply IHE.
    - simpl. apply ncon. apply IHE.
Qed.

(** The proof below took me several hours.... *)    
Theorem subseq_trans : forall (l1 l2 l3 : list nat),
    subseq l1 l2 -> subseq l2 l3 -> subseq l1 l3.
Proof.
    intros l1 l2 l3 E1 E2.
    generalize dependent l1.
    induction E2.
    - intros l3 E. inversion E. apply emp.
    - intros l3 E.
      inversion E.
      + apply emp. 
      + apply con. specialize (IHE2 l0). apply IHE2 in H1. apply H1.
      + specialize (IHE2 l3). apply IHE2 in H1. apply ncon. apply H1.
    - intros l3 E.
      specialize (IHE2 l3). apply IHE2 in E. apply ncon. apply E.
Qed. 
      
(** [] *)

(** **** Exercise: 2 stars, optionalM (R_provability2)  *)
(** Suppose we give Coq the following definition:

    Inductive R : nat -> list nat -> Prop :=
      | c1 : R 0 []
      | c2 : forall n l, R n l -> R (S n) (n :: l)
      | c3 : forall n l, R (S n) l -> R n l.

    Which of the following propositions are provable?

    - [R 2 [1;0]]
    - [R 1 [1;2;1;0]]
    - [R 6 [3;2;1;0]]  *)

(** Answer: R a b <=> length b >= a, so answer is -Yes -Yes -No *)


(* ################################################################# *)
(** * Case Study: Regular Expressions *)

(** The [ev] property provides a simple example for illustrating
    inductive definitions and the basic techniques for reasoning about
    them, but it is not terribly exciting -- after all, it is
    equivalent to the two non-inductive of evenness that we had
    already seen, and does not seem to offer any concrete benefit over
    them.  To give a better sense of the power of inductive
    definitions, we now show how to use them to model a classic
    concept in computer science: _regular expressions_. *)

(** Regular expressions are a simple language for describing strings,
    defined as follows: *)

Inductive reg_exp (T : Type) : Type :=
| EmptySet : reg_exp T
| EmptyStr : reg_exp T
| Char : T -> reg_exp T
| App : reg_exp T -> reg_exp T -> reg_exp T
| Union : reg_exp T -> reg_exp T -> reg_exp T
| Star : reg_exp T -> reg_exp T.

Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.

(** Note that this definition is _polymorphic_: Regular
    expressions in [reg_exp T] describe strings with characters drawn
    from [T] -- that is, lists of elements of [T].

    (We depart slightly from standard practice in that we do not
    require the type [T] to be finite.  This results in a somewhat
    different theory of regular expressions, but the difference is not
    significant for our purposes.) *)

(** We connect regular expressions and strings via the following
    rules, which define when a regular expression _matches_ some
    string:

      - The expression [EmptySet] does not match any string.

      - The expression [EmptyStr] matches the empty string [[]].

      - The expression [Char x] matches the one-character string [[x]].

      - If [re1] matches [s1], and [re2] matches [s2], then [App re1
        re2] matches [s1 ++ s2].

      - If at least one of [re1] and [re2] matches [s], then [Union re1
        re2] matches [s].

      - Finally, if we can write some string [s] as the concatenation of
        a sequence of strings [s = s_1 ++ ... ++ s_k], and the
        expression [re] matches each one of the strings [s_i], then
        [Star re] matches [s].

        As a special case, the sequence of strings may be empty, so
        [Star re] always matches the empty string [[]] no matter what
        [re] is.

    We can easily translate this informal definition into an
    [Inductive] one as follows: *)

Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
| MEmpty : exp_match [] EmptyStr
| MChar : forall x, exp_match [x] (Char x)
| MApp : forall s1 re1 s2 re2,
           exp_match s1 re1 ->
           exp_match s2 re2 ->
           exp_match (s1 ++ s2) (App re1 re2)
| MUnionL : forall s1 re1 re2,
              exp_match s1 re1 ->
              exp_match s1 (Union re1 re2)
| MUnionR : forall re1 s2 re2,
              exp_match s2 re2 ->
              exp_match s2 (Union re1 re2)
| MStar0 : forall re, exp_match [] (Star re)
| MStarApp : forall s1 s2 re,
               exp_match s1 re ->
               exp_match s2 (Star re) ->
               exp_match (s1 ++ s2) (Star re).

(** Again, for readability, we can also display this definition using
    inference-rule notation.  At the same time, let's introduce a more
    readable infix notation. *)

Notation "s =~ re" := (exp_match s re) (at level 80).

(**

                          ----------------                    (MEmpty)
                           [] =~ EmptyStr

                          ---------------                      (MChar)
                           [x] =~ Char x

                       s1 =~ re1    s2 =~ re2
                      -------------------------                 (MApp)
                       s1 ++ s2 =~ App re1 re2

                              s1 =~ re1
                        ---------------------                (MUnionL)
                         s1 =~ Union re1 re2

                              s2 =~ re2
                        ---------------------                (MUnionR)
                         s2 =~ Union re1 re2

                          ---------------                     (MStar0)
                           [] =~ Star re

                      s1 =~ re    s2 =~ Star re
                     ---------------------------            (MStarApp)
                        s1 ++ s2 =~ Star re
*)

(** Notice that these rules are not _quite_ the same as the informal
    ones that we gave at the beginning of the section.  First, we
    don't need to include a rule explicitly stating that no string
    matches [EmptySet]; we just don't happen to include any rule that
    would have the effect of some string matching [EmptySet].  (Indeed,
    the syntax of inductive definitions doesn't even _allow_ us to
    give such a "negative rule.")

    Second, the informal rules for [Union] and [Star] correspond
    to two constructors each: [MUnionL] / [MUnionR], and [MStar0] /
    [MStarApp].  The result is logically equivalent to the original
    rules but more convenient to use in Coq, since the recursive
    occurrences of [exp_match] are given as direct arguments to the
    constructors, making it easier to perform induction on evidence.
    (The [exp_match_ex1] and [exp_match_ex2] exercises below ask you
    to prove that the constructors given in the inductive declaration
    and the ones that would arise from a more literal transcription of
    the informal rules are indeed equivalent.)

    Let's illustrate these rules with a few examples. *)

Example reg_exp_ex1 : [1] =~ Char 1.
Proof.
  apply MChar.
Qed.

Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1] _ [2]).
  - apply MChar.
  - apply MChar.
Qed.

(** (Notice how the last example applies [MApp] to the strings [[1]]
    and [[2]] directly.  Since the goal mentions [[1; 2]] instead of
    [[1] ++ [2]], Coq wouldn't be able to figure out how to split the
    string on its own.)

    Using [inversion], we can also show that certain strings do _not_
    match a regular expression: *)

Example reg_exp_ex3 : ~ ([1; 2] =~ Char 1).
Proof.
  intros H. inversion H.
Qed.

(** We can define helper functions to help write down regular
    expressions. The [reg_exp_of_list] function constructs a regular
    expression that matches exactly the list that it receives as an
    argument: *)

Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.

Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof.
  simpl. apply (MApp [1]).
  { apply MChar. }
  apply (MApp [2]).
  { apply MChar. }
  apply (MApp [3]).
  { apply MChar. }
  apply MEmpty.
Qed.

(** We can also prove general facts about [exp_match].  For instance,
    the following lemma shows that every string [s] that matches [re]
    also matches [Star re]. *)

Lemma MStar1 :
  forall T s (re : reg_exp T) ,
    s =~ re ->
    s =~ Star re.
Proof.
  intros T s re H.
  rewrite <- (app_nil_r _ s).
  apply (MStarApp s [] re).
  - apply H.
  - apply MStar0.
Qed.

(** (Note the use of [app_nil_r] to change the goal of the theorem to
    exactly the same shape expected by [MStarApp].) *)

(** **** Exercise: 3 stars (exp_match_ex1)  *)
(** The following lemmas show that the informal matching rules given
    at the beginning of the chapter can be obtained from the formal
    inductive definition. *)

Lemma empty_is_empty : forall T (s : list T),
  ~ (s =~ EmptySet).
Proof.
  intros T s H.
  inversion H.
Qed.


Lemma MUnion' : forall T (s : list T) (re1 re2 : reg_exp T),
  s =~ re1 \/ s =~ re2 ->
  s =~ Union re1 re2.
Proof.
  intros T s re1 re2 H.
  destruct H.
  - apply MUnionL. apply H.
  - apply MUnionR. apply H.
Qed.

(** The next lemma is stated in terms of the [fold] function from the
    [Poly] chapter: If [ss : list (list T)] represents a sequence of
    strings [s1, ..., sn], then [fold app ss []] is the result of
    concatenating them all together. *)

Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp T),
  (forall s, In s ss -> s =~ re) ->
  fold app ss [] =~ Star re.
Proof.
  intros T ss re H.
  induction ss.
  - simpl. apply MStar0.
  - simpl.
    assert (forall s : list T, In s ss -> s =~ re). {
        intros s H1. specialize (H s).
        assert (In s (x :: ss)). {
            simpl. right. apply H1.
        }
        apply H in H0.
        apply H0.
    }
    specialize (H x). assert (H1: In x (x :: ss)). {
    simpl. left. reflexivity.
   }
   apply H in H1.
   apply MStarApp.
   -- apply H1.
   -- apply IHss in H0. apply H0.
Qed. 
(** [] *)

(** **** Exercise: 4 stars (reg_exp_of_list)  *)
(** Prove that [reg_exp_of_list] satisfies the following
    specification: *)


Lemma reg_exp_of_list_spec : forall T (s1 s2 : list T),
  s1 =~ reg_exp_of_list s2 <-> s1 = s2.
Proof.
  intros T s1 s2.
  split.
  - intros H. generalize dependent s1.
    induction s2.
    + intros s1 H. simpl in H. inversion H. reflexivity.
    + intros s1 H. simpl in H. inversion H. inversion H3.
      apply IHs2 in H4. rewrite <- H4. simpl. reflexivity.
  - intros H. generalize dependent s1.
    induction s2.
    + intros s1 H. simpl. rewrite -> H. apply MEmpty.
    + intros s1 H. destruct s1.
      -- inversion H.
      -- inversion H. simpl. specialize (IHs2 s2).
         assert (s2 = s2). { reflexivity. }
         apply IHs2 in H0.
         assert ([x] =~ Char x). { apply MChar. }
         apply (MApp [x] (Char x) s2 (reg_exp_of_list s2)).
         ++ apply H3.
         ++ apply H0.
Qed.
(** [] *)

(** Since the definition of [exp_match] has a recursive
    structure, we might expect that proofs involving regular
    expressions will often require induction on evidence.  For
    example, suppose that we wanted to prove the following intuitive
    result: If a regular expression [re] matches some string [s], then
    all elements of [s] must occur somewhere in [re].  To state this
    theorem, we first define a function [re_chars] that lists all
    characters that occur in a regular expression: *)

Fixpoint re_chars {T} (re : reg_exp T) : list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.

(** We can then phrase our theorem as follows: *)

Theorem in_re_match : forall T (s : list T) (re : reg_exp T) (x : T),
  s =~ re ->
  In x s ->
  In x (re_chars re).
Proof.
  intros T s re x Hmatch Hin.
  induction Hmatch
    as [
        |x'
        |s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2 re2 Hmatch IH
        |re|s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  (* WORKED IN CLASS *)
  - (* MEmpty *)
    apply Hin.
  - (* MChar *)
    apply Hin.
  - simpl. rewrite in_app_iff in *.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      left. apply (IH1 Hin).
    + (* In x s2 *)
      right. apply (IH2 Hin).
  - (* MUnionL *)
    simpl. rewrite in_app_iff.
    left. apply (IH Hin).
  - (* MUnionR *)
    simpl. rewrite in_app_iff.
    right. apply (IH Hin).
  - (* MStar0 *)
    destruct Hin.

(** Something interesting happens in the [MStarApp] case.  We obtain
    _two_ induction hypotheses: One that applies when [x] occurs in
    [s1] (which matches [re]), and a second one that applies when [x]
    occurs in [s2] (which matches [Star re]).  This is a good
    illustration of why we need induction on evidence for [exp_match],
    as opposed to [re]: The latter would only provide an induction
    hypothesis for strings that match [re], which would not allow us
    to reason about the case [In x s2]. *)

  - (* MStarApp *)
    simpl. rewrite in_app_iff in Hin.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      apply (IH1 Hin).
    + (* In x s2 *)
      apply (IH2 Hin).
Qed.

(** **** Exercise: 4 stars (re_not_empty)  *)
(** Write a recursive function [re_not_empty] that tests whether a
    regular expression matches some string. Prove that your function
    is correct. *)

Fixpoint re_not_empty {T : Type} (re : reg_exp T) : bool := 
  match re with
  | EmptySet => false
  | EmptyStr => true
  | Char x => true
  | App re1 re2 => (re_not_empty re1) && (re_not_empty re2)
  | Union re1 re2 => (re_not_empty re1) || (re_not_empty re2)
  | Star re => true
  end.

Lemma re_not_empty_correct : forall T (re : reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  intros T re.
  split.
  - intros H.
    induction re.
    + inversion H. inversion H0.
    + simpl. reflexivity.
    + simpl. reflexivity.
    + simpl. inversion H. inversion H0.
      assert (exists s : list T, s =~ re1). {
        exists s1. apply H4.
      }
      assert (exists s : list T, s =~ re2). {
        exists s2. apply H5.
      }
      apply IHre1 in H6.
      apply IHre2 in H7. 
      rewrite -> H6.
      rewrite -> H7.
      simpl. reflexivity.
    + simpl. inversion H. inversion H0.
      -- assert (exists s : list T, s =~ re1). {
        exists x. apply H3.
      }
      apply IHre1 in H5.
      rewrite -> H5.
      simpl. reflexivity.
      -- assert (exists s : list T, s =~ re2). {
        exists x. apply H3.
      }
      apply IHre2 in H5.
      rewrite -> H5.
      destruct (re_not_empty re1).
      --- simpl. reflexivity.
      --- simpl. reflexivity.
    + simpl. reflexivity.
  - intros H. induction re.
    + inversion H.
    + exists []. apply MEmpty.
    + exists [t]. apply MChar.
    + inversion H. destruct (re_not_empty re1).
      -- assert (true = true). { reflexivity. }
         apply IHre1 in H0.
         simpl in H1. 
         apply IHre2 in H1.
         inversion H1.
         inversion H0.
         exists (x0 ++ x).
         apply MApp.
         --- apply H3.
         --- apply H2.
      -- simpl in H1. inversion H1.
    + inversion H. destruct (re_not_empty re1).
      -- assert (true = true). { reflexivity. }
         apply IHre1 in H0.
         inversion H0.
         exists x. apply MUnionL. apply H2.
      -- simpl in H1. apply IHre2 in H1. inversion H1.
         exists x. apply MUnionR. apply H0.
    + exists []. apply MStar0.
Qed.
(** [] *)

(* ================================================================= *)
(** ** The [remember] Tactic *)

(** One potentially confusing feature of the [induction] tactic is
    that it happily lets you try to set up an induction over a term
    that isn't sufficiently general.  The effect of this is to lose
    information (much as [destruct] can do), and leave you unable to
    complete the proof.  Here's an example: *)

Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.

(** Just doing an [inversion] on [H1] won't get us very far in the
    recursive cases. (Try it!). So we need induction. Here is a naive
    first attempt: *)

  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].

(** But now, although we get seven cases (as we would expect from the
    definition of [exp_match]), we have lost a very important bit of
    information from [H1]: the fact that [s1] matched something of the
    form [Star re].  This means that we have to give proofs for _all_
    seven constructors of this definition, even though all but two of
    them ([MStar0] and [MStarApp]) are contradictory.  We can still
    get the proof to go through for a few constructors, such as
    [MEmpty]... *)

  - (* MEmpty *)
    simpl. intros H. apply H.

(** ... but most cases get stuck.  For [MChar], for instance, we
    must show that

    s2 =~ Char x' -> x' :: s2 =~ Char x',

    which is clearly impossible. *)

  - (* MChar. Stuck... *)
Abort.

(** The problem is that [induction] over a Prop hypothesis only works
    properly with hypotheses that are completely general, i.e., ones
    in which all the arguments are variables, as opposed to more
    complex expressions, such as [Star re].

    (In this respect, [induction] on evidence behaves more like
    [destruct] than like [inversion].)

    We can solve this problem by generalizing over the problematic
    expressions with an explicit equality: *)

Lemma star_app: forall T (s1 s2 : list T) (re re' : reg_exp T),
  s1 =~ re' ->
  re' = Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.

(** We can now proceed by performing induction over evidence directly,
    because the argument to the first hypothesis is sufficiently
    general, which means that we can discharge most cases by inverting
    the [re' = Star re] equality in the context.

    This idiom is so common that Coq provides a tactic to
    automatically generate such equations for us, avoiding thus the
    need for changing the statements of our theorems. *)

(** Invoking the tactic [remember e as x] causes Coq to (1) replace
    all occurrences of the expression [e] by the variable [x], and (2)
    add an equation [x = e] to the context.  Here's how we can use it
    to show the above result: *)
Abort.

Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re'.

(** We now have [Heqre' : re' = Star re]. *)

  generalize dependent s2.
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].

(** The [Heqre'] is contradictory in most cases, which allows us to
    conclude immediately. *)

  - (* MEmpty *)  inversion Heqre'.
  - (* MChar *)   inversion Heqre'.
  - (* MApp *)    inversion Heqre'.
  - (* MUnionL *) inversion Heqre'.
  - (* MUnionR *) inversion Heqre'.

(** The interesting cases are those that correspond to [Star].  Note
    that the induction hypothesis [IH2] on the [MStarApp] case
    mentions an additional premise [Star re'' = Star re'], which
    results from the equality generated by [remember]. *)

  - (* MStar0 *)
    inversion Heqre'. intros s H. apply H.

  - (* MStarApp *)
    inversion Heqre'. rewrite H0 in IH2, Hmatch1.
    intros s2 H1. rewrite <- app_assoc.
    apply MStarApp.
    + apply Hmatch1.
    + apply IH2.
      * reflexivity.
      * apply H1.
Qed.

(** **** Exercise: 4 stars (exp_match_ex2)  *)

(** The [MStar''] lemma below (combined with its converse, the
    [MStar'] exercise above), shows that our definition of [exp_match]
    for [Star] is equivalent to the informal one given previously. *)

Lemma MStar'' : forall T (s : list T) (re : reg_exp T),
  s =~ Star re ->
  exists ss : list (list T),
    s = fold app ss []
    /\ forall s', In s' ss -> s' =~ re.
Proof.
  intros T s re H.
  remember (Star re) as re'.
  induction H.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
    exists []. split.
    + reflexivity.
    + intros s' H. inversion H.
  - inversion Heqre'.
    rewrite -> H2 in H.
    rewrite -> H2 in IHexp_match2.
    assert (Star re = Star re). { reflexivity. }
    apply IHexp_match2 in H1.
    inversion H1.
    exists ([s1] ++ x).
    split.
    + simpl. apply proj1 in H3. rewrite <- H3. reflexivity.
    + intros s' E. simpl in E. destruct E.
      -- rewrite <- H4. apply H.
      -- apply proj2 in H3. specialize (H3 s'). apply H3 in H4. apply H4.
Qed. 


(** [] *)

(** **** Exercise: 5 stars, advanced (pumping)  *)
(** One of the first really interesting theorems in the theory of
    regular expressions is the so-called _pumping lemma_, which
    states, informally, that any sufficiently long string [s] matching
    a regular expression [re] can be "pumped" by repeating some middle
    section of [s] an arbitrary number of times to produce a new
    string also matching [re].

    To begin, we need to define "sufficiently long."  Since we are
    working in a constructive logic, we actually need to be able to
    calculate, for each regular expression [re], the minimum length
    for strings [s] to guarantee "pumpability." *)

Module Pumping.

Fixpoint pumping_constant {T} (re : reg_exp T) : nat :=
  match re with
  | EmptySet => 0
  | EmptyStr => 1
  | Char _ => 2
  | App re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Union re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Star _ => 1
  end.

(** Next, it is useful to define an auxiliary function that repeats a
    string (appends it to itself) some number of times. *)

Fixpoint napp {T} (n : nat) (l : list T) : list T :=
  match n with
  | 0 => []
  | S n' => l ++ napp n' l
  end.

Lemma napp_plus: forall T (n m : nat) (l : list T),
  napp (n + m) l = napp n l ++ napp m l.
Proof.
  intros T n m l.
  induction n as [|n IHn].
  - reflexivity.
  - simpl. rewrite IHn, app_assoc. reflexivity.
Qed.

(** Now, the pumping lemma itself says that, if [s =~ re] and if the
    length of [s] is at least the pumping constant of [re], then [s]
    can be split into three substrings [s1 ++ s2 ++ s3] in such a way
    that [s2] can be repeated any number of times and the result, when
    combined with [s1] and [s3] will still match [re].  Since [s2] is
    also guaranteed not to be the empty string, this gives us
    a (constructive!) way to generate strings matching [re] that are
    as long as we like. *)

Lemma length_app : forall T (a b : list T),
  length (a ++ b) = length a + length b.
Proof.
  intros.
  induction a.
  - simpl. reflexivity.
  - simpl. rewrite -> IHa. reflexivity.
Qed.

Lemma le_zero : forall (a : nat),
  0 <= a.
Proof.
  intros.
  induction a.
  - apply le_n.
  - apply le_S. apply IHa.
Qed.

Lemma s_le : forall (a b : nat),
  S a <= b -> a <= pred b.
Proof.
  intros a b.
  generalize dependent a.
  induction b.
  - intros. inversion H.
  - intros. simpl. inversion H.
    + apply le_n.
    + assert (a <= S a). { apply le_S. apply le_n. }
      apply (le_trans a (S a) b).
      -- apply H2.
      -- apply H1.
Qed.

Lemma le_plus : forall (a b : nat),
  a <= b + a.
Proof.
  intros.
  induction b.
  - simpl. apply le_n.
  - simpl. apply le_S. apply IHb.
Qed.

Lemma le_ss : forall (a b : nat),
  a <= b -> S a <= S b.
Proof.
  intros.
  induction H.
  - apply le_n.
  -assert (S m <= S (S m)). {
    apply le_S.
    apply le_n.
  }
  apply (le_trans (S a) (S m) (S (S m))).
  + apply IHle.
  + apply H0.
Qed.

Lemma ss_le : forall (a b : nat),
  S a <= S b -> a <= b.
Proof.
  intros.
  inversion H.
  - apply le_n.
  - assert (a <= S a). { apply le_S. apply le_n. }
    apply (le_trans a (S a) b).
    + apply H2.
    + apply H1.
Qed.

Lemma ab_leq_cd : forall (a b c d : nat),
  a + b <= c + d -> a <= c \/ b <= d.
Proof.
  induction a.
  - intros. left. apply le_zero.
  - intros. destruct c.
    + right. simpl in H. assert (b <= S (a + b)). {
      apply le_S. apply le_plus.
    }
    apply (le_trans b (S (a + b)) d).
    -- apply H0.
    -- apply H.
    + simpl in H. rewrite -> plus_n_Sm in H. rewrite -> plus_n_Sm in H.
      specialize (IHa (S b) c (S d)).
      apply IHa in H.
      destruct H.
      -- left. apply le_ss. apply H.
      -- right. apply ss_le. apply H.
Qed. 

Lemma match_napp_star : forall T (m : nat) (x : list T) (s : reg_exp T),
  x =~ s -> napp m x =~ Star s.
Proof.
  intros.
  induction m.
  - simpl. apply MStar0.
  - simpl. apply MStarApp.
    + apply H.
    + apply IHm. 
Qed.

Lemma pumping : forall T (re : reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.

(** To streamline the proof (which you are to fill in), the [omega]
    tactic, which is enabled by the following [Require], is helpful in
    several places for automatically completing tedious low-level
    arguments involving equalities or inequalities over natural
    numbers.  We'll return to [omega] in a later chapter, but feel
    free to experiment with it now if you like.  The first case of the
    induction gives an example of how it is used. *)

 Require Import Coq.micromega.Lia.

Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - (* MEmpty *)
    simpl. lia.
  - intros H. simpl in H. inversion H. inversion H1.
  - intros H. simpl in H.
    assert (H1: pumping_constant re1 <= length s1 \/ pumping_constant re2 <= length s2). {
      rewrite -> length_app in H.
      apply ab_leq_cd.
      apply H.
    }
    destruct H1.
    + apply IH1 in H0. inversion H0. inversion H1. inversion H2.
      exists x. exists x0. exists (x1 ++ s2).
      split.
      -- apply proj1 in H3. rewrite -> H3. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity.
      -- split.
        ++ apply proj2 in H3. apply proj1 in H3. apply H3.
        ++ apply proj2 in H3. apply proj2 in H3. intros m. specialize (H3 m).
           assert ((x ++ napp m x0 ++ x1) ++ s2 = x ++ napp m x0 ++ x1 ++ s2). {
             rewrite <- app_assoc. rewrite <- app_assoc. reflexivity.
           }
           rewrite <- H4.
           apply MApp.
           --- apply H3.
           --- apply Hmatch2.
    + apply IH2 in H0. inversion H0. inversion H1. inversion H2.
      exists (s1 ++ x). exists x0. exists x1.
      split.
      -- apply proj1 in H3. rewrite -> H3. rewrite -> app_assoc. reflexivity.
      -- split.
        ++ apply proj2 in H3. apply proj1 in H3. apply H3.
        ++ apply proj2 in H3. apply proj2 in H3. intros m. specialize (H3 m).
           rewrite <- app_assoc. apply MApp.
           --- apply Hmatch1.
           --- apply H3.
  - intros H. simpl in H. assert (pumping_constant re1 <= length s1). {
      assert (pumping_constant re1 <= pumping_constant re1 + pumping_constant re2). {
        rewrite -> plus_comm.
        apply le_plus.
      }
      apply (le_trans (pumping_constant re1) (pumping_constant re1 + pumping_constant re2) (length s1)).
      - apply H0.
      - apply H.
    }
    apply IH in H0.
    inversion H0. inversion H1. inversion H2.
    exists x. exists x0. exists x1.
    split.
    -- apply proj1 in H3. apply H3.
    -- split.
      ++ apply proj2 in H3. apply proj1 in H3. apply H3.
      ++ apply proj2 in H3. apply proj2 in H3. intros m.
         specialize (H3 m). apply MUnionL. apply H3.
  - intros H. simpl in H. assert (pumping_constant re2 <= length s2). {
    assert (pumping_constant re2 <= pumping_constant re1 + pumping_constant re2). {
      apply le_plus.
    }
    apply (le_trans (pumping_constant re2) (pumping_constant re1 + pumping_constant re2) (length s2)).
    - apply H0.
    - apply H.
  }
  apply IH in H0.
  inversion H0. inversion H1. inversion H2.
  exists x. exists x0. exists x1.
  split.
  -- apply proj1 in H3. apply H3.
  -- split.
    ++ apply proj2 in H3. apply proj1 in H3. apply H3.
    ++ apply proj2 in H3. apply proj2 in H3. intros m.
        specialize (H3 m). apply MUnionR. apply H3.
  - intros. inversion H.
  - intros H. simpl in H. destruct s2.
    + inversion Hmatch1.
      -- rewrite <- H0 in H. inversion H.
      -- exists []. exists [x]. exists []. split.
        ++ simpl. reflexivity.
        ++ split.
          --- unfold not. intros. inversion H2.
          --- intros m. simpl. rewrite -> app_nil_r. apply (match_napp_star T m [x] (Char x)). apply MChar.
      -- exists []. exists s1. exists []. split.
        ++ simpl. rewrite -> H2. reflexivity.
        ++ split.
          --- rewrite -> app_nil_r in H. unfold not. intros E. rewrite -> E in H. inversion H.
          --- intros m. simpl. rewrite -> app_nil_r. apply (match_napp_star T m s1 (App re1 re2)). rewrite -> H3. apply Hmatch1.
      -- exists []. exists s1. exists []. split.
        ++ simpl.  reflexivity.
        ++ split.
          --- rewrite -> app_nil_r in H. unfold not. intros E. rewrite -> E in H. inversion H.
          --- intros m. simpl. rewrite -> app_nil_r. apply (match_napp_star T m s1 (Union re1 re2)). rewrite -> H2. apply Hmatch1.
      -- exists []. exists s1. exists []. split.
        ++ simpl.  reflexivity.
        ++ split.
          --- rewrite -> app_nil_r in H. unfold not. intros E. rewrite -> E in H. inversion H.
          --- intros m. simpl. rewrite -> app_nil_r. apply (match_napp_star T m s1 (Union re1 re2)). rewrite -> H2. apply Hmatch1.
      -- rewrite <- H0 in H. inversion H.
      -- exists []. exists s1. exists []. split.
        ++ simpl. rewrite -> H2.  reflexivity.
        ++ split.
          --- rewrite -> app_nil_r in H. unfold not. intros E. rewrite -> E in H. inversion H.
          --- intros m. simpl. rewrite -> app_nil_r. apply (match_napp_star T m s1 (Star re0)). rewrite -> H3. apply Hmatch1.
    + assert (pumping_constant (Star re) <= length (t :: s2)). {
        simpl. assert (0 <= length s2). { apply le_zero. } apply le_ss in H0. apply H0.
      }
      apply IH2 in H0. inversion H0. inversion H1. inversion H2.
      exists (s1 ++ x). exists x0. exists x1. split.
      -- apply proj1 in H3. rewrite -> H3. rewrite -> app_assoc. reflexivity.
      -- split.
        ++ apply proj2 in H3. apply proj1 in H3. apply H3.
        ++ intros m. apply proj2 in H3. apply proj2 in H3. specialize (H3 m).
           rewrite <- app_assoc. apply MStarApp.
           --- apply Hmatch1.
           --- apply H3.
Qed.

End Pumping.
(** [] *)

(* ################################################################# *)
(** * Case Study: Improving Reflection *)

(** We've seen in the [Logic] chapter that we often need to
    relate boolean computations to statements in [Prop].  But
    performing this conversion in the way we did it there can result
    in tedious proof scripts.  Consider the proof of the following
    theorem: *)

Theorem filter_not_empty_In : forall n l,
  filter (beq_nat n) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l = [] *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (beq_nat n m) eqn:H.
    + (* beq_nat n m = true *)
      intros _. rewrite beq_nat_true_iff in H. rewrite H.
      left. reflexivity.
    + (* beq_nat n m = false *)
      intros H'. right. apply IHl'. apply H'.
Qed.

(** In the first branch after [destruct], we explicitly apply
    the [beq_nat_true_iff] lemma to the equation generated by
    destructing [beq_nat n m], to convert the assumption [beq_nat n m
    = true] into the assumption [n = m]; then we had to [rewrite]
    using this assumption to complete the case.

    We can streamline this by defining an inductive proposition that
    yields a better case-analysis principle for [beq_nat n m].
    Instead of generating an equation such as [beq_nat n m = true],
    which is generally not directly useful, this principle gives us
    right away the assumption we really need: [n = m].

    We'll actually define something a bit more general, which can be
    used with arbitrary properties (and not just equalities): *)

Module FirstTry.

Inductive reflect : Prop -> bool -> Prop :=
| ReflectT : forall (P:Prop), P -> reflect P true
| ReflectF : forall (P:Prop), ~ P -> reflect P false.

(** Before explaining this, let's rearrange it a little: Since the
    types of both [ReflectT] and [ReflectF] begin with
    [forall (P:Prop)], we can make the definition a bit more readable
    and easier to work with by making [P] a parameter of the whole
    Inductive declaration. *)

End FirstTry.

Inductive reflect (P : Prop) : bool -> Prop :=
| ReflectT : P -> reflect P true
| ReflectF : ~ P -> reflect P false.

(** The [reflect] property takes two arguments: a proposition
    [P] and a boolean [b].  Intuitively, it states that the property
    [P] is _reflected_ in (i.e., equivalent to) the boolean [b]: [P]
    holds if and only if [b = true].  To see this, notice that, by
    definition, the only way we can produce evidence that [reflect P
    true] holds is by showing that [P] is true and using the
    [ReflectT] constructor.  If we invert this statement, this means
    that it should be possible to extract evidence for [P] from a
    proof of [reflect P true].  Conversely, the only way to show
    [reflect P false] is by combining evidence for [~ P] with the
    [ReflectF] constructor.

    It is easy to formalize this intuition and show that the two
    statements are indeed equivalent: *)

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  (* WORKED IN CLASS *)
  intros P b H. destruct b.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. inversion H'.
Qed.

(** **** Exercise: 2 stars, recommended (reflect_iff)  *)
Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  intros P b H. destruct b.
  - split. 
    + reflexivity.
    + inversion H. intros. apply H0.
  - split.
    + inversion H. intros. unfold not in H0. apply H0 in H1. inversion H1.
    + intros. inversion H0.
Qed.
(** [] *)

(** The advantage of [reflect] over the normal "if and only if"
    connective is that, by destructing a hypothesis or lemma of the
    form [reflect P b], we can perform case analysis on [b] while at
    the same time generating appropriate hypothesis in the two
    branches ([P] in the first subgoal and [~ P] in the second). *)

Lemma beq_natP : forall n m, reflect (n = m) (beq_nat n m).
Proof.
  intros n m.
  apply iff_reflect. rewrite beq_nat_true_iff. reflexivity.
Qed.

(** The new proof of [filter_not_empty_In] now goes as follows.
    Notice how the calls to [destruct] and [apply] are combined into a
    single call to [destruct]. *)

(** (To see this clearly, look at the two proofs of
    [filter_not_empty_In] with Coq and observe the differences in
    proof state at the beginning of the first case of the
    [destruct].) *)

Theorem filter_not_empty_In' : forall n l,
  filter (beq_nat n) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l = [] *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (beq_natP n m) as [H | H].
    + (* n = m *)
      intros _. rewrite H. left. reflexivity.
    + (* n <> m *)
      intros H'. right. apply IHl'. apply H'.
Qed.

(** **** Exercise: 3 stars, recommended (beq_natP_practice)  *)
(** Use [beq_natP] as above to prove the following: *)

Fixpoint count n l :=
  match l with
    [] => 0
  | m :: l' => (if beq_nat n m then 1 else 0) + count n l'
  end.

Theorem beq_natP_practice : forall n l,
  count n l = 0 -> ~(In n l).
Proof.
  intros n l H.
  induction l.
  - unfold not. intros H1. inversion H1.
  - unfold not. intros H1. simpl in H1. destruct H1.
    + simpl in H. assert (n = x). { rewrite -> H0. reflexivity. } 
      apply beq_nat_true_iff in H1. rewrite -> H1 in H. inversion H.
    + simpl in H. assert (count n l = 0). {
        destruct (if beq_nat n x then 1 else 0). 
        - simpl in H. apply H.
        - inversion H.
      }
      apply IHl in H1. unfold not in H1. apply H1 in H0. inversion H0.
Qed.

(** [] *)

(** This technique gives us only a small gain in convenience for
    the proofs we've seen here, but using [reflect] consistently often
    leads to noticeably shorter and clearer scripts as proofs get
    larger.  We'll see many more examples in later chapters.

    The use of the [reflect] property was popularized by _SSReflect_,
    a Coq library that has been used to formalize important results in
    mathematics, including as the 4-color theorem and the
    Feit-Thompson theorem.  The name SSReflect stands for _small-scale
    reflection_, i.e., the pervasive use of reflection to simplify
    small proof steps with boolean computations. *)

(* ################################################################# *)
(** * Additional Exercises *)

(** **** Exercise: 3 stars, recommended (nostutter)  *)
(** Formulating inductive definitions of properties is an important
    skill you'll need in this course.  Try to solve this exercise
    without any help at all.

    We say that a list "stutters" if it repeats the same element
    consecutively.  The property "[nostutter mylist]" means that
    [mylist] does not stutter.  Formulate an inductive definition for
    [nostutter].  (This is different from the [NoDup] property in the
    exercise above; the sequence [1;4;1] repeats but does not
    stutter.) *)

Inductive nostutter {X:Type} : list X -> Prop :=
  | stemp : nostutter []
  | stsig : forall (x : X), nostutter [x]
  | stcon : forall (x y : X) (h : list X), x <> y -> nostutter (y :: h) -> nostutter (x :: (y :: h)).
  
(** Make sure each of these tests succeeds, but feel free to change
    the suggested proof (in comments) if the given one doesn't work
    for you.  Your definition might be different from ours and still
    be correct, in which case the examples might need a different
    proof.  (You'll notice that the suggested proofs use a number of
    tactics we haven't talked about, to make them more robust to
    different possible ways of defining [nostutter].  You can probably
    just uncomment and use them as-is, but you can also prove each
    example with more basic tactics.)  *)

Example test_nostutter_1: nostutter [3;1;4;1;5;6].
Proof.
  apply stcon.
  - unfold not. intros. inversion H.
  - apply stcon.
    -- unfold not. intros. inversion H.
    -- apply stcon.
      --- unfold not. intros. inversion H.
      --- apply stcon.
        ---- unfold not. intros. inversion H.
        ---- apply stcon.
          + unfold not. intros. inversion H.
          + apply stsig.
Qed.
(* 
  Proof. repeat constructor; apply beq_nat_false_iff; auto.
  Qed.
*)

Example test_nostutter_2:  nostutter (@nil nat).
Proof.
  apply stemp.
Qed.
(* 
  Proof. repeat constructor; apply beq_nat_false_iff; auto.
  Qed.
*)

Example test_nostutter_3:  nostutter [5].
Proof.
  apply stsig.
Qed.
(* 
  Proof. repeat constructor; apply beq_nat_false; auto. Qed.
*)

Example test_nostutter_4:      not (nostutter [3;1;1;4]).
Proof.
  unfold not. intros.
  inversion H.
  inversion H4.
  unfold not in H7. assert (1 = 1). { reflexivity. }
  apply H7 in H10.
  inversion H10.
Qed.
(* 
  Proof. intro.
  repeat match goal with
    h: nostutter _ |- _ => inversion h; clear h; subst
  end.
  contradiction H1; auto. Qed.
*)
(** [] *)

(** **** Exercise: 4 stars, advanced (filter_challenge)  *)
(** Let's prove that our definition of [filter] from the [Poly]
    chapter matches an abstract specification.  Here is the
    specification, written out informally in English:

    A list [l] is an "in-order merge" of [l1] and [l2] if it contains
    all the same elements as [l1] and [l2], in the same order as [l1]
    and [l2], but possibly interleaved.  For example,

    [1;4;6;2;3]

    is an in-order merge of

    [1;6;2]

    and

    [4;3].

    Now, suppose we have a set [X], a function [test: X->bool], and a
    list [l] of type [list X].  Suppose further that [l] is an
    in-order merge of two lists, [l1] and [l2], such that every item
    in [l1] satisfies [test] and no item in [l2] satisfies test.  Then
    [filter test l = l1].

    Translate this specification into a Coq theorem and prove
    it.  (You'll need to begin by defining what it means for one list
    to be a merge of two others.  Do this with an inductive relation,
    not a [Fixpoint].)  *)
Inductive in_order_merge {X : Type} : list X -> list X -> list X -> Prop :=
  | iome2 : forall (x : list X), in_order_merge x x []
  | iome1 : forall (x : list X), in_order_merge x [] x
  | iomc1 : forall (l : list X) (x : X) (a b : list X),
                      in_order_merge l a b -> in_order_merge (x :: l) (x :: a) b
  | iomc2 : forall (l : list X) (x : X) (a b : list X),
                      in_order_merge l a b -> in_order_merge (x :: l) a (x :: b).

Lemma filter_all : forall {X : Type} (l : list X) (test : X -> bool),
  (forall x : X, In x l -> test x = true) -> filter test l = l.
Proof.
  intros.
  induction l.
  - simpl. reflexivity.
  - simpl in H. assert (test x = true). {
      specialize (H x). assert (x = x \/ In x l). { left. reflexivity. }
      apply H in H0. apply H0.
    }
    simpl.
    rewrite -> H0.
    assert (forall x : X, In x l -> test x = true). {
      intros. specialize (H x0). assert (x = x0 \/ In x0 l). { right. apply H1. }
      apply H in H2. apply H2.
    }
    apply IHl in H1. rewrite -> H1. reflexivity.
Qed.

Lemma filter_none : forall {X : Type} (l : list X) (test : X -> bool),
  (forall x : X, In x l -> test x = false) -> filter test l = [].
Proof.
  intros.
  induction l.
  - simpl. reflexivity.
  - simpl in H. assert (test x = false). {
      specialize (H x). assert (x = x \/ In x l). { left. reflexivity. }
      apply H in H0. apply H0.
    }
    simpl.
    rewrite -> H0.
    assert (forall x : X, In x l -> test x = false). {
      intros. specialize (H x0). assert (x = x0 \/ In x0 l). { right. apply H1. }
      apply H in H2. apply H2.
    }
    apply IHl in H1. rewrite -> H1. reflexivity.
Qed.

Theorem filter_abstract1 : forall {X : Type} (l a b : list X) (test : X -> bool),
  (forall (x : X), In x a -> test x = true) ->
  (forall (x : X), In x b -> test x = false) ->
  in_order_merge l a b ->
  filter test l = a.
Proof.
  intros.
  generalize dependent a.
  generalize dependent b.
  induction l.
  - intros. inversion H1. 
    + simpl. reflexivity.
    + simpl. reflexivity.
  - intros. inversion H1.
    + rewrite -> H3. apply (filter_all a test). apply H.
    + rewrite -> H4. apply (filter_none b test). apply H0.
    + specialize (IHl b). 
      assert ( forall a : list X,
      (forall x : X, In x a -> test x = true) -> 
      in_order_merge l a b -> filter test l = a). {
        apply IHl. apply H0. } 
      specialize (H7 a0).
      apply IHl in H6. 
      -- assert (test x = true). {
          assert (In x a). {
            rewrite <- H3.
            simpl. left. reflexivity.
          }
          apply H in H8.
          apply H8.
        }
        simpl. rewrite -> H8. rewrite -> H6. reflexivity.
      -- intros x1 E. apply H0 in E. apply E.
      -- intros. assert (In x1 a). { rewrite <- H3. simpl. right. apply H8. }  
         apply H in H9. apply H9.
    + specialize (IHl b0).
      assert (forall a : list X,
      (forall x : X, In x a -> test x = true) ->
      in_order_merge l a b0 -> filter test l = a). {
        apply IHl. intros. assert (In x1 b). {
          rewrite <- H5. simpl. right. apply H7.
        }
        apply H0 in H8. apply H8.
      }
      specialize (H7 a). apply (H7 H) in H6.
      assert (In x b). {
        rewrite <- H5. simpl. left. reflexivity.
      }
      apply H0 in H8.
      simpl.
      rewrite -> H8.
      apply H6.
Qed. 
(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 5 stars, advanced, optional (filter_challenge_2)  *)
(** A different way to characterize the behavior of [filter] goes like
    this: Among all subsequences of [l] with the property that [test]
    evaluates to [true] on all their members, [filter test l] is the
    longest.  Formalize this claim and prove it. *)
Lemma le_ss : forall (a b : nat),
  a <= b -> S a <= S b.
Proof.
  intros.
  induction H.
  - apply le_n.
  -assert (S m <= S (S m)). {
    apply le_S.
    apply le_n.
  }
  apply (le_trans (S a) (S m) (S (S m))).
  + apply IHle.
  + apply H0.
Qed.

Inductive sub_seq {X : Type} : list X -> list X -> Prop :=
| ss_emp : forall (l : list X), sub_seq [] l
| ss_con : forall (n : X) (l1 l2 : list X), sub_seq l1 l2 -> sub_seq (n :: l1) (n :: l2)
| ss_ncon : forall (n : X) (l1 l2 : list X), sub_seq l1 l2 -> sub_seq l1 (n :: l2).

Theorem filter_challenge_2 : forall {X : Type} (l1 l2 : list X) (test : X -> bool),
  (forall x : X, In x l1 -> test x = true) -> 
  (sub_seq l1 l2) ->
  length l1 <= length (filter test l2).
Proof.
  intros.
  generalize dependent l1.
  induction l2.
  - intros. destruct l1.
    + simpl. apply le_n.
    + inversion H0.
  - intros. inversion H0.
    + simpl. induction(length (if test x then x :: filter test l2 else filter test l2)).
      -- apply le_n.
      -- apply le_S. apply IHn.
    + assert (test x = true). {
        assert (In x l1). {
          rewrite <- H2. simpl. left. apply H1.
        }
        apply H in H5. apply H5.
      }
      simpl. rewrite -> H5. simpl. apply le_ss.
      specialize (IHl2 l0).
      apply IHl2.
      -- intros. assert (In x0 l1). {
          rewrite <- H2. simpl. right. apply H6.
         }
         apply H in H7.
         apply H7.
      -- apply H3.
    + specialize (IHl2 l1). apply IHl2 in H.
      -- simpl. destruct (test x).
        ++ simpl. apply (le_trans (length l1) (length (filter test l2)) (S (length (filter test l2)))). apply H.
           apply le_S. apply le_n.
        ++ apply H.
      -- apply H3.
Qed.

  
(** [] *)

(** **** Exercise: 4 stars, optional (palindromes)  *)
(** A palindrome is a sequence that reads the same backwards as
    forwards.

    - Define an inductive proposition [pal] on [list X] that
      captures what it means to be a palindrome. (Hint: You'll need
      three cases.  Your definition should be based on the structure
      of the list; just having a single constructor like

        c : forall l, l = rev l -> pal l

      may seem obvious, but will not work very well.)

    - Prove ([pal_app_rev]) that

       forall l, pal (l ++ rev l).

    - Prove ([pal_rev] that)

       forall l, pal l -> l = rev l.
*)

Inductive pal {X : Type} : list X -> Prop :=
| pal_emp : pal []
| pal_sig : forall (n : X), pal [n]
| pal_con : forall (n : X) (l : list X), pal l -> pal ([n] ++ l ++ [n]).

Theorem pal_app_rev : forall {X : Type} (l : list X),
  pal (l ++ rev l).
Proof.
  intros.
  induction l.
  - simpl. apply pal_emp.
  - simpl. assert ([x] ++ (l ++ rev l) ++ [x] = x :: l ++ rev l ++ [x]). {
      rewrite <- app_assoc. simpl. reflexivity.
    }
    rewrite <- H. apply pal_con. apply IHl.
Qed.

Theorem pal_rev : forall {X : Type} (l : list X),
  pal l -> l = rev l.
Proof.
  intros.
  induction H.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. rewrite -> rev_app_distr. simpl. rewrite <- IHpal. reflexivity.
Qed. 

(** [] *)

(** **** Exercise: 5 stars, optional (palindrome_converse)  *)
(** Again, the converse direction is significantly more difficult, due
    to the lack of evidence.  Using your definition of [pal] from the
    previous exercise, prove that

     forall l, l = rev l -> pal l.
*)

Lemma list_head_tail : forall {X : Type} (l : list X) (n : nat),
  length l = S (S n) -> exists (x1 x2 : X) (l1 : list X), l = [x1] ++ l1 ++ [x2].
Proof.
  intros.
  destruct l.
  - inversion H.
  - inversion H. assert (rev (rev l) = l). { apply rev_involutive. }
    rewrite <- H0 in H1. rewrite <- H0.
    destruct (rev l).
    + simpl in H1. inversion H1.
    + exists x. exists x0. exists (rev l0).
      simpl. reflexivity.
Qed.

Lemma app_r : forall {X : Type} (l1 l2 : list X) (x : X),
  l1 ++ [x] = l2 ++ [x] -> l1 = l2.
Proof.
  intros X l1.
  induction l1.
  - intros. inversion H. destruct l2.
    + reflexivity.
    + inversion H1. destruct l2.
      -- inversion H3.
      -- inversion H3.
  - intros.
    destruct l2.
    + inversion H. destruct l1.
      -- inversion H2.
      -- inversion H2.
    + inversion H. apply IHl1 in H2. rewrite -> H2. reflexivity.
Qed. 

Lemma length_app : forall T (a b : list T),
  length (a ++ b) = length a + length b.
Proof.
  intros.
  induction a.
  - simpl. reflexivity.
  - simpl. rewrite -> IHa. reflexivity.
Qed.

Lemma ss_le : forall (a b : nat),
  S a <= S b -> a <= b.
Proof.
  intros.
  inversion H.
  - apply le_n.
  - assert (a <= S a). { apply le_S. apply le_n. }
    apply (le_trans a (S a) b).
    + apply H2.
    + apply H1.
Qed.

Theorem palindrome_converse_length : forall {X : Type} (n : nat) (l : list X),
  length l <= n -> l = rev l -> pal l.
Proof.
  intros X n.
  induction n.
  - intros. destruct l.
    + apply pal_emp.
    + inversion H.
  - intros. inversion H.
    + destruct n.
      -- destruct l.
        ++ apply pal_emp.
        ++ simpl in H2. inversion H2. destruct l.
            --- apply pal_sig.
            --- inversion H3.
      -- apply list_head_tail in H2. inversion H2. inversion H1. inversion H3.
         assert (x = x0). {
           rewrite -> H4 in H0.
           simpl in H0. rewrite -> rev_app_distr in H0. inversion H0. reflexivity.
         }
         assert (x1 = rev x1). {
           rewrite -> H4 in H0.
           simpl in H0. rewrite -> rev_app_distr in H0. simpl in H0. inversion H0.
           apply app_r in H8. apply H8.
         }
         assert (length x1 <= S n). {
           assert (S (length x1) <= length l). {
             rewrite -> H4. simpl. apply le_ss. rewrite -> length_app. simpl.
             rewrite <- (plus_n_Sm (length x1) 0). apply le_S. rewrite -> plus_0_r. apply le_n.
           }
           apply ss_le.
           apply (le_trans (S (length x1)) (length l) (S (S n))).
           - apply H7.
           - apply H.
         }
         specialize (IHn x1).
         apply IHn in H7.
         ++ rewrite -> H4. rewrite -> H5. apply pal_con. apply H7.
         ++ apply H6.
    + specialize (IHn l). apply IHn in H2.
      ++ apply H2.
      ++ apply H0.
Qed.
      
Theorem palindrome_converse : forall {X : Type} (l : list X),
  l = rev l -> pal l.
Proof.
  intros.
  apply (palindrome_converse_length (length l) l).
  - apply le_n.
  - apply H.
Qed.

(** [] *)

(** **** Exercise: 4 stars, advanced, optional (NoDup)  *)
(** Recall the definition of the [In] property from the [Logic]
    chapter, which asserts that a value [x] appears at least once in a
    list [l]: *)

(* Fixpoint In (A : Type) (x : A) (l : list A) : Prop :=
   match l with
   | [] => False
   | x' :: l' => x' = x \/ In A x l'
   end *)

(** Your first task is to use [In] to define a proposition [disjoint X
    l1 l2], which should be provable exactly when [l1] and [l2] are
    lists (with elements of type X) that have no elements in
    common. *)

Inductive disjoint {X : Type} : list X -> list X -> Prop :=
  | djemp : forall (l : list X), disjoint [ ] l
  | djcon : forall (l1 l2 : list X) (x : X), disjoint l1 l2 -> ~(In x l2) -> disjoint (x :: l1) l2.

(** Next, use [In] to define an inductive proposition [NoDup X
    l], which should be provable exactly when [l] is a list (with
    elements of type [X]) where every member is different from every
    other.  For example, [NoDup nat [1;2;3;4]] and [NoDup
    bool []] should be provable, while [NoDup nat [1;2;1]] and
    [NoDup bool [true;true]] should not be.  *)

Inductive nodup {X : Type} : list X -> Prop :=
  | ndemp : nodup []
  | ndcon : forall (x : X) (l : list X), ~(In x l) -> nodup l -> nodup (x :: l).

(** Finally, state and prove one or more interesting theorems relating
    [disjoint], [NoDup] and [++] (list append).  *)

Theorem intere : forall {X : Type} (l1 l2 : list X),
  nodup l1 -> nodup l2 -> disjoint l1 l2 -> nodup (l1 ++ l2).
Proof.
  intros X l1.
  induction l1.
  - intros. simpl. apply H0.
  - intros. simpl. apply ndcon.
    + rewrite -> in_app_iff. unfold not. intros. destruct H2.
      -- inversion H. apply H5 in H2. inversion H2.
      -- inversion H1. apply H7 in H2. inversion H2.
    + assert (nodup l1). {
        inversion H.
        apply H5.
      }
      assert (disjoint l1 l2). {
        inversion H1. apply H5.
      }
      specialize (IHl1 l2).
      apply IHl1.
      -- apply H2.
      -- apply H0.
      -- apply H3.
Qed.
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (pigeonhole principle)  *)
(** The _pigeonhole principle_ states a basic fact about counting: if
   we distribute more than [n] items into [n] pigeonholes, some
   pigeonhole must contain at least two items.  As often happens, this
   apparently trivial fact about numbers requires non-trivial
   machinery to prove, but we now have enough... *)

(** First prove an easy useful lemma. *)

Lemma in_split : forall (X:Type) (x:X) (l:list X),
  In x l ->
  exists l1 l2, l = l1 ++ x :: l2.
Proof.
  intros.
  induction l.
  - inversion H.
  - inversion H. 
    + exists []. exists l. simpl. rewrite -> H0. reflexivity.
    + apply IHl in H0. inversion H0. inversion H1.
      exists (x0 :: x1). exists x2. simpl. rewrite <- H2. reflexivity.
Qed.

(** Now define a property [repeats] such that [repeats X l] asserts
    that [l] contains at least one repeated element (of type [X]).  *)

Inductive repeats {X:Type} : list X -> Prop :=
  | rep_lst : forall (x : X) (l : list X), repeats l -> repeats (x :: l)
  | rep_con : forall (x : X) (l : list X), In x l -> repeats (x :: l).

(** Now, here's a way to formalize the pigeonhole principle.  Suppose
    list [l2] represents a list of pigeonhole labels, and list [l1]
    represents the labels assigned to a list of items.  If there are
    more items than labels, at least two items must have the same
    label -- i.e., list [l1] must contain repeats.

    This proof is much easier if you use the [excluded_middle]
    hypothesis to show that [In] is decidable, i.e., [forall x l, (In x
    l) \/ ~ (In x l)].  However, it is also possible to make the proof
    go through _without_ assuming that [In] is decidable; if you
    manage to do this, you will not need the [excluded_middle]
    hypothesis. *)

Theorem pigeonhole_principle: forall (X:Type) (l1  l2:list X),
   excluded_middle ->
   (forall x, In x l1 -> In x l2) ->
   length l2 < length l1 ->
   repeats l1.
Proof.
   intros X l1. induction l1 as [|x l1' IHl1'].
   - intros. simpl in H1. inversion H1.
   - intros. assert ((In x l1') \/ ~(In x l1')). {
      apply (H (In x l1')).
     }
     destruct H2.
     + apply rep_con. apply H2.
     + apply rep_lst. assert (In x l2). {
        specialize (H0 x). assert (In x (x :: l1')). {
          simpl. left. reflexivity.
        }
        apply H0 in H3. apply H3.
       }
       assert (exists l0 l1, l2 = l0 ++ x :: l1). {
        apply (in_split X x l2 H3).  
       }
       inversion H4.
       inversion H5.
       specialize (IHl1' (x0 ++ x1)).
       assert (forall x : X, In x l1' -> In x (x0 ++ x1)). {
         intros. assert (In x2 l2). {
           assert (In x2 (x :: l1')). {
             simpl. right. apply H7.
           }
           apply H0 in H8.
           apply H8.
         }
         rewrite -> H6 in H8.
         rewrite -> in_app_iff in H8. destruct H8.
         - rewrite -> in_app_iff. left. apply H8.
         - simpl in H8. destruct H8.
          + rewrite <- H8 in H7. apply H2 in H7. inversion H7.
          + rewrite -> in_app_iff. right. apply H8.
       }
       assert (length (x0 ++ x1) < length l1'). {
         simpl in H1.
         unfold lt in H1. apply ss_le in H1.
         unfold lt. assert (S (length (x0 ++ x1)) <= length l2). {
           rewrite -> H6. 
           rewrite -> length_app.
           rewrite -> length_app.
           simpl. rewrite -> plus_n_Sm. apply le_n.
         }
         apply (le_trans (S (length (x0 ++ x1))) (length l2) (length l1')).
         - apply H8.
         - apply H1.
       }
       apply IHl1'.
       -- apply H.
       -- apply H7.
       -- apply H8.
Qed.
  
(** [] *)


(** $Date: 2016-10-11 14:39:27 -0400 (Tue, 11 Oct 2016) $ *)