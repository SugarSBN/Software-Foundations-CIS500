(** * Typechecking: A Typechecker for STLC *)

(** The [has_type] relation of the STLC defines what it means for a
    term to belong to a type (in some context).  But it doesn't, by
    itself, tell us how to _check_ whether or not a term is well
    typed.

    Fortunately, the rules defining [has_type] are _syntax directed_
    -- that is, for every syntactic form of the language, there is
    just one rule that can be used to give a type to terms of that
    form.  This makes it straightforward to translate the typing rules
    into clauses of a typechecking _function_ that takes a term and a
    context and either returns the term's type or else signals that
    the term is not typable.  *)

(* This short chapter constructs such a function and proves it
   correct. *)

   Require Import Coq.Bool.Bool.
   Require Import Maps.
   Require Import Smallstep.
   Require Import Stlc.
   
   Module STLCChecker.
   Import STLC.
   
   (* ################################################################# *)
   (** * Comparing Types *)
   
   (** First, we need a function to compare two types for equality... *)
   
   Fixpoint beq_ty (T1 T2:ty) : bool :=
     match T1,T2 with
     | TBool, TBool =>
         true
     | TArrow T11 T12, TArrow T21 T22 =>
         andb (beq_ty T11 T21) (beq_ty T12 T22)
     | _,_ =>
         false
     end.
   
   (** ... and we need to establish the usual two-way connection between
       the boolean result returned by [beq_ty] and the logical
       proposition that its inputs are equal. *)
   
   Lemma beq_ty_refl : forall T1,
     beq_ty T1 T1 = true.
   Proof.
     intros T1. induction T1; simpl.
       reflexivity.
       rewrite IHT1_1. rewrite IHT1_2. reflexivity.  Qed.
   
   Lemma beq_ty__eq : forall T1 T2,
     beq_ty T1 T2 = true -> T1 = T2.
   Proof with auto.
     intros T1. induction T1; intros T2 Hbeq; destruct T2; inversion Hbeq.
     - (* T1=TBool *)
       reflexivity.
     - (* T1=TArrow T1_1 T1_2 *)
       rewrite andb_true_iff in H0. inversion H0 as [Hbeq1 Hbeq2].
       apply IHT1_1 in Hbeq1. apply IHT1_2 in Hbeq2. subst...  Qed.
   
   (* ################################################################# *)
   (** * The Typechecker *)
   
   (** The typechecker works by walking over the structure of the given
       term, returning either [Some T] or [None].  Each time we make a
       recursive call to find out the types of the subterms, we need to
       pattern-match on the results to make sure that they are not
       [None].  Also, in the [tapp] case, we use pattern matching to
       extract the left- and right-hand sides of the function's arrow
       type (and fail if the type of the function is not [TArrow T11 T12]
       for some [T1] and [T2]). *)
   
   Fixpoint type_check (Gamma:context) (t:tm) : option ty :=
     match t with
     | tvar x =>
         Gamma x
     | tabs x T11 t12 =>
         match type_check (update Gamma x T11) t12 with
         | Some T12 => Some (TArrow T11 T12)
         | _ => None
         end
     | tapp t1 t2 =>
         match type_check Gamma t1, type_check Gamma t2 with
         | Some (TArrow T11 T12),Some T2 =>
             if beq_ty T11 T2 then Some T12 else None
         | _,_ => None
         end
     | ttrue =>
         Some TBool
     | tfalse =>
         Some TBool
     | tif guard t f =>
         match type_check Gamma guard with
         | Some TBool =>
             match type_check Gamma t, type_check Gamma f with
             | Some T1, Some T2 =>
                 if beq_ty T1 T2 then Some T1 else None
             | _,_ => None
             end
         | _ => None
         end
     end.
   
   (* ################################################################# *)
   (** * Properties *)
   
   (** To verify that this typechecking algorithm is correct, we show
       that it is _sound_ and _complete_ for the original [has_type]
       relation -- that is, [type_check] and [has_type] define the same
       partial function. *)
   
   Theorem type_checking_sound : forall Gamma t T,
     type_check Gamma t = Some T -> has_type Gamma t T.
   Proof with eauto.
     intros Gamma t. generalize dependent Gamma.
     induction t; intros Gamma T Htc; inversion Htc.
     - (* tvar *) eauto.
     - (* tapp *)
       remember (type_check Gamma t1) as TO1.
       remember (type_check Gamma t2) as TO2.
       destruct TO1 as [T1|]; try solve_by_invert;
       destruct T1 as [|T11 T12]; try solve_by_invert.
       destruct TO2 as [T2|]; try solve_by_invert.
       destruct (beq_ty T11 T2) eqn: Heqb;
       try solve_by_invert.
       apply beq_ty__eq in Heqb.
       inversion H0; subst...
     - (* tabs *)
       rename i into y. rename t into T1.
       remember (update Gamma y T1) as G'.
       remember (type_check G' t0) as TO2.
       destruct TO2; try solve_by_invert.
       inversion H0; subst...
     - (* ttrue *) eauto.
     - (* tfalse *) eauto.
     - (* tif *)
       remember (type_check Gamma t1) as TOc.
       remember (type_check Gamma t2) as TO1.
       remember (type_check Gamma t3) as TO2.
       destruct TOc as [Tc|]; try solve_by_invert.
       destruct Tc; try solve_by_invert.
       destruct TO1 as [T1|]; try solve_by_invert.
       destruct TO2 as [T2|]; try solve_by_invert.
       destruct (beq_ty T1 T2) eqn:Heqb;
       try solve_by_invert.
       apply beq_ty__eq in Heqb.
       inversion H0. subst. subst...
   Qed.
   
   Theorem type_checking_complete : forall Gamma t T,
     has_type Gamma t T -> type_check Gamma t = Some T.
   Proof with auto.
     intros Gamma t T Hty.
     induction Hty; simpl.
     - (* T_Var *) eauto.
     - (* T_Abs *) rewrite IHHty...
     - (* T_App *)
       rewrite IHHty1. rewrite IHHty2.
       rewrite (beq_ty_refl T11)...
     - (* T_True *) eauto.
     - (* T_False *) eauto.
     - (* T_If *) rewrite IHHty1. rewrite IHHty2.
       rewrite IHHty3. rewrite (beq_ty_refl T)...
   Qed.
   
   End STLCChecker.
   
   (* ################################################################# *)
   (** * Exercises *)
   
   (** **** Exercise: 5 stars (typechecker_extensions)  *)
   (** In this exercise we'll extend the typechecker to deal with the
       extended features discussed in chapter [MoreStlc].  Your job
       is to fill in the omitted cases in the following. *)
   
   Module TypecheckerExtensions.
   Require Import MoreStlc.
   Import STLCExtended.
     
   Fixpoint beq_ty (T1 T2: ty) : bool :=
     match T1,T2 with
     | TNat, TNat =>
         true
     | TUnit, TUnit =>
         true
     | TArrow T11 T12, TArrow T21 T22 =>
         andb (beq_ty T11 T21) (beq_ty T12 T22)
     | TProd T11 T12, TProd T21 T22 =>
         andb (beq_ty T11 T21) (beq_ty T12 T22)
     | TSum T11 T12, TSum T21 T22 =>
         andb (beq_ty T11 T21) (beq_ty T12 T22)
     | TList T11, TList T21 =>
         beq_ty T11 T21
     | _,_ =>
         false
     end.
   
   Lemma beq_ty_refl : forall T1,
     beq_ty T1 T1 = true.
   Proof.
     intros T1.
     induction T1; simpl;
       try reflexivity;
       try (rewrite IHT1_1; rewrite IHT1_2; reflexivity);
       try (rewrite IHT1; reflexivity).  Qed.
   
   Lemma beq_ty__eq : forall T1 T2,
     beq_ty T1 T2 = true -> T1 = T2.
   Proof.
     intros T1.
     induction T1; intros T2 Hbeq; destruct T2; inversion Hbeq;
       try reflexivity;
       try (rewrite andb_true_iff in H0; inversion H0 as [Hbeq1 Hbeq2];
            apply IHT1_1 in Hbeq1; apply IHT1_2 in Hbeq2; subst; auto);
       try (apply IHT1 in Hbeq; subst; auto).
    Qed.
   
   Fixpoint type_check (Gamma:context) (t:tm) : option ty :=
     match t with
     | tvar x =>
         Gamma x
     | tabs x T11 t12 =>
         match type_check (update Gamma x T11) t12 with
         | Some T12 => Some (TArrow T11 T12)
         | _ => None
         end
     | tapp t1 t2 =>
         match type_check Gamma t1, type_check Gamma t2 with
         | Some (TArrow T11 T12),Some T2 =>
             if beq_ty T11 T2 then Some T12 else None
         | _,_ => None
         end
     | tnat _ =>
         Some TNat
     | tsucc t1 =>
         match type_check Gamma t1 with
         | Some TNat => Some TNat
         | _ => None
         end
     | tpred t1 =>
         match type_check Gamma t1 with
         | Some TNat => Some TNat
         | _ => None
         end
     | tmult t1 t2 =>
         match type_check Gamma t1, type_check Gamma t2 with
         | Some TNat, Some TNat => Some TNat
         | _,_ => None
         end
     | tif0 guard t f =>
         match type_check Gamma guard with
         | Some TNat =>
             match type_check Gamma t, type_check Gamma f with
             | Some T1, Some T2 =>
                 if beq_ty T1 T2 then Some T1 else None
             | _,_ => None
             end
         | _ => None
         end
     | tpair t0 t1 =>
        match type_check Gamma t0 with
        | Some T => match type_check Gamma t1 with
            | Some T1 => Some (TProd T T1)
            | None => None
          end
        | None => None
        end
     | tfst t =>
        match type_check Gamma t with
        | Some (TProd T T1) => Some T
        | _ => None
        end
     | tsnd t =>
        match type_check Gamma t with
        | Some (TProd T T1) => Some T1
        | _ => None
        end
     | tunit => Some TUnit
     | tlet x v t => 
        match type_check Gamma v with
        | None => None
        | Some T => type_check (update Gamma x T) t
        end
     | tinl T2 t1 => 
        match type_check Gamma t1 with
        | None => None
        | Some T => Some (TSum T T2)
        end
     | tinr T1 t2 =>
        match type_check Gamma t2 with
        | None => None
        | Some T => Some (TSum T1 T)
        end
     | tlcase t0 t1 x21 x22 t2 =>
         match type_check Gamma t0 with
         | Some (TList T) =>
             match type_check Gamma t1,
                   type_check (update (update Gamma x22 (TList T)) x21 T) t2 with
             | Some T1', Some T2' =>
                 if beq_ty T1' T2' then Some T1' else None
             | _,_ => None
             end
         | _ => None
         end
     | tcase t0 x t1 y t2 =>
        match type_check Gamma t0 with
        | Some (TSum T1 T2) => 
            match (type_check (update Gamma x T1) t1) with
            | Some T' => match (type_check (update Gamma y T2) t2) with
                | Some T'' => if (beq_ty T' T'' ) then Some T' else None
                | _ => None
                end
            | _ => None
            end
        | _ => None
        end
     | tnil T => Some (TList T)
     | tcons t1 t2 =>
        match type_check Gamma t1 with
        | Some T => 
            match type_check Gamma t2 with
            | Some (TList T1) => if (beq_ty T T1) then Some (TList T) else None
            | _ => None
            end
        | _ => None
        end
     | tfix t =>
        match type_check Gamma t with
        | Some (TArrow T T1) => match (beq_ty T T1) with
            | true => Some T
            | false => None
            end
        | _ => None
        end
     end.
   
   (* Just for fun, we'll do the soundness proof with just a bit more
      automation than above, using these "mega-tactics": *)
   Ltac invert_typecheck Gamma t T :=
     remember (type_check Gamma t) as TO;
     destruct TO as [T|]; 
     try solve_by_invert; try (inversion H0; eauto); try (subst; eauto).
   
   Ltac fully_invert_typecheck Gamma t T T1 T2 :=
     let TX := fresh T in
     remember (type_check Gamma t) as TO;
     destruct TO as [TX|]; try solve_by_invert;
     destruct TX as [T1 T2| | | T1 T2| T1 T2| T1];
     try solve_by_invert; try (inversion H0; eauto); try (subst; eauto).
   
   Ltac case_equality S T :=
     destruct (beq_ty S T) eqn: Heqb;
     inversion H0; apply beq_ty__eq in Heqb; subst; subst; eauto.
   
   Theorem type_checking_sound : forall Gamma t T,
     type_check Gamma t = Some T -> has_type Gamma t T.
   Proof with eauto.
     intros Gamma t. generalize dependent Gamma.
     induction t; intros Gamma T Htc; inversion Htc.
     - (* tvar *) eauto.
     - (* tapp *)
       fully_invert_typecheck Gamma t1 T1 T11 T12.
       invert_typecheck Gamma t2 T2.
       case_equality T11 T2.
     - (* tabs *)
       rename i into x. rename t into T1.
       remember (update Gamma x T1) as Gamma'.
       invert_typecheck Gamma' t0 T0.
     - (* tnat *) eauto.
     - (* tsucc *)
       rename t into t1.
       fully_invert_typecheck Gamma t1 T1 T11 T12.
     - (* tpred *)
       rename t into t1.
       fully_invert_typecheck Gamma t1 T1 T11 T12.
     - (* tmult *)
       fully_invert_typecheck Gamma t1 T1 T11 T12.
       fully_invert_typecheck Gamma t2 T2 T21 T12.
     - (* tif0 *)
       fully_invert_typecheck Gamma t1 T1 T11 T12.
       invert_typecheck Gamma t2 T2.
       invert_typecheck Gamma t3 T3.
       case_equality T2 T3.
     - destruct (type_check Gamma t1) eqn: eq.
        + destruct (type_check Gamma t2) eqn: eq1.
            -- inversion H0. subst. apply T_Pair. apply IHt1. assumption. apply IHt2. assumption.
            -- inversion H0.
        + inversion H0.
     - destruct (type_check Gamma t) eqn: eq.
        + destruct t0; try (inversion H0).
          apply IHt in eq. subst. apply (T_Fst Gamma t T t0_2). assumption.
        + inversion H0.
     - destruct (type_check Gamma t) eqn: eq.
        + destruct t0; try (inversion H0).
          apply (T_Snd Gamma t t0_1 T). apply IHt. subst. assumption.
        + inversion H0.
     - apply T_Unit.
     - destruct (type_check Gamma t1) eqn: eq.
        + apply (T_Let Gamma t1 t i t2 T). apply IHt1. assumption. apply IHt2. assumption.
        + inversion H0.
     - destruct (type_check Gamma t0) eqn: eq.
        + inversion H0. subst. apply (T_Inl Gamma t0 t1). apply IHt. assumption.
        + inversion H0.
     - destruct (type_check Gamma t0) eqn: eq.
        + inversion H0. subst. apply (T_Inr Gamma t0 t). apply IHt. assumption.
        + inversion H0.
     - destruct (type_check Gamma t1) eqn: eq; try (inversion H0).
        destruct t eqn: eq1; try (inversion H0).
        destruct (type_check (update Gamma i t0_1) t2) eqn: eq2; try (inversion H0).
        destruct (type_check (update Gamma i0 t0_2) t3) eqn: eq3; try (inversion H0).
        destruct (beq_ty t0 t4) eqn: eq4; try (inversion H0).
        apply beq_ty__eq in eq4. subst.
        apply (T_Case Gamma t1 i t0_1 t2 i0 t0_2 t3).
        + apply IHt1. assumption.
        + apply IHt2. assumption.
        + apply IHt3. assumption.
     - apply T_Nil.
     - destruct (type_check Gamma t1) eqn: eq; try (inversion H0).
       destruct (type_check Gamma t2) eqn: eq1; try (inversion H0).
       destruct t0 eqn: eq2; try (inversion H0). 
       destruct (beq_ty t t3) eqn: eq3; try (inversion H0). apply beq_ty__eq in eq3.
       subst.
       apply T_Cons. apply IHt1. assumption. apply IHt2. assumption.
     - (* tlcase *)
       rename i into x31. rename i0 into x32.
       fully_invert_typecheck Gamma t1 T1 T11 T12.
       invert_typecheck Gamma t2 T2.
       remember (update (update Gamma x32 (TList T11)) x31 T11) as Gamma'2.
       invert_typecheck Gamma'2 t3 T3.
       case_equality T2 T3.
     - destruct (type_check Gamma t) eqn: eq; try (inversion H0).
       destruct t0 eqn: eq1; try (inversion H0).
       destruct (beq_ty t1_1 t1_2) eqn: eq2; try (inversion H0).
       subst.
       apply T_Fix. apply IHt. apply beq_ty__eq in eq2. subst. assumption.
   Qed.
   
   Theorem type_checking_complete : forall Gamma t T,
     has_type Gamma t T -> type_check Gamma t = Some T.
   Proof.
     intros Gamma t T Hty.
     induction Hty; simpl;
       try (rewrite IHHty);
       try (rewrite IHHty1);
       try (rewrite IHHty2);
       try (rewrite IHHty3);
       try (rewrite (beq_ty_refl T)); 
       try (rewrite (beq_ty_refl T1)); 
       try (rewrite (beq_ty_refl T2)); 
       eauto.
   Qed. 
   End TypecheckerExtensions.
   (** [] *)
   
   (** **** Exercise: 5 stars, optional (stlc_step_function)  *)
   (** Above, we showed how to write a typechecking function and prove it
       sound and complete for the typing relation.  Do the same for the
       operational semantics -- i.e., write a function [stepf] of type
       [tm -> option tm] and prove that it is sound and complete with
       respect to [step] from chapter [MoreStlc]. *)
   
   Module StepFunction.
   Import TypecheckerExtensions.
   Require Import MoreStlc.
   Import STLCExtended.
   Require Import Coq.Bool.Bool.

   Require Import String.

   
   Fixpoint is_value (t : tm) : bool := match t with
   | tabs x T t => true
   | tnat n => true
   | tpair t1 t2 => andb (is_value t1) (is_value t2) 
   | tunit => true
   | tinl T v => is_value v
   | tinr T v => is_value v
   | tnil T => true
   | tcons h t => andb (is_value h) (is_value t)
   | _ => false
   end.

   Fixpoint stepf (t : tm) : option tm := 
    match t with
    | tapp t1 t2 => 
        match is_value t1 with
        | true => 
          match is_value t2 with
          | true =>
            match t1 with
            | (tabs x _ t) => Some ([x := t2] t)
            | _ => None
            end
          | false =>
            match stepf t2 with
            | Some t' => Some (tapp t1 t')
            | _ => None
            end
          end
        | false => 
          match (stepf t1) with
          | Some t' => Some (tapp t' t2)
          | _ => None
          end
        end
    | tsucc t => 
        match t with
        | tnat n => Some (tnat (S n))
        | _ => 
          match stepf t with
          | Some t' => Some (tsucc t')
          | _ => None
          end
        end
    | tpred t =>
        match t with
        | tnat n => Some (tnat (pred n))
        | _ =>
          match stepf t with
          | Some t' => Some (tpred t')
          | _ => None
          end
        end
    | tmult t1 t2 =>
        match t1, t2 with
        | tnat n, tnat m => Some (tnat (n * m))
        | _, _ => 
          match is_value t1 with
          | true =>
            match stepf t2 with
            | Some t2' => Some (tmult t1 t2')
            | _ => None
            end
          | false =>
            match stepf t1 with
            | Some t1' => Some (tmult t1' t2)
            | _ => None
            end
          end
        end
    | tif0 t t1 t2 =>
      match t with
      | tnat 0 => Some t1 
      | tnat (S n) => Some t2
      | _ => 
        match stepf t with
        | Some t' => Some (tif0 t' t1 t2)
        | _ => None
        end
      end
    | tpair t1 t2 =>
      match is_value t1 with
      | true =>
        match stepf t2 with
        | Some t' => Some (tpair t1 t')
        | None => None
        end
      | false => 
        match stepf t1 with
        | Some t' => Some (tpair t' t2)
        | None => None
        end
      end
    | tfst t =>
      match is_value t with
      | true =>
        match t with
        | tpair t1 t2 => Some t1
        | _ => 
          match stepf t with
          | Some t' => Some (tfst t')
          | _ => None
          end
        end
       | false =>
          match stepf t with
          | Some t' => Some (tfst t')
          | _ => None
          end
       end
    | tsnd t =>
      match is_value t with
      | true =>
        match t with
        | tpair t1 t2 => Some t2
        | _ => 
          match stepf t with
          | Some t' => Some (tsnd t')
          | _ => None
          end
        end
      | false =>
          match stepf t with
          | Some t' => Some (tsnd t')
          | _ => None
          end
      end
    | tlet x t t1 =>
      match is_value t with
      | true => Some ([x := t] t1)
      | false => 
        match stepf t with
        | Some t' => Some (tlet x t' t1)
        | _ => None
        end
      end
    | tinl T t =>
      match stepf t with
      | Some t' => Some (tinl T t')
      | _ => None
      end
    | tinr T t =>
      match stepf t with
      | Some t' => Some (tinr T t')
      | _ => None
      end
    | tcase t0 x1 t1 x2 t2 =>
      match t0 with
      | (tinl T v) => 
        match is_value v with
        | true => Some ([x1 := v] t1)
        | false => 
          match stepf t0 with
          | Some t' => Some (tcase t' x1 t1 x2 t2)
          | _ => None
          end
        end
      | (tinr T v) =>
        match is_value v with
        | true => Some ([x2 := v] t2)
        | false => 
          match stepf t0 with
          | Some t' => Some (tcase t' x1 t1 x2 t2)
          | _ => None
          end
        end
      | _ =>
        match stepf t0 with
        | Some t' => Some (tcase t' x1 t1 x2 t2)
        | _ => None
        end
      end
    | tcons h t =>
      match is_value h with
      | true =>
        match stepf t with
        | Some t' => Some (tcons h t')
        | _ => None
        end 
      | false =>
        match stepf h with
        | Some h' => Some (tcons h' t)
        | _ => None
        end
      end
    | tlcase t1 t2 x1 x2 t3 =>
      match t1 with
      | (tnil T) => Some t2
      | (tcons h t) =>
        match is_value h, is_value t with
        | true, true => Some (subst x2 t (subst x1 h t3))
        | _, _ => 
          match stepf t1 with 
          | Some t1' => Some (tlcase t1' t2 x1 x2 t3)
          | _ => None
          end
        end
      | _ =>
        match stepf t1 with 
        | Some t1' => Some (tlcase t1' t2 x1 x2 t3)
        | _ => None
        end
      end
    | tfix t => 
      match t with
      | (tabs x T t1) => Some ([x := (tfix (tabs x T t1))] t1)
      | _ => 
        match stepf t with
        | Some t' => Some (tfix t')
        | _ => None
        end
      end
    | _ => None
    end.
  
   Theorem value_is_value : forall t,
    value t <-> is_value t = true.
   Proof.
     induction t; split; intros; try (inversion H); subst.
     - simpl. reflexivity.
     - apply v_abs.
     - reflexivity.
     - apply v_nat.
     - simpl. apply IHt1 in H2. apply IHt2 in H3. rewrite H2. rewrite H3. reflexivity.
     - destruct (is_value t1) eqn: eq; try (inversion H1).
       destruct (is_value t2) eqn: eq1; try (inversion H1).
       subst. apply IHt1 in H2. apply IHt2 in H1. apply v_pair. assumption. assumption.
     - reflexivity.
     - apply v_unit.
     - simpl. apply IHt in H1. assumption.
     - apply v_inl. apply IHt in H1. assumption.
     - simpl. apply IHt in H1. assumption.
     - apply v_inr. apply IHt in H1. assumption.
     - reflexivity.
     - apply v_lnil.
     - simpl. apply IHt1 in H2. apply IHt2 in H3. rewrite H2. rewrite H3. reflexivity.
     - destruct (is_value t1) eqn: eq; try (inversion H1).
       destruct (is_value t2) eqn: eq1; try (inversion H2).
       apply IHt1 in H1. apply IHt2 in H2.
       apply v_lcons. assumption. assumption.
   Qed.

   Theorem step_stepf : forall t t1,
    (stepf t = Some t1) -> (t ==> t1).
   Proof.
     induction t; intros.
     - inversion H.
     - inversion H.
       destruct (is_value t1) eqn: eq.
       + destruct (is_value t2) eqn: eq1.
         -- destruct t1; try (inversion H1).
            apply ST_AppAbs. apply value_is_value. assumption.
         -- destruct (stepf t2) eqn: eq2.
            inversion H1. apply ST_App2. apply value_is_value. assumption. apply IHt2. reflexivity.
            inversion H1.
       + destruct (stepf t1) eqn: eq1.
         -- inversion H1. apply ST_App1. apply IHt1. reflexivity.
         -- inversion H1.
     - inversion H.
     - inversion H. 
     - inversion H. 
       destruct (stepf t) eqn: eq; try
         (destruct t eqn: eq1; try (inversion H1; apply ST_Succ1; apply IHt; reflexivity);
         inversion H1; subst; apply ST_SuccNat).
     - inversion H.
        destruct (stepf t) eqn: eq; try
         (destruct t eqn: eq1; try (inversion H1; apply ST_Pred; apply IHt; reflexivity);
         inversion H1; subst; apply ST_PredNat).
     - inversion H.
       destruct (stepf t2) eqn: eq; try(
        destruct (stepf t1) eqn: eq1; try(
        destruct (is_value t1) eqn: eq2;
          try(destruct t1 eqn: eq3; try (inversion H1; apply ST_Mult2; try (apply value_is_value; assumption); try (apply IHt2; reflexivity));
             destruct t2 eqn: eq4; try (inversion H1; apply ST_Mult2; try (apply value_is_value; assumption); try (apply IHt2; reflexivity));
             inversion H1; apply ST_MultNats);
          try(destruct t1 eqn: eq3; try (inversion eq2); try (inversion H1; apply ST_Mult1; apply IHt1; reflexivity))
       )).
     - inversion H. destruct (stepf t1) eqn: eq.
      + destruct t1 eqn: eq1; try (inversion H1; apply ST_If01; apply IHt1; reflexivity).
        destruct n.
          -- inversion H1. apply ST_If0Zero.
          -- inversion H1. apply ST_If0Nonzero.
      + destruct t1 eqn: eq1; try (inversion H1).
        destruct n.
        -- inversion H1. apply ST_If0Zero.
        -- inversion H1. apply ST_If0Nonzero.
     - inversion H.
       destruct (is_value t1) eqn: eq.
       + destruct (stepf t2) eqn: eq1; try (inversion H1).
         apply ST_Pair2. apply value_is_value. assumption. apply IHt2. reflexivity.
       + destruct (stepf t1) eqn: eq1; try (inversion H1).
         apply ST_Pair1. apply IHt1. reflexivity.
     - inversion H. 
       destruct (is_value t) eqn: eq.
       + destruct (stepf t) eqn: eq1.
        -- destruct t; try (inversion H1; apply ST_Fst1; apply IHt; reflexivity).
           simpl in eq. inversion H1. 
           apply ST_FstPair; apply value_is_value.
           subst. destruct (is_value t1). reflexivity. inversion eq.
           destruct (is_value t3). reflexivity. destruct (is_value t2); try (inversion eq).
        -- destruct t; try(inversion H1). subst.  simpl in eq.
           apply ST_FstPair; apply value_is_value. 
           subst. destruct (is_value t1). reflexivity. inversion eq.
           destruct (is_value t3). reflexivity. destruct (is_value t1); try (inversion eq).
       + destruct (stepf t); try (inversion H1).
         apply ST_Fst1. apply IHt. reflexivity.
     - inversion H. 
        destruct (is_value t) eqn: eq.
        + destruct (stepf t) eqn: eq1.
          -- destruct t; try (inversion H1; apply ST_Snd1; apply IHt; reflexivity).
            simpl in eq. inversion H1. 
            apply ST_SndPair; apply value_is_value; subst.
            subst. destruct (is_value t2). reflexivity. inversion eq.
            destruct (is_value t1).  reflexivity. destruct (is_value t2); try (inversion eq).
          -- destruct t; try(inversion H1). subst.  simpl in eq.
            apply ST_SndPair; apply value_is_value. 
            subst. destruct (is_value t2). reflexivity. inversion eq.
            destruct (is_value t1). reflexivity. destruct (is_value t2); try (inversion eq).
        + destruct (stepf t); try (inversion H1).
          apply ST_Snd1. apply IHt. reflexivity.
     - inversion H.
     - inversion H.
       destruct (is_value t1) eqn: eq.
       + inversion H1. apply ST_LetValue. apply value_is_value. assumption.
       + destruct (stepf t1) eqn: eq1; try (inversion H1). apply ST_Let1. apply IHt1. reflexivity.
     - inversion H.
       destruct (stepf t0) eqn: eq.
      + inversion H1. apply ST_Inl. apply IHt. reflexivity.
      + inversion H1.
     - inversion H.
       destruct (stepf t0) eqn: eq.
      + inversion H1. apply ST_Inr. apply IHt. reflexivity.
      + inversion H1.
     - inversion H.
      destruct (stepf t1) eqn: eq.
      + destruct t1 eqn: eq1; try (inversion H1; apply ST_Case; apply IHt1; reflexivity).
        -- destruct (is_value t5) eqn: eq2.
          ++ inversion H1. apply ST_CaseInl. apply value_is_value. assumption.
          ++ inversion H1. apply ST_Case. apply IHt1. reflexivity.
        -- destruct (is_value t5) eqn: eq2.
          ++ inversion H1. apply ST_CaseInr. apply value_is_value. assumption.
          ++ inversion H1. apply ST_Case. apply IHt1. reflexivity.
      + destruct t1 eqn: eq1; try (inversion H1).
        -- destruct (is_value t4) eqn: eq2.
          ++ inversion H1. apply ST_CaseInl. apply value_is_value. assumption.
          ++ inversion H1.
        -- destruct (is_value t4) eqn: eq2.
          ++ inversion H1. apply ST_CaseInr. apply value_is_value. assumption.
          ++ inversion H1.
      - inversion H.
      - inversion H.
        destruct (is_value t1) eqn: eq.
        + destruct (stepf t2) eqn: eq1; try (inversion H1).
          apply ST_Cons2. apply value_is_value. assumption. apply IHt2. reflexivity.
        + destruct (stepf t1); try (inversion H1).
          apply ST_Cons1. apply IHt1. reflexivity.
      - inversion H.
        destruct (stepf t1) eqn: eq.
        + destruct t1; try(inversion H1; apply ST_Lcase1; apply IHt1; reflexivity).
          inversion H1. apply ST_LcaseNil.
          destruct (is_value t1_1) eqn: eq1.
          -- destruct (is_value t1_2) eqn: eq2.
            ++ inversion H1. apply ST_LcaseCons. apply value_is_value. assumption. apply value_is_value. assumption.
            ++ inversion H1. apply ST_Lcase1. apply IHt1. reflexivity.
          -- inversion H1. apply ST_Lcase1. apply IHt1. reflexivity.
        + destruct t1; try (inversion H1).
          -- apply ST_LcaseNil.
          -- destruct (is_value t1_1) eqn: eq1.
           ++ destruct (is_value t1_2) eqn: eq2.
            inversion H1. apply ST_LcaseCons. apply value_is_value. assumption. apply value_is_value. assumption.
            inversion H1.
           ++ inversion H1.
      - inversion H.
        destruct (stepf t) eqn: eq.
        + destruct t eqn: eq1; try (inversion H1; apply ST_Fix1; apply IHt; reflexivity).
          inversion H1. apply ST_FixAbs.
        + destruct t; try (inversion H1).
          apply ST_FixAbs.
   Qed.
   
   Lemma value_nf : forall t t1,
    t ==> t1 -> is_value t = false.
   Proof.
     induction t; intros; try (reflexivity).
     - inversion H.
     - inversion H.
     - inversion H.
      + subst. apply IHt1 in H3. simpl. rewrite H3. reflexivity.
      + subst. apply IHt2 in H4. simpl. rewrite H4. destruct (is_value t1); try (reflexivity).
     - inversion H.
     - inversion H. subst. apply IHt in H3. simpl. assumption.
     - inversion H. subst. apply IHt in H3. simpl. assumption.
     - inversion H. 
     - inversion H.
      + subst. apply IHt1 in H3. simpl. rewrite H3. reflexivity.
      + subst. apply IHt2 in H4. simpl. rewrite H4. destruct (is_value t1); try (reflexivity).
    Qed.
   
   Theorem stepf_step : forall t t1,
    (t ==> t1) -> (stepf t = Some t1).
   Proof.
    induction t; intros.
    - inversion H.
    - inversion H.
      + subst. apply value_is_value in H3. simpl. rewrite H3. reflexivity.
      + subst. assert (is_value t1 = false). { apply value_nf in H3. assumption. }
        simpl. rewrite H0. apply IHt1 in H3. rewrite H3. reflexivity.
      + subst. simpl. apply value_is_value in H2. rewrite H2. assert (is_value t2 = false). { apply value_nf in H4. assumption. } 
        rewrite H0. apply IHt2 in H4. rewrite H4. reflexivity.
    - inversion H.
    - inversion H.
    - inversion H.
      + subst. simpl.
        apply IHt in H1. rewrite H1. destruct t; try (reflexivity).
          inversion H1.
      + subst. simpl. reflexivity.
    - inversion H.
      + subst. simpl.
        apply IHt in H1. rewrite H1. destruct t; try (reflexivity).
          inversion H1.
      + subst. simpl. reflexivity.
    - inversion H.
      + subst. assert (is_value t1 = false). { apply value_nf in H3. assumption. }
        simpl. rewrite H0. apply IHt1 in H3. rewrite H3.
        destruct t1; try (reflexivity). destruct t2; try (reflexivity).
        inversion H3.
      + subst. apply value_is_value in H2. simpl. rewrite H2. apply IHt2 in H4.
        rewrite H4. destruct t1; try (reflexivity). destruct t2; try (reflexivity).
        inversion H4.
      + subst. simpl. reflexivity.
    - inversion H; subst.
      + assert (is_value t1 = false). { apply value_nf in H4. assumption. }
        simpl. apply IHt1 in H4. rewrite H4.
        destruct t1; try (reflexivity). inversion H4.
      + simpl. reflexivity.
      + simpl. reflexivity.
    - inversion H; subst.
      + simpl. assert (is_value t1 = false). { apply value_nf in H3. assumption. }
        rewrite H0. apply IHt1 in H3. rewrite H3. reflexivity.
      + apply value_is_value in H2. simpl. rewrite H2.
        apply IHt2 in H4. rewrite H4. reflexivity.
    - inversion H; subst.
      + assert (is_value t = false). { apply value_nf in H1. assumption. } 
        simpl. rewrite H0. apply IHt in H1. rewrite H1. reflexivity.
      + apply value_is_value in H1. apply value_is_value in H2.
        simpl. rewrite H1. rewrite H2. simpl. reflexivity.
    - inversion H; subst.
      + assert (is_value t = false). { apply value_nf in H1. assumption. } 
        simpl. rewrite H0. apply IHt in H1. rewrite H1. reflexivity.
      + apply value_is_value in H1. apply value_is_value in H2.
        simpl. rewrite H1. rewrite H2. simpl. reflexivity.
    - inversion H.
    - inversion H; subst.
      + assert (is_value t1 = false). { apply value_nf in H4. assumption. }
        simpl. rewrite H0. apply IHt1 in H4. rewrite H4. reflexivity.
      + apply value_is_value in H4. simpl. rewrite H4. reflexivity.
    - inversion H. subst. simpl. apply IHt in H3. rewrite H3. reflexivity.
    - inversion H. subst. apply IHt in H3. simpl. rewrite H3. reflexivity.
    - inversion H; subst.
      + simpl. destruct t1 eqn: eq; try ( apply IHt1 in H6; rewrite H6; reflexivity).
        -- inversion H6. subst. assert (is_value t0 = false). { apply value_nf in H3. assumption. }
           rewrite H0. apply IHt1 in H6. rewrite H6. reflexivity.
        -- inversion H6. subst. assert (is_value t0 = false). { apply value_nf in H3. assumption. }
           rewrite H0. apply IHt1 in H6. rewrite H6. reflexivity.
      + simpl. apply value_is_value in H6. rewrite H6. reflexivity.
      + simpl. apply value_is_value in H6. rewrite H6. reflexivity.
    - inversion H.
    - inversion H; subst.
      + assert (is_value t1 = false). { apply value_nf in H3. assumption. }
        simpl. rewrite H0. apply IHt1 in H3. rewrite H3. reflexivity.
      + simpl. apply value_is_value in H2. rewrite H2. apply IHt2 in H4. rewrite H4.
        reflexivity.
    - inversion H; subst.
      + simpl. 
        assert (stepf t1 = Some t1'). { apply IHt1 in H6. assumption. }
        destruct (stepf t1) eqn: eq; try (inversion H0).
        subst.
        destruct t1 eqn: eq1; try (inversion H6; reflexivity).
        destruct (is_value t4) eqn: eq2; try (reflexivity).
        destruct (is_value t5) eqn: eq3; try (reflexivity).
        apply value_nf in H6. simpl in H6.
        rewrite eq2 in H6. rewrite eq3 in H6. inversion H6.
      + simpl. reflexivity.
      + apply value_is_value in H6. apply value_is_value in H7. simpl.
        rewrite H6. rewrite H7. reflexivity.
    - inversion H.
      + subst. simpl.
        assert (stepf t = Some t'). { apply IHt. assumption. }
        rewrite H0.
        destruct t; try (reflexivity).
        inversion H1.
      + simpl. reflexivity.
    Qed.

    Theorem equiv_step_stepf : forall t t1,
     (t ==> t1) <-> (stepf t = Some t1).
    Proof.
      split.
      apply stepf_step.
      apply step_stepf.
    Qed.

    End StepFunction.
   (** [] *)
   
   (** **** Exercise: 5 stars, optional (stlc_impl)  *)
   (** Using the Imp parser described in the [ImpParser] chapter as
       a guide, build a parser for extended Stlc programs.  Combine it
       with the typechecking and stepping functions from above to yield a
       complete typechecker and interpreter for this language. *)
   
   Module StlcImpl.
   Import StepFunction.
   
   (*
    I would rather write parser in C++...
    So this part is neglected 
   *)

   End StlcImpl.
   (** [] *)
   
   (** $Date: 2016-12-01 22:35:27 -0500 (Thu, 01 Dec 2016) $ *)