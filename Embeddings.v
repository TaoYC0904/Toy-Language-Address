Require Import Toy.Imp Toy.Language.
Require Import Toy.UnifySL.implementation.
Import T.

Module Assertion_Shallow.
Import Denote_Aexp.
Import Denote_Bexp.
Import Denote_Com.

Definition exp {A : Type} (P : A -> Assertion) : Assertion := fun st => exists a, P a st.

Definition inj (b : bexp) : Assertion := fun st => true_set (beval b) st.

Definition eqp (a : aexp) (v : Z) : Assertion := fun st => (aeval a) st = Some v.

Definition safea (a : aexp) : Assertion := fun st => ~ (aeval a) st = None.

Definition safeb (b : bexp) : Assertion := fun st => ~ error_set (beval b) st.

Definition mapsto_ (p : addr) : Assertion := fun st => (exists v, (snd st) p = Some v) /\ (forall p', p <> p' -> (snd st) p' = None).

Definition mapsto (p : addr) (v : Z) : Assertion := fun st => (snd st) p = Some v /\ (forall p', p <> p' -> (snd st) p' = None).

Definition derives : Assertion -> Assertion -> Prop := fun P Q => forall st, P st -> Q st.

Definition store_update (s : store) (X : var) (v : option Z) : store :=
  match v with
  | Some n => fun Y => if (Nat.eq_dec Y X) then n else s Y
  | None => fun Y => 0
  end.

Definition subst (P : Assertion) (X : var) (v : Z) : Assertion :=
  fun st => P (store_update (fst st) X (Some v), snd st).

Definition heap_update (h : heap) (p : addr) (v : option Z) : heap :=
  fun q => if (Z.eq_dec p q) then v else h q.

End Assertion_Shallow.

Module Validity.
Import Assertion_Shallow.
Import Denote_Com.

Definition valid (P : Assertion) (c : com) (Q Rb Rc : Assertion) : Prop :=
  forall st1 st2, P st1 ->
    (~ com_error (ceval c) st1) /\
    (com_normal (ceval c) st1 st2 -> Q st2) /\
    (com_break (ceval c) st1 st2 -> Rb st2) /\
    (com_cont (ceval c) st1 st2 -> Rc st2).

End Validity.

Module tacticforOSA.

Ltac UFsepcon := unfold sepcon in *; 
                 unfold WeakSemantics.WeakSemantics.sepcon in *;
                 unfold SeparationAlgebra.join in *.

Ltac UFjoin := unfold stateJ in *; unfold stateJoin in *;
               unfold OSAGenerators.prod_Join in *;
               unfold SeparationAlgebra.join in *;
               unfold store_join in *;
               unfold OSAGenerators.equiv_Join in *.

Ltac UFheapjoin := unfold heap_join in *;
                   unfold OSAExamples.Heap_Join in *;
                   unfold OSAGenerators.fun_Join in *;
                   unfold SeparationAlgebra.join in *;
                   unfold OSAGenerators.option_Join in *.

Lemma osajoin : forall (st1 st2 st : state), 
  (forall x, @OSAGenerators.option_join Z (@OSAGenerators.trivial_Join Z)
          (snd st1 x) (snd st2 x) (snd st x)) <-> 
  (forall p, (exists v, snd st1 p = Some v /\ snd st2 p = None /\ snd st p = Some v) \/
             (exists v, snd st1 p = None /\ snd st2 p = Some v /\ snd st p = Some v) \/
             (snd st1 p = None ) /\ (snd st2 p = None) /\ (snd st p = None)). 
Proof.
  intros.
  unfold iff; split.
  + intros.
    specialize (H p).
    destruct (snd st1 p), (snd st2 p), (snd st p).
    - inversion H. tauto.
    - inversion H.
    - inversion H. rewrite <- H0.
      left. exists z. tauto.
    - inversion H.
    - inversion H.
      right. left. exists z0. tauto.
    - inversion H.
    - inversion H.
    - right. right. tauto.
  + intros.
    specialize (H x).
    destruct (snd st1 x), (snd st2 x), (snd st x).
    - destruct H as [? | [? | ?]].
      * destruct H as [v [? [? ?]]]. inversion H0.
      * destruct H as [v [? [? ?]]]. inversion H.
      * destruct H as [? [? ?]]. inversion H.
    - destruct H as [? | [? | ?]].
      * destruct H as [v [? [? ?]]]. inversion H0.
      * destruct H as [v [? [? ?]]]. inversion H.
      * destruct H as [? [? ?]]. inversion H.
    - destruct H as [? | [? | ?]].
      * destruct H as [v [? [? ?]]].
        inversion H. inversion H1. subst. constructor.
      * destruct H as [v [? [? ?]]]. inversion H0.
      * destruct H as [? [? ?]]. inversion H.
    - destruct H as [? | [? | ?]].
      * destruct H as [v [? [? ?]]]. inversion H1.
      * destruct H as [v [? [? ?]]]. inversion H.
      * destruct H as [? [? ?]]. inversion H.
    - destruct H as [? | [? | ?]].
      * destruct H as [v [? [? ?]]]. inversion H.
      * destruct H as [v [? [? ?]]]. 
        inversion H0. inversion H1. subst. constructor.
      * destruct H as [? [? ?]]. inversion H0.
    - destruct H as [? | [? | ?]].
      * destruct H as [v [? [? ?]]]. inversion H.
      * destruct H as [v [? [? ?]]]. inversion H1.
      * destruct H as [? [? ?]]. inversion H0.
    - destruct H as [? | [? | ?]].
      * destruct H as [v [? [? ?]]]. inversion H.
      * destruct H as [v [? [? ?]]]. inversion H0.
      * destruct H as [? [? ?]]. inversion H1.
    - destruct H as [? | [? | ?]].
      * destruct H as [v [? [? ?]]]. inversion H.
      * destruct H as [v [? [? ?]]]. inversion H0.
      * constructor.
Qed.

End tacticforOSA.

Module AssertionDerivationRules.
Import Denote_Aexp Denote_Bexp.
Import Assertion_Shallow.
Import tacticforOSA.

Lemma Assertion_eqp_safea : forall P e v,
  derives P (eqp e v) -> 
  derives P (safea e).
Proof.
  unfold derives; intros.
  specialize (H st H0).
  unfold eqp, safea in *.
  unfold not; intros.
  rewrite H1 in H; inversion H.
Qed.

Example true_false_contradiction : forall b s,
  true_set (beval b) s ->
  false_set (beval b) s ->
  False.
Proof.
  induction b; intros.
  + inversion H0.
  + inversion H.
  + simpl in *.
    destruct (aeval a1 s), (aeval a2 s); tauto.
  + simpl in *.
    destruct (aeval a1 s), (aeval a2 s); tauto.
  + simpl in *.
    specialize (IHb s); tauto.
  + simpl in *.
    unfold Sets.intersect, Sets.union in *.
    specialize (IHb1 s); specialize (IHb2 s); tauto.
Qed.

Lemma Assertion_inj_safeb : forall P b,
  (derives P (inj b) \/ derives P (inj (BNot b)))->
  derives P (safeb b).
Proof.
  unfold derives; intros.
  unfold safeb, inj in *.
  unfold not; intros.
  simpl in *.
  assert (forall st, P st -> (true_set (beval b) st) \/ (false_set (beval b) st)).
  { intros; destruct H; specialize (H st0 H2); tauto. }
  clear H. specialize (H2 st H0).
  induction b.
  + inversion H1.
  + inversion H1.
  + destruct H2; simpl in *;
    destruct (aeval a1 st), (aeval a2 st); tauto.
  + destruct H2; simpl in *;
    destruct (aeval a1 st), (aeval a2 st); tauto.
  + simpl in *. tauto.
  + simpl in *. unfold Sets.union, Sets.intersect in *.
    destruct H1 as [? | ?]; destruct H2 as [? | [? | ?]]; try tauto.
    apply (true_false_contradiction b1 st); tauto.
Qed.

Lemma Assertion_add : forall P e1 e2 v1 v2,
  derives P (eqp e1 v1) ->
  derives P (eqp e2 v2) ->
  derives P (eqp (APlus e1 e2) (v1 + v2)).
Proof.
  unfold derives; intros.
  specialize (H st H1).
  specialize (H0 st H1).
  unfold eqp in *.
  simpl. unfold add_sem.
  rewrite H, H0. tauto.
Qed.

Lemma Assertion_sub : forall P e1 e2 v1 v2,
  derives P (eqp e1 v1) ->
  derives P (eqp e2 v2) ->
  derives P (eqp (AMinus e1 e2) (v1 - v2)).
Proof.
  unfold derives; intros.
  specialize (H st H1).
  specialize (H0 st H1).
  unfold eqp in *.
  simpl. unfold sub_sem.
  rewrite H, H0. tauto.
Qed.

Lemma Assertion_mul : forall P e1 e2 v1 v2,
  derives P (eqp e1 v1) ->
  derives P (eqp e2 v2) ->
  derives P (eqp (AMult e1 e2) (v1 * v2)).
Proof.
  unfold derives; intros.
  specialize (H st H1).
  specialize (H0 st H1).
  unfold eqp in *.
  simpl. unfold mul_sem.
  rewrite H, H0. tauto.
Qed.

Lemma Assertion_div : forall P e1 e2 v1 v2,
  derives P (eqp e1 v1) ->
  derives P (eqp e2 v2) ->
  v2 <> 0 ->
  derives P (eqp (ADiv e1 e2) (v1 / v2)).
Proof.
  unfold derives; intros.
  specialize (H st H2).
  specialize (H0 st H2).
  unfold eqp in *.
  simpl. unfold div_sem.
  rewrite H, H0.
  destruct (Z.eq_dec v2 0); tauto.
Qed.

Lemma Assertion_deref : forall P X p v,
  derives P (eqp (AId X) p) ->
  derives P (sepcon (mapsto p v) truep) ->
  derives P (eqp (ADeref (AId X)) v).
Proof.
  unfold derives; intros.
  specialize (H st H1).
  specialize (H0 st H1).
  unfold eqp in *.
  UFsepcon.
  destruct H0 as [st1 [st2 [? [? ?]]]].
  unfold mapsto, truep in *.
  destruct H2; clear H3.
  simpl in *. inversion H.
  unfold deref_sem. rewrite H5.
  assert (snd st p = Some v).
  { UFjoin.
    destruct H0 as [_ ?].
    UFheapjoin.
    rewrite osajoin in H0.
    specialize (H0 p). destruct H0 as [? | [? | ?]].
    + destruct H0 as [v0 [? [? ?]]].
      rewrite H0 in H2. rewrite H2 in H6. tauto.
    + destruct H0 as [v0 [? [? ?]]].
      rewrite H0 in H2; inversion H2.
    + destruct H0 as [? [? ?]].
      rewrite H0 in H2; inversion H2. }
  rewrite H3. tauto.
Qed.

Lemma Assertion_andp_subst : forall P Q X v,
  andp (subst P X v) (subst Q X v) = subst (andp P Q) X v.
Proof.
  intros.
  remember (andp (subst P X v) (subst Q X v)) as P1.
  remember (subst (andp P Q) X v) as P2.
  assert (forall st, P1 st = P2 st).
  { intros. subst P1 P2. unfold andp, subst. tauto. }
  eapply FunctionalExtensionality.functional_extensionality_dep. 
  tauto.
Qed.

Lemma Assertion_orp_subst : forall P Q X v,
  orp (subst P X v) (subst Q X v) = subst (orp P Q) X v.
Proof.
  intros.
  remember (orp (subst P X v) (subst Q X v)) as P1.
  remember (subst (orp P Q) X v) as P2.
  assert (forall st, P1 st = P2 st).
  { intros. subst P1 P2. unfold orp, subst. tauto. }
  eapply FunctionalExtensionality.functional_extensionality_dep. 
  tauto.
Qed.

Lemma Assertion_sepcon_subst : forall P Q X v st,
  sepcon (subst P X v) (subst Q X v) st <-> subst (sepcon P Q) X v st.
Proof.
  intros.
  remember (sepcon (subst P X v) (subst Q X v)) as P1.
  remember (subst (sepcon P Q) X v) as P2.
  unfold iff; split; intros.
  + subst P1 P2. UFsepcon.
    unfold subst. destruct H as [st1 [st2 [? [? ?]]]].
    remember (store_update (fst st1) X (Some v), snd st1) as st1'.
    remember (store_update (fst st2) X (Some v), snd st2) as st2'.
    exists st1', st2'.
    split.
    2:{ split; subst st1' st2'; unfold subst in *; tauto. }
    UFjoin. destruct H as [[? ?] ?].
    split.
    { subst st1' st2'. unfold fst at 1 3 5 7. rewrite H, H2. tauto. }
    UFheapjoin. rewrite osajoin in *. 
    intros. specialize (H3 p).
    destruct H3 as [? | [? | ?]].
    - left.
      destruct H3 as [v0 [? [? ?]]].
      exists v0.
      subst st1' st2'. unfold snd at 1 3 5. tauto.
    - right. left.
      destruct H3 as [v0 [? [? ?]]].
      exists v0.
      subst st1' st2'. unfold snd at 1 3 5. tauto.
    - right. right.
      destruct H3 as [? [? ?]].
      subst st1' st2'. unfold snd at 1 3 5. tauto.
  + subst P1 P2. UFsepcon.
    unfold subst. destruct H as [st1 [st2 [? [? ?]]]].
    remember (store_update (fst st1) X (Some v), snd st1) as st1'.
    remember (store_update (fst st2) X (Some v), snd st2) as st2'.
    admit.
Admitted.

Lemma Assertion_exp_subst : forall {A : Type} (P : A -> Assertion) X v,
  subst (exp P) X v = exp (fun a => subst (P a) X v).
Proof.
  intros.
  remember (subst (exp P) X v) as P1.
  remember (exp (fun a => subst (P a) X v)) as P2.
  assert (forall st, P1 st = P2 st).
  { intros. subst P1 P2. unfold subst, exp. tauto. }
  eapply FunctionalExtensionality.functional_extensionality_dep. 
  tauto.
Qed.

End AssertionDerivationRules.
