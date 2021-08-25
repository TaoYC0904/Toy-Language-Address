Require Import ZArith.
Require Import QArith.
Require Import Toy.lib.
Require Import Toy.type.
Require Import Toy.UnifySL.implementation.
Require Import Toy.Language.
Require Import Toy.Embeddings.
Open Scope Z.
Import T.
Import Denote_Aexp Denote_Bexp Denote_Term Denote_Assertion_D Denote_Com.
Import Assertion_Shallow Validity tactics.

Module BasicRulesSound.

Theorem consequence_rule_sound : forall P P' c Q Q' Rb Rb' Rc Rc',
  derives P P' ->
  valid P' c Q' Rb' Rc' ->
  derives Q' Q ->
  derives Rb' Rb ->
  derives Rc' Rc ->
  valid P c Q Rb Rc.
Proof.
  unfold derives, valid; intros.
  specialize (H st1 H4).
  specialize (H0 st1 st2 H). destruct H0 as [? [? [? ?]]].
  split; try split; try split; unfold not; intros.
  + tauto.
  + exact (H1 st2 (H5 H8)).
  + exact (H2 st2 (H6 H8)).
  + exact (H3 st2 (H7 H8)).
Qed.

Theorem skip_rule_sound : forall P, valid P CSkip P falsep falsep.
Proof.
  unfold valid; intros.
  split; try split; try split; simpl; try tauto.
  unfold BinRel.id. intros; subst; tauto.
Qed.

Theorem break_rule_sound : forall P, valid P CBreak falsep P falsep.
Proof.
  unfold valid; intros.
  split; try split; try split; simpl; try tauto.
  unfold BinRel.id; intros; subst; tauto.
Qed.

Theorem cont_rule_sound : forall P, valid P CCont falsep falsep P.
Proof.
  unfold valid; intros.
  split; try split; try split; simpl; try tauto.
  unfold BinRel.id; intros; subst; tauto.
Qed.

Theorem if_rule_sound : forall P Q Rb Rc b c1 c2,
  valid (andp P (inj b)) c1 Q Rb Rc ->
  valid (andp P (inj (BNot b))) c2 Q Rb Rc ->
  valid (andp P (safeb b)) (CIf b c1 c2) Q Rb Rc.
Proof.
  unfold valid, andp, inj, safeb; intros.
  specialize (H st1 st2). specialize (H0 st1 st2).
  split; try split; try split.
  + unfold not; intros.
    simpl in H2. unfold Sets.union, Sets.intersect in H2.
    tauto.
  + simpl; intros.
    unfold BinRel.union, BinRel.concat, BinRel.testrel in H2.
    destruct H2 as [[st1' ?] | [st1' ?]]; destruct H2 as [[? ?] ?];
    subst; tauto.
  + simpl; intros.
    unfold BinRel.union, BinRel.concat, BinRel.testrel in H2.
    destruct H2 as [[st1' ?] | [st1' ?]]; destruct H2 as [[? ?] ?];
    subst; tauto.
  + simpl; intros.
    unfold BinRel.union, BinRel.concat, BinRel.testrel in H2.
    destruct H2 as [[st1' ?] | [st1' ?]]; destruct H2 as [[? ?] ?];
    subst; tauto.
Qed.

Theorem for_rule_sound : forall P P' Q c ci,
  valid P c P' Q P' ->
  valid P' ci P falsep falsep ->
  valid P (CFor c ci) Q falsep falsep.
Proof.
  unfold valid; intros.
  split.
  { unfold not; intros. simpl in H2.
    unfold Sets.omega_union in H2.
    destruct H2 as [n ?].
    revert st1 H1 H2; induction n; intros.
    + simpl in *. unfold Sets.union, BinRel.dia in H2.
      destruct H2 as [? | [st' [? ?]]].
      - specialize (H st1 st2 H1); tauto.
      - specialize (H st1 st' H1); destruct H as [? [? [? ?]]].
        specialize (H0 st' st2 (H4 H2)); tauto.
    + simpl in H2. unfold BinRel.dia, BinRel.union, BinRel.concat in H2.
      destruct H2 as [st3 [[? | ? ] ?]].
      - destruct H2 as [st4 [? ?]].
        specialize (H st1 st4 H1). destruct H as [? [? [? ?]]].
        specialize (H0 st4 st3 (H5 H2)). 
        specialize (IHn st3). tauto.
      - destruct H2 as [st4 [? ?]].
        specialize (H st1 st4).
        specialize (H0 st4 st3).
        specialize (IHn st3). tauto. }
  split.
  { simpl; intros.
    unfold BinRel.omega_union in H2.
    destruct H2 as [n ?].
    revert st1 H1 H2; induction n; intros.
    + simpl in H2. unfold BinRel.union, BinRel.concat in H2.
      destruct H2 as [? | [st' [? ?]]].
      - specialize (H st1 st2); tauto.
      - specialize (H st1 st').
        specialize (H0 st' st2); tauto.
    + simpl in H2. unfold BinRel.concat, BinRel.union in H2.
      destruct H2 as [st3 [[? | ?] ?]];
      destruct H2 as [st4 [? ?]];
        specialize (H st1 st4);
        specialize (H0 st4 st3);
        specialize (IHn st3); tauto. }
  simpl; tauto.
Qed.

Theorem set_rule_sound : forall P e v X,
  derives P (eqp e v) ->
  valid P (CSet X e) (andp (eqp (AId X) v) (exp (subst P X))) falsep falsep.
Proof.
  unfold valid, derives. intros.
  split.
  { unfold not; intros.
    simpl in H1.
    specialize (H st1 H0). unfold eqp in H.
    rewrite H in H1; inversion H1. }
  split.
  { intros.
    specialize (H st1 H0).
    simpl in H1; rewrite H in H1. destruct H1.
    split.
    + unfold eqp; simpl. rewrite H1; tauto.
    + unfold exp, subst.
      exists (fst st1 X).
      remember (store_update (fst st2) X (Some (fst st1 X))) as s1'.
      assert (forall Y, fst st1 Y = s1' Y).
      { intros. subst s1'.
        unfold store_update.
        destruct (Nat.eq_dec Y X).
        + rewrite e0; tauto.
        + destruct H2. specialize (H2 Y n). rewrite H2; tauto. }
      assert (fst st1 = s1').
      { eapply FunctionalExtensionality.functional_extensionality_dep. tauto. }
      rewrite <- H4. destruct st1. 
      destruct H2. rewrite H5. unfold fst, snd; tauto. }
  simpl; tauto.
Qed.

Lemma andjoin : forall e v st1 st2 st,
  aeval e st1 = Some v ->
  stateJ st1 st2 st ->
  aeval e st = Some v.
Proof.
  intros.
  unfold stateJ in *.
  unfold OSAGenerators.prod_Join in H0.
  unfold SeparationAlgebra.join in H0.
  destruct H0.
  unfold storeJ in H0.
  unfold OSAGenerators.equiv_Join in H0.
  destruct H0.
  revert v H; induction e; simpl in *; intros.
  + tauto.
  + rewrite <- H0; tauto.
  + unfold add_sem in *.
    destruct (aeval e1 st1), (aeval e2 st1); try inversion H.
    specialize (IHe1 z). specialize (IHe2 z0).
    assert (aeval e1 st = Some z). tauto.
    assert (aeval e2 st = Some z0). tauto.
    rewrite H3, H5. tauto.
  + unfold sub_sem in *.
    destruct (aeval e1 st1), (aeval e2 st1); try inversion H.
    specialize (IHe1 z). specialize (IHe2 z0).
    assert (aeval e1 st = Some z). tauto.
    assert (aeval e2 st = Some z0). tauto.
    rewrite H3, H5. tauto.
  + unfold mul_sem in *.
    destruct (aeval e1 st1), (aeval e2 st1); try inversion H.
    specialize (IHe1 z). specialize (IHe2 z0).
    assert (aeval e1 st = Some z). tauto.
    assert (aeval e2 st = Some z0). tauto.
    rewrite H3, H5. tauto.
  + unfold div_sem in *.
    destruct (aeval e1 st1), (aeval e2 st1); try inversion H.
    specialize (IHe1 z). specialize (IHe2 z0).
    assert (aeval e1 st = Some z). tauto.
    assert (aeval e2 st = Some z0). tauto.
    rewrite H3, H5. tauto.
  + unfold deref_sem in *.
    destruct (aeval e st1); [| inversion H]. rename z into p.
    assert (aeval e st = Some p). { apply IHe. tauto. }
    rewrite H3.
    assert (exists x, snd st1 p = Some x).
    { destruct (snd st1 p); [| inversion H]. exists s; tauto. }
    destruct H4 as [x ?].
    rewrite H4 in H.
    ufHeapj H1.
    specialize (H1 p).
    Print ufoptionj.
    pose proof (ufoptionj _ (snd st1 p)).
    rewrite ufoptionj in H1.

 
  
  
  
  admit.
Admitted.


Theorem hoare_store_sound : forall P e1 e2 p v,
  derives P (andp (eqp e1 p) (eqp e2 v)) ->
  valid (sepcon P (mapsto_ p)) (CStore e1 e2) (sepcon P (mapsto p v)) falsep falsep.
Proof.
  unfold derives, valid; intros.
  split. unfold sepcon, SepCon in *.
  destruct H0 as [st11 [st12 [? [? ?]]]].
  { unfold not; intros.
    simpl in H1.
    specialize (H st11 H0).
    unfold andp, eqp in H.



