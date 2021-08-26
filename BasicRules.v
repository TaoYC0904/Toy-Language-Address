Require Import ZArith.
Require Import QArith.
Require Import Toy.lib.
Require Import Toy.type.
Require Import Toy.UnifySL.implementation.
Require Import Toy.Language.
Require Import Toy.Embeddings.
Require Import Coq.micromega.Psatz.
Require Import Lqa.
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

Lemma andjoin1 : forall e v st1 st2 st,
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
    pose proof (ufoptionj QZandLock_Join (snd st1 p) (snd st2 p) (snd st p)).
    rewrite H5 in H1; clear H5.
    destruct H1 as [? | [? | [? | ?]]].
    - destruct H1 as [? [? ?]]. rewrite H4 in H1; inversion H1.
    - destruct H1 as [x' [? [? ?]]]. rewrite H4 in H1; inversion H1.
    - destruct H1 as [x' [? [? ?]]]. 
      rewrite H4 in H1; inversion H1; subst x'.
      rewrite H6, H. tauto.
    - rename x into x1.
      destruct H1 as [x1' [x2 [x [? [? [? ?]]]]]].
      rewrite H4 in H1; inversion H1; subst x1'. rewrite H6.
      unfold QZandLock_Join in H7.
      rewrite ufsumj in H7. destruct H7.
      2:{ destruct H7 as [xr1 [xr2 [xr [? [? [? ?]]]]]].
        rewrite H7 in H. inversion H. }
      destruct H7 as [xr1 [xr2 [xr [? [? [? ?]]]]]].
      rewrite H7 in H. rewrite H9.
      unfold QZ_Join in H10.
      unfold OSAGenerators.prod_Join in H10.
      destruct H10.
      unfold SeparationAlgebra.join in H11.
      unfold Z_Join in H11.
      unfold OSAGenerators.equiv_Join in H11.
      destruct H11.
      destruct xr1 as (q1, v1).
      destruct xr as (q0, v0).
      unfold snd in H11. rewrite <-H11.
      unfold SeparationAlgebra.join in H10.
      unfold Q_Join in H10. unfold fst in H10.
      destruct (Qlt_le_dec 0 q1). 2:{ lra. }
      destruct (Qlt_le_dec 0 q0). 2:{ lra. }
      tauto.
Qed.

Theorem hoare_store_sound : forall P e1 e2 p v,
  derives P (andp (eqp e1 p) (eqp e2 v)) ->
  valid (sepcon P (fullper p)) (CStore e1 e2) (sepcon P (mapsto p v)) falsep falsep.
Proof.
  unfold derives, valid. intros.
  unfold andp in H.
  ufSepcon H0. destruct H0 as [st11 [st12 [? [? ?]]]].
  split.
  { unfold not; intros.
    simpl in H3.
    pose proof H st11 H0.
    unfold eqp in H4. destruct H4.
    pose proof (andjoin1 e1 p st11 st12 st1 H4 H2).
    rewrite H6 in H3.
    pose proof (andjoin1 e2 v st11 st12 st1 H5 H2).
    rewrite H7 in H3.
    assert (exists x, snd st1 p = Some x).
    { ufStatej H2. destruct H2.
      ufHeapj H8. specialize (H8 p). rewrite ufoptionj in H8.
      unfold fullper in H1. destruct H1.
      destruct H1 as [z ?].
      destruct H8 as [? | [? | [? | ?]]].
      + destruct H8 as [? [? ?]]. rewrite H10 in H1. inversion H1.
      + destruct H8 as [x [? [? ?]]]. exists x; tauto.
      + destruct H8 as [x [? [? ?]]]. rewrite H10 in H1; inversion H1.
      + destruct H8 as [x1 [x2 [x [? [? [? ?]]]]]].
        exists x; tauto. }
    destruct H8 as [x ?].
    rewrite H8 in H3.
    unfold fullper in H1. destruct H1 as [[z ?] ?].
    assert (snd st1 p = Some (inl (1%Q, z))).
    { ufStatej H2. destruct H2.
      ufHeapj H10. specialize (H10 p). rewrite ufoptionj in H10.
      destruct H10 as [? | [? | [? | ?]]].
      + destruct H10 as [? [? ?]]. rewrite H11 in H1. inversion H1.
      + destruct H10 as [x' [? [? ?]]]. rewrite H11 in H1. inversion H1. 
        rewrite H1 in H12. tauto.
      + destruct H10 as [x' [? [? ?]]]. rewrite H11 in H1. inversion H1.
      + destruct H10 as [x1 [x2 [x' [? [? [? ?]]]]]].
        unfold QZandLock_Join in H13. rewrite ufsumj in H13.
        destruct H13. 2:{
        destruct H13 as [xr1 [xr2 [xr [? [? [? ?]]]]]].
        rewrite H11 in H1. rewrite H14 in H1. inversion H1. }
        destruct H13 as [xl1 [xl2 [xl [? [? [? ?]]]]]].
        rewrite H11 in H1. rewrite H14 in H1. inversion H1.
        unfold QZ_Join in H16. 
        unfold OSAGenerators.prod_Join in H16.
        destruct H16.
        unfold SeparationAlgebra.join in H16, H17.
        unfold Q_Join in H16. unfold Z_Join in H17.
        unfold OSAGenerators.equiv_Join in H17.
        destruct H17.
        destruct xl as (q', z'). simpl in H16, H17, H19.
        rewrite H18 in H19. simpl in H19. subst z'.
        rewrite <-H19 in H15.
        rewrite H18 in H16. simpl in H16.
        assert (q' == 1). {lra. }
        rewrite H12. rewrite H15. lra. }
    rewrite H8 in H10. inversion H10.
    rewrite H12 in H3. lra. }
  split.
  { intros. 
    pose proof (H st11 H0).
    unfold eqp in H4; destruct H4.
    assert (aeval e1 st1 = Some p).
    { eapply andjoin1; [exact H4 | exact H2]. }
    assert (aeval e2 st1 = Some v).
    { eapply andjoin1; [exact H5 | exact H2]. }
    ufsepcon. 
    remember (fst st12, heap_update (snd st12) p (Some v)) as st22.
    exists st11, st22.
    split; try tauto. split.
    { unfold mapsto. unfold fullper in H1.
      destruct H1 as [[v' ?] ?].
      split.
      + subst st22. unfold snd at 1.
        unfold heap_update. destruct (Z.eq_dec p p); try tauto.
        exists 1%Q. rewrite H1. tauto.
      + subst st22. intros.
        unfold snd at 1. unfold heap_update.
        destruct (Z.eq_dec p' p); try tauto.
        exact (H8 p' n). }
    simpl in H3; rewrite H6, H7 in H3.
    remember (snd st1 p) as s'.
    destruct (s'); try tauto.
    destruct s; try tauto.
    destruct p0 as (q1, z1).
    remember (snd st2 p) as s''.
    destruct s''; try tauto.
    destruct s; try tauto.
    destruct p0 as (q2, z2).
    destruct H3 as [? [? [? [? ?]]]].
    ufstatej. ufStatej H2.
    unfold SeparationAlgebra.join in H2.
    destruct H2.
    split.
    { subst st22. unfold fst at 2. rewrite <-H11. tauto. }
    ufheapj. ufHeapj H12.
    intros pp. specialize (H12 pp).
    rewrite ufoptionj in *. destruct H12 as [? | [? | [? | ?]]].
    + left. split; try tauto. destruct H12 as [? [? ?]].
      subst st22. unfold heap_update.  unfold snd at 1.
      destruct (Z.eq_dec pp p).
      - subst pp. rewrite H14 in Heqs'. inversion Heqs'.
      - specialize (H10 pp n). rewrite H10. tauto.
    + right; left.  destruct H12 as [vv [? [? ?]]].
      subst st22. unfold snd at 2. unfold heap_update.
      destruct (Z.eq_dec pp p).
      - subst pp.
        unfold fullper in H1. destruct H1.
        destruct H1 as [v' ?].
        rewrite H1. exists (inl (1%Q, v)).
        split; try split; try tauto.
        rewrite <-Heqs''. rewrite H9. 
        rewrite H8. tauto.
      - exists vv.
        specialize (H10 pp n). rewrite H10. tauto.
    + right; right; left. destruct H12 as [vv [? [? ?]]].
      subst st22. unfold snd at 2. unfold heap_update.
      destruct (Z.eq_dec pp p).
      - subst pp.
        unfold fullper in H1. destruct H1 as [[v' ?] ?].
        rewrite H13 in H1. inversion H1.
      - exists vv.
        specialize (H10 pp n). rewrite H10. tauto.
    + right; right; right. 
      destruct H12 as [vv1 [vv2 [vv [? [? [? ?]]]]]].
      subst st22. unfold heap_update.
      unfold snd at 2. destruct (Z.eq_dec pp p).
      - subst pp. rewrite H13.
        unfold QZandLock_Join in *. rewrite ufsumj in H15.
        destruct H15.
        2:{ destruct H15 as [? [? [? [? [? [? ?]]]]]]. 
            rewrite H17 in H14. rewrite H14 in Heqs'. inversion Heqs'. }
        destruct H15 as [vl1 [vl2 [vl [? [? [? ?]]]]]].
        subst vv1 vv2 vv. 
        destruct vl1 as (qq1, qz1).
        destruct vl2 as (qq2, qz2).
        rewrite H14 in Heqs'. inversion Heqs'. subst vl.
        subst. clear Heqs'.
        exists (inl (qq1, z1)), (inl (qq2, z1)), (inl (1%Q, z1)).
        unfold QZ_Join in H18. unfold OSAGenerators.prod_Join in H18.
        unfold SeparationAlgebra.join in H18.
        destruct H18. unfold Z_Join in H8. unfold OSAGenerators.equiv_Join in H8.
        destruct H8. inversion H8. inversion H9. unfold snd in H15, H16. subst.
        split.
        { rewrite H12. tauto. }
        split.
        { rewrite H} 



        repeat eexists. exact H12. rewrite Heqs''. tauto.
        rewrite ufsumj. left.
        eexists. eexists. eexists.
        split; [tauto |]. split; [tauto |]. split; [tauto |].
        unfold QZ_Join in *. unfold OSAGenerators.prod_Join in *.
        unfold fst, snd in H18. unfold SeparationAlgebra.join in H18.
        split. 2:{
        unfold SeparationAlgebra.join, snd.
        unfold Z_Join. unfold OSAGenerators.equiv_Join.
        destruct H18. unfold Z_Join in H16. unfold OSAGenerators.equiv_Join in H16.
        subst. split; try tauto.

          


    





      

