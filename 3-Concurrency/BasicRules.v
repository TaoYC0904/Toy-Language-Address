Require Import ZArith.
Require Import QArith.
Require Import Toy.CC.lib.
Require Import Toy.CC.type.
Require Import Toy.CC.usl.implementation.
Require Import Toy.CC.Language.
Require Import Toy.CC.Embeddings.
Require Import Coq.micromega.Psatz.
Require Import Lqa.
Open Scope Z.
Import T.
Import Denote_Aexp Denote_Bexp Denote_Term Denote_Assertion_D Denote_Com.
Import Assertion_Shallow Validity tactics Deep_Shallow.

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

Theorem store_rule_sound : forall P e1 e2 p v,
  derives P (andp (eqp e1 p) (eqp e2 v)) ->
  valid (sepcon P (mapsto_ p 1%Q)) (CStore e1 e2) (sepcon P (mapsto p 1%Q v)) falsep falsep.
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
      unfold mapsto_ in H1. destruct H1.
      destruct H1 as [z ?].
      destruct H8 as [? | [? | [? | ?]]].
      + destruct H8 as [? [? ?]]. rewrite H10 in H1. inversion H1.
      + destruct H8 as [x [? [? ?]]]. exists x; tauto.
      + destruct H8 as [x [? [? ?]]]. rewrite H10 in H1; inversion H1.
      + destruct H8 as [x1 [x2 [x [? [? [? ?]]]]]].
        exists x; tauto. }
    destruct H8 as [x ?].
    rewrite H8 in H3.
    unfold mapsto_ in H1. destruct H1 as [[z ?] ?].
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
    ufsepcon. specialize (H st11 H0). unfold eqp in H. destruct H.
    assert (aeval e1 st1 = Some p).
    { eapply andjoin1; [exact H | exact H2]. }
    assert (aeval e2 st1 = Some v).
    { eapply andjoin1; [exact H4 | exact H2]. }
    simpl in H3. rewrite H5, H6 in H3.
    remember (snd st1 p) as h1p.
    destruct h1p; [| inversion H3].
    destruct s; [| inversion H3].
    rename p0 into h1p. destruct h1p as (h1pq, h1pz).
    remember (snd st2 p) as h2p.
    destruct h2p; [| inversion H3].
    destruct s; [| inversion H3].
    rename p0 into h2p. destruct h2p as (h2pq, h2pz).
    destruct H3 as [? [? [? [? ?]]]]. subst.
    unfold mapsto_ in H1. destruct H1 as [[h1pz' ?] ?].
    remember (heap_update (snd st12) p (Some v)) as h22.
    remember (fst st12, h22) as st22.
    exists st11, st22.
    split; [tauto |].
    assert (mapsto p 1%Q v st22).
    { unfold mapsto. split.
      + subst st22 h22. unfold snd at 1, heap_update.
        destruct (Z.eq_dec p p); try tauto.
        rewrite H1. tauto.
      + intros.
        subst st22 h22. unfold snd at 1, heap_update.
        destruct (Z.eq_dec p' p); try tauto.
        exact (H3 p' n). }
    rename H7 into H77.
    split; [exact H77 |].
    ufstatej. ufStatej H2. destruct H2.
    split.
    { ufStorej H2. ufstorej.
      subst. unfold fst at 3. rewrite <-H10. tauto. }
    ufheapj. ufHeapj H7.
    intros pp. specialize (H7 pp).
    rewrite ufoptionj in *.
    destruct H7 as [? | [? | [? | ?]]].
    + left.
      destruct H7 as [? [? ?]].
      subst. unfold snd at 2, heap_update.
      destruct (Z.eq_dec pp p).
      - subst. rewrite H8 in H1; inversion H1.
      - specialize (H9 pp n); rewrite H9; tauto.
    + right; left.
      destruct H7 as [vv [? [? ?]]].
      subst. unfold snd at 2, heap_update.
      destruct (Z.eq_dec pp p).
      - subst pp. rewrite H8.
        rewrite H8 in H1; inversion H1. 
        subst. rewrite <-Heqh2p.
        exists (inl (1%Q, v)). tauto.
      - specialize (H9 pp n); rewrite H9.
        exists vv. tauto.
    + right; right; left.
      destruct H7 as [vv [? [? ?]]].
      subst. unfold snd at 2, heap_update.
      destruct (Z.eq_dec pp p).
      - subst pp. rewrite H1 in H8. inversion H8.
      - specialize (H9 pp n); rewrite H9.
        exists vv. tauto.
    + right; right; right.
      destruct H7 as [vv1 [vv2 [vv [? [? [? ?]]]]]].
      subst. unfold snd at 2, heap_update.
      destruct (Z.eq_dec pp p).
      - subst pp. rewrite H8.
        destruct vv2.
        2:{ unfold QZandLock_Join in H12. rewrite ufsumj in H12.
          destruct H12; destruct H12 as [? [? [? [? [? [? ?]]]]]].
          + inversion H13. + subst. rewrite H11 in Heqh1p; inversion Heqh1p. }
        destruct p0 as (q12, z12). 
        unfold QZandLock_Join in H12. rewrite ufsumj in H12.
        destruct H12.
        2:{ destruct H12 as [? [? [? [? [? [? ?]]]]]]. subst. inversion H13. }
        destruct H12 as [vl1 [vl2 [vl [? [? [? ?]]]]]].
        subst. destruct vl as (q1, z1). destruct vl1 as (q11, z11).
        inversion H13; subst.
        rename H11 into Hst1. rename H8 into Hst12. rename H7 into Hst11.
        exists (inl (q11, z11)), (inl (q12, v)), (inl (1%Q, v)).
        split; [tauto |]. split; [tauto |]. split; [rewrite Heqh2p; tauto |].
        unfold QZandLock_Join. rewrite ufsumj. left.
        exists (q11, z11), (q12, v), (1%Q, v).
        unfold QZ_Join in H15.
        unfold OSAGenerators.prod_Join in H15.
        unfold SeparationAlgebra.join in H15. destruct H15.
        unfold Q_Join in H7.
        unfold fst in H7. destruct H7 as [? [? [? [? [? [? ?]]]]]].
        assert (q1 == 1).
        { rewrite Hst1 in Heqh1p. inversion Heqh1p. lra. }
        assert (q12 == 1).
        { rewrite Hst12 in H1. inversion H1. lra. }
        lra.
      - specialize (H9 pp n).
        rewrite H9.
        exists vv1, vv2, vv. tauto. }
  simpl. unfold BinRel.empty. tauto.
Qed.

Definition emptyheap : heap := fun _ => None.

Theorem make_rule_sound : forall l P P' Q Q',
  P = DeepintoShallow P' ->
  Q = DeepintoShallow Q' ->  
  valid (sepcon P (sepcon Q (mapsto_ l 1%Q))) (CMake l P' Q') (sepcon Q (hasLock l 1%Q P')) falsep falsep.
Proof.
  unfold valid; intros.
  split.
  { (* safety *)
    unfold not; intros.
    simpl in H2. unfold not in H2. destruct H2.
    + (* no mem satisfying P *)  
      apply H2. clear H2.
      ufSepcon H1.
      destruct H1 as [st11 [st12 [? [? ?]]]].
      exists st11, st12. split; [tauto |].
      subst P. unfold DeepintoShallow in H1. tauto.
    + (* no permission to l *)
      ufSepcon H1.
      destruct H1 as [st11 [st12 [? [? ?]]]].
      destruct H3 as [st121 [st122 [? [? ?]]]].
      unfold mapsto_ in H5. destruct H5 as [[v ?] ?].
      (* st12 has permission to l *)
      assert (snd st12 l <> None).
      { ufStatej H6. destruct H6. ufHeapj H8.
        specialize (H8 l). rewrite ufoptionj in H8.
        destruct H8 as [? | [? | [? | ?]]].
        + destruct H8 as [? [? ?]]. rewrite H9 in H5. inversion H5.
        + unfold not; intros.
          destruct H8 as [v' [? [? ?]]]. rewrite H11 in H9. inversion H9.
        + unfold not; intros.
          destruct H8 as [v' [? [? ?]]]. rewrite H11 in H9. inversion H9.
        + unfold not; intros.
          destruct H8 as [v1 [v2 [v' [? [? [? ?]]]]]].
          rewrite H11 in H9; inversion H9. }     
      (* st 1 has permission to l *)
      ufStatej H4. destruct H4. ufHeapj H9.
      specialize (H9 l). rewrite ufoptionj in H9.
      destruct H9 as [? | [? | [? | ?]]].
      - destruct H9 as [? [? ?]]. rewrite H10 in H8. tauto.
      - destruct H9 as [v' [? [? ?]]]. rewrite H11 in H2; inversion H2.
      - destruct H9 as [v' [? [? ?]]]. rewrite H11 in H2; inversion H2.
      - destruct H9 as [v1 [v2 [v' [? [? [? ?]]]]]].
        rewrite H11 in H2. inversion H2. }
  split.
  { (* normal exit *)
    intros.
    simpl in H2.
    destruct H2 as [st11 [st12 [st121 [st122 [st21 [st22 [? [? [? [? [? [? [? ?]]]]]]]]]]]]].
    ufsepcon. exists st21, st22. 
    split. { subst Q. unfold DeepintoShallow. tauto. }
    split. { unfold hasLock_sem. unfold hasLock_sem in H9. unfold hasLock. tauto.  }
    tauto. }
  simpl. tauto.
Qed.
  
Theorem deallocate_rule_sound : forall l P P',
  P = DeepintoShallow P' ->
  valid (hasLock l 1%Q P') (CDeallocate l) (sepcon P (mapsto_ l 1%Q))falsep falsep.
Proof.
  unfold valid; intros.
  split.
  { (* safety *)
    unfold not; intros. 
    unfold hasLock in H0. destruct H0.
    simpl in H1. rewrite H0 in H1. tauto. }
  split.
  { (* normal exit *)
    intros. 
    unfold hasLock in H0. destruct H0.
    simpl in H1. rewrite H0 in H1.
    destruct H1 as [st21 [st22 [? [? ?]]]].
    ufsepcon. exists st21, st22.
    split. { subst P. unfold DeepintoShallow. tauto. }
    split. 
    { rewrite H4. unfold mapsto_, heap_Update. split.
      + unfold snd at 1. destruct (Z.eq_dec l l); try tauto.
        exists 0. reflexivity.
      + intros pp ?.
        unfold snd at 1. destruct (Z.eq_dec pp l); try tauto.
        exact (H2 pp n). }
    tauto. }
  tauto.
Qed.

Theorem acquire_rule_sound : forall l P P' pi,
  P = DeepintoShallow P' ->
  valid (hasLock l pi P') (CAcquire l) (sepcon P (readytoRelease l pi P')) falsep falsep.
Proof.
  unfold valid; intros.
  split.
  { unfold not; intros.
    unfold hasLock in H0. destruct H0.
    simpl in H1. rewrite H0 in H1. tauto. }
  split.
  { intros. 
    unfold hasLock in H0. destruct H0.
    simpl in H1. rewrite H0 in H1.
    destruct H1 as [st21 [st22 [? [? ?]]]].
    ufsepcon. exists st21, st22.
    split. { subst P. unfold DeepintoShallow; tauto. }
    split; [| tauto].
    unfold readytoRelease; split.
    + rewrite H4. unfold snd at 1.
      unfold heap_Update. destruct (Z.eq_dec l l); try tauto. 
    + intros pp ?.
      rewrite H4; unfold snd at 1; unfold heap_Update.
      destruct (Z.eq_dec pp l); try tauto.
      exact (H2 pp n). }
  tauto.
Qed.

Lemma invariantjoin : forall st1 st2 st l P pi,
  stateJ st1 st2 st ->
  snd st2 l = Some (inr (pi, Some tt, P)) -> 
  exists pi', snd st l = Some (inr (pi', Some tt, P)).
Proof.
  intros.
  ufStatej H. destruct H.
  ufHeapj H1. specialize (H1 l). rewrite ufoptionj in H1.
  destruct H1 as [? | [? | [? | ?]]].
  + destruct H1 as [? [? ?]]. rewrite H2 in H0. inversion H0.
  + destruct H1 as [? [? [? ?]]]. rewrite H2 in H0; inversion H0.
    subst. eexists; exact H3.
  + destruct H1 as [? [? [? ?]]]. rewrite H2 in H0; inversion H0.
  + destruct H1 as [v1 [v2 [v [? [? [? ?]]]]]].
    unfold QZandLock_Join in H4. rewrite ufsumj in H4.
    destruct H4.
    { destruct H4 as [? [? [? [? [? [? ?]]]]]].
      subst. rewrite H2 in H0; inversion H0. }
    destruct H4 as [vr1 [vr2 [vr [? [? [? ?]]]]]]. subst.
    rewrite H2 in H0. inversion H0. subst.
    destruct vr1 as ((pi1, x), P1).
    destruct vr as ((pi12, x12), PP).
    unfold lock_Join in H7.
    unfold OSAGenerators.prod_Join in H7.
    unfold SeparationAlgebra.join in H7.
    unfold lock1_Join, lock2_Join in H7. destruct H7.
    unfold OSAGenerators.equiv_Join in H5.
    unfold snd in H5; destruct H5; subst.
    unfold OSAGenerators.prod_Join in H4.
    unfold SeparationAlgebra.join in H4.
    unfold optionunit_Join in H4. destruct H4.
    unfold OSAGenerators.option_Join in H5. unfold snd, fst in H5.
    rewrite ufoptionj in H5.
    destruct H5 as [? | [? | [? | ?]]].
    - destruct H5 as [? [? ?]]. inversion H6.
    - destruct H5 as [? [? [? ?]]]. inversion H6; subst.
      eexists; exact H3.
    - destruct H5 as [? [? [? ?]]]. inversion H6. 
    - destruct H5 as [? [? [? [? [? [? ?]]]]]].
      unfold OSAGenerators.trivial_Join in H8. contradiction.
Qed.

Theorem release_rule_sound : forall l P P' Q Q' pi,
  P = DeepintoShallow P' ->
  Q = DeepintoShallow Q' ->
  valid (sepcon P (sepcon Q (readytoRelease l pi P'))) (CRelease l Q' pi) (sepcon Q (hasLock l pi P')) falsep falsep.
Proof.
  unfold valid; intros.
  split.
  { unfold not; intros.
    ufSepcon H1. destruct H1 as [st11 [st12 [? [[st121 [st122 [? [? ?]]]] ?]]]].
    unfold readytoRelease in H4. destruct H4.
    assert (exists pi', snd st12 l = Some (inr (pi', Some tt, P'))).
    { ufStatej H5. destruct H5.
      ufHeapj H8. specialize (H8 l). rewrite ufoptionj in H8.
      destruct H8 as [? | [? | [? | ?]]].
      + destruct H8 as [? [? ?]]. rewrite H9 in H4. inversion H4.
      + destruct H8 as [v [? [? ?]]]. rewrite H9 in H4. inversion H4. subst.
        exists pi. tauto.
      + destruct H8 as [v [? [? ?]]]. rewrite H9 in H4. inversion H4.
      + destruct H8 as [v1 [v2 [v [? [? [? ?]]]]]].
        rewrite H9 in H4; inversion H4; subst.
        unfold QZandLock_Join in H11. rewrite ufsumj in H11.
        destruct H11.
        { destruct H as [? [? [? [? [? [? ?]]]]]]. inversion H0. }
        destruct H as [vr1 [vr2 [vr [? [? [? ?]]]]]].
        inversion H0; subst.
        destruct vr1 as ((pi1, x1), P1).
        destruct vr as ((pi12, x12), PP).
        unfold lock_Join in H12. unfold OSAGenerators.prod_Join in H12.
        unfold SeparationAlgebra.join in H12.
        unfold lock1_Join, lock2_Join in H12. destruct H12.
        unfold OSAGenerators.equiv_Join in H11. destruct H11.
        unfold snd in H11, H12. subst.
        unfold OSAGenerators.prod_Join in H.
        unfold SeparationAlgebra.join in H. destruct H.
        unfold optionunit_Join in H11. unfold snd, fst in H11.
        rewrite ufoptionj in H11. 
        destruct H11 as [? | [? | [? | ?]]].
        - destruct H11 as [? [? ?]]. inversion H12.
        - destruct H11 as [? [? [? ?]]].
          inversion H12. subst.
          eexists; exact H10.
        - destruct H11 as [? [? [? ?]]]. inversion H12. 
        - destruct H11 as [? [? [? [? [? [? ?]]]]]].
          unfold OSAGenerators.trivial_Join in H14. contradiction. }
    destruct H8 as [pi' ?].
    assert (exists pi'', snd st1 l = Some (inr (pi'', Some tt, P'))).
    { ufStatej H6. destruct H6.
      ufHeapj H9. specialize (H9 l). rewrite ufoptionj in H9.
      destruct H9 as [? | [? | [? | ?]]].
      + destruct H9 as [? [? ?]]. rewrite H10 in H8. inversion H8.
      + destruct H9 as [v [? [? ?]]]. 
        rewrite H10 in H8. inversion H8. subst.
        eexists. exact H11.
      + destruct H9 as [v [? [? ?]]].
        rewrite H10 in H8. inversion H8.
      + destruct H9 as [v1 [v2 [v [? [? [? ?]]]]]].
        rewrite H10 in H8. inversion H8; subst.
        unfold QZandLock_Join in H12. rewrite ufsumj in H12.
        destruct H12.
        { destruct H as [? [? [? [? [? [? ?]]]]]]. inversion H0. }
        destruct H as [vr1 [vr2 [vr [? [? [? ?]]]]]]. 
        inversion H0; subst.
        destruct vr1 as ((pi1, x1), P1).
        destruct vr as ((pi12, x12), PP).
        unfold lock_Join in H13. unfold OSAGenerators.prod_Join in H13.
        unfold SeparationAlgebra.join in H13.
        unfold lock1_Join, lock2_Join in H13.
        destruct H13.
        unfold OSAGenerators.equiv_Join in H12.
        unfold snd in H12; destruct H12. subst.
        unfold OSAGenerators.prod_Join in H.
        unfold SeparationAlgebra.join in H.
        destruct H. 
        unfold optionunit_Join in H12. unfold snd, fst in H12.
        rewrite ufoptionj in H12.
        destruct H12 as [? | [? | [? | ?]]].
        - destruct H12 as [? [? ?]]. inversion H13.
        - destruct H12 as [? [? [? ?]]].
          inversion H13. subst.
          eexists; exact H11.
        - destruct H12 as [? [? [? ?]]]. inversion H13.
        - destruct H12 as [? [? [? [? [? [? ?]]]]]].
          unfold OSAGenerators.trivial_Join in H15. tauto. }
    destruct H9 as [pi'' ?].
    simpl in H2. rewrite H9 in H2.
    unfold not in H2; apply H2.
    exists st11, st12. split; [tauto|].
    subst. unfold DeepintoShallow in *; tauto. }
  split.
  { intros. simpl in H2.
    destruct H2 as [st11 [st12 [st121 [st122 [st21 [st22 [PP [? [? [? [? [? [? [? ?]]]]]]]]]]]]]].
    ufsepcon. exists st21, st22.
    split. { subst. unfold DeepintoShallow. tauto. }
    split; [| tauto].
    unfold hasLock.
    unfold hasLock_sem in H9. split; [| tauto].
    ufSepcon H1.
    destruct H1 as [st11' [st12' [? ?]]].
    destruct H10 as [[st121' [st122' [? [? ?]]]] ?].
    unfold readytoRelease in H11.
    unfold readytoRelease_sem in H7.
    destruct H11, H7.
    pose proof (invariantjoin _ _ _ _ _ _ H12 H11).
    destruct H16 as [? ?].
    pose proof (invariantjoin _ _ _ _ _ _ H13 H16).
    destruct H17.
    pose proof (invariantjoin _ _ _ _ _ _ H3 H7).
    destruct H18.
    pose proof (invariantjoin _ _ _ _ _ _ H2 H18).
    destruct H19.
    rewrite H17 in H19.
    inversion H19. subst. try tauto. }
  simpl; tauto.
Qed.

(* Theorem release_rule_sound : forall l P P' Q Q' pi,
  P = DeepintoShallow P' ->
  Q = DeepintoShallow Q' ->
  valid (sepcon P (sepcon Q (readytoRelease l pi P'))) (CRelease l Q') (sepcon Q (hasLock l pi P')) falsep falsep.
Proof.
  unfold valid; intros.
  split.
  { unfold not; intros.
    ufSepcon H1.
    destruct H1 as [st11 [st12 [? [? ?]]]].
    destruct H3 as [st121 [st122 [? [? ?]]]].
    unfold readytoRelease in H5. destruct H5.
    assert (exists pi', snd st12 l = Some (inr (pi', Some tt, P'))).
    { ufStatej H6. destruct H6. ufHeapj H8. 
      specialize (H8 l). rewrite ufoptionj in H8.
      destruct H8 as [? | [? | [? | ?]]].
      + destruct H8 as [? [? ?]]. rewrite H9 in H5. inversion H5.
      + destruct H8 as [vv [? [? ?]]].
        rewrite H9 in H5; inversion H5.
        rewrite H12 in H10. exists pi. tauto.
      + destruct H8 as [vv [? [? ?]]].
        rewrite H9 in H5; inversion H5.
      + destruct H8 as [v1 [v2 [v' [? [? [? ?]]]]]].
        rewrite H9 in H5. inversion H5. subst v2.
        unfold QZandLock_Join in H11. rewrite ufsumj in H11.
        destruct H11. 
        { destruct H11 as [? [? [? [? [? [? ?]]]]]]. inversion H12. }
        destruct H11 as [vl1 [vl2 [vl [? [? [? ?]]]]]].
        inversion H12. 
        destruct vl1 as ((pi1, x1), P1).
        destruct vl as ((pi12, x'), PP).
        unfold lock_Join in H14.
        unfold OSAGenerators.prod_Join in H14.
        destruct H14.
        unfold SeparationAlgebra.join in H14, H15.
        subst vl2.
        unfold lock1_Join in H14.
        unfold OSAGenerators.prod_Join in H14.
        destruct H14.
        unfold SeparationAlgebra.join in H14, H16.
        unfold Q_Join in H14.
        unfold optionunit_Join, fst, snd in H16. 
        unfold lock2_Join, snd in H15.
        unfold OSAGenerators.equiv_Join in H15. 
        destruct H15. rewrite <-H17 in H15.
        subst P1 PP.
        assert (x' = Some tt).
        { rewrite ufoptionj in H16.
          destruct H16 as [? | [? | [? | ?]]].
        + destruct H15 as [? [? ?]]. inversion H16.
        + destruct H15 as [? [? [? ?]]].
          inversion H16. subst x. tauto.
        + destruct H15 as [? [? [? ?]]]. inversion H16.
        + destruct H15 as [? [? [? [? [? [? ?]]]]]].
          unfold OSAGenerators.trivial_Join in H18. contradiction. }
        subst x'.
        unfold fst in H14.
        exists pi12. rewrite H10. rewrite H13. tauto. }
    destruct H8 as [pi' ?].
    assert (exists pi'', snd st1 l = Some (inr (pi'', Some tt, P'))).
    { ufStatej H4. destruct H4. ufHeapj H9.
      specialize (H9 l). rewrite ufoptionj in H9.
      destruct H9 as [? | [? | [? | ?]]].
      + destruct H9 as [? [? ?]].
        rewrite H10 in H8. inversion H8.
      + destruct H9 as [vv [? [? ?]]].
        rewrite H10 in H8. inversion H8. rewrite H13 in H11.
        eexists. exact H11.
      + destruct H9 as [vv [? [? ?]]].
        rewrite H10 in H8. inversion H8.
      + destruct H9 as [v1 [v2 [v' [? [? [? ?]]]]]].
        rewrite H10 in H8. inversion H8. subst v2.
        unfold QZandLock_Join in H12.
        rewrite ufsumj in H12. destruct H12.
        { destruct H12 as [? [? [? [? [? [? ?]]]]]].
          inversion H13. }
        destruct H12 as [vr1 [vr2 [vr [? [? [? ?]]]]]].
        subst v'. inversion H13; subst vr2.
        destruct vr1 as ((pi1, x), P1).
        destruct vr as ((pi12, xx), PP).
        unfold lock_Join in H15.
        unfold OSAGenerators.prod_Join in H15.
        unfold SeparationAlgebra.join in H15.
        destruct H15.
        unfold lock1_Join in H14.
        unfold OSAGenerators.prod_Join in H14.
        unfold SeparationAlgebra.join in H14.
        destruct H14.
        unfold lock2_Join in H15.
        unfold OSAGenerators.equiv_Join, snd in H15.
        destruct H15. rewrite <-H17 in H15. subst P1 PP.
        unfold optionunit_Join in H16.
        assert (xx = Some tt).
        { unfold snd, fst in H16.
          rewrite ufoptionj in H16.
          destruct H16 as [? | [? | [? | ?]]].
          + destruct H15 as [? [? ?]]. inversion H16.
          + destruct H15 as [v [? [? ?]]].
            inversion H16. subst v. tauto.
          + destruct H15 as [? [? [? ?]]]. inversion H16.
          + destruct H15 as [? [? [? [? [? [? ?]]]]]].
            unfold OSAGenerators.trivial_Join in H18. contradiction. }
        subst xx.
        exists pi12. tauto. }
    destruct H9 as [pi'' ?].
    simpl in H2. rewrite H9 in H2.
    unfold not in H2; apply H2.
    exists st11, st12; split; try tauto.
    subst. unfold DeepintoShallow in *. tauto. }
  split.
  { intros.
    simpl in H2.
    destruct H2 as [st11 [st12 [st121 [st122 [st21 [st22 [PP [pi' [? [? [? [? [? [? [? ?]]]]]]]]]]]]]]].
    ufsepcon.
    exists st21, st22.
    split. { subst; unfold DeepintoShallow; tauto. }
    split; [| tauto].
    unfold hasLock.
    unfold hasLock_sem in H9.
    split; try tauto.
     *)
    
End BasicRulesSound. 
