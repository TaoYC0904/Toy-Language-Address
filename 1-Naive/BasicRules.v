Require Import ZArith.
Require Import Toy.Naive.lib.
Require Import Toy.Naive.Language.
Require Import Toy.Naive.Embeddings.
Require Import Toy.Naive.usl.implementation.

Module BasicRulesSound.
Import Validity Assertion_Shallow Denote_Aexp Denote_Bexp Denote_Com.
Import tacticforOSA T.

Theorem hoare_skip_sound : forall P, valid P CSkip P falsep falsep.
Proof.
  unfold valid.
  intros P st1 st2 HP.
  split; try split; try split.
  + unfold not; simpl; tauto.
  + intros Hc. simpl in Hc. unfold BinRel.id in *. subst. tauto.
  + intros Hc. simpl in Hc; tauto. 
  + intros Hc. simpl in Hc; tauto.
Qed.

Theorem hoare_break_sound : forall P, valid P CBreak falsep P falsep.
Proof.
  unfold valid.
  intros P st1 st2 HP.
  split; try split; try split.
  + unfold not; simpl; tauto.
  + intros Hc. simpl in Hc; tauto.
  + intros Hc. simpl in Hc. unfold BinRel.id in *. subst. tauto.
  + intros Hc. simpl in Hc; tauto.
Qed.

Theorem hoare_cont_sound : forall P, valid P CCont falsep falsep P.
Proof.
  intros P st1 st2 HP.
  split; try split; try split.
  + unfold not; simpl; tauto.
  + intros Hc. simpl in Hc; tauto.
  + intros Hc. simpl in Hc; tauto.
  + intros Hc. simpl in Hc. unfold BinRel.id in *. subst. tauto.
Qed.

Theorem hoare_seq_sound : forall P Q R Rb Rc c1 c2,
  valid P c1 Q Rb Rc ->
  valid Q c2 R Rb Rc ->
  valid P (CSeq c1 c2) R Rb Rc.
Proof. 
  unfold valid.
  intros P Q R Rb Rc c1 c2 Hc1 Hc2.
  intros st1 st2 HP.
  split; try split; try split.
  + unfold not; intros.
    simpl in H; destruct H.
    - specialize (Hc1 st1 st2); tauto.
    - destruct H as [st3 [? ?]].
      specialize (Hc1 st1 st3 HP).
      destruct Hc1 as [? [? [? ?]]].
      specialize (H2 H).
      specialize (Hc2 st3 st2); tauto.
  + intros Hc.
    simpl in Hc. destruct Hc as [st3 [? ?]].
    specialize (Hc1 st1 st3 HP).
    destruct Hc1 as [? [? [? ?]]].
    specialize (H2 H).
    specialize (Hc2 st3 st2 H2); tauto.
  + intros Hc.
    simpl in Hc. destruct Hc as [? | [st3 [? ?]]].
    - specialize (Hc1 st1 st2); tauto.
    - specialize (Hc1 st1 st3 HP).
      specialize (Hc2 st3 st2). tauto.
  + intros Hc.
    simpl in Hc. destruct Hc as [? | [st3 [? ?]]].
    - specialize (Hc1 st1 st2); tauto.
    - specialize (Hc1 st1 st3 HP).
      specialize (Hc2 st3 st2). tauto.
Qed.

Lemma true_false_contradiction : forall b s,
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

Theorem hoare_consequence_sound : forall P P' Q Q' Rb Rb' Rc Rc' c,
  derives P P' ->
  valid P' c Q' Rb' Rc' ->
  derives Q' Q ->
  derives Rb' Rb ->
  derives Rc' Rc ->
  valid P c Q Rb Rc.
Proof.
  intros P P' Q Q' Rb Rb' Rc Rc' c HP Hc HQ HRb HRc.
  unfold valid in *.
  intros.
  specialize (Hc st1 st2).
  unfold derives in *.
  specialize (HP st1); specialize (HQ st2).
  specialize (HRb st2); specialize (HRc st2).
  tauto.
Qed.

Theorem hoare_load_sound : forall P e v X,
  derives P (eqp e v) ->
  valid P (CAss_load X e) (andp (eqp (AId X) v) (exp (subst P X))) falsep falsep.
Proof.
  unfold derives, valid; intros.
  specialize (H st1 H0).
  split.
  { unfold not; intros.
    simpl in *.
    unfold eqp in H. rewrite H in H1; inversion H1. }
  split.
  { intros.
    simpl in *.
    unfold eqp in H.
    rewrite H in H1. destruct H1 as [? [? ?]].
    split.
    + unfold eqp in *. simpl in *.
      rewrite H1; tauto.
    + unfold exp, subst in *.
      exists (fst st1 X).
      remember (store_update (fst st2) X (Some (fst st1 X))) as s'.
      assert (forall Y, s' Y = fst st1 Y).
      { intros.
        subst s'. unfold store_update.
        destruct (Nat.eq_dec Y X).
        + subst X; tauto.
        + specialize (H2 Y n); tauto. }
      assert (s' = fst st1).
      { eapply FunctionalExtensionality.functional_extensionality_dep.
        apply H4. }
      rewrite H5, <-H3.
      destruct st1; unfold fst, snd; tauto. }
  split; simpl; tauto.
Qed.

Lemma aeval_join1 : forall e st1 st2 st v,
  stateJ st1 st2 st ->
  aeval e st1 = Some v ->
  aeval e st = Some v.
Proof.
  intros.
  UFjoin.
  simpl in *. destruct H as [[? ?] ?].
  UFheapjoin.
  rewrite osajoin in H2.
  revert v H0; induction e.
  + simpl. tauto.
  + simpl in *. rewrite <-H. tauto.
  + simpl in *. intros. unfold add_sem in *.
    destruct (aeval e1 st1), (aeval e2 st1); try inversion H0.
    specialize (IHe1 z). specialize (IHe2 z0).
    assert (aeval e1 st = Some z). { tauto. }
    assert (aeval e2 st = Some z0). { tauto. }
    rewrite H3, H5. tauto.
  + simpl in *. intros. unfold sub_sem in *.
    destruct (aeval e1 st1), (aeval e2 st1); try inversion H0.
    specialize (IHe1 z). specialize (IHe2 z0).
    assert (aeval e1 st = Some z). { tauto. }
    assert (aeval e2 st = Some z0). { tauto. }
    rewrite H3, H5. tauto.
  + simpl in *. intros. unfold mul_sem in *.
    destruct (aeval e1 st1), (aeval e2 st1); try inversion H0.
    specialize (IHe1 z). specialize (IHe2 z0).
    assert (aeval e1 st = Some z). { tauto. }
    assert (aeval e2 st = Some z0). { tauto. }
    rewrite H3, H5. tauto.
  + simpl in *. intros. unfold div_sem in *.
    destruct (aeval e1 st1), (aeval e2 st1); try inversion H0.
    destruct (Z.eq_dec z0 0); try inversion H0.
    specialize (IHe1 z). specialize (IHe2 z0).
    assert (aeval e1 st = Some z). { tauto. }
    assert (aeval e2 st = Some z0). { tauto. }
    rewrite H3, H6. destruct (Z.eq_dec z0 0); tauto.
  + simpl in *. intros. unfold deref_sem in *.
    destruct (aeval e st1); try inversion H0.
    rename z into p. specialize (IHe p).
    assert (aeval e st = Some p). { tauto. }
    clear H4.
    specialize (H2 p). destruct H2 as [? | [? | ?]].
    - destruct H2 as [v0 [? [? ?]]].
      rewrite H2 in H0. inversion H0. subst v0.
      rewrite H3, H5, H2. tauto.
    - destruct H2 as [v0 [? [? ?]]].
      rewrite H2 in H0. inversion H0.
    - destruct H2 as [? [? ?]].
      rewrite H2 in H0. inversion H0.
Qed.

Lemma aeval_join2 : forall e st1 st2 st v,
  stateJ st1 st2 st ->
  aeval e st2 = Some v ->
  aeval e st = Some v.
Proof.
  intros.
  UFjoin.
  simpl in *. destruct H as [[? ?] ?].
  UFheapjoin.
  rewrite osajoin in H2.
  revert v H0; induction e.
  + simpl. tauto.
  + simpl in *. rewrite <-H1. tauto.
  + simpl in *. intros. unfold add_sem in *.
    destruct (aeval e1 st2), (aeval e2 st2); try inversion H0.
    specialize (IHe1 z). specialize (IHe2 z0).
    assert (aeval e1 st = Some z). { tauto. }
    assert (aeval e2 st = Some z0). { tauto. }
    rewrite H3, H5. tauto.
  + simpl in *. intros. unfold sub_sem in *.
    destruct (aeval e1 st2), (aeval e2 st2); try inversion H0.
    specialize (IHe1 z). specialize (IHe2 z0).
    assert (aeval e1 st = Some z). { tauto. }
    assert (aeval e2 st = Some z0). { tauto. }
    rewrite H3, H5. tauto.
  + simpl in *. intros. unfold mul_sem in *.
    destruct (aeval e1 st2), (aeval e2 st2); try inversion H0.
    specialize (IHe1 z). specialize (IHe2 z0).
    assert (aeval e1 st = Some z). { tauto. }
    assert (aeval e2 st = Some z0). { tauto. }
    rewrite H3, H5. tauto.
  + simpl in *. intros. unfold div_sem in *.
    destruct (aeval e1 st2), (aeval e2 st2); try inversion H0.
    destruct (Z.eq_dec z0 0); try inversion H0.
    specialize (IHe1 z). specialize (IHe2 z0).
    assert (aeval e1 st = Some z). { tauto. }
    assert (aeval e2 st = Some z0). { tauto. }
    rewrite H3, H6. destruct (Z.eq_dec z0 0); tauto.
  + simpl in *. intros. unfold deref_sem in *.
    destruct (aeval e st2); try inversion H0.
    rename z into p. specialize (IHe p).
    assert (aeval e st = Some p). { tauto. }
    clear H4.
    specialize (H2 p). destruct H2 as [? | [? | ?]].
    - destruct H2 as [v0 [? [? ?]]].
      rewrite H4 in H0. inversion H0.
    - destruct H2 as [v0 [? [? ?]]].
      rewrite H4 in H0. inversion H0. subst v0.
      rewrite H3, H5, H4. tauto.
    - destruct H2 as [? [? ?]].
      rewrite H4 in H0. inversion H0.
Qed.

Theorem hoare_store_sound : forall P e1 e2 p v,
  derives P (andp (eqp e1 p) (eqp e2 v)) ->
  valid (sepcon P (mapsto_ p)) (CAss_store e1 e2) (sepcon P (mapsto p v)) falsep falsep.
Proof.
  unfold derives, valid; intros.
  split.
  { unfold not; intros.
    UFsepcon. destruct H0 as [st11 [st12 [? [? ?]]]].
    specialize (H st11 H2).
    destruct H. unfold eqp in H, H4.
    pose proof (aeval_join1 _ _ _ _ _ H0 H).
    pose proof (aeval_join1 _ _ _ _ _ H0 H4).
    simpl in *. rewrite H5, H6 in H1.
    unfold mapsto_ in H3. destruct H3.
    destruct H3 as [v0 ?].
    UFjoin. destruct H0.
    UFheapjoin. rewrite osajoin in H8.
    specialize (H8 p).
    destruct H8 as [? | [? | ?]].
    + destruct H8 as [? [? [? ?]]].
      rewrite H9 in H3. inversion H3.
    + destruct H8 as [? [? [? ?]]].
      rewrite H10 in H1. inversion H1.
    + destruct H8 as [? [? ?]].
      rewrite H9 in H3. inversion H3. }
  split.
  { intros.
    UFsepcon. destruct H0 as [st11 [st12 [? [? ?]]]].
    remember (fst st1, heap_update (snd st12) p (Some v)) as st22.
    exists st11, st22.
    specialize (H st11 H2).
    destruct H. unfold eqp in *.
    pose proof (aeval_join1 _ _ _ _ _ H0 H).
    pose proof (aeval_join1 _ _ _ _ _ H0 H4).
    UFjoin. destruct H0 as [[? ?] ?].
    simpl in H1. rewrite H5, H6 in H1.
    destruct H1 as [? [? [? ?]]].
    split; split; try split.
    + rewrite H0, H11; tauto.
    + subst st22. unfold fst at 1. tauto.
    + UFheapjoin. rewrite osajoin in *.
      intros p0. specialize (H8 p0).
      destruct H8 as [? | [? | ?]].
      - left.
        destruct H8 as [v0 [? [? ?]]].
        subst st22. unfold heap_update. unfold snd at 2.
        destruct (Z.eq_dec p p0).
        * subst p0. unfold mapsto_ in H3.
          destruct H3 as [[v' ?] ?].
          rewrite H3 in H12. inversion H12.
        * exists v0.
          specialize (H10 p0 n). rewrite H13 in H10.
          tauto. 
      - right. left.
        destruct H8 as [v0 [? [? ?]]].
        subst st22. unfold heap_update. unfold snd at 2.
        destruct (Z.eq_dec p p0).
        * exists v. subst p0. tauto.
        * exists v0. 
          specialize (H10 p0 n). rewrite H10. tauto.
      - right. right.
        destruct H8 as [? [? ?]].
        unfold mapsto_ in H3.
        destruct H3 as [[v' ?] ?].
        destruct (Z.eq_dec p p0).
        * subst p0. rewrite H3 in H12; inversion H12.
        * subst st22. unfold heap_update. unfold snd at 2.
          destruct (Z.eq_dec p p0); try tauto.
          specialize (H10 p0 n). rewrite H10. tauto.
    + tauto.
    + subst st22. unfold heap_update. unfold snd at 1.
      destruct (Z.eq_dec p p); tauto.
    + intros. subst st22. unfold heap_update. unfold snd at 1.
      destruct (Z.eq_dec p p'); try tauto.
      unfold mapsto_ in H3.
      destruct H3. eapply H13. tauto. }
  split; simpl; tauto.
Qed.

End BasicRulesSound.
