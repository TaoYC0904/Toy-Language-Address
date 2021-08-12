Require Import Toy.Imp.
Require Import Toy.Language.
Require Import Toy.Embeddings.

Module BasicRulesSound.
Import Validity Assertion_Shallow Denote_State Denote_Aexp Denote_Bexp Denote_Com.

Theorem hoare_skip_sound : forall P, valid P CSkip P falsep falsep.
Proof.
  unfold valid.
  intros P st1 st2 HP.
  split; try split; try split.
  + unfold not; simpl; tauto.
  + intros Hc. simpl in Hc; subst; tauto.
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
  + intros Hc. simpl in Hc; subst; tauto.
  + intros Hc. simpl in Hc; tauto.
Qed.

Theorem hoare_cont_sound : forall P, valid P CCont falsep falsep P.
Proof.
  intros P st1 st2 HP.
  split; try split; try split.
  + unfold not; simpl; tauto.
  + intros Hc. simpl in Hc; tauto.
  + intros Hc. simpl in Hc; tauto.
  + intros Hc. simpl in Hc; subst; tauto.
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

Theorem hoare_if_sound : forall P Q Rb Rc b c1 c2,
  valid (andp P (inj b)) c1 Q Rb Rc ->
  valid (andp P (negp (inj b))) c2 Q Rb Rc ->
  valid (andp P (safeb b)) (CIf b c1 c2) Q Rb Rc.
Proof.
  unfold valid.
  intros P Q Rb Rc b c1 c2 HT HF.
  intros st1 st2 ?.
  unfold andp, safeb in H.
  destruct H as [HP HSafe].
  split; try split; try split.
  + unfold not; intros.
    simpl in H. destruct H as [? | [? | ?]].
    - tauto.
    - assert (andp P (inj b) st1).
      { unfold andp, inj. tauto. }
      specialize (HT st1 st2 H0); tauto.
    - assert (andp P (negp (inj b)) st1).
      { unfold andp, negp, inj. 
        split; try tauto.
        unfold not; intros.
        eapply (true_false_contradiction b (fst st1)); tauto. }
      specialize (HF st1 st2 H0); tauto.
  + intros Hc.
    simpl in Hc.
    destruct Hc as [[Hc1 Hc2] | [Hc1 Hc2]].
    - assert (andp P (inj b) st1).
      { unfold andp, inj. tauto. }
      specialize (HT st1 st2). tauto.
    - assert (andp P (negp (inj b)) st1).
      { unfold andp, negp, inj.
        split; try tauto.
        unfold not; intros.
        eapply (true_false_contradiction b (fst st1)); tauto. }
      specialize (HF st1 st2); tauto.
  + intros Hc.
    simpl in Hc.
    destruct Hc as [[Hc1 Hc2] | [Hc1 Hc2]].
    - assert (andp P (inj b) st1).
      { unfold andp, inj. tauto. }
      specialize (HT st1 st2). tauto.
    - assert (andp P (negp (inj b)) st1).
      { unfold andp, negp, inj.
        split; try tauto.
        unfold not; intros.
        eapply (true_false_contradiction b (fst st1)); tauto. }
      specialize (HF st1 st2); tauto.
  + intros Hc.
    simpl in Hc.
    destruct Hc as [[Hc1 Hc2] | [Hc1 Hc2]].
    - assert (andp P (inj b) st1).
      { unfold andp, inj. tauto. }
      specialize (HT st1 st2). tauto.
    - assert (andp P (negp (inj b)) st1).
      { unfold andp, negp, inj.
        split; try tauto.
        unfold not; intros.
        eapply (true_false_contradiction b (fst st1)); tauto. }
      specialize (HF st1 st2); tauto.
Qed.

Theorem hoare_for_sound : forall P P' Q c ci,
  valid P c P' Q P' ->
  valid P' ci P falsep falsep ->
  valid P (CFor c ci) Q falsep falsep.
Proof.
  intros P P' Q c ci Hlb Hinc.
  unfold valid in *.
  intros st1 st2 HP.
  split; try split; try split.
  + unfold not; intros.
    simpl in H; destruct H as [n ?].
    revert st1 HP H; induction n.
    - intros st1 HP H.
      simpl in H. destruct H.
      * specialize (Hlb st1 st2); tauto.
      * destruct H as [st' ?].
        specialize (Hlb st1 st'); specialize (Hinc st' st2); tauto.
    - intros st1 HP H.
      simpl in H.
      destruct H as [st3 [[? | ?] ?]].
      * destruct H as [st4 [? ?]].
        specialize (Hlb st1 st4); specialize (Hinc st4 st3).
        specialize (IHn st3); tauto.
      * destruct H as [st4 [? ?]].
        specialize (Hlb st1 st4); specialize (Hinc st4 st3).
        specialize (IHn st3); tauto.
  + intros Hc.
    simpl in Hc; destruct Hc as [n Hc].
    revert st1 HP Hc; induction n.
    - intros st1 HP H.
      simpl in H; destruct H as [? | [st3 ?]].
      * specialize (Hlb st1 st2); tauto.
      * specialize (Hlb st1 st3); specialize (Hinc st3 st2); tauto.
    - intros st1 HP H.
      simpl in H; destruct H as [st3 [[[st4 [? ?]] | [st4 [? ?]]] ?]].
      * specialize (Hlb st1 st4); specialize (Hinc st4 st3).
        specialize (IHn st3); tauto.
      * specialize (Hlb st1 st4); specialize (Hinc st4 st3).
        specialize (IHn st3); tauto.
  + simpl; tauto.
  + simpl; tauto.
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

Theorem hoare_set_sound : forall P X e v,
  derives P (eqp e v) ->
  valid (andp P (safea e)) (CAss_set X e) (andp (eqp (AId X) v) (exp (subst_set P X))) falsep falsep.
Proof.
  unfold valid. intros.
  unfold derives, eqp in H.
  unfold andp, safea in H0.
  destruct H0 as [? ?].
  specialize (H st1 H0).
  split.
  { unfold not; simpl; tauto. }
  split.
  { intros.
    unfold andp, eqp, exp, subst_set.
    simpl in H2. destruct H2. split.
    + simpl. rewrite H2. tauto.
    + exists ((fst st1) X).
      remember (store_update (fst st2) X (Some (fst st1 X))) as s'.
      assert (forall X, s' X = (fst st1) X).
      { destruct H3. intros Y.
        unfold store_update in Heqs'.
        subst s'.
        destruct (Nat.eq_dec Y X).
        - rewrite e0. tauto.
        - specialize (H3 Y). specialize (H3 n). rewrite H3. tauto. } 
      assert (store_update (fst st2) X (Some (fst st1 X)) = fst st1).
      { eapply FunctionalExtensionality.functional_extensionality_dep.
        subst. tauto. }
      subst.
      destruct H3. rewrite <- H6.
      rewrite H5.
      destruct st1 in *.
      unfold fst, snd. tauto. }
  split; simpl; tauto.
Qed.

Theorem hoare_load_sound : forall P X e p v,
  derives P (andp (eqp e p) (mapsto p v)) ->
  valid P (CAss_load X e) (andp (eqp (AId X) v) (exp (subst_load P X))) falsep falsep.
Proof.
  unfold valid; intros.
  unfold derives, andp, eqp, mapsto in H.
  specialize (H st1 H0).
  destruct H as [? [? ?]].
  split.
  { unfold not; intros.
    simpl in H3.
    rewrite H, H1 in H3. inversion H3. }
  split.
  { intros.
    unfold andp, eqp, exp; simpl.
    split.
    + simpl in H3.
      rewrite H in H3.
      destruct H3 as [? [? ?]].
      rewrite H3; tauto.
    + simpl in H3.
      rewrite H in H3.
      destruct H3 as [? [? ?]].
      exists ((fst st1) X).
      unfold subst_load.
      remember (store_update (fst st2) X (Some (fst st1 X))) as s'.
      assert (forall Y, s' Y = fst st1 Y).
      { intros. subst s'; unfold store_update.
        destruct (Nat.eq_dec Y X).
        + rewrite e0; tauto.
        + specialize (H4 Y n); tauto. }
      assert (s' = fst st1).
      { eapply FunctionalExtensionality.functional_extensionality_dep. tauto. }
      rewrite H7, <-H5.
      destruct st1.
      unfold fst, snd; tauto. }
  split; simpl; tauto.
Qed.

Theorem hoare_store_sound : forall P e1 e2 p v,
  derives P (andp (eqp e1 p) (eqp e2 v)) ->
  valid (sepcon P (mapsto_ p)) (CAss_store e1 e2) (sepcon P (mapsto p v)) falsep falsep.
Proof.
  unfold valid; intros.
  unfold derives, andp, eqp in H.
  unfold andp, sepcon, mapsto_ in H0.
  destruct H0 as [st11 [st12 [? [? [? ?]]]]].
  split.
  { unfold not; intros.
    unfold join in H0.
    destruct H0 as [? [? ?]].
    specialize (H st11 H1).
    destruct H.
    rewrite H0, H5 in H.
    rewrite H0, H5 in H7.
    simpl in H4.
    rewrite H, H7 in H4.
    destruct H2 as [v0 ?].
    unfold join_heap in H6.
    specialize (H6 p).
    destruct H6 as [? | [? | ?]].
    + destruct H6 as [? [? [? ?]]]. rewrite H9 in H4; inversion H4. 
    + destruct H6 as [? [? [? ?]]]. rewrite H9 in H4; inversion H4.
    + destruct H6 as [? [? ?]].
      rewrite H8 in H2; inversion H2. }
  split.
  { intros.
    specialize (H st11 H1).
    destruct H.
    unfold join in H0.
    destruct H0 as [? [? ?]].
    rewrite H0, H6 in H.
    rewrite H0, H6 in H5.
    simpl in H4.
    rewrite H, H5 in H4.
    destruct H4 as [? [? [? ?]]].
    unfold sepcon, mapsto.
    remember (fst st12, (heap_update (snd st12) p (Some v))) as st22.
    exists st11, st22.
    split.
    { unfold join.
      split; try split.
      + subst st22. unfold fst at 2. tauto.
      + subst st22. unfold fst at 1.
        rewrite H6; tauto.
      + unfold join_heap in *.
        intros; specialize (H7 p0).
        destruct H7 as [? | [? | ?]].
        - left.
          subst st22; unfold heap_update.
          unfold snd at 2.
          destruct H7 as [v0 [? [? ?]]].
          destruct (Z.eq_dec p p0).
          { subst p0. destruct H2 as [v1 ?]. rewrite H2 in H11. inversion H11. }
          exists v0.
          split; try split; try tauto.
          specialize (H9 p0 n).
          rewrite H9. tauto. 
        - right. left.
          destruct H7 as [v0 [? [? ?]]].
          subst st22; unfold heap_update.
          unfold snd at 2.
          destruct (Z.eq_dec p p0).
          * exists v; subst p0.
            split; try split; try tauto.
          * exists v0.
            specialize (H9 p0 n).
            rewrite H9; tauto.
        - right. right.
          subst st22; unfold heap_update.
          unfold snd at 2.
          destruct (Z.eq_dec p p0).
          { subst p0. tauto. }
          specialize (H9 p0 n).
          rewrite H9; tauto. }
      split; try tauto.
      split.
      { subst st22; unfold heap_update.
        unfold snd at 1.
        destruct (Z.eq_dec); try tauto. }
      intros.
      specialize (H3 p' H11).
      subst st22; unfold heap_update.
      unfold snd at 1.
      destruct (Z.eq_dec p p'); try tauto. }
  split; simpl; tauto.
Qed.

End BasicRulesSound.
