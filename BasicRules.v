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
Import Assertion_Shallow Validity.

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


