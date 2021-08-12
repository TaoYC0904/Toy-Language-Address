Require Import Toy.Imp.
Require Import Toy.Language.
Require Import Toy.Embeddings.

Module BasicRules.
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
        



