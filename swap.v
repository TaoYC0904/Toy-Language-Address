Require Import Toy.UnifySL.implementation.
Require Import Toy.Imp.
Require Import Toy.Language.
Require Import Toy.Embeddings.
Require Import Toy.BasicRules.
Require Import Coq.Lists.List.
Import Toy.UnifySL.implementation.
Import T.
Import Denote_Aexp Denote_Bexp Denote_Com.
Import Assertion_Shallow AssertionDerivationRules.
Import Validity tacticforOSA.
Import BasicRulesSound.

Definition p1 : var := 1%nat.
Definition p2 : var := 2%nat.
Definition t : var := 3%nat.

Definition asgn1 : com := CAss_load t (ADeref (AId p1)).
Definition asgn2 : com := CAss_store (AId p1) (ADeref (AId p2)).
Definition asgn3 : com := CAss_store (AId p2) (AId t).
Definition swap : com := CSeq asgn1 (CSeq asgn2 asgn3).

Definition pointertoval (p : var) (x : Z) : Assertion := eqp (ADeref (AId p)) x.

Theorem swap_sepc : forall x y,
  valid (sepcon (pointertoval p1 x) (pointertoval p2 y)) swap (sepcon (pointertoval p1 y) (pointertoval p2 x)) falsep falsep.
Proof.
  unfold valid. intros.
  split.
  { unfold not; intros.
    UFsepcon. destruct H as [st11 [st12 [? [? ?]]]].
    unfold pointertoval in *. unfold eqp in *.
    simpl in H0.
    destruct H0.
    { unfold deref_sem in H0.
      simpl in H1. unfold deref_sem in H1.
      Check aeval_join1.

      destruct (snd st1 (fst st1 p1)); inversion H0.







  (*  t := *x;
     *x := *y;
     *y := t; *)