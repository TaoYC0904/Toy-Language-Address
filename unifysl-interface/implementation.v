Require Import ZArith.
Require Import QArith.
Require Import Lqa.
Require Import Coq.micromega.Psatz.
Require Import FP.UnifySL.interface.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Model.OrderedSA.
Require Import Logic.SeparationLogic.Model.OSAGenerators.
Require Import Logic.SeparationLogic.Semantics.WeakSemantics.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.

Definition var : Type := nat.
Definition store : Type := var -> Z.
Definition addr : Type := Z.
Definition heap : Type := addr -> option (Q * Z).
Definition state : Type := store * heap.
Definition Assertion : Type := state -> Prop.

Definition storeJ : Join store := equiv_Join.

Definition storeSA : SeparationAlgebra store := equiv_SA.

Definition Q_Join : Join Q := fun q1 q2 q => 
  0 <= q1 /\ 0 <= q2 /\ 0 <= q /\ q1 <= 1 /\ q2 <= 1 /\ q <= 1 /\ Qeq q (q1 + q2).

Definition Q_SA : @SeparationAlgebra Q Q_Join.
Proof.
  constructor; intros; unfold join, Q_Join in *;
  [| exists (mxyz - mx)]; repeat (split; try tauto; lra).
Qed.

Definition Z_Join : Join Z := equiv_Join.

Definition Z_SA : SeparationAlgebra Z:= equiv_SA.

Definition s_Join : Join (Q * Z):= @prod_Join _ _ Q_Join Z_Join.

Definition s_SA : SeparationAlgebra (Q * Z) := @prod_SA Q Z Q_Join Z_Join Q_SA Z_SA.

Definition heapJ : Join heap := @fun_Join _ _ (@option_Join _ (s_Join)).

Definition heapSA : SeparationAlgebra heap := @fun_SA _ _ _ (@option_SA _ _ (s_SA)).

Definition stateJ : Join state := @prod_Join _ _ storeJ heapJ.

Definition stateSA : SeparationAlgebra state := @prod_SA store heap storeJ heapJ storeSA heapSA.

Definition SepCon (P : Assertion) (Q : Assertion) : Assertion :=
  fun st => exists st1 st2, (P st1) /\ (Q st2) /\ (stateJ st1 st2 st).

Module NaiveLang <: LanguageSig.
  Definition expr := Assertion.
  Section NaiveLang.
    Definition context := expr -> Prop.
    Definition provable (e : expr) : Prop := forall st, e st.
    Definition impp (e1 e2 : expr) : expr := fun st => e1 st -> e2 st.
    Definition andp (e1 e2 : expr) : expr := fun st => e1 st /\ e2 st.
    Definition orp (e1 e2 : expr) : expr := fun st => e1 st \/ e2 st.
    Definition sepcon := SepCon.
    Definition negp (e : expr) : expr := fun st => ~ e st.
    Definition falsep : expr := fun st => False.
    Definition truep : expr := fun st => True.
    Definition emp : expr := fun st => forall p, snd st p = None.
  End NaiveLang.
End NaiveLang.

Module NaiveRule.
Include DerivedNames (NaiveLang).

Instance L : Language := (Build_Language expr) .
Instance minL : (MinimumLanguage L) := (Build_MinimumLanguage L impp) .
Instance andpL : (AndLanguage L) := (Build_AndLanguage L andp) .
Instance sepconL : (SepconLanguage L) := (Build_SepconLanguage L sepcon) .
Instance falsepL : (FalseLanguage L) := (Build_FalseLanguage L falsep) .

Lemma falsep_sepcon_impp : (forall x : expr, provable (impp (sepcon falsep x) falsep)) .
Proof.
  unfold provable, impp, sepcon, falsep. intros. 
  destruct H as [st1 [st2 ?]]. tauto.
Qed.

Lemma sepcon_comm_impp : (forall x y : expr, provable (impp (sepcon x y) (sepcon y x))) .
Proof.
  intros x y.
  exact (@sound_sepcon_comm L _ _ (Build_Model state) (unit_kMD _) tt stateR stateJ stateSA (Pred_SM _) (Pred_kminSM _) (Pred_fsepconSM _) x y).
Qed.

Lemma sepcon_assoc1 : (forall x y z : expr, provable (impp (sepcon x (sepcon y z)) (sepcon (sepcon x y) z))) .
Proof.
  intros x y z.
  exact (@sound_sepcon_assoc1 L _ _ (Build_Model state) (unit_kMD _) tt stateR stateJ stateSA (Pred_SM _) (Pred_kminSM _) (Pred_fsepconSM _) x y z).
Qed. 

Lemma sepcon_mono : (forall x1 x2 y1 y2 : expr, provable (impp x1 x2) -> provable (impp y1 y2) -> provable (impp (sepcon x1 y1) (sepcon x2 y2))) .
Proof.
  unfold provable, impp, sepcon.
  intros.
  destruct H1 as [st1 [st2 ?]].
  exists st1, st2. 
  split; try tauto.
  specialize (H st1). specialize (H0 st2).
  tauto.
Qed.

Lemma andp_intros : (forall x y : expr, provable (impp x (impp y (andp x y)))) .
Proof.
  unfold provable, impp, andp. auto.
Qed.

Lemma andp_elim1 : (forall x y : expr, provable (impp (andp x y) x)) .
Proof.
  unfold provable, impp, andp. tauto.
Qed.

Lemma andp_elim2 : (forall x y : expr, provable (impp (andp x y) y)) .
Proof.
  unfold provable, impp, andp. tauto.
Qed.

Lemma modus_ponens : (forall x y : expr, provable (impp x y) -> provable x -> provable y) .
Proof.
  unfold provable, impp, andp. auto.
Qed.

Lemma axiom1 : (forall x y : expr, provable (impp x (impp y x))) .
Proof.
  unfold provable, impp. auto.
Qed.

Lemma axiom2 : (forall x y z : expr, provable (impp (impp x (impp y z)) (impp (impp x y) (impp x z)))) .
Proof.
  unfold provable, impp. auto.
Qed.

End NaiveRule.
