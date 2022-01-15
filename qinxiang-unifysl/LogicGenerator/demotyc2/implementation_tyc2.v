Require Import ZArith.
Require Import interface_tyc2.

Require Import Logic.SeparationLogic.Sound.Sound_Flat.
Require Import Logic.SeparationLogic.ShallowEmbedded.PredicateSeparationLogic.

Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.ProofTheory.BasicDeduction.

Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimumLogic.ProofTheory.TheoryOfJudgement.

Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.PropositionalLogic.ProofTheory.TheoryOfIteratedConnectives.
Require Import Logic.PropositionalLogic.ProofTheory.TheoryOfClassicalAxioms.
Require Import Logic.PropositionalLogic.ProofTheory.TheoryOfPropositionalConnectives.

Require Import Logic.MetaLogicInj.Syntax.
Require Import Logic.MetaLogicInj.ProofTheory.ProofRules.

Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.Semantics.WeakSemantics.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.ProofTheory.DerivedRules.
Require Import Logic.SeparationLogic.ProofTheory.TheoryOfCancel.
Require Import Logic.SeparationLogic.ProofTheory.TheoryOfSeparationAxioms.
Require Import Logic.SeparationLogic.ProofTheory.IterSepcon.
Require Import Logic.SeparationLogic.ProofTheory.Corable.
Require Import Logic.SeparationLogic.ProofTheory.Deduction.

Require Import Logic.GeneralLogic.ProofTheory.BasicLogicEquiv.
Require Import Logic.GeneralLogic.ShallowEmbedded.PredicateAsLang.
Require Import Logic.PropositionalLogic.ShallowEmbedded.PredicatePropositionalLogic.

Require Import Logic.SeparationLogic.Model.OSAExamples.
Require Import Logic.SeparationLogic.Model.OSAGenerators.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.

Definition var : Type := nat.

Definition store : Type := var -> Z.

Definition addr : Type := Z.

Definition heap : Type := Heap addr Z.

Definition state : Type := store * heap.

(* Definition join_heap : heap -> heap -> heap -> Prop :=
  fun h1 h2 h3 => 
    forall p : Z,
      (exists v, h1 p = Some v /\ h2 p = None /\ h3 p = Some v) \/
      (exists v, h1 p = None /\ h2 p = Some v /\ h3 p = Some v) \/
      (h1 p = None /\ h2 p = None /\ h3 p = None).

Definition join : state -> state -> state -> Prop :=
  fun st1 st2 st3 => fst st1 = fst st2 /\ fst st2 = fst st3 /\ join_heap (snd st1) (snd st2) (snd st3).

Definition SepCon (e1 e2 : state -> Prop) : state -> Prop :=
  fun st => exists st1 st2, join st1 st2 st /\ e1 st1 /\ e2 st2. *)

(* Definition jjoin (x y : nat -> option Z) : nat -> option Z :=
  fun p => match x p, y p with
    | Some n1, Some n2 => None
    | Some n1, None => Some n1
    | None, Some n2 => Some n2
    | None, None => None
  end. *)

Instance stateR : KripkeModel.KI.Relation (state) := fun x y => x = y.

Instance store_join : Join store := equiv_Join.

Instance heap_join : Join heap := Heap_Join addr Z.

Instance stateJoin : Join state := prod_Join store heap.

Instance stateJ : SeparationAlgebra.Join (state) := stateJoin.

Instance storeSA : SeparationAlgebra store := equiv_SA.

Instance heapSA : SeparationAlgebra heap := Heap_SA addr Z.

Instance stateSA : SeparationAlgebra state := prod_SA store heap.

Module NaiveLang <: LanguageSig.
  Definition expr := state -> Prop.
  Section NaiveLang.
    Definition context := expr -> Prop.
    Definition provable (e : expr) : Prop := forall st, e st.
    Definition impp (e1 e2 : expr) : expr := fun st => e1 st -> e2 st.
    Definition andp (e1 e2 : expr) : expr := fun st => e1 st /\ e2 st.
    Definition sepcon := WeakSemantics.sepcon.
    Definition falsep : expr := fun st => False.
    Definition emp : expr := fun st => forall p, (snd st) p = None.
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

Module T := LogicTheorem NaiveLang NaiveRule.
(*Module Solver := IPSolver NaiveLang.*)
Import T.