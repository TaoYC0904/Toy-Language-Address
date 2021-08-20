Require Import Coq.Numbers.BinNums.
Require Import Coq.PArith.BinPosDef.
Require Import Logic.lib.PTree.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Lists.List.
Import ListNotations.

Module Type LanguageSig.
  Parameter Inline expr : Type .
  Definition context := (expr -> Prop) .
  Parameter provable : (expr -> Prop) .
  Parameter impp : (expr -> expr -> expr) .
  Parameter andp : (expr -> expr -> expr) .
  Parameter orp : (expr -> expr -> expr) .
  Parameter Inline sepcon : (expr -> expr -> expr) .
  Parameter negp : (expr -> expr) .
  Parameter falsep : expr .
  Parameter truep : expr .
  Parameter emp : expr .
End LanguageSig.

Module DerivedNames (Names: LanguageSig).
Include Names.
  Definition multi_imp := (fun (xs : list expr) (y : expr) => fold_right impp y xs) .
  Definition empty_context := (Empty_set expr) .
  Definition derivable := (fun (Phi : expr -> Prop) (x : expr) => exists xs : list expr, Forall Phi xs /\ provable (multi_imp xs x)) .
End DerivedNames.

Module Type PrimitiveRuleSig (Names: LanguageSig).
Include DerivedNames (Names).
  Axiom falsep_sepcon_impp : (forall x : expr, provable (impp (sepcon falsep x) falsep)) .
  Axiom sepcon_comm_impp : (forall x y : expr, provable (impp (sepcon x y) (sepcon y x))) .
  Axiom sepcon_assoc1 : (forall x y z : expr, provable (impp (sepcon x (sepcon y z)) (sepcon (sepcon x y) z))) .
  Axiom sepcon_mono : (forall x1 x2 y1 y2 : expr, provable (impp x1 x2) -> provable (impp y1 y2) -> provable (impp (sepcon x1 y1) (sepcon x2 y2))) .
  Axiom andp_intros : (forall x y : expr, provable (impp x (impp y (andp x y)))) .
  Axiom andp_elim1 : (forall x y : expr, provable (impp (andp x y) x)) .
  Axiom andp_elim2 : (forall x y : expr, provable (impp (andp x y) y)) .
  Axiom modus_ponens : (forall x y : expr, provable (impp x y) -> provable x -> provable y) .
  Axiom axiom1 : (forall x y : expr, provable (impp x (impp y x))) .
  Axiom axiom2 : (forall x y z : expr, provable (impp (impp x (impp y z)) (impp (impp x y) (impp x z)))) .
End PrimitiveRuleSig.

Module Type LogicTheoremSig (Names: LanguageSig) (Rules: PrimitiveRuleSig Names).
Include Rules.
Parameter Inline tree_pos : Type .
  Axiom provable_derivable : (forall x : expr, provable x <-> derivable empty_context x) .
  Axiom deduction_andp_intros : (forall (Phi : context) (x y : expr), derivable Phi x -> derivable Phi y -> derivable Phi (andp x y)) .
  Axiom deduction_andp_elim1 : (forall (Phi : context) (x y : expr), derivable Phi (andp x y) -> derivable Phi x) .
  Axiom deduction_andp_elim2 : (forall (Phi : context) (x y : expr), derivable Phi (andp x y) -> derivable Phi y) .
  Axiom deduction_modus_ponens : (forall (Phi : context) (x y : expr), derivable Phi x -> derivable Phi (impp x y) -> derivable Phi y) .
  Axiom deduction_impp_intros : (forall (Phi : Ensemble expr) (x y : expr), derivable (Union expr Phi (Singleton expr x)) y -> derivable Phi (impp x y)) .
  Axiom derivable_finite_witnessed : (forall (Phi : context) (y : expr), derivable Phi y -> exists xs : list expr, Forall Phi xs /\ derivable (fun x : expr => In x xs) y) .
  Axiom deduction_weaken : (forall (Phi Psi : Ensemble expr) (x : expr), Included expr Phi Psi -> derivable Phi x -> derivable Psi x) .
  Axiom derivable_assum : (forall (Phi : Ensemble expr) (x : expr), Ensembles.In expr Phi x -> derivable Phi x) .
  Axiom deduction_subst : (forall (Phi Psi : context) (y : expr), (forall x : expr, Psi x -> derivable Phi x) -> derivable (Union expr Phi Psi) y -> derivable Phi y) .
  Axiom provable_impp_refl : (forall x : expr, provable (impp x x)) .
  Axiom provable_impp_refl' : (forall x y : expr, x = y -> provable (impp x y)) .
  Axiom provable_impp_arg_switch : (forall x y z : expr, provable (impp (impp x (impp y z)) (impp y (impp x z)))) .
  Axiom provable_impp_trans : (forall x y z : expr, provable (impp (impp x y) (impp (impp y z) (impp x z)))) .
  Axiom provable_multi_imp_shrink : (forall (xs : list expr) (x y : expr), provable (impp (impp x (multi_imp xs (impp x y))) (multi_imp xs (impp x y)))) .
  Axiom provable_multi_imp_arg_switch1 : (forall (xs : list expr) (x y : expr), provable (impp (impp x (multi_imp xs y)) (multi_imp xs (impp x y)))) .
  Axiom provable_multi_imp_arg_switch2 : (forall (xs : list expr) (x y : expr), provable (impp (multi_imp xs (impp x y)) (impp x (multi_imp xs y)))) .
  Axiom provable_add_multi_imp_left_head : (forall (xs1 xs2 : list expr) (y : expr), provable (impp (multi_imp xs2 y) (multi_imp (xs1 ++ xs2) y))) .
  Axiom provable_add_multi_imp_left_tail : (forall (xs1 xs2 : list expr) (y : expr), provable (impp (multi_imp xs1 y) (multi_imp (xs1 ++ xs2) y))) .
  Axiom provable_multi_imp_modus_ponens : (forall (xs : list expr) (y z : expr), provable (impp (multi_imp xs y) (impp (multi_imp xs (impp y z)) (multi_imp xs z)))) .
  Axiom provable_multi_imp_weaken : (forall (xs : list expr) (x y : expr), provable (impp x y) -> provable (impp (multi_imp xs x) (multi_imp xs y))) .
  Axiom provable_impp_refl_instance : (RelationClasses.Reflexive (fun x y : expr => provable (impp x y))) .
  Axiom deduction_impp_elim : (forall (Phi : context) (x y : expr), derivable Phi (impp x y) -> derivable (Union expr Phi (Singleton expr x)) y) .
  Axiom deduction_theorem : (forall (Phi : context) (x y : expr), derivable (Union expr Phi (Singleton expr x)) y <-> derivable Phi (impp x y)) .
  Axiom deduction_theorem_multi_imp : (forall (Phi : context) (xs : list expr) (y : expr), derivable (Union expr Phi (fun x : expr => In x xs)) y <-> derivable Phi (multi_imp xs y)) .
  Axiom derivable_impp_refl : (forall (Phi : context) (x : expr), derivable Phi (impp x x)) .
  Axiom deduction_left_impp_intros : (forall (Phi : context) (x y : expr), derivable Phi x -> derivable Phi (impp y x)) .
  Axiom derivable_modus_ponens : (forall (Phi : context) (x y : expr), derivable Phi (impp x (impp (impp x y) y))) .
  Axiom deduction_impp_trans : (forall (Phi : context) (x y z : expr), derivable Phi (impp x y) -> derivable Phi (impp y z) -> derivable Phi (impp x z)) .
  Axiom deduction_impp_arg_switch : (forall (Phi : context) (x y z : expr), derivable Phi (impp x (impp y z)) -> derivable Phi (impp y (impp x z))) .
  Axiom provable_proper_impp : (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (impp x y)) Basics.impl) provable) .
  Axiom impp_proper_impp : (Morphisms.Proper (Morphisms.respectful (Basics.flip (fun x y : expr => provable (impp x y))) (Morphisms.respectful (fun x y : expr => provable (impp x y)) (fun x y : expr => provable (impp x y)))) impp) .
  Axiom derivable_proper_impp : (Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful (fun x y : expr => provable (impp x y)) Basics.impl)) derivable) .
  Axiom impp_curry : (forall x y z : expr, provable (impp (impp x (impp y z)) (impp (andp x y) z))) .
  Axiom impp_uncurry : (forall x y z : expr, provable (impp (impp (andp x y) z) (impp x (impp y z)))) .
  Axiom solve_impp_trans : (forall x y z : expr, provable (impp x y) -> provable (impp y z) -> provable (impp x z)) .
  Axiom andp_proper_impp : (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (impp x y)) (Morphisms.respectful (fun x y : expr => provable (impp x y)) (fun x y : expr => provable (impp x y)))) andp) .
  Axiom cancel_one_succeed : (forall u x y z : expr, provable (impp (sepcon x y) z) -> provable (impp (sepcon (sepcon u x) y) (sepcon u z))) .
  Axiom cancel_one_giveup : (forall x y z w v : expr, provable (impp (sepcon x (sepcon y z)) (sepcon w v)) -> provable (impp (sepcon (sepcon y x) z) (sepcon w v))) .
  Axiom cancel_rev : (forall x y z w : expr, provable (impp (sepcon (sepcon y x) z) w) -> provable (impp (sepcon x (sepcon y z)) w)) .
  Axiom sepcon_proper_impp : (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (impp x y)) (Morphisms.respectful (fun x y : expr => provable (impp x y)) (fun x y : expr => provable (impp x y)))) sepcon) .
  Axiom expr_deep : Set .
  Axiom impp_deep : (expr_deep -> expr_deep -> expr_deep) .
  Axiom sepcon_deep : (expr_deep -> expr_deep -> expr_deep) .
  Axiom emp_deep : expr_deep .
  Axiom varp_deep : (nat -> expr_deep) .
  Axiom var_pos : (expr -> option positive -> tree_pos) .
  Axiom sepcon_pos : (tree_pos -> tree_pos -> tree_pos) .
  Axiom cancel_mark : (expr_deep -> expr_deep -> tree_pos -> tree_pos -> tree_pos * tree_pos) .
  Axiom cancel_different : (tree_pos -> tree_pos -> expr) .
  Axiom cancel_same : (tree_pos -> tree_pos -> Prop) .
  Axiom restore : (tree_pos -> tree_pos -> expr) .
  Existing Instance provable_impp_refl_instance .
  Existing Instance provable_proper_impp .
  Existing Instance impp_proper_impp .
  Existing Instance derivable_proper_impp .
  Existing Instance andp_proper_impp .
  Existing Instance sepcon_proper_impp .
End LogicTheoremSig.

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
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.ProofTheory.DerivedRules.
Require Import Logic.SeparationLogic.ProofTheory.TheoryOfCancel.
Require Import Logic.SeparationLogic.ProofTheory.TheoryOfSeparationAxioms.
Require Import Logic.SeparationLogic.ProofTheory.IterSepcon.
Require Import Logic.SeparationLogic.ProofTheory.Corable.
Require Import Logic.SeparationLogic.ProofTheory.Deduction.
Require Import Logic.GeneralLogic.ProofTheory.BasicLogicEquiv.

Module LogicTheorem (Names: LanguageSig) (Rules: PrimitiveRuleSig Names) <: LogicTheoremSig Names Rules.
Include Rules.
  Instance L : Language := (Build_Language expr) .
  Instance minL : (MinimumLanguage L) := (Build_MinimumLanguage L impp) .
  Instance andpL : (AndLanguage L) := (Build_AndLanguage L andp) .
  Instance orpL : (OrLanguage L) := (Build_OrLanguage L orp) .
  Instance sepconL : (SepconLanguage L) := (Build_SepconLanguage L sepcon) .
  Instance negpL : (NegLanguage L) := (Build_NegLanguage L negp) .
  Instance falsepL : (FalseLanguage L) := (Build_FalseLanguage L falsep) .
  Instance truepL : (TrueLanguage L) := (Build_TrueLanguage L truep) .
  Instance empL : (EmpLanguage L) := (Build_EmpLanguage L emp) .
  Instance GammaP : (Provable L) := (Build_Provable L provable) .
  Instance GammaD : (Derivable L) := (Build_Derivable L derivable) .
  Instance minAX : (MinimumAxiomatization L GammaP) := (Build_MinimumAxiomatization L minL GammaP modus_ponens axiom1 axiom2) .
  Instance andpAX : (AndAxiomatization L GammaP) := (Build_AndAxiomatization L minL andpL GammaP andp_intros andp_elim1 andp_elim2) .
  Instance sepconAX_weak : (SepconAxiomatization_weak L GammaP) := (Build_SepconAxiomatization_weak L minL sepconL GammaP sepcon_comm_impp sepcon_assoc1) .
  Instance sepcon_mono_AX : (SepconMonoAxiomatization L GammaP) := (Build_SepconMonoAxiomatization L minL sepconL GammaP sepcon_mono) .
  Instance sepcon_falsep_AX : (SepconFalseAxiomatization L GammaP) := (Build_SepconFalseAxiomatization L minL falsepL sepconL GammaP falsep_sepcon_impp) .
  Instance GammaDP : (DerivableProvable L GammaP GammaD) := Provable2Derivable_Normal .
  Instance GammaPD : (ProvableDerivable L GammaP GammaD) := Axiomatization2SequentCalculus_GammaPD .
  Instance bSC : (BasicSequentCalculus L GammaD) := Axiomatization2SequentCalculus_bSC .
  Instance fwSC : (FiniteWitnessedSequentCalculus L GammaD) := Axiomatization2SequentCalculus_fwSC .
  Instance minSC : (MinimumSequentCalculus L GammaD) := Axiomatization2SequentCalculus_minSC .
  Instance andpSC : (AndSequentCalculus L GammaD) := Axiomatization2SequentCalculus_andpSC .
  Instance sepconAX : (SepconAxiomatization L GammaP) := SepconAxiomatizationWeak2SepconAxiomatization .
Definition tree_pos : Type := tree_pos.
  Definition provable_derivable : (forall x : expr, provable x <-> derivable empty_context x) := provable_derivable .
  Definition deduction_andp_intros : (forall (Phi : context) (x y : expr), derivable Phi x -> derivable Phi y -> derivable Phi (andp x y)) := deduction_andp_intros .
  Definition deduction_andp_elim1 : (forall (Phi : context) (x y : expr), derivable Phi (andp x y) -> derivable Phi x) := deduction_andp_elim1 .
  Definition deduction_andp_elim2 : (forall (Phi : context) (x y : expr), derivable Phi (andp x y) -> derivable Phi y) := deduction_andp_elim2 .
  Definition deduction_modus_ponens : (forall (Phi : context) (x y : expr), derivable Phi x -> derivable Phi (impp x y) -> derivable Phi y) := deduction_modus_ponens .
  Definition deduction_impp_intros : (forall (Phi : Ensemble expr) (x y : expr), derivable (Union expr Phi (Singleton expr x)) y -> derivable Phi (impp x y)) := deduction_impp_intros .
  Definition derivable_finite_witnessed : (forall (Phi : context) (y : expr), derivable Phi y -> exists xs : list expr, Forall Phi xs /\ derivable (fun x : expr => In x xs) y) := derivable_finite_witnessed .
  Definition deduction_weaken : (forall (Phi Psi : Ensemble expr) (x : expr), Included expr Phi Psi -> derivable Phi x -> derivable Psi x) := deduction_weaken .
  Definition derivable_assum : (forall (Phi : Ensemble expr) (x : expr), Ensembles.In expr Phi x -> derivable Phi x) := derivable_assum .
  Definition deduction_subst : (forall (Phi Psi : context) (y : expr), (forall x : expr, Psi x -> derivable Phi x) -> derivable (Union expr Phi Psi) y -> derivable Phi y) := deduction_subst .
  Definition provable_impp_refl : (forall x : expr, provable (impp x x)) := provable_impp_refl .
  Definition provable_impp_refl' : (forall x y : expr, x = y -> provable (impp x y)) := provable_impp_refl' .
  Definition provable_impp_arg_switch : (forall x y z : expr, provable (impp (impp x (impp y z)) (impp y (impp x z)))) := provable_impp_arg_switch .
  Definition provable_impp_trans : (forall x y z : expr, provable (impp (impp x y) (impp (impp y z) (impp x z)))) := provable_impp_trans .
  Definition provable_multi_imp_shrink : (forall (xs : list expr) (x y : expr), provable (impp (impp x (multi_imp xs (impp x y))) (multi_imp xs (impp x y)))) := provable_multi_imp_shrink .
  Definition provable_multi_imp_arg_switch1 : (forall (xs : list expr) (x y : expr), provable (impp (impp x (multi_imp xs y)) (multi_imp xs (impp x y)))) := provable_multi_imp_arg_switch1 .
  Definition provable_multi_imp_arg_switch2 : (forall (xs : list expr) (x y : expr), provable (impp (multi_imp xs (impp x y)) (impp x (multi_imp xs y)))) := provable_multi_imp_arg_switch2 .
  Definition provable_add_multi_imp_left_head : (forall (xs1 xs2 : list expr) (y : expr), provable (impp (multi_imp xs2 y) (multi_imp (xs1 ++ xs2) y))) := provable_add_multi_imp_left_head .
  Definition provable_add_multi_imp_left_tail : (forall (xs1 xs2 : list expr) (y : expr), provable (impp (multi_imp xs1 y) (multi_imp (xs1 ++ xs2) y))) := provable_add_multi_imp_left_tail .
  Definition provable_multi_imp_modus_ponens : (forall (xs : list expr) (y z : expr), provable (impp (multi_imp xs y) (impp (multi_imp xs (impp y z)) (multi_imp xs z)))) := provable_multi_imp_modus_ponens .
  Definition provable_multi_imp_weaken : (forall (xs : list expr) (x y : expr), provable (impp x y) -> provable (impp (multi_imp xs x) (multi_imp xs y))) := provable_multi_imp_weaken .
  Definition provable_impp_refl_instance : (RelationClasses.Reflexive (fun x y : expr => provable (impp x y))) := provable_impp_refl_instance .
  Definition deduction_impp_elim : (forall (Phi : context) (x y : expr), derivable Phi (impp x y) -> derivable (Union expr Phi (Singleton expr x)) y) := deduction_impp_elim .
  Definition deduction_theorem : (forall (Phi : context) (x y : expr), derivable (Union expr Phi (Singleton expr x)) y <-> derivable Phi (impp x y)) := deduction_theorem .
  Definition deduction_theorem_multi_imp : (forall (Phi : context) (xs : list expr) (y : expr), derivable (Union expr Phi (fun x : expr => In x xs)) y <-> derivable Phi (multi_imp xs y)) := deduction_theorem_multi_imp .
  Definition derivable_impp_refl : (forall (Phi : context) (x : expr), derivable Phi (impp x x)) := derivable_impp_refl .
  Definition deduction_left_impp_intros : (forall (Phi : context) (x y : expr), derivable Phi x -> derivable Phi (impp y x)) := deduction_left_impp_intros .
  Definition derivable_modus_ponens : (forall (Phi : context) (x y : expr), derivable Phi (impp x (impp (impp x y) y))) := derivable_modus_ponens .
  Definition deduction_impp_trans : (forall (Phi : context) (x y z : expr), derivable Phi (impp x y) -> derivable Phi (impp y z) -> derivable Phi (impp x z)) := deduction_impp_trans .
  Definition deduction_impp_arg_switch : (forall (Phi : context) (x y z : expr), derivable Phi (impp x (impp y z)) -> derivable Phi (impp y (impp x z))) := deduction_impp_arg_switch .
  Definition provable_proper_impp : (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (impp x y)) Basics.impl) provable) := provable_proper_impp .
  Definition impp_proper_impp : (Morphisms.Proper (Morphisms.respectful (Basics.flip (fun x y : expr => provable (impp x y))) (Morphisms.respectful (fun x y : expr => provable (impp x y)) (fun x y : expr => provable (impp x y)))) impp) := impp_proper_impp .
  Definition derivable_proper_impp : (Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful (fun x y : expr => provable (impp x y)) Basics.impl)) derivable) := derivable_proper_impp .
  Definition impp_curry : (forall x y z : expr, provable (impp (impp x (impp y z)) (impp (andp x y) z))) := impp_curry .
  Definition impp_uncurry : (forall x y z : expr, provable (impp (impp (andp x y) z) (impp x (impp y z)))) := impp_uncurry .
  Definition solve_impp_trans : (forall x y z : expr, provable (impp x y) -> provable (impp y z) -> provable (impp x z)) := solve_impp_trans .
  Definition andp_proper_impp : (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (impp x y)) (Morphisms.respectful (fun x y : expr => provable (impp x y)) (fun x y : expr => provable (impp x y)))) andp) := andp_proper_impp .
  Definition cancel_one_succeed : (forall u x y z : expr, provable (impp (sepcon x y) z) -> provable (impp (sepcon (sepcon u x) y) (sepcon u z))) := cancel_one_succeed .
  Definition cancel_one_giveup : (forall x y z w v : expr, provable (impp (sepcon x (sepcon y z)) (sepcon w v)) -> provable (impp (sepcon (sepcon y x) z) (sepcon w v))) := cancel_one_giveup .
  Definition cancel_rev : (forall x y z w : expr, provable (impp (sepcon (sepcon y x) z) w) -> provable (impp (sepcon x (sepcon y z)) w)) := cancel_rev .
  Definition sepcon_proper_impp : (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (impp x y)) (Morphisms.respectful (fun x y : expr => provable (impp x y)) (fun x y : expr => provable (impp x y)))) sepcon) := sepcon_proper_impp .
  Definition expr_deep : Set := expr_deep .
  Definition impp_deep : (expr_deep -> expr_deep -> expr_deep) := impp_deep .
  Definition sepcon_deep : (expr_deep -> expr_deep -> expr_deep) := sepcon_deep .
  Definition emp_deep : expr_deep := emp_deep .
  Definition varp_deep : (nat -> expr_deep) := varp_deep .
  Definition var_pos : (expr -> option positive -> tree_pos) := var_pos .
  Definition sepcon_pos : (tree_pos -> tree_pos -> tree_pos) := sepcon_pos .
  Definition cancel_mark : (expr_deep -> expr_deep -> tree_pos -> tree_pos -> tree_pos * tree_pos) := cancel_mark .
  Definition cancel_different : (tree_pos -> tree_pos -> expr) := cancel_different .
  Definition cancel_same : (tree_pos -> tree_pos -> Prop) := cancel_same .
  Definition restore : (tree_pos -> tree_pos -> expr) := restore .
  Existing Instance provable_impp_refl_instance .
  Existing Instance provable_proper_impp .
  Existing Instance impp_proper_impp .
  Existing Instance derivable_proper_impp .
  Existing Instance andp_proper_impp .
  Existing Instance sepcon_proper_impp .
End LogicTheorem.

(*Require Logic.PropositionalLogic.DeepEmbedded.Solver.
Module IPSolver (Names: LanguageSig).
  Import Names.
  Ltac ip_solve :=
    change expr with Base.expr;
    change provable with Base.provable;
    change impp with Syntax.impp;
    change andp with Syntax.andp;
    intros; Solver.SolverSound.ipSolver.
End IPSolver.*)
