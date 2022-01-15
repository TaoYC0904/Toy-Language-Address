Require Import HypotheticalExternLib .
Require Import Coq.Numbers.BinNums.
Require Import Coq.PArith.BinPosDef.
Require Import Logic.lib.PTree.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Lists.List.
Import ListNotations.

Module Type LanguageSig.
  Parameter Inline expr : forall `{ para }, Type .
  Section LanguageSig.
  Context `{ para }.
  Parameter provable : (expr -> Prop) .
  Parameter impp : (expr -> expr -> expr) .
  Parameter andp : (expr -> expr -> expr) .
  Parameter Inline sepcon : (expr -> expr -> expr) .
  Parameter Inline emp : expr .
  End LanguageSig.
End LanguageSig.

Module DerivedNames (Names: LanguageSig).
Include Names.
  Definition __PARA__ : Type :=  para .
  Section DerivedNames.
  Context `{ para }.
  Definition iffp := (fun x y : expr => andp (impp x y) (impp y x)) .
  Definition multi_imp := (fun (xs : list expr) (y : expr) => fold_right impp y xs) .
  Definition derivable1 := (fun x y : expr => provable (impp x y)) .
  Definition logic_equiv := (fun x y : expr => provable (impp x y) /\ provable (impp y x)) .
  End DerivedNames.
End DerivedNames.

Module Type PrimitiveRuleSig (Names: LanguageSig).
Include DerivedNames (Names).
  Section PrimitiveRuleSig.
  Context `{ para }.
  Axiom sepcon_emp : (forall x : expr, provable (iffp (sepcon x emp) x)) .
  Axiom sepcon_comm : (forall x y : expr, provable (iffp (sepcon x y) (sepcon y x))) .
  Axiom sepcon_assoc : (forall x y z : expr, provable (iffp (sepcon x (sepcon y z)) (sepcon (sepcon x y) z))) .
  Axiom sepcon_mono : (forall x1 x2 y1 y2 : expr, provable (impp x1 x2) -> provable (impp y1 y2) -> provable (impp (sepcon x1 y1) (sepcon x2 y2))) .
  Axiom andp_intros : (forall x y : expr, provable (impp x (impp y (andp x y)))) .
  Axiom andp_elim1 : (forall x y : expr, provable (impp (andp x y) x)) .
  Axiom andp_elim2 : (forall x y : expr, provable (impp (andp x y) y)) .
  Axiom modus_ponens : (forall x y : expr, provable (impp x y) -> provable x -> provable y) .
  Axiom axiom1 : (forall x y : expr, provable (impp x (impp y x))) .
  Axiom axiom2 : (forall x y z : expr, provable (impp (impp x (impp y z)) (impp (impp x y) (impp x z)))) .
  End PrimitiveRuleSig.
End PrimitiveRuleSig.

Module Type LogicTheoremSig (Names: LanguageSig) (Rules: PrimitiveRuleSig Names).
Include Rules.
Parameter Inline tree_pos : forall `{ para }, Type .
  Section LogicTheoremSig.
  Context `{ para }.
  Axiom logic_equiv_derivable1 : (forall x y : expr, logic_equiv x y <-> derivable1 x y /\ derivable1 y x) .
  Axiom logic_equiv_impp : (forall x1 x2 y1 y2 : expr, logic_equiv x1 x2 -> logic_equiv y1 y2 -> logic_equiv (impp x1 y1) (impp x2 y2)) .
  Axiom logic_equiv_refl : (forall x : expr, logic_equiv x x) .
  Axiom logic_equiv_symm : (forall x y : expr, logic_equiv x y -> logic_equiv y x) .
  Axiom logic_equiv_trans : (forall x y z : expr, logic_equiv x y -> logic_equiv y z -> logic_equiv x z) .
  Axiom sepcon_emp_left : (forall x : expr, derivable1 (sepcon x emp) x) .
  Axiom sepcon_emp_right : (forall x : expr, derivable1 x (sepcon x emp)) .
  Axiom derivable1_sepcon_comm : (forall x y : expr, derivable1 (sepcon x y) (sepcon y x)) .
  Axiom derivable1_sepcon_assoc1 : (forall x y z : expr, derivable1 (sepcon x (sepcon y z)) (sepcon (sepcon x y) z)) .
  Axiom derivable1_sepcon_mono : (forall x1 x2 y1 y2 : expr, derivable1 x1 x2 -> derivable1 y1 y2 -> derivable1 (sepcon x1 y1) (sepcon x2 y2)) .
  Axiom derivable1_refl : (forall x : expr, derivable1 x x) .
  Axiom derivable1_trans : (forall x y z : expr, derivable1 x y -> derivable1 y z -> derivable1 x z) .
  Axiom sepcon_emp1 : (forall x : expr, provable (impp (sepcon x emp) x)) .
  Axiom sepcon_emp2 : (forall x : expr, provable (impp x (sepcon x emp))) .
  Axiom sepcon_comm_impp : (forall x y : expr, provable (impp (sepcon x y) (sepcon y x))) .
  Axiom sepcon_assoc1 : (forall x y z : expr, provable (impp (sepcon x (sepcon y z)) (sepcon (sepcon x y) z))) .
  Axiom iffp_intros : (forall x y : expr, provable (impp (impp x y) (impp (impp y x) (iffp x y)))) .
  Axiom iffp_elim1 : (forall x y : expr, provable (impp (iffp x y) (impp x y))) .
  Axiom iffp_elim2 : (forall x y : expr, provable (impp (iffp x y) (impp y x))) .
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
  Axiom provable_proper_impp : (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (impp x y)) Basics.impl) provable) .
  Axiom impp_proper_impp : (Morphisms.Proper (Morphisms.respectful (Basics.flip (fun x y : expr => provable (impp x y))) (Morphisms.respectful (fun x y : expr => provable (impp x y)) (fun x y : expr => provable (impp x y)))) impp) .
  Axiom andp_comm : (forall x y : expr, provable (iffp (andp x y) (andp y x))) .
  Axiom andp_assoc : (forall x y z : expr, provable (iffp (andp (andp x y) z) (andp x (andp y z)))) .
  Axiom impp_curry : (forall x y z : expr, provable (impp (impp x (impp y z)) (impp (andp x y) z))) .
  Axiom impp_uncurry : (forall x y z : expr, provable (impp (impp (andp x y) z) (impp x (impp y z)))) .
  Axiom solve_impp_trans : (forall x y z : expr, provable (impp x y) -> provable (impp y z) -> provable (impp x z)) .
  Axiom andp_proper_impp : (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (impp x y)) (Morphisms.respectful (fun x y : expr => provable (impp x y)) (fun x y : expr => provable (impp x y)))) andp) .
  Axiom provable_iffp_equiv : (RelationClasses.Equivalence (fun x y : expr => provable (iffp x y))) .
  Axiom provable_proper_iffp : (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (iffp x y)) iff) provable) .
  Axiom impp_proper_iffp : (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (iffp x y)) (Morphisms.respectful (fun x y : expr => provable (iffp x y)) (fun x y : expr => provable (iffp x y)))) impp) .
  Axiom andp_proper_iffp : (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (iffp x y)) (Morphisms.respectful (fun x y : expr => provable (iffp x y)) (fun x y : expr => provable (iffp x y)))) andp) .
  Axiom iffp_proper_iffp : (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (iffp x y)) (Morphisms.respectful (fun x y : expr => provable (iffp x y)) (fun x y : expr => provable (iffp x y)))) iffp) .
  Axiom cancel_ready : (forall x y : expr, provable (impp (sepcon x emp) y) -> provable (impp x y)) .
  Axiom cancel_one_succeed : (forall u x y z : expr, provable (impp (sepcon x y) z) -> provable (impp (sepcon (sepcon u x) y) (sepcon u z))) .
  Axiom cancel_one_giveup : (forall x y z w v : expr, provable (impp (sepcon x (sepcon y z)) (sepcon w v)) -> provable (impp (sepcon (sepcon y x) z) (sepcon w v))) .
  Axiom cancel_rev : (forall x y z w : expr, provable (impp (sepcon (sepcon y x) z) w) -> provable (impp (sepcon x (sepcon y z)) w)) .
  Axiom cancel_finish : (forall x : expr, provable (impp (sepcon x emp) x)) .
  Axiom sepcon_proper_impp : (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (impp x y)) (Morphisms.respectful (fun x y : expr => provable (impp x y)) (fun x y : expr => provable (impp x y)))) sepcon) .
  Axiom sepcon_proper_iffp : (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (iffp x y)) (Morphisms.respectful (fun x y : expr => provable (iffp x y)) (fun x y : expr => provable (iffp x y)))) sepcon) .
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
  Axiom cancel_sound : (forall tep teq : tree_pos, cancel_same tep teq -> provable (cancel_different tep teq) -> provable (restore tep teq)) .
  Axiom impp_proper_equiv : (Morphisms.Proper (Morphisms.respectful logic_equiv (Morphisms.respectful logic_equiv logic_equiv)) impp) .
  Axiom sepcon_proper_logic_equiv : (Morphisms.Proper (Morphisms.respectful logic_equiv (Morphisms.respectful logic_equiv logic_equiv)) sepcon) .
  Axiom provable_proper_equiv : (Morphisms.Proper (Morphisms.respectful logic_equiv iff) provable) .
  Axiom logic_equiv_refl_instance : (RelationClasses.Reflexive logic_equiv) .
  Axiom logic_equiv_symm_instance : (RelationClasses.Symmetric logic_equiv) .
  Axiom logic_equiv_trans_instance : (RelationClasses.Transitive logic_equiv) .
  Axiom sepcon_comm_logic_equiv : (forall x y : expr, logic_equiv (sepcon x y) (sepcon y x)) .
  Axiom sepcon_assoc_logic_equiv : (forall x y z : expr, logic_equiv (sepcon x (sepcon y z)) (sepcon (sepcon x y) z)) .
  Axiom sepcon_emp_logic_equiv : (forall x : expr, logic_equiv (sepcon x emp) x) .
  Existing Instance provable_impp_refl_instance .
  Existing Instance provable_proper_impp .
  Existing Instance impp_proper_impp .
  Existing Instance andp_proper_impp .
  Existing Instance provable_iffp_equiv .
  Existing Instance provable_proper_iffp .
  Existing Instance impp_proper_iffp .
  Existing Instance andp_proper_iffp .
  Existing Instance iffp_proper_iffp .
  Existing Instance sepcon_proper_impp .
  Existing Instance sepcon_proper_iffp .
  Existing Instance impp_proper_equiv .
  Existing Instance sepcon_proper_logic_equiv .
  Existing Instance provable_proper_equiv .
  Existing Instance logic_equiv_refl_instance .
  Existing Instance logic_equiv_symm_instance .
  Existing Instance logic_equiv_trans_instance .
  End LogicTheoremSig.
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
  Section LogicTheorem.
  Context `{ para }.
  Instance L : Language := (Build_Language expr) .
  Instance minL : (MinimumLanguage L) := (Build_MinimumLanguage L impp) .
  Instance andpL : (AndLanguage L) := (Build_AndLanguage L andp) .
  Instance sepconL : (SepconLanguage L) := (Build_SepconLanguage L sepcon) .
  Instance empL : (EmpLanguage L) := (Build_EmpLanguage L emp) .
  Instance iffpL : (IffLanguage L) := (Build_IffLanguage L iffp) .
  Instance GammaP : (Provable L) := (Build_Provable L provable) .
  Instance GammaD1 : (Derivable1 L) := (Build_Derivable1 L derivable1) .
  Instance GammaE : (LogicEquiv L) := (Build_LogicEquiv L logic_equiv) .
  Instance minAX : (MinimumAxiomatization L GammaP) := (Build_MinimumAxiomatization L minL GammaP modus_ponens axiom1 axiom2) .
  Instance andpAX : (AndAxiomatization L GammaP) := (Build_AndAxiomatization L minL andpL GammaP andp_intros andp_elim1 andp_elim2) .
  Instance sepconAX_weak_iffp : (SepconAxiomatization_weak_iffp L GammaP) := (Build_SepconAxiomatization_weak_iffp L iffpL sepconL GammaP sepcon_comm sepcon_assoc) .
  Instance sepcon_mono_AX : (SepconMonoAxiomatization L GammaP) := (Build_SepconMonoAxiomatization L minL sepconL GammaP sepcon_mono) .
  Instance empAX_iffp : (EmpAxiomatization_iffp L GammaP) := (Build_EmpAxiomatization_iffp L iffpL sepconL empL GammaP sepcon_emp) .
  Instance iffpDef : (IffDefinition_And_Imp L) := AndImp2Iff_Normal .
  Instance GammaD1P : (Derivable1Provable L GammaP GammaD1) := Provable2Derivable1_Normal .
  Instance GammaEP : (EquivProvable L GammaP GammaE) := Provable2Equiv_Normal .
  Instance iffpAX : (IffAxiomatization L GammaP) := IffFromDefToAX_And_Imp .
  Instance sepconAX_weak : (SepconAxiomatization_weak L GammaP) := SepconAxiomatizationWeakIff2SepconAxiomatizationWeak .
  Instance sepconAX : (SepconAxiomatization L GammaP) := SepconAxiomatizationWeak2SepconAxiomatization .
  Instance empAX : (EmpAxiomatization L GammaP) := EmpAxiomatizationIff2EmpAxiomatization .
  Instance bD : (BasicDeduction L GammaD1) := Axiomatization2Deduction_bD .
  Instance sepconD : (SepconDeduction L GammaD1) := SeparationLogic.Axiomatization2Deduction_sepconD .
  Instance empD : (EmpDeduction L GammaD1) := Axiomatization2Deduction_empD .
  Instance bE : (BasicLogicEquiv L GammaE) := Axiomatization2Equiv_bE .
  Instance GammaED1 : (EquivDerivable1 L GammaD1 GammaE) := Axiomatization2Deduction_GammaED1 .
  Instance imppE : (ImpLogicEquiv L GammaE) := Axiomatization2LogicEquiv_imppE .
Definition tree_pos : Type := tree_pos.
  Definition logic_equiv_derivable1 : (forall x y : expr, logic_equiv x y <-> derivable1 x y /\ derivable1 y x) := logic_equiv_derivable1 .
  Definition logic_equiv_impp : (forall x1 x2 y1 y2 : expr, logic_equiv x1 x2 -> logic_equiv y1 y2 -> logic_equiv (impp x1 y1) (impp x2 y2)) := logic_equiv_impp .
  Definition logic_equiv_refl : (forall x : expr, logic_equiv x x) := logic_equiv_refl .
  Definition logic_equiv_symm : (forall x y : expr, logic_equiv x y -> logic_equiv y x) := logic_equiv_symm .
  Definition logic_equiv_trans : (forall x y z : expr, logic_equiv x y -> logic_equiv y z -> logic_equiv x z) := logic_equiv_trans .
  Definition sepcon_emp_left : (forall x : expr, derivable1 (sepcon x emp) x) := sepcon_emp_left .
  Definition sepcon_emp_right : (forall x : expr, derivable1 x (sepcon x emp)) := sepcon_emp_right .
  Definition derivable1_sepcon_comm : (forall x y : expr, derivable1 (sepcon x y) (sepcon y x)) := derivable1_sepcon_comm .
  Definition derivable1_sepcon_assoc1 : (forall x y z : expr, derivable1 (sepcon x (sepcon y z)) (sepcon (sepcon x y) z)) := derivable1_sepcon_assoc1 .
  Definition derivable1_sepcon_mono : (forall x1 x2 y1 y2 : expr, derivable1 x1 x2 -> derivable1 y1 y2 -> derivable1 (sepcon x1 y1) (sepcon x2 y2)) := derivable1_sepcon_mono .
  Definition derivable1_refl : (forall x : expr, derivable1 x x) := derivable1_refl .
  Definition derivable1_trans : (forall x y z : expr, derivable1 x y -> derivable1 y z -> derivable1 x z) := derivable1_trans .
  Definition sepcon_emp1 : (forall x : expr, provable (impp (sepcon x emp) x)) := sepcon_emp1 .
  Definition sepcon_emp2 : (forall x : expr, provable (impp x (sepcon x emp))) := sepcon_emp2 .
  Definition sepcon_comm_impp : (forall x y : expr, provable (impp (sepcon x y) (sepcon y x))) := sepcon_comm_impp .
  Definition sepcon_assoc1 : (forall x y z : expr, provable (impp (sepcon x (sepcon y z)) (sepcon (sepcon x y) z))) := sepcon_assoc1 .
  Definition iffp_intros : (forall x y : expr, provable (impp (impp x y) (impp (impp y x) (iffp x y)))) := iffp_intros .
  Definition iffp_elim1 : (forall x y : expr, provable (impp (iffp x y) (impp x y))) := iffp_elim1 .
  Definition iffp_elim2 : (forall x y : expr, provable (impp (iffp x y) (impp y x))) := iffp_elim2 .
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
  Definition provable_proper_impp : (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (impp x y)) Basics.impl) provable) := provable_proper_impp .
  Definition impp_proper_impp : (Morphisms.Proper (Morphisms.respectful (Basics.flip (fun x y : expr => provable (impp x y))) (Morphisms.respectful (fun x y : expr => provable (impp x y)) (fun x y : expr => provable (impp x y)))) impp) := impp_proper_impp .
  Definition andp_comm : (forall x y : expr, provable (iffp (andp x y) (andp y x))) := andp_comm .
  Definition andp_assoc : (forall x y z : expr, provable (iffp (andp (andp x y) z) (andp x (andp y z)))) := andp_assoc .
  Definition impp_curry : (forall x y z : expr, provable (impp (impp x (impp y z)) (impp (andp x y) z))) := impp_curry .
  Definition impp_uncurry : (forall x y z : expr, provable (impp (impp (andp x y) z) (impp x (impp y z)))) := impp_uncurry .
  Definition solve_impp_trans : (forall x y z : expr, provable (impp x y) -> provable (impp y z) -> provable (impp x z)) := solve_impp_trans .
  Definition andp_proper_impp : (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (impp x y)) (Morphisms.respectful (fun x y : expr => provable (impp x y)) (fun x y : expr => provable (impp x y)))) andp) := andp_proper_impp .
  Definition provable_iffp_equiv : (RelationClasses.Equivalence (fun x y : expr => provable (iffp x y))) := provable_iffp_equiv .
  Definition provable_proper_iffp : (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (iffp x y)) iff) provable) := provable_proper_iffp .
  Definition impp_proper_iffp : (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (iffp x y)) (Morphisms.respectful (fun x y : expr => provable (iffp x y)) (fun x y : expr => provable (iffp x y)))) impp) := impp_proper_iffp .
  Definition andp_proper_iffp : (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (iffp x y)) (Morphisms.respectful (fun x y : expr => provable (iffp x y)) (fun x y : expr => provable (iffp x y)))) andp) := andp_proper_iffp .
  Definition iffp_proper_iffp : (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (iffp x y)) (Morphisms.respectful (fun x y : expr => provable (iffp x y)) (fun x y : expr => provable (iffp x y)))) iffp) := iffp_proper_iffp .
  Definition cancel_ready : (forall x y : expr, provable (impp (sepcon x emp) y) -> provable (impp x y)) := cancel_ready .
  Definition cancel_one_succeed : (forall u x y z : expr, provable (impp (sepcon x y) z) -> provable (impp (sepcon (sepcon u x) y) (sepcon u z))) := cancel_one_succeed .
  Definition cancel_one_giveup : (forall x y z w v : expr, provable (impp (sepcon x (sepcon y z)) (sepcon w v)) -> provable (impp (sepcon (sepcon y x) z) (sepcon w v))) := cancel_one_giveup .
  Definition cancel_rev : (forall x y z w : expr, provable (impp (sepcon (sepcon y x) z) w) -> provable (impp (sepcon x (sepcon y z)) w)) := cancel_rev .
  Definition cancel_finish : (forall x : expr, provable (impp (sepcon x emp) x)) := cancel_finish .
  Definition sepcon_proper_impp : (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (impp x y)) (Morphisms.respectful (fun x y : expr => provable (impp x y)) (fun x y : expr => provable (impp x y)))) sepcon) := sepcon_proper_impp .
  Definition sepcon_proper_iffp : (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (iffp x y)) (Morphisms.respectful (fun x y : expr => provable (iffp x y)) (fun x y : expr => provable (iffp x y)))) sepcon) := sepcon_proper_iffp .
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
  Definition cancel_sound : (forall tep teq : tree_pos, cancel_same tep teq -> provable (cancel_different tep teq) -> provable (restore tep teq)) := cancel_sound .
  Definition impp_proper_equiv : (Morphisms.Proper (Morphisms.respectful logic_equiv (Morphisms.respectful logic_equiv logic_equiv)) impp) := impp_proper_equiv .
  Definition sepcon_proper_logic_equiv : (Morphisms.Proper (Morphisms.respectful logic_equiv (Morphisms.respectful logic_equiv logic_equiv)) sepcon) := sepcon_proper_logic_equiv .
  Definition provable_proper_equiv : (Morphisms.Proper (Morphisms.respectful logic_equiv iff) provable) := provable_proper_equiv .
  Definition logic_equiv_refl_instance : (RelationClasses.Reflexive logic_equiv) := logic_equiv_refl_instance .
  Definition logic_equiv_symm_instance : (RelationClasses.Symmetric logic_equiv) := logic_equiv_symm_instance .
  Definition logic_equiv_trans_instance : (RelationClasses.Transitive logic_equiv) := logic_equiv_trans_instance .
  Definition sepcon_comm_logic_equiv : (forall x y : expr, logic_equiv (sepcon x y) (sepcon y x)) := sepcon_comm_logic_equiv .
  Definition sepcon_assoc_logic_equiv : (forall x y z : expr, logic_equiv (sepcon x (sepcon y z)) (sepcon (sepcon x y) z)) := sepcon_assoc_logic_equiv .
  Definition sepcon_emp_logic_equiv : (forall x : expr, logic_equiv (sepcon x emp) x) := sepcon_emp_logic_equiv .
  End LogicTheorem.
  Existing Instance provable_impp_refl_instance .
  Existing Instance provable_proper_impp .
  Existing Instance impp_proper_impp .
  Existing Instance andp_proper_impp .
  Existing Instance provable_iffp_equiv .
  Existing Instance provable_proper_iffp .
  Existing Instance impp_proper_iffp .
  Existing Instance andp_proper_iffp .
  Existing Instance iffp_proper_iffp .
  Existing Instance sepcon_proper_impp .
  Existing Instance sepcon_proper_iffp .
  Existing Instance impp_proper_equiv .
  Existing Instance sepcon_proper_logic_equiv .
  Existing Instance provable_proper_equiv .
  Existing Instance logic_equiv_refl_instance .
  Existing Instance logic_equiv_symm_instance .
  Existing Instance logic_equiv_trans_instance .
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
