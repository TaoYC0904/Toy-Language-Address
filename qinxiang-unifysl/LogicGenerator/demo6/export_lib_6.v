Require Import HypotheticalExternLib .
Require Import implementation_6 .
Require Import Coq.Numbers.BinNums.
Require Import Coq.PArith.BinPosDef.
Require Import Logic.lib.PTree.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Lists.List.
Import ListNotations.

Module ___LogicTheorem___ :=  T .
Module EXPO.
Import ___LogicTheorem___.
  Section EXPO_SECTION.
  Context `{ para }.

  Declare Scope EXPO_scope.
  Local Open Scope EXPO_scope.

  Definition expr : Type := ltac:(let x0 := eval unfold expr in expr in exact x0).
  Ltac unfold_tac x :=
    let x0 :=
    eval cbv beta delta [
       expr
      ] in x
      in exact x0.

  Local Notation "'UNFOLD' x" := ltac:(unfold_tac x) (only parsing, at level 99): EXPO_scope.

  Definition provable : UNFOLD (expr -> Prop) := provable .
  Definition impp : UNFOLD (expr -> expr -> expr) := impp .
  Definition andp : UNFOLD (expr -> expr -> expr) := andp .
  Definition sepcon : UNFOLD (expr -> expr -> expr) := ltac:(let x0 := eval unfold sepcon in sepcon in exact x0).
  Definition emp : UNFOLD expr := ltac:(let x0 := eval unfold emp in emp in exact x0).

  Ltac unfold2_tac x :=
    let x0 :=
    eval cbv beta delta [
       expr
       sepcon
       emp
    ] in x
    in exact x0.
  Local Notation "'UNFOLD2' x" := ltac:(unfold2_tac x) (only parsing, at level 99): EXPO_scope.

  Definition derivable1 := UNFOLD2 (fun x y : expr => provable (impp x y)) .
  Definition logic_equiv := UNFOLD2 (fun x y : expr => provable (impp x y) /\ provable (impp y x)) .
  Definition iffp := UNFOLD2 (fun x y : expr => andp (impp x y) (impp y x)) .
  Definition multi_imp := UNFOLD2 (fun (xs : list expr) (y : expr) => fold_right impp y xs) .
  Definition sepcon_emp : UNFOLD2 (forall x : expr, provable (iffp (sepcon x emp) x)) := sepcon_emp .
  Definition sepcon_comm : UNFOLD2 (forall x y : expr, provable (iffp (sepcon x y) (sepcon y x))) := sepcon_comm .
  Definition sepcon_assoc : UNFOLD2 (forall x y z : expr, provable (iffp (sepcon x (sepcon y z)) (sepcon (sepcon x y) z))) := sepcon_assoc .
  Definition sepcon_mono : UNFOLD2 (forall x1 x2 y1 y2 : expr, provable (impp x1 x2) -> provable (impp y1 y2) -> provable (impp (sepcon x1 y1) (sepcon x2 y2))) := sepcon_mono .
  Definition andp_intros : UNFOLD2 (forall x y : expr, provable (impp x (impp y (andp x y)))) := andp_intros .
  Definition andp_elim1 : UNFOLD2 (forall x y : expr, provable (impp (andp x y) x)) := andp_elim1 .
  Definition andp_elim2 : UNFOLD2 (forall x y : expr, provable (impp (andp x y) y)) := andp_elim2 .
  Definition modus_ponens : UNFOLD2 (forall x y : expr, provable (impp x y) -> provable x -> provable y) := modus_ponens .
  Definition axiom1 : UNFOLD2 (forall x y : expr, provable (impp x (impp y x))) := axiom1 .
  Definition axiom2 : UNFOLD2 (forall x y z : expr, provable (impp (impp x (impp y z)) (impp (impp x y) (impp x z)))) := axiom2 .
Definition tree_pos : Type := tree_pos.
  Definition logic_equiv_derivable1 : UNFOLD2 (forall x y : expr, logic_equiv x y <-> derivable1 x y /\ derivable1 y x) := logic_equiv_derivable1 .
  Definition logic_equiv_impp : UNFOLD2 (forall x1 x2 y1 y2 : expr, logic_equiv x1 x2 -> logic_equiv y1 y2 -> logic_equiv (impp x1 y1) (impp x2 y2)) := logic_equiv_impp .
  Definition logic_equiv_refl : UNFOLD2 (forall x : expr, logic_equiv x x) := logic_equiv_refl .
  Definition logic_equiv_symm : UNFOLD2 (forall x y : expr, logic_equiv x y -> logic_equiv y x) := logic_equiv_symm .
  Definition logic_equiv_trans : UNFOLD2 (forall x y z : expr, logic_equiv x y -> logic_equiv y z -> logic_equiv x z) := logic_equiv_trans .
  Definition sepcon_emp_left : UNFOLD2 (forall x : expr, derivable1 (sepcon x emp) x) := sepcon_emp_left .
  Definition sepcon_emp_right : UNFOLD2 (forall x : expr, derivable1 x (sepcon x emp)) := sepcon_emp_right .
  Definition derivable1_sepcon_comm : UNFOLD2 (forall x y : expr, derivable1 (sepcon x y) (sepcon y x)) := derivable1_sepcon_comm .
  Definition derivable1_sepcon_assoc1 : UNFOLD2 (forall x y z : expr, derivable1 (sepcon x (sepcon y z)) (sepcon (sepcon x y) z)) := derivable1_sepcon_assoc1 .
  Definition derivable1_sepcon_mono : UNFOLD2 (forall x1 x2 y1 y2 : expr, derivable1 x1 x2 -> derivable1 y1 y2 -> derivable1 (sepcon x1 y1) (sepcon x2 y2)) := derivable1_sepcon_mono .
  Definition derivable1_refl : UNFOLD2 (forall x : expr, derivable1 x x) := derivable1_refl .
  Definition derivable1_trans : UNFOLD2 (forall x y z : expr, derivable1 x y -> derivable1 y z -> derivable1 x z) := derivable1_trans .
  Definition sepcon_emp1 : UNFOLD2 (forall x : expr, provable (impp (sepcon x emp) x)) := sepcon_emp1 .
  Definition sepcon_emp2 : UNFOLD2 (forall x : expr, provable (impp x (sepcon x emp))) := sepcon_emp2 .
  Definition sepcon_comm_impp : UNFOLD2 (forall x y : expr, provable (impp (sepcon x y) (sepcon y x))) := sepcon_comm_impp .
  Definition sepcon_assoc1 : UNFOLD2 (forall x y z : expr, provable (impp (sepcon x (sepcon y z)) (sepcon (sepcon x y) z))) := sepcon_assoc1 .
  Definition iffp_intros : UNFOLD2 (forall x y : expr, provable (impp (impp x y) (impp (impp y x) (iffp x y)))) := iffp_intros .
  Definition iffp_elim1 : UNFOLD2 (forall x y : expr, provable (impp (iffp x y) (impp x y))) := iffp_elim1 .
  Definition iffp_elim2 : UNFOLD2 (forall x y : expr, provable (impp (iffp x y) (impp y x))) := iffp_elim2 .
  Definition provable_impp_refl : UNFOLD2 (forall x : expr, provable (impp x x)) := provable_impp_refl .
  Definition provable_impp_refl' : UNFOLD2 (forall x y : expr, x = y -> provable (impp x y)) := provable_impp_refl' .
  Definition provable_impp_arg_switch : UNFOLD2 (forall x y z : expr, provable (impp (impp x (impp y z)) (impp y (impp x z)))) := provable_impp_arg_switch .
  Definition provable_impp_trans : UNFOLD2 (forall x y z : expr, provable (impp (impp x y) (impp (impp y z) (impp x z)))) := provable_impp_trans .
  Definition provable_multi_imp_shrink : UNFOLD2 (forall (xs : list expr) (x y : expr), provable (impp (impp x (multi_imp xs (impp x y))) (multi_imp xs (impp x y)))) := provable_multi_imp_shrink .
  Definition provable_multi_imp_arg_switch1 : UNFOLD2 (forall (xs : list expr) (x y : expr), provable (impp (impp x (multi_imp xs y)) (multi_imp xs (impp x y)))) := provable_multi_imp_arg_switch1 .
  Definition provable_multi_imp_arg_switch2 : UNFOLD2 (forall (xs : list expr) (x y : expr), provable (impp (multi_imp xs (impp x y)) (impp x (multi_imp xs y)))) := provable_multi_imp_arg_switch2 .
  Definition provable_add_multi_imp_left_head : UNFOLD2 (forall (xs1 xs2 : list expr) (y : expr), provable (impp (multi_imp xs2 y) (multi_imp (xs1 ++ xs2) y))) := provable_add_multi_imp_left_head .
  Definition provable_add_multi_imp_left_tail : UNFOLD2 (forall (xs1 xs2 : list expr) (y : expr), provable (impp (multi_imp xs1 y) (multi_imp (xs1 ++ xs2) y))) := provable_add_multi_imp_left_tail .
  Definition provable_multi_imp_modus_ponens : UNFOLD2 (forall (xs : list expr) (y z : expr), provable (impp (multi_imp xs y) (impp (multi_imp xs (impp y z)) (multi_imp xs z)))) := provable_multi_imp_modus_ponens .
  Definition provable_multi_imp_weaken : UNFOLD2 (forall (xs : list expr) (x y : expr), provable (impp x y) -> provable (impp (multi_imp xs x) (multi_imp xs y))) := provable_multi_imp_weaken .
  Definition provable_impp_refl_instance : UNFOLD2 (RelationClasses.Reflexive (fun x y : expr => provable (impp x y))) := provable_impp_refl_instance .
  Definition provable_proper_impp : UNFOLD2 (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (impp x y)) Basics.impl) provable) := provable_proper_impp .
  Definition impp_proper_impp : UNFOLD2 (Morphisms.Proper (Morphisms.respectful (Basics.flip (fun x y : expr => provable (impp x y))) (Morphisms.respectful (fun x y : expr => provable (impp x y)) (fun x y : expr => provable (impp x y)))) impp) := impp_proper_impp .
  Definition andp_comm : UNFOLD2 (forall x y : expr, provable (iffp (andp x y) (andp y x))) := andp_comm .
  Definition andp_assoc : UNFOLD2 (forall x y z : expr, provable (iffp (andp (andp x y) z) (andp x (andp y z)))) := andp_assoc .
  Definition impp_curry : UNFOLD2 (forall x y z : expr, provable (impp (impp x (impp y z)) (impp (andp x y) z))) := impp_curry .
  Definition impp_uncurry : UNFOLD2 (forall x y z : expr, provable (impp (impp (andp x y) z) (impp x (impp y z)))) := impp_uncurry .
  Definition solve_impp_trans : UNFOLD2 (forall x y z : expr, provable (impp x y) -> provable (impp y z) -> provable (impp x z)) := solve_impp_trans .
  Definition andp_proper_impp : UNFOLD2 (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (impp x y)) (Morphisms.respectful (fun x y : expr => provable (impp x y)) (fun x y : expr => provable (impp x y)))) andp) := andp_proper_impp .
  Definition provable_iffp_equiv : UNFOLD2 (RelationClasses.Equivalence (fun x y : expr => provable (iffp x y))) := provable_iffp_equiv .
  Definition provable_proper_iffp : UNFOLD2 (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (iffp x y)) iff) provable) := provable_proper_iffp .
  Definition impp_proper_iffp : UNFOLD2 (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (iffp x y)) (Morphisms.respectful (fun x y : expr => provable (iffp x y)) (fun x y : expr => provable (iffp x y)))) impp) := impp_proper_iffp .
  Definition andp_proper_iffp : UNFOLD2 (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (iffp x y)) (Morphisms.respectful (fun x y : expr => provable (iffp x y)) (fun x y : expr => provable (iffp x y)))) andp) := andp_proper_iffp .
  Definition iffp_proper_iffp : UNFOLD2 (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (iffp x y)) (Morphisms.respectful (fun x y : expr => provable (iffp x y)) (fun x y : expr => provable (iffp x y)))) iffp) := iffp_proper_iffp .
  Definition cancel_ready : UNFOLD2 (forall x y : expr, provable (impp (sepcon x emp) y) -> provable (impp x y)) := cancel_ready .
  Definition cancel_one_succeed : UNFOLD2 (forall u x y z : expr, provable (impp (sepcon x y) z) -> provable (impp (sepcon (sepcon u x) y) (sepcon u z))) := cancel_one_succeed .
  Definition cancel_one_giveup : UNFOLD2 (forall x y z w v : expr, provable (impp (sepcon x (sepcon y z)) (sepcon w v)) -> provable (impp (sepcon (sepcon y x) z) (sepcon w v))) := cancel_one_giveup .
  Definition cancel_rev : UNFOLD2 (forall x y z w : expr, provable (impp (sepcon (sepcon y x) z) w) -> provable (impp (sepcon x (sepcon y z)) w)) := cancel_rev .
  Definition cancel_finish : UNFOLD2 (forall x : expr, provable (impp (sepcon x emp) x)) := cancel_finish .
  Definition sepcon_proper_impp : UNFOLD2 (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (impp x y)) (Morphisms.respectful (fun x y : expr => provable (impp x y)) (fun x y : expr => provable (impp x y)))) sepcon) := sepcon_proper_impp .
  Definition sepcon_proper_iffp : UNFOLD2 (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (iffp x y)) (Morphisms.respectful (fun x y : expr => provable (iffp x y)) (fun x y : expr => provable (iffp x y)))) sepcon) := sepcon_proper_iffp .
  Definition expr_deep : UNFOLD2 Set := expr_deep .
  Definition impp_deep : UNFOLD2 (expr_deep -> expr_deep -> expr_deep) := impp_deep .
  Definition sepcon_deep : UNFOLD2 (expr_deep -> expr_deep -> expr_deep) := sepcon_deep .
  Definition emp_deep : UNFOLD2 expr_deep := emp_deep .
  Definition varp_deep : UNFOLD2 (nat -> expr_deep) := varp_deep .
  Definition var_pos : UNFOLD2 (expr -> option positive -> tree_pos) := var_pos .
  Definition sepcon_pos : UNFOLD2 (tree_pos -> tree_pos -> tree_pos) := sepcon_pos .
  Definition cancel_mark : UNFOLD2 (expr_deep -> expr_deep -> tree_pos -> tree_pos -> tree_pos * tree_pos) := cancel_mark .
  Definition cancel_different : UNFOLD2 (tree_pos -> tree_pos -> expr) := cancel_different .
  Definition cancel_same : UNFOLD2 (tree_pos -> tree_pos -> Prop) := cancel_same .
  Definition restore : UNFOLD2 (tree_pos -> tree_pos -> expr) := restore .
  Definition cancel_sound : UNFOLD2 (forall tep teq : tree_pos, cancel_same tep teq -> provable (cancel_different tep teq) -> provable (restore tep teq)) := cancel_sound .
  Definition impp_proper_equiv : UNFOLD2 (Morphisms.Proper (Morphisms.respectful logic_equiv (Morphisms.respectful logic_equiv logic_equiv)) impp) := impp_proper_equiv .
  Definition sepcon_proper_logic_equiv : UNFOLD2 (Morphisms.Proper (Morphisms.respectful logic_equiv (Morphisms.respectful logic_equiv logic_equiv)) sepcon) := sepcon_proper_logic_equiv .
  Definition provable_proper_equiv : UNFOLD2 (Morphisms.Proper (Morphisms.respectful logic_equiv iff) provable) := provable_proper_equiv .
  Definition logic_equiv_refl_instance : UNFOLD2 (RelationClasses.Reflexive logic_equiv) := logic_equiv_refl_instance .
  Definition logic_equiv_symm_instance : UNFOLD2 (RelationClasses.Symmetric logic_equiv) := logic_equiv_symm_instance .
  Definition logic_equiv_trans_instance : UNFOLD2 (RelationClasses.Transitive logic_equiv) := logic_equiv_trans_instance .
  Definition sepcon_comm_logic_equiv : UNFOLD2 (forall x y : expr, logic_equiv (sepcon x y) (sepcon y x)) := sepcon_comm_logic_equiv .
  Definition sepcon_assoc_logic_equiv : UNFOLD2 (forall x y z : expr, logic_equiv (sepcon x (sepcon y z)) (sepcon (sepcon x y) z)) := sepcon_assoc_logic_equiv .
  Definition sepcon_emp_logic_equiv : UNFOLD2 (forall x : expr, logic_equiv (sepcon x emp) x) := sepcon_emp_logic_equiv .

  End EXPO_SECTION.

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

End EXPO.

Module EXPO_TRANSPARENTS.
Import EXPO.
Declare Scope expo_transparent_scope.
Notation
  "'expr'"
    := (ltac:(let x0 := eval unfold expr in expr in exact x0)) (only parsing, at level 99): expo_transparent_scope.
Notation
  "'sepcon'"
    := (ltac:(let x0 := eval unfold sepcon in sepcon in exact x0)) (only parsing, at level 99): expo_transparent_scope.
Notation
  "'emp'"
    := (ltac:(let x0 := eval unfold emp in emp in exact x0)) (only parsing, at level 99): expo_transparent_scope.
End EXPO_TRANSPARENTS.
