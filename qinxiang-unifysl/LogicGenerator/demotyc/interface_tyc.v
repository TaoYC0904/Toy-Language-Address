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
  Parameter andp : (expr -> expr -> expr) .
  Parameter orp : (expr -> expr -> expr) .
  Parameter falsep : expr .
  Parameter Inline sepcon : (expr -> expr -> expr) .
  Parameter wand : (expr -> expr -> expr) .
  Parameter Inline emp : expr .
  Parameter impp : (expr -> expr -> expr) .
  Parameter iffp : (expr -> expr -> expr) .
End LanguageSig.

Module DerivedNames (Names: LanguageSig).
Include Names.
  Definition negp := (fun x : expr => impp x falsep) .
  Definition truep := (impp falsep falsep) .
  Definition multi_imp := (fun (xs : list expr) (y : expr) => fold_right impp y xs) .
  Definition iter_andp := (fun xs : list expr => fold_left andp xs truep) .
  Definition iter_sepcon := (fun xs : list expr => fold_left sepcon xs emp) .
  Definition empty_context := (Empty_set expr) .
  Definition derivable := (fun (Phi : expr -> Prop) (x : expr) => exists xs : list expr, Forall Phi xs /\ provable (multi_imp xs x)) .
  Definition derivable1 := (fun x y : expr => provable (impp x y)) .
  Definition logic_equiv := (fun x y : expr => provable (impp x y) /\ provable (impp y x)) .
End DerivedNames.

Module Type PrimitiveRuleSig (Names: LanguageSig).
Include DerivedNames (Names).
  Axiom deduction_contrapositivePP : (forall (Phi : Ensemble expr) (x y : expr), derivable (Union expr Phi (Singleton expr y)) x -> derivable (Union expr Phi (Singleton expr (negp x))) (negp y)) .
  Axiom deduction_contradiction_elim : (forall (Phi : context) (x y : expr), derivable Phi x -> derivable Phi (negp x) -> derivable Phi y) .
  Axiom deduction_double_negp_intros : (forall (Phi : context) (x : expr), derivable Phi x -> derivable Phi (negp (negp x))) .
  Axiom deduction_iffp_intros : (forall (Phi : Ensemble expr) (x y : expr), derivable (Union expr Phi (Singleton expr x)) y -> derivable (Union expr Phi (Singleton expr y)) x -> derivable Phi (iffp x y)) .
  Axiom deduction_iffp_elim1 : (forall (Phi : context) (x y : expr), derivable Phi (iffp x y) -> derivable (Union expr Phi (Singleton expr x)) y) .
  Axiom deduction_iffp_elim2 : (forall (Phi : context) (x y : expr), derivable Phi (iffp x y) -> derivable (Union expr Phi (Singleton expr y)) x) .
  Axiom deduction_truep_intros : (forall Phi : context, derivable Phi truep) .
  Axiom deduction_falsep_elim : (forall (Phi : context) (x : expr), derivable Phi falsep -> derivable Phi x) .
  Axiom deduction_orp_intros1 : (forall (Phi : context) (x y : expr), derivable Phi x -> derivable Phi (orp x y)) .
  Axiom deduction_orp_intros2 : (forall (Phi : context) (x y : expr), derivable Phi y -> derivable Phi (orp x y)) .
  Axiom deduction_orp_elim : (forall (Phi : Ensemble expr) (x y z : expr), derivable (Union expr Phi (Singleton expr x)) z -> derivable (Union expr Phi (Singleton expr y)) z -> derivable (Union expr Phi (Singleton expr (orp x y))) z) .
  Axiom deduction_andp_intros : (forall (Phi : context) (x y : expr), derivable Phi x -> derivable Phi y -> derivable Phi (andp x y)) .
  Axiom deduction_andp_elim1 : (forall (Phi : context) (x y : expr), derivable Phi (andp x y) -> derivable Phi x) .
  Axiom deduction_andp_elim2 : (forall (Phi : context) (x y : expr), derivable Phi (andp x y) -> derivable Phi y) .
  Axiom deduction_modus_ponens : (forall (Phi : context) (x y : expr), derivable Phi x -> derivable Phi (impp x y) -> derivable Phi y) .
  Axiom deduction_impp_intros : (forall (Phi : Ensemble expr) (x y : expr), derivable (Union expr Phi (Singleton expr x)) y -> derivable Phi (impp x y)) .
  Axiom derivable_finite_witnessed : (forall (Phi : context) (y : expr), derivable Phi y -> exists xs : list expr, Forall Phi xs /\ derivable (fun x : expr => In x xs) y) .
  Axiom deduction_weaken : (forall (Phi Psi : Ensemble expr) (x : expr), Included expr Phi Psi -> derivable Phi x -> derivable Psi x) .
  Axiom derivable_assum : (forall (Phi : Ensemble expr) (x : expr), Ensembles.In expr Phi x -> derivable Phi x) .
  Axiom deduction_subst : (forall (Phi Psi : context) (y : expr), (forall x : expr, Psi x -> derivable Phi x) -> derivable (Union expr Phi Psi) y -> derivable Phi y) .
  Axiom falsep_sepcon_impp : (forall x : expr, provable (impp (sepcon falsep x) falsep)) .
  Axiom orp_sepcon_impp : (forall x y z : expr, provable (impp (sepcon (orp x y) z) (orp (sepcon x z) (sepcon y z)))) .
  Axiom iter_sepcon_spec_left1 : (forall xs : list expr, provable (impp (iter_sepcon xs) (fold_left sepcon xs emp))) .
  Axiom iter_sepcon_spec_left2 : (forall xs : list expr, provable (impp (fold_left sepcon xs emp) (iter_sepcon xs))) .
  Axiom sepcon_emp1 : (forall x : expr, provable (impp (sepcon x emp) x)) .
  Axiom sepcon_emp2 : (forall x : expr, provable (impp x (sepcon x emp))) .
  Axiom wand_sepcon_adjoint : (forall x y z : expr, provable (impp (sepcon x y) z) <-> provable (impp x (wand y z))) .
  Axiom sepcon_comm_impp : (forall x y : expr, provable (impp (sepcon x y) (sepcon y x))) .
  Axiom sepcon_assoc1 : (forall x y z : expr, provable (impp (sepcon x (sepcon y z)) (sepcon (sepcon x y) z))) .
  Axiom sepcon_mono : (forall x1 x2 y1 y2 : expr, provable (impp x1 x2) -> provable (impp y1 y2) -> provable (impp (sepcon x1 y1) (sepcon x2 y2))) .
  Axiom iter_andp_spec_left : (forall xs : list expr, provable (iffp (iter_andp xs) (fold_left andp xs truep))) .
  Axiom contrapositivePP : (forall x y : expr, provable (impp (impp y x) (impp (negp x) (negp y)))) .
  Axiom contradiction_elim1 : (forall x y : expr, provable (impp (negp x) (impp x y))) .
  Axiom double_negp_intros : (forall x : expr, provable (impp x (negp (negp x)))) .
  Axiom iffp_intros : (forall x y : expr, provable (impp (impp x y) (impp (impp y x) (iffp x y)))) .
  Axiom iffp_elim1 : (forall x y : expr, provable (impp (iffp x y) (impp x y))) .
  Axiom iffp_elim2 : (forall x y : expr, provable (impp (iffp x y) (impp y x))) .
  Axiom truep_intros : (provable truep) .
  Axiom falsep_elim : (forall x : expr, provable (impp falsep x)) .
  Axiom orp_intros1 : (forall x y : expr, provable (impp x (orp x y))) .
  Axiom orp_intros2 : (forall x y : expr, provable (impp y (orp x y))) .
  Axiom orp_elim : (forall x y z : expr, provable (impp (impp x z) (impp (impp y z) (impp (orp x y) z)))) .
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
  Axiom logic_equiv_derivable1 : (forall x y : expr, logic_equiv x y <-> derivable1 x y /\ derivable1 y x) .
  Axiom provable_derivable : (forall x : expr, provable x <-> derivable empty_context x) .
  Axiom logic_equiv_impp : (forall x1 x2 y1 y2 : expr, logic_equiv x1 x2 -> logic_equiv y1 y2 -> logic_equiv (impp x1 y1) (impp x2 y2)) .
  Axiom logic_equiv_refl : (forall x : expr, logic_equiv x x) .
  Axiom logic_equiv_symm : (forall x y : expr, logic_equiv x y -> logic_equiv y x) .
  Axiom logic_equiv_trans : (forall x y z : expr, logic_equiv x y -> logic_equiv y z -> logic_equiv x z) .
  Axiom sepcon_emp_left : (forall x : expr, derivable1 (sepcon x emp) x) .
  Axiom sepcon_emp_right : (forall x : expr, derivable1 x (sepcon x emp)) .
  Axiom derivable1_wand_sepcon_adjoint : (forall x y z : expr, derivable1 (sepcon x y) z <-> derivable1 x (wand y z)) .
  Axiom derivable1_sepcon_comm : (forall x y : expr, derivable1 (sepcon x y) (sepcon y x)) .
  Axiom derivable1_sepcon_assoc1 : (forall x y z : expr, derivable1 (sepcon x (sepcon y z)) (sepcon (sepcon x y) z)) .
  Axiom derivable1_sepcon_mono : (forall x1 x2 y1 y2 : expr, derivable1 x1 x2 -> derivable1 y1 y2 -> derivable1 (sepcon x1 y1) (sepcon x2 y2)) .
  Axiom derivable1_refl : (forall x : expr, derivable1 x x) .
  Axiom derivable1_trans : (forall x y z : expr, derivable1 x y -> derivable1 y z -> derivable1 x z) .
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
  Axiom negp_fold_unfold : (forall x : expr, provable (iffp (negp x) (impp x falsep))) .
  Axiom deduction_negp_fold : (forall (Phi : Ensemble expr) (x : expr), derivable (Union expr Phi (Singleton expr x)) falsep -> derivable Phi (negp x)) .
  Axiom deduction_negp_unfold : (forall (Phi : context) (x : expr), derivable Phi (negp x) -> derivable (Union expr Phi (Singleton expr x)) falsep) .
  Axiom demorgan_orp_negp : (forall x y : expr, provable (impp (orp (negp x) (negp y)) (negp (andp x y)))) .
  Axiom demorgan_negp_orp : (forall x y : expr, provable (iffp (negp (orp x y)) (andp (negp x) (negp y)))) .
  Axiom provable_truep : (provable truep) .
  Axiom andp_comm : (forall x y : expr, provable (iffp (andp x y) (andp y x))) .
  Axiom andp_assoc : (forall x y z : expr, provable (iffp (andp (andp x y) z) (andp x (andp y z)))) .
  Axiom orp_comm : (forall x y : expr, provable (iffp (orp x y) (orp y x))) .
  Axiom orp_assoc : (forall x y z : expr, provable (iffp (orp (orp x y) z) (orp x (orp y z)))) .
  Axiom andp_dup : (forall x : expr, provable (iffp (andp x x) x)) .
  Axiom orp_dup : (forall x : expr, provable (iffp (orp x x) x)) .
  Axiom impp_curry : (forall x y z : expr, provable (impp (impp x (impp y z)) (impp (andp x y) z))) .
  Axiom impp_uncurry : (forall x y z : expr, provable (impp (impp (andp x y) z) (impp x (impp y z)))) .
  Axiom solve_impp_trans : (forall x y z : expr, provable (impp x y) -> provable (impp y z) -> provable (impp x z)) .
  Axiom solve_andp_intros : (forall x y : expr, provable x -> provable y -> provable (andp x y)) .
  Axiom solve_andp_elim1 : (forall x y : expr, provable (andp x y) -> provable x) .
  Axiom solve_andp_elim2 : (forall x y : expr, provable (andp x y) -> provable y) .
  Axiom negp_fold : (forall x : expr, provable (impp (impp x falsep) (negp x))) .
  Axiom negp_unfold : (forall x : expr, provable (impp (negp x) (impp x falsep))) .
  Axiom andp_proper_impp : (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (impp x y)) (Morphisms.respectful (fun x y : expr => provable (impp x y)) (fun x y : expr => provable (impp x y)))) andp) .
  Axiom orp_proper_impp : (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (impp x y)) (Morphisms.respectful (fun x y : expr => provable (impp x y)) (fun x y : expr => provable (impp x y)))) orp) .
  Axiom negp_proper_impp : (Morphisms.Proper (Morphisms.respectful (Basics.flip (fun x y : expr => provable (impp x y))) (fun x y : expr => provable (impp x y))) negp) .
  Axiom provable_iffp_equiv : (RelationClasses.Equivalence (fun x y : expr => provable (iffp x y))) .
  Axiom provable_proper_iffp : (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (iffp x y)) iff) provable) .
  Axiom impp_proper_iffp : (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (iffp x y)) (Morphisms.respectful (fun x y : expr => provable (iffp x y)) (fun x y : expr => provable (iffp x y)))) impp) .
  Axiom andp_proper_iffp : (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (iffp x y)) (Morphisms.respectful (fun x y : expr => provable (iffp x y)) (fun x y : expr => provable (iffp x y)))) andp) .
  Axiom orp_proper_iffp : (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (iffp x y)) (Morphisms.respectful (fun x y : expr => provable (iffp x y)) (fun x y : expr => provable (iffp x y)))) orp) .
  Axiom iffp_proper_iffp : (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (iffp x y)) (Morphisms.respectful (fun x y : expr => provable (iffp x y)) (fun x y : expr => provable (iffp x y)))) iffp) .
  Axiom negp_proper_iffp : (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (iffp x y)) (fun x y : expr => provable (iffp x y))) negp) .
  Axiom derivable_proper_iffp : (Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful (fun x y : expr => provable (iffp x y)) iff)) derivable) .
  Axiom iter_andp_spec_right : (forall xs : list expr, provable (iffp (iter_andp xs) (fold_right andp truep xs))) .
  Axiom iter_andp_unfold_left_assoc : (forall xs : list expr, provable (iffp (iter_andp xs) match xs with
                                                                                            | []%list => truep
                                                                                            | x :: xs0 => (fix f (xs1 : list expr) (x0 : expr) {struct xs1} : expr := match xs1 with
                                                                                                                                                                      | []%list => x0
                                                                                                                                                                      | x1 :: xs2 => f xs2 (andp x0 x1)
                                                                                                                                                                      end) xs0 x
                                                                                            end)) .
  Axiom iter_andp_unfold_right_assoc : (forall xs : list expr, provable (iffp (iter_andp xs) ((fix f (xs0 : list expr) : expr := match xs0 with
                                                                                                                                 | []%list => truep
                                                                                                                                 | [x]%list => x
                                                                                                                                 | x :: (_ :: _) as xs1 => andp x (f xs1)
                                                                                                                                 end) xs))) .
  Axiom falsep_sepcon : (forall x : expr, provable (iffp (sepcon falsep x) falsep)) .
  Axiom provable_wand_sepcon_modus_ponens1 : (forall x y : expr, provable (impp (sepcon (wand x y) x) y)) .
  Axiom wand_andp : (forall x y z : expr, provable (iffp (wand x (andp y z)) (andp (wand x y) (wand x z)))) .
  Axiom sepcon_falsep : (forall x : expr, provable (iffp (sepcon x falsep) falsep)) .
  Axiom provable_wand_sepcon_modus_ponens2 : (forall x y : expr, provable (impp (sepcon x (wand x y)) y)) .
  Axiom wand_mono : (forall x1 x2 y1 y2 : expr, provable (impp x2 x1) -> provable (impp y1 y2) -> provable (impp (wand x1 y1) (wand x2 y2))) .
  Axiom orp_wand : (forall x y z : expr, provable (iffp (wand (orp x y) z) (andp (wand x z) (wand y z)))) .
  Axiom sepcon_iter_sepcon : (forall xs ys : list expr, provable (iffp (sepcon (iter_sepcon xs) (iter_sepcon ys)) (iter_sepcon (xs ++ ys)))) .
  Axiom cancel_ready : (forall x y : expr, provable (impp (sepcon x emp) y) -> provable (impp x y)) .
  Axiom cancel_one_succeed : (forall u x y z : expr, provable (impp (sepcon x y) z) -> provable (impp (sepcon (sepcon u x) y) (sepcon u z))) .
  Axiom cancel_one_giveup : (forall x y z w v : expr, provable (impp (sepcon x (sepcon y z)) (sepcon w v)) -> provable (impp (sepcon (sepcon y x) z) (sepcon w v))) .
  Axiom cancel_rev : (forall x y z w : expr, provable (impp (sepcon (sepcon y x) z) w) -> provable (impp (sepcon x (sepcon y z)) w)) .
  Axiom cancel_finish : (forall x : expr, provable (impp (sepcon x emp) x)) .
  Axiom iter_sepcon_unfold_right_assoc : (forall xs : list expr, provable (iffp (iter_sepcon xs) ((fix f (xs0 : list expr) : expr := match xs0 with
                                                                                                                                     | []%list => emp
                                                                                                                                     | [x]%list => x
                                                                                                                                     | x :: (_ :: _) as xs1 => sepcon x (f xs1)
                                                                                                                                     end) xs))) .
  Axiom iter_sepcon_unfold_left_assoc : (forall xs : list expr, provable (iffp (iter_sepcon xs) match xs with
                                                                                                | []%list => emp
                                                                                                | x :: xs0 => (fix f (xs1 : list expr) (x0 : expr) {struct xs1} : expr := match xs1 with
                                                                                                                                                                          | []%list => x0
                                                                                                                                                                          | x1 :: xs2 => f xs2 (sepcon x0 x1)
                                                                                                                                                                          end) xs0 x
                                                                                                end)) .
  Axiom sepcon_proper_impp : (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (impp x y)) (Morphisms.respectful (fun x y : expr => provable (impp x y)) (fun x y : expr => provable (impp x y)))) sepcon) .
  Axiom wand_proper_impp : (Morphisms.Proper (Morphisms.respectful (Basics.flip (fun x y : expr => provable (impp x y))) (Morphisms.respectful (fun x y : expr => provable (impp x y)) (fun x y : expr => provable (impp x y)))) wand) .
  Axiom sepcon_proper_iffp : (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (iffp x y)) (Morphisms.respectful (fun x y : expr => provable (iffp x y)) (fun x y : expr => provable (iffp x y)))) sepcon) .
  Axiom wand_proper_iffp : (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (iffp x y)) (Morphisms.respectful (fun x y : expr => provable (iffp x y)) (fun x y : expr => provable (iffp x y)))) wand) .
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
  Existing Instance derivable_proper_impp .
  Existing Instance andp_proper_impp .
  Existing Instance orp_proper_impp .
  Existing Instance negp_proper_impp .
  Existing Instance provable_iffp_equiv .
  Existing Instance provable_proper_iffp .
  Existing Instance impp_proper_iffp .
  Existing Instance andp_proper_iffp .
  Existing Instance orp_proper_iffp .
  Existing Instance iffp_proper_iffp .
  Existing Instance negp_proper_iffp .
  Existing Instance derivable_proper_iffp .
  Existing Instance sepcon_proper_impp .
  Existing Instance wand_proper_impp .
  Existing Instance sepcon_proper_iffp .
  Existing Instance wand_proper_iffp .
  Existing Instance impp_proper_equiv .
  Existing Instance sepcon_proper_logic_equiv .
  Existing Instance provable_proper_equiv .
  Existing Instance logic_equiv_refl_instance .
  Existing Instance logic_equiv_symm_instance .
  Existing Instance logic_equiv_trans_instance .
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
  Instance andpL : (AndLanguage L) := (Build_AndLanguage L andp) .
  Instance orpL : (OrLanguage L) := (Build_OrLanguage L orp) .
  Instance falsepL : (FalseLanguage L) := (Build_FalseLanguage L falsep) .
  Instance sepconL : (SepconLanguage L) := (Build_SepconLanguage L sepcon) .
  Instance wandL : (WandLanguage L) := (Build_WandLanguage L wand) .
  Instance empL : (EmpLanguage L) := (Build_EmpLanguage L emp) .
  Instance minL : (MinimumLanguage L) := (Build_MinimumLanguage L impp) .
  Instance iffpL : (IffLanguage L) := (Build_IffLanguage L iffp) .
  Instance negpL : (NegLanguage L) := (Build_NegLanguage L negp) .
  Instance truepL : (TrueLanguage L) := (Build_TrueLanguage L truep) .
  Instance iter_andp_L : (IterAndLanguage L) := (Build_IterAndLanguage L iter_andp) .
  Instance iter_sepcon_L : (IterSepconLanguage L) := (Build_IterSepconLanguage L iter_sepcon) .
  Instance GammaP : (Provable L) := (Build_Provable L provable) .
  Instance GammaD : (Derivable L) := (Build_Derivable L derivable) .
  Instance GammaD1 : (Derivable1 L) := (Build_Derivable1 L derivable1) .
  Instance GammaE : (LogicEquiv L) := (Build_LogicEquiv L logic_equiv) .
  Instance minAX : (MinimumAxiomatization L GammaP) := (Build_MinimumAxiomatization L minL GammaP modus_ponens axiom1 axiom2) .
  Instance andpAX : (AndAxiomatization L GammaP) := (Build_AndAxiomatization L minL andpL GammaP andp_intros andp_elim1 andp_elim2) .
  Instance orpAX : (OrAxiomatization L GammaP) := (Build_OrAxiomatization L minL orpL GammaP orp_intros1 orp_intros2 orp_elim) .
  Instance falsepAX : (FalseAxiomatization L GammaP) := (Build_FalseAxiomatization L minL falsepL GammaP falsep_elim) .
  Instance truepAX : (TrueAxiomatization L GammaP) := (Build_TrueAxiomatization L truepL GammaP truep_intros) .
  Instance iffpAX : (IffAxiomatization L GammaP) := (Build_IffAxiomatization L minL iffpL GammaP iffp_intros iffp_elim1 iffp_elim2) .
  Instance inegpAX : (IntuitionisticNegAxiomatization L GammaP) := (Build_IntuitionisticNegAxiomatization L minL negpL GammaP contrapositivePP contradiction_elim1 double_negp_intros) .
  Instance iter_andp_AXL : (IterAndAxiomatization_left L GammaP) := (Build_IterAndAxiomatization_left L truepL andpL iffpL iter_andp_L GammaP iter_andp_spec_left) .
  Instance sepconAX : (SepconAxiomatization L GammaP) := (Build_SepconAxiomatization L minL sepconL GammaP sepcon_comm_impp sepcon_assoc1 sepcon_mono) .
  Instance wandAX : (WandAxiomatization L GammaP) := (Build_WandAxiomatization L minL sepconL wandL GammaP wand_sepcon_adjoint) .
  Instance empAX : (EmpAxiomatization L GammaP) := (Build_EmpAxiomatization L minL sepconL empL GammaP sepcon_emp1 sepcon_emp2) .
  Instance iter_sepcon_AXL : (IterSepconAxiomatization_left L GammaP) := (Build_IterSepconAxiomatization_left L minL sepconL empL iter_sepcon_L GammaP iter_sepcon_spec_left1 iter_sepcon_spec_left2) .
  Instance sepcon_orp_AX : (SepconOrAxiomatization L GammaP) := (Build_SepconOrAxiomatization L minL orpL sepconL GammaP orp_sepcon_impp) .
  Instance sepcon_falsep_AX : (SepconFalseAxiomatization L GammaP) := (Build_SepconFalseAxiomatization L minL falsepL sepconL GammaP falsep_sepcon_impp) .
  Instance sepconAX_weak : (SepconAxiomatization_weak L GammaP) := (Build_SepconAxiomatization_weak L minL sepconL GammaP sepcon_comm_impp sepcon_assoc1) .
  Instance bSC : (BasicSequentCalculus L GammaD) := (Build_BasicSequentCalculus L GammaD deduction_weaken derivable_assum deduction_subst) .
  Instance fwSC : (FiniteWitnessedSequentCalculus L GammaD) := (Build_FiniteWitnessedSequentCalculus L GammaD derivable_finite_witnessed) .
  Instance minSC : (MinimumSequentCalculus L GammaD) := (Build_MinimumSequentCalculus L minL GammaD deduction_modus_ponens deduction_impp_intros) .
  Instance andpSC : (AndSequentCalculus L GammaD) := (Build_AndSequentCalculus L andpL GammaD deduction_andp_intros deduction_andp_elim1 deduction_andp_elim2) .
  Instance orpSC : (OrSequentCalculus L GammaD) := (Build_OrSequentCalculus L orpL GammaD deduction_orp_intros1 deduction_orp_intros2 deduction_orp_elim) .
  Instance falsepSC : (FalseSequentCalculus L GammaD) := (Build_FalseSequentCalculus L falsepL GammaD deduction_falsep_elim) .
  Instance truepSC : (TrueSequentCalculus L GammaD) := (Build_TrueSequentCalculus L truepL GammaD deduction_truep_intros) .
  Instance iffpSC : (IffSequentCalculus L GammaD) := (Build_IffSequentCalculus L iffpL GammaD deduction_iffp_intros deduction_iffp_elim1 deduction_iffp_elim2) .
  Instance inegpSC : (IntuitionisticNegSequentCalculus L GammaD) := (Build_IntuitionisticNegSequentCalculus L negpL GammaD deduction_contrapositivePP deduction_contradiction_elim deduction_double_negp_intros) .
  Instance negpDef : (NegDefinition_False_Imp L) := FalseImp2Neg_Normal .
  Instance truepDef : (TrueDefinition_False_Imp L) := FalseImp2True_Normal .
  Instance iter_andp_DL : (IterAndDefinition_left L) := FoldLeftAnd2IterAnd_Normal .
  Instance iter_sepcon_DL : (IterSepconDefinition_left L) := FoldLeftSepcon2IterSepcon_Normal .
  Instance GammaDP : (DerivableProvable L GammaP GammaD) := Provable2Derivable_Normal .
  Instance GammaD1P : (Derivable1Provable L GammaP GammaD1) := Provable2Derivable1_Normal .
  Instance GammaEP : (EquivProvable L GammaP GammaE) := Provable2Equiv_Normal .
  Instance GammaPD : (ProvableDerivable L GammaP GammaD) := Axiomatization2SequentCalculus_GammaPD .
  Instance sepcon_mono_AX : (SepconMonoAxiomatization L GammaP) := TheoryOfSeparationAxioms.Adj2SepconMono .
  Instance bD : (BasicDeduction L GammaD1) := Axiomatization2Deduction_bD .
  Instance sepconD : (SepconDeduction L GammaD1) := SeparationLogic.Axiomatization2Deduction_sepconD .
  Instance wandD : (WandDeduction L GammaD1) := Axiomatization2Deduction_wandD .
  Instance empD : (EmpDeduction L GammaD1) := Axiomatization2Deduction_empD .
  Instance bE : (BasicLogicEquiv L GammaE) := Axiomatization2Equiv_bE .
  Instance GammaED1 : (EquivDerivable1 L GammaD1 GammaE) := Axiomatization2Deduction_GammaED1 .
  Instance imppE : (ImpLogicEquiv L GammaE) := Axiomatization2LogicEquiv_imppE .
Definition tree_pos : Type := tree_pos.
  Definition logic_equiv_derivable1 : (forall x y : expr, logic_equiv x y <-> derivable1 x y /\ derivable1 y x) := logic_equiv_derivable1 .
  Definition provable_derivable : (forall x : expr, provable x <-> derivable empty_context x) := provable_derivable .
  Definition logic_equiv_impp : (forall x1 x2 y1 y2 : expr, logic_equiv x1 x2 -> logic_equiv y1 y2 -> logic_equiv (impp x1 y1) (impp x2 y2)) := logic_equiv_impp .
  Definition logic_equiv_refl : (forall x : expr, logic_equiv x x) := logic_equiv_refl .
  Definition logic_equiv_symm : (forall x y : expr, logic_equiv x y -> logic_equiv y x) := logic_equiv_symm .
  Definition logic_equiv_trans : (forall x y z : expr, logic_equiv x y -> logic_equiv y z -> logic_equiv x z) := logic_equiv_trans .
  Definition sepcon_emp_left : (forall x : expr, derivable1 (sepcon x emp) x) := sepcon_emp_left .
  Definition sepcon_emp_right : (forall x : expr, derivable1 x (sepcon x emp)) := sepcon_emp_right .
  Definition derivable1_wand_sepcon_adjoint : (forall x y z : expr, derivable1 (sepcon x y) z <-> derivable1 x (wand y z)) := derivable1_wand_sepcon_adjoint .
  Definition derivable1_sepcon_comm : (forall x y : expr, derivable1 (sepcon x y) (sepcon y x)) := derivable1_sepcon_comm .
  Definition derivable1_sepcon_assoc1 : (forall x y z : expr, derivable1 (sepcon x (sepcon y z)) (sepcon (sepcon x y) z)) := derivable1_sepcon_assoc1 .
  Definition derivable1_sepcon_mono : (forall x1 x2 y1 y2 : expr, derivable1 x1 x2 -> derivable1 y1 y2 -> derivable1 (sepcon x1 y1) (sepcon x2 y2)) := derivable1_sepcon_mono .
  Definition derivable1_refl : (forall x : expr, derivable1 x x) := derivable1_refl .
  Definition derivable1_trans : (forall x y z : expr, derivable1 x y -> derivable1 y z -> derivable1 x z) := derivable1_trans .
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
  Definition negp_fold_unfold : (forall x : expr, provable (iffp (negp x) (impp x falsep))) := negp_fold_unfold .
  Definition deduction_negp_fold : (forall (Phi : Ensemble expr) (x : expr), derivable (Union expr Phi (Singleton expr x)) falsep -> derivable Phi (negp x)) := deduction_negp_fold .
  Definition deduction_negp_unfold : (forall (Phi : context) (x : expr), derivable Phi (negp x) -> derivable (Union expr Phi (Singleton expr x)) falsep) := deduction_negp_unfold .
  Definition demorgan_orp_negp : (forall x y : expr, provable (impp (orp (negp x) (negp y)) (negp (andp x y)))) := demorgan_orp_negp .
  Definition demorgan_negp_orp : (forall x y : expr, provable (iffp (negp (orp x y)) (andp (negp x) (negp y)))) := demorgan_negp_orp .
  Definition provable_truep : (provable truep) := provable_truep .
  Definition andp_comm : (forall x y : expr, provable (iffp (andp x y) (andp y x))) := andp_comm .
  Definition andp_assoc : (forall x y z : expr, provable (iffp (andp (andp x y) z) (andp x (andp y z)))) := andp_assoc .
  Definition orp_comm : (forall x y : expr, provable (iffp (orp x y) (orp y x))) := orp_comm .
  Definition orp_assoc : (forall x y z : expr, provable (iffp (orp (orp x y) z) (orp x (orp y z)))) := orp_assoc .
  Definition andp_dup : (forall x : expr, provable (iffp (andp x x) x)) := andp_dup .
  Definition orp_dup : (forall x : expr, provable (iffp (orp x x) x)) := orp_dup .
  Definition impp_curry : (forall x y z : expr, provable (impp (impp x (impp y z)) (impp (andp x y) z))) := impp_curry .
  Definition impp_uncurry : (forall x y z : expr, provable (impp (impp (andp x y) z) (impp x (impp y z)))) := impp_uncurry .
  Definition solve_impp_trans : (forall x y z : expr, provable (impp x y) -> provable (impp y z) -> provable (impp x z)) := solve_impp_trans .
  Definition solve_andp_intros : (forall x y : expr, provable x -> provable y -> provable (andp x y)) := solve_andp_intros .
  Definition solve_andp_elim1 : (forall x y : expr, provable (andp x y) -> provable x) := solve_andp_elim1 .
  Definition solve_andp_elim2 : (forall x y : expr, provable (andp x y) -> provable y) := solve_andp_elim2 .
  Definition negp_fold : (forall x : expr, provable (impp (impp x falsep) (negp x))) := negp_fold .
  Definition negp_unfold : (forall x : expr, provable (impp (negp x) (impp x falsep))) := negp_unfold .
  Definition andp_proper_impp : (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (impp x y)) (Morphisms.respectful (fun x y : expr => provable (impp x y)) (fun x y : expr => provable (impp x y)))) andp) := andp_proper_impp .
  Definition orp_proper_impp : (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (impp x y)) (Morphisms.respectful (fun x y : expr => provable (impp x y)) (fun x y : expr => provable (impp x y)))) orp) := orp_proper_impp .
  Definition negp_proper_impp : (Morphisms.Proper (Morphisms.respectful (Basics.flip (fun x y : expr => provable (impp x y))) (fun x y : expr => provable (impp x y))) negp) := negp_proper_impp .
  Definition provable_iffp_equiv : (RelationClasses.Equivalence (fun x y : expr => provable (iffp x y))) := provable_iffp_equiv .
  Definition provable_proper_iffp : (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (iffp x y)) iff) provable) := provable_proper_iffp .
  Definition impp_proper_iffp : (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (iffp x y)) (Morphisms.respectful (fun x y : expr => provable (iffp x y)) (fun x y : expr => provable (iffp x y)))) impp) := impp_proper_iffp .
  Definition andp_proper_iffp : (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (iffp x y)) (Morphisms.respectful (fun x y : expr => provable (iffp x y)) (fun x y : expr => provable (iffp x y)))) andp) := andp_proper_iffp .
  Definition orp_proper_iffp : (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (iffp x y)) (Morphisms.respectful (fun x y : expr => provable (iffp x y)) (fun x y : expr => provable (iffp x y)))) orp) := orp_proper_iffp .
  Definition iffp_proper_iffp : (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (iffp x y)) (Morphisms.respectful (fun x y : expr => provable (iffp x y)) (fun x y : expr => provable (iffp x y)))) iffp) := iffp_proper_iffp .
  Definition negp_proper_iffp : (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (iffp x y)) (fun x y : expr => provable (iffp x y))) negp) := negp_proper_iffp .
  Definition derivable_proper_iffp : (Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful (fun x y : expr => provable (iffp x y)) iff)) derivable) := derivable_proper_iffp .
  Definition iter_andp_spec_right : (forall xs : list expr, provable (iffp (iter_andp xs) (fold_right andp truep xs))) := iter_andp_spec_right .
  Definition iter_andp_unfold_left_assoc : (forall xs : list expr, provable (iffp (iter_andp xs) match xs with
                                                                                                 | []%list => truep
                                                                                                 | x :: xs0 => (fix f (xs1 : list expr) (x0 : expr) {struct xs1} : expr := match xs1 with
                                                                                                                                                                           | []%list => x0
                                                                                                                                                                           | x1 :: xs2 => f xs2 (andp x0 x1)
                                                                                                                                                                           end) xs0 x
                                                                                                 end)) := iter_andp_unfold_left_assoc .
  Definition iter_andp_unfold_right_assoc : (forall xs : list expr, provable (iffp (iter_andp xs) ((fix f (xs0 : list expr) : expr := match xs0 with
                                                                                                                                      | []%list => truep
                                                                                                                                      | [x]%list => x
                                                                                                                                      | x :: (_ :: _) as xs1 => andp x (f xs1)
                                                                                                                                      end) xs))) := iter_andp_unfold_right_assoc .
  Definition falsep_sepcon : (forall x : expr, provable (iffp (sepcon falsep x) falsep)) := falsep_sepcon .
  Definition provable_wand_sepcon_modus_ponens1 : (forall x y : expr, provable (impp (sepcon (wand x y) x) y)) := provable_wand_sepcon_modus_ponens1 .
  Definition wand_andp : (forall x y z : expr, provable (iffp (wand x (andp y z)) (andp (wand x y) (wand x z)))) := wand_andp .
  Definition sepcon_falsep : (forall x : expr, provable (iffp (sepcon x falsep) falsep)) := sepcon_falsep .
  Definition provable_wand_sepcon_modus_ponens2 : (forall x y : expr, provable (impp (sepcon x (wand x y)) y)) := provable_wand_sepcon_modus_ponens2 .
  Definition wand_mono : (forall x1 x2 y1 y2 : expr, provable (impp x2 x1) -> provable (impp y1 y2) -> provable (impp (wand x1 y1) (wand x2 y2))) := wand_mono .
  Definition orp_wand : (forall x y z : expr, provable (iffp (wand (orp x y) z) (andp (wand x z) (wand y z)))) := orp_wand .
  Definition sepcon_iter_sepcon : (forall xs ys : list expr, provable (iffp (sepcon (iter_sepcon xs) (iter_sepcon ys)) (iter_sepcon (xs ++ ys)))) := sepcon_iter_sepcon .
  Definition cancel_ready : (forall x y : expr, provable (impp (sepcon x emp) y) -> provable (impp x y)) := cancel_ready .
  Definition cancel_one_succeed : (forall u x y z : expr, provable (impp (sepcon x y) z) -> provable (impp (sepcon (sepcon u x) y) (sepcon u z))) := cancel_one_succeed .
  Definition cancel_one_giveup : (forall x y z w v : expr, provable (impp (sepcon x (sepcon y z)) (sepcon w v)) -> provable (impp (sepcon (sepcon y x) z) (sepcon w v))) := cancel_one_giveup .
  Definition cancel_rev : (forall x y z w : expr, provable (impp (sepcon (sepcon y x) z) w) -> provable (impp (sepcon x (sepcon y z)) w)) := cancel_rev .
  Definition cancel_finish : (forall x : expr, provable (impp (sepcon x emp) x)) := cancel_finish .
  Definition iter_sepcon_unfold_right_assoc : (forall xs : list expr, provable (iffp (iter_sepcon xs) ((fix f (xs0 : list expr) : expr := match xs0 with
                                                                                                                                          | []%list => emp
                                                                                                                                          | [x]%list => x
                                                                                                                                          | x :: (_ :: _) as xs1 => sepcon x (f xs1)
                                                                                                                                          end) xs))) := iter_sepcon_unfold_right_assoc .
  Definition iter_sepcon_unfold_left_assoc : (forall xs : list expr, provable (iffp (iter_sepcon xs) match xs with
                                                                                                     | []%list => emp
                                                                                                     | x :: xs0 => (fix f (xs1 : list expr) (x0 : expr) {struct xs1} : expr := match xs1 with
                                                                                                                                                                               | []%list => x0
                                                                                                                                                                               | x1 :: xs2 => f xs2 (sepcon x0 x1)
                                                                                                                                                                               end) xs0 x
                                                                                                     end)) := iter_sepcon_unfold_left_assoc .
  Definition sepcon_proper_impp : (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (impp x y)) (Morphisms.respectful (fun x y : expr => provable (impp x y)) (fun x y : expr => provable (impp x y)))) sepcon) := sepcon_proper_impp .
  Definition wand_proper_impp : (Morphisms.Proper (Morphisms.respectful (Basics.flip (fun x y : expr => provable (impp x y))) (Morphisms.respectful (fun x y : expr => provable (impp x y)) (fun x y : expr => provable (impp x y)))) wand) := wand_proper_impp .
  Definition sepcon_proper_iffp : (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (iffp x y)) (Morphisms.respectful (fun x y : expr => provable (iffp x y)) (fun x y : expr => provable (iffp x y)))) sepcon) := sepcon_proper_iffp .
  Definition wand_proper_iffp : (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (iffp x y)) (Morphisms.respectful (fun x y : expr => provable (iffp x y)) (fun x y : expr => provable (iffp x y)))) wand) := wand_proper_iffp .
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
  Existing Instance provable_impp_refl_instance .
  Existing Instance provable_proper_impp .
  Existing Instance impp_proper_impp .
  Existing Instance derivable_proper_impp .
  Existing Instance andp_proper_impp .
  Existing Instance orp_proper_impp .
  Existing Instance negp_proper_impp .
  Existing Instance provable_iffp_equiv .
  Existing Instance provable_proper_iffp .
  Existing Instance impp_proper_iffp .
  Existing Instance andp_proper_iffp .
  Existing Instance orp_proper_iffp .
  Existing Instance iffp_proper_iffp .
  Existing Instance negp_proper_iffp .
  Existing Instance derivable_proper_iffp .
  Existing Instance sepcon_proper_impp .
  Existing Instance wand_proper_impp .
  Existing Instance sepcon_proper_iffp .
  Existing Instance wand_proper_iffp .
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
