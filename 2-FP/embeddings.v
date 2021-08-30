Require Import FP.Language.
Require Import FP.UnifySL.implementation.
Require Import ZArith.
Require Import QArith.
Import T.
Import Denote_Aexp Denote_Bexp Denote_Com.
Open Scope Z.

Module Assertion_Shallow.

Definition exp {A : Type} (P : A -> Assertion) : Assertion := fun st => exists a, P a st.

Definition inj (b : bexp) : Assertion := fun st => true_set (beval b) st.

Definition eqp (a : aexp) (v : Z) : Assertion := fun st => (aeval a) st = Some v.

Definition safea (a : aexp) : Assertion := fun st => ~ (aeval a) st = None.

Definition safeb (b : bexp) : Assertion := fun st => ~ error_set (beval b) st.

Definition mapsto_ (p : addr) : Assertion := fun st => (exists q v, snd st p = Some (q, v)) /\ (forall p', p' <> p -> snd st p' = None).

Definition mapsto (p : addr) (v : Z) : Assertion := fun st => (exists q, snd st p = Some (q, v)) /\ (forall p', p' <> p -> snd st p' = None).

Definition derives : Assertion -> Assertion -> Prop := fun P Q => forall st, P st -> Q st.

Definition store_update (s : store) (X : var) (v : Z) : store := fun Y => if (Nat.eq_dec Y X) then v else s Y.

Definition substp (P : Assertion) (X : var) (v : Z) : Assertion := fun st => P (store_update (fst st) X v, snd st).

Definition heap_update (h : heap) (p : addr) (v : option (Q * Z)) : heap := fun p' => if (Z.eq_dec p' p) then v else h p'.

End Assertion_Shallow.

Module Validity.
Import Assertion_Shallow.
Import Denote_Com.

Definition valid (P : Assertion) (c : com) (Q Rb Rc : Assertion) : Prop :=
  forall st1 st2, P st1 ->
    (~ com_error (ceval c) st1) /\
    (com_normal (ceval c) st1 st2 -> Q st2) /\
    (com_break (ceval c) st1 st2 -> Rb st2) /\
    (com_cont (ceval c) st1 st2 -> Rc st2).

End Validity.

Module tacticsforUnifySL.
Ltac UFsepcon' := unfold sepcon; unfold SepCon. 
Ltac UFsepcon H := unfold sepcon in H; unfold SepCon in H.
Ltac UFjoin' := unfold stateJ; unfold OSAGenerators.prod_Join; unfold SeparationAlgebra.join.
Ltac UFjoin H := unfold stateJ in H; unfold OSAGenerators.prod_Join in H; unfold SeparationAlgebra.join in H.
Ltac UFstore' := unfold storeJ; unfold OSAGenerators.equiv_Join.
Ltac UFstore H := unfold storeJ in H; unfold OSAGenerators.equiv_Join in H.

Goal forall P Q st, sepcon P Q st.
Proof.
	intros.
	UFsepcon'.
	exists st, st.
	UFjoin'.
	UFstore'.
	unfold heapJ.
	unfold OSAGenerators.fun_Join.
	unfold SeparationAlgebra.join.
	unfold OSAGenerators.option_Join.
	unfold OSAGenerators.option_join.



