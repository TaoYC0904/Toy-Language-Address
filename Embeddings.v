Require Import ZArith.
Require Import QArith.
Require Import Toy.UnifySL.implementation.
Require Import Toy.lib.
Require Import Toy.type.
Require Import Toy.Language.
Import T.
Import Denote_Aexp Denote_Bexp Denote_Term Denote_Assertion_D Denote_Com.

Module Assertion_Shallow.
Import Denote_Aexp.
Import Denote_Bexp.
Import Denote_Com.

Definition exp {A : Type} (P : A -> Assertion) : Assertion := fun st => exists a, P a st.

Definition inj (b : bexp) : Assertion := fun st => true_set (beval b) st.

Definition eqp (a : aexp) (v : Z) : Assertion := fun st => (aeval a) st = Some v.

Definition safea (a : aexp) : Assertion := fun st => ~ (aeval a) st = None.

Definition safeb (b : bexp) : Assertion := fun st => ~ error_set (beval b) st.

Definition mapsto_ (p : addr) : Assertion := fun st => (exists q v, snd st p = Some (inl (q, v))) /\ (forall p', p' <> p -> snd st p' = None).

Definition mapsto (p : addr) (v : Z) : Assertion := fun st => (exists q, snd st p = Some (inl (q, v))) /\ (forall p', p' <> p -> snd st p' = None).

Definition derives : Assertion -> Assertion -> Prop := fun P Q => forall st, P st -> Q st.

Definition store_update (s : store) (X : var) (v : option Z) : store :=
  match v with
  | Some n => fun Y => if (Nat.eq_dec Y X) then n else s Y
  | None => fun Y => 0
  end.

Definition subst (P : Assertion) (X : var) (v : Z) : Assertion :=
  fun st => P (store_update (fst st) X (Some v), snd st).

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