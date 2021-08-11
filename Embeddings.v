Require Import Toy.Imp Toy.Language.

Module Assertion_Shallow.
Import Denote_Aexp.
Import Denote_Bexp.
Import Denote_Com.
Import Denote_State.

Definition Assertion : Type := state -> Prop.

Definition negp (P : Assertion) : Assertion := fun st => ~ P st.

Definition andp (P Q : Assertion) : Assertion := fun st => P st /\ Q st.

Definition orp (P Q : Assertion) : Assertion := fun st => P st \/ Q st.

Definition falsep : Assertion := fun st => False.

Definition truep : Assertion := fun st => True.

Definition inj (b : bexp) : Assertion := fun st => true_set (beval b) (fst st).

Definition safea (a : aexp) : Assertion := fun st => ~ (aeval a) (fst st) = None.

Definition safeb (b : bexp) : Assertion := fun st => ~ error_set (beval b) (fst st).

Definition derives : Assertion -> Assertion -> Prop := fun P Q => forall st, P st -> Q st.

End Assertion_Shallow.

Module Validity.
Import Denote_State.
Import Assertion_Shallow.
Import Denote_Com.

Definition valid (P : Assertion) (c : com) (Q Rb Rc : Assertion) : Prop :=
  forall st1 st2, P st1 ->
    (~ com_error (ceval c) st1) /\
    (com_normal (ceval c) st1 st2 -> Q st2) /\
    (com_break (ceval c) st1 st2 -> Rb st2) /\
    (com_cont (ceval c) st1 st2 -> Rc st2).

End Validity.