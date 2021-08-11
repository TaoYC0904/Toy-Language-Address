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

Definition store_update (s : store) (X : var) (v : option Z) : store :=
  match v with
  | Some n => fun Y => if (Nat.eq_dec X Y) then n else s Y
  | None => fun Y => 0
  end.

Definition heap_update (h : heap) (p : addr) (v : option Z) : heap :=
  fun q => if (Z.eq_dec p q) then v else h q.

Definition join_heap : heap -> heap -> heap -> Prop :=
  fun h1 h2 h3 => 
    forall p : Z,
      (exists v, h1 p = Some v /\ h2 p = None /\ h3 p = Some v) \/
      (exists v, h1 p = None /\ h2 p = Some v /\ h3 p = Some v) \/
      (h1 p = None /\ h2 p = None /\ h3 p = None).

Definition join : state -> state -> state -> Prop :=
  fun st1 st2 st3 => fst st1 = fst st2 /\ fst st2 = fst st3 /\ join_heap (snd st1) (snd st2) (snd st3).

Definition sepcon (P Q : Assertion) : Assertion :=
  fun st => exists st1 st2, join st1 st2 st /\ P st1 /\ Q st2.

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