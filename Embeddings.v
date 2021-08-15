Require Import Toy.Imp Toy.Language.
Require Import Toy.UnifySL.implementation.
Import T.

Module Assertion_Shallow.
Import Denote_Aexp.
Import Denote_Bexp.
Import Denote_Com.

Definition exp {A : Type} (P : A -> Assertion) : Assertion := fun st => exists a, P a st.

Definition inj (b : bexp) : Assertion := fun st => true_set (beval b) (fst st).

Definition eqp (a : aexp) (v : Z) : Assertion := fun st => (aeval a) (fst st) = Some v.

Definition safea (a : aexp) : Assertion := fun st => ~ (aeval a) (fst st) = None.

Definition safeb (b : bexp) : Assertion := fun st => ~ error_set (beval b) (fst st).

Definition mapsto_ (p : addr) : Assertion := fun st => (exists v, (snd st) p = Some v) /\ (forall p', p <> p' -> (snd st) p' = None).

Definition mapsto (p : addr) (v : Z) : Assertion := fun st => (snd st) p = Some v /\ (forall p', p <> p' -> (snd st) p' = None).

Definition derives : Assertion -> Assertion -> Prop := fun P Q => forall st, P st -> Q st.

Definition store_update (s : store) (X : var) (v : option Z) : store :=
  match v with
  | Some n => fun Y => if (Nat.eq_dec Y X) then n else s Y
  | None => fun Y => 0
  end.

Definition heap_update (h : heap) (p : addr) (v : option Z) : heap :=
  fun q => if (Z.eq_dec p q) then v else h q.

Definition subst_set (P : Assertion) (X : var) (v : Z) : Assertion :=
  fun st => P (store_update (fst st) X (Some v), snd st).

Definition subst_load (P : Assertion) (X : var) (v : Z) : Assertion :=
  fun st => P (store_update (fst st) X (Some v), snd st).

(* Definition join_heap : heap -> heap -> heap -> Prop :=
  fun h1 h2 h3 => 
    forall p : Z,
      (exists v, h1 p = Some v /\ h2 p = None /\ h3 p = Some v) \/
      (exists v, h1 p = None /\ h2 p = Some v /\ h3 p = Some v) \/
      (h1 p = None /\ h2 p = None /\ h3 p = None).

Definition join : state -> state -> state -> Prop :=
  fun st1 st2 st3 => fst st1 = fst st2 /\ fst st2 = fst st3 /\ join_heap (snd st1) (snd st2) (snd st3).

Definition sepcon (P Q : Assertion) : Assertion :=
  fun st => exists st1 st2, join st1 st2 st /\ P st1 /\ Q st2. *)
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

Module tacticforOSA.

Ltac UFsepcon := unfold sepcon in *; 
                 unfold WeakSemantics.WeakSemantics.sepcon in *;
                 unfold SeparationAlgebra.join in *.

Ltac UFjoin := unfold stateJ in *; unfold stateJoin in *;
               unfold OSAGenerators.prod_Join in *;
               unfold SeparationAlgebra.join in *;
               unfold store_join in *;
               unfold OSAGenerators.equiv_Join in *.

Ltac UFheapjoin := unfold heap_join in *;
                   unfold OSAExamples.Heap_Join in *;
                   unfold OSAGenerators.fun_Join in *;
                   unfold SeparationAlgebra.join in *;
                   unfold OSAGenerators.option_Join in *.

Lemma osajoin : forall (st1 st2 st : state), 
  (forall x, @OSAGenerators.option_join Z (@OSAGenerators.trivial_Join Z)
          (snd st1 x) (snd st2 x) (snd st x)) <-> 
  (forall p, (exists v, snd st1 p = Some v /\ snd st2 p = None /\ snd st p = Some v) \/
             (exists v, snd st1 p = None /\ snd st2 p = Some v /\ snd st p = Some v) \/
             (snd st1 p = None ) /\ (snd st2 p = None) /\ (snd st p = None)). 
Proof.
  intros.
  unfold iff; split.
  + intros.
    specialize (H p).
    destruct (snd st1 p), (snd st2 p), (snd st p).
    - inversion H. tauto.
    - inversion H.
    - inversion H. rewrite <- H0.
      left. exists z. tauto.
    - inversion H.
    - inversion H.
      right. left. exists z0. tauto.
    - inversion H.
    - inversion H.
    - right. right. tauto.
  + intros.
    specialize (H x).
    destruct (snd st1 x), (snd st2 x), (snd st x).
    - destruct H as [? | [? | ?]].
      * destruct H as [v [? [? ?]]]. inversion H0.
      * destruct H as [v [? [? ?]]]. inversion H.
      * destruct H as [? [? ?]]. inversion H.
    - destruct H as [? | [? | ?]].
      * destruct H as [v [? [? ?]]]. inversion H0.
      * destruct H as [v [? [? ?]]]. inversion H.
      * destruct H as [? [? ?]]. inversion H.
    - destruct H as [? | [? | ?]].
      * destruct H as [v [? [? ?]]].
        inversion H. inversion H1. subst. constructor.
      * destruct H as [v [? [? ?]]]. inversion H0.
      * destruct H as [? [? ?]]. inversion H.
    - destruct H as [? | [? | ?]].
      * destruct H as [v [? [? ?]]]. inversion H1.
      * destruct H as [v [? [? ?]]]. inversion H.
      * destruct H as [? [? ?]]. inversion H.
    - destruct H as [? | [? | ?]].
      * destruct H as [v [? [? ?]]]. inversion H.
      * destruct H as [v [? [? ?]]]. 
        inversion H0. inversion H1. subst. constructor.
      * destruct H as [? [? ?]]. inversion H0.
    - destruct H as [? | [? | ?]].
      * destruct H as [v [? [? ?]]]. inversion H.
      * destruct H as [v [? [? ?]]]. inversion H1.
      * destruct H as [? [? ?]]. inversion H0.
    - destruct H as [? | [? | ?]].
      * destruct H as [v [? [? ?]]]. inversion H.
      * destruct H as [v [? [? ?]]]. inversion H0.
      * destruct H as [? [? ?]]. inversion H1.
    - destruct H as [? | [? | ?]].
      * destruct H as [v [? [? ?]]]. inversion H.
      * destruct H as [v [? [? ?]]]. inversion H0.
      * constructor.
Qed.

End tacticforOSA.
