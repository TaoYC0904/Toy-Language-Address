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

Definition mapsto_ (p : addr) (pi : Q) : Assertion := fun st => (exists v, snd st p = Some (inl (pi, v))) /\ (forall p', p' <> p -> snd st p' = None).

Definition mapsto (p : addr) (pi : Q) (v : Z) : Assertion := fun st => snd st p = Some (inl (pi, v)) /\ (forall p', p' <> p -> snd st p' = None).

Definition derives : Assertion -> Assertion -> Prop := fun P Q => forall st, P st -> Q st.

Definition store_update (s : store) (X : var) (v : option Z) : store :=
  match v with
  | Some n => fun Y => if (Nat.eq_dec Y X) then n else s Y
  | None => fun Y => 0
  end.

Definition subst (P : Assertion) (X : var) (v : Z) : Assertion :=
  fun st => P (store_update (fst st) X (Some v), snd st).

Definition heap_update (h : heap) (p : addr) (v : option Z) : heap :=
  match v with
  | Some n => fun p' => if (Z.eq_dec p' p) then match h p' with
    | Some (inl (q, z)) => Some (inl (q, n))
    | _ => None
  end else h p' 
  | _ => fun p' => None 
  end. 
  
Definition hasLock (L : addr) (pi : Q) (R : Assertion_D) : Assertion :=
  fun st => snd st L = Some (inr (pi, None, R)) /\ (forall p, p <> L -> snd st p = None).

Definition readytoRelease (L : addr) (pi : Q) (R : Assertion_D) : Assertion :=
  fun st => snd st L = Some (inr (pi, Some tt, R)) /\ (forall p, p <> L -> snd st p = None).

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

Module Deep_Shallow.

Definition DeepintoShallow (P : Assertion_D) : Assertion :=
  fun st => Assertion_Denote P st.

End Deep_Shallow.

Module tactics.
Import Assertion_Shallow.

Ltac ufsepcon := unfold sepcon; unfold SepCon.
Ltac ufSepcon H := unfold sepcon in H; unfold SepCon in H.
Ltac ufstatej := unfold stateJ; unfold OSAGenerators.prod_Join; unfold SeparationAlgebra.join.
Ltac ufStatej H := unfold stateJ in H; unfold OSAGenerators.prod_Join in H; unfold SeparationAlgebra.join in H.
Ltac ufstorej := unfold storeJ; unfold OSAGenerators.equiv_Join.
Ltac ufStorej H := unfold storeJ in H; unfold OSAGenerators.equiv_Join in H.
Ltac ufheapj := unfold heapJ; unfold OSAGenerators.fun_Join; unfold SeparationAlgebra.join; unfold OSAGenerators.option_Join.
Ltac ufHeapj H := unfold heapJ in H; unfold OSAGenerators.fun_Join in H; unfold SeparationAlgebra.join in H; unfold OSAGenerators.option_Join in H.

(* Lemma heapoptionj : forall (st st1 st2 : state) (x : addr),
@OSAGenerators.option_join (Q * Z + Q * option unit * Assertion_D) QZandLock_Join
(snd st1 x) (snd st2 x) (snd st x) <-> 
  (snd st1 x = None /\ snd st2 x = None /\ snd st x = None) \/
  (exists v, snd st1 x = Some v /\ snd st2 x = None /\ snd st x = Some v) \/
  (exists v, snd st1 x = None /\ snd st2 x = Some v /\ snd st x = Some v) \/
  (exists v1 v2 v, snd st1 x = Some v1 /\ snd st2 x = Some v2 /\ snd st x = Some v /\ QZandLock_Join v1 v2 v).
Proof.
  unfold iff. split.
  + intros.
    destruct H.
    - tauto.
    - right. right. left. exists a. tauto.
    - right. left. exists a. tauto.
    - right. right. right. exists a, b, c. tauto.
  + intros.
    destruct H as [? | [? | [? | ?]]].
    - destruct H as [? [? ?]]. rewrite H, H0, H1. constructor.
    - destruct H as [v [? [? ?]]]. rewrite H, H0, H1. constructor.
    - destruct H as [v [? [? ?]]]. rewrite H, H0, H1. constructor.
    - destruct H as [v1 [v2 [v [? [? [? ?]]]]]].
      rewrite H, H0, H1. constructor. tauto.
Qed. *)

Lemma ufoptionj : forall {A : Type} (J : SeparationAlgebra.Join A) (a1 a2 a : option A) , 
  @OSAGenerators.option_join A J a1 a2 a <->
  (a1 = None /\ a2 = None /\ a = None) \/
  (exists v, a1 = None /\ a2 = Some v /\ a = Some v) \/
  (exists v, a1 = Some v /\ a2 = None /\ a = Some v) \/
  (exists v1 v2 v, a1 = Some v1 /\ a2 = Some v2 /\ a = Some v /\ J v1 v2 v).
Proof.
  unfold iff; split; intros.
  + destruct H.
    - left; tauto.
    - right; left; exists a; tauto.
    - right; right; left; exists a; tauto.
    - right; right; right. exists a,b,c; tauto.
  + destruct H as [? | [? | [? | ?]]].
    - destruct H as [? [? ?]]. rewrite H, H0, H1; constructor.
    - destruct H as [v [? [? ?]]]. rewrite H, H0, H1; constructor.
    - destruct H as [v [? [? ?]]]. rewrite H, H0, H1; constructor.
    - destruct H as [v1 [v2 [v [? [? [? ?]]]]]].
      rewrite H, H0, H1; constructor; tauto.
Qed.

Lemma ufsumj : forall {A B : Type} (J1 : SeparationAlgebra.Join A) (J2 : SeparationAlgebra.Join B) (a1 a2 a : A + B),
  @OSAGenerators.sum_join A B J1 J2 a1 a2 a <->
  (exists al1 al2 al, a1 = inl al1 /\ a2 = inl al2 /\ a = inl al /\ J1 al1 al2 al) \/
  (exists ar1 ar2 ar, a1 = inr ar1 /\ a2 = inr ar2 /\ a = inr ar /\ J2 ar1 ar2 ar).
Proof.
  unfold iff; split; intros.
  + destruct H.
    - left; exists a, b, c; tauto.
    - right; exists a, b, c; tauto.
  + destruct H.
    - destruct H as [al1 [al2 [al [? [? [? ?]]]]]].
      rewrite H, H0, H1. constructor; tauto.
    - destruct H as [ar1 [ar2 [ar [? [? [? ?]]]]]].
      rewrite H, H0, H1. constructor; tauto.
Qed.

Goal forall x1 x2 x, QZandLock_Join x1 x2 x.
Proof.
  unfold QZandLock_Join.
  intros.
  rewrite ufsumj.
  left. exists (0.5%Q, 1), (0.5%Q, 1), (1%Q, 1).
  split; try split; try split. admit. admit. admit.
  unfold QZ_Join.
  unfold OSAGenerators.prod_Join.
  unfold SeparationAlgebra.join.
  unfold Q_Join, Z_Join.





Admitted.

End tactics.
