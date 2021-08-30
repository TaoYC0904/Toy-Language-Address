Require Import FP.UnifySL.interface.
Require Import FP.UnifySL.implementation.
Require Import ZArith.
Require Import QArith.
Import T.
Open Scope Z.

Definition mapsto (p : addr) (z : Z) : Assertion := fun st => exists q, snd st p = Some (q, z).
Definition mapsto' (p : addr) (q : Q) (z : Z) : Assertion := fun st => snd st p = Some (q, z).
Definition exp {A : Type} (P : A -> Assertion) : Assertion := fun st => exists a, P a st.
Definition NULL : addr := -1.

Fixpoint listrep (p : Z) (l : list Z) (q1 q2 : Q) : Assertion :=
  match l with
	  | nil => fun _ => p = NULL 
	  | cons x l' => sepcon (mapsto' p q1 x) (exp (fun t => sepcon (mapsto' (p + 1) q2 t) (listrep t l' q1 q2)))
  end.
	