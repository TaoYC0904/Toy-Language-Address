Require Import ZArith.
Require Import QArith.
Require Import Coq.micromega.Psatz.
Require Import Toy.lib.
Open Scope Z.

Definition var : Type := nat.
Definition store : Type := var -> Z.
Definition addr : Type := Z.

Inductive aexp : Type :=
  | ANum (n : Z)
  | AId (X : var)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
  | ADiv (a1 a2 : aexp)
  | ADeref (a : aexp).

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Inductive term : Type := 
  | TNum (n : Z)
  | TDenote (a : aexp)
  | TPlus (t1 t2 : term)
  | TMinus (t1 t2 : term)
  | TMult (t1 t2 : term)
  | TDiv (t1 t2 : term)
  | TDeref (t : term).

Inductive Assertion_D : Type :=
  | DLe (t1 t2 : term)
  | DLt (t1 t2 : term)
  | DEq (t1 t2 : term)
  | DInj (b : bexp)
  | DProp (P : Prop)
  | DOr (d1 d2 : Assertion_D)
  | DAnd (d2 d2 : Assertion_D)
  | DNot (d : Assertion_D)
  | DMapsto (pt : term) (vt : term)
  | DHasLock (L : addr) (pi : Q) (R : Assertion_D)
  | DReadytoRel (L : addr) (pi : Q) (R : Assertion_D).

Inductive com : Type :=
  | CSkip
  | CBreak
  | CCont
  | CSet (X : var) (a : aexp)
  | CStore (a1 : aexp) (a2 : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CFor (c1 c2 : com)
  | CNew (X : var)
  | CDelete (X : var)
  | CMake (p : addr) (Q : Assertion_D)
  | CAcquire (p : addr)
  | CRelease (p : addr)
  | CFinalize (p : addr).

Definition heap : Type := addr -> (option ((Q * Z) + (Q * (option unit) * Assertion_D))).
Definition state : Type := store * heap.
Definition Assertion : Type := state -> Prop.

Record bexp_denote : Type := {
  true_set : state -> Prop;
  false_set : state -> Prop;
  error_set : state -> Prop; }.

Record com_denote : Type := {
  com_normal : state -> state -> Prop;
  com_break : state -> state -> Prop;
  com_cont : state -> state -> Prop;
  com_error : state -> Prop }.
