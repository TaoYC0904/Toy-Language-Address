Require Import ZArith.
Require Import QArith.
Definition t : Type := Q * (option unit) * nat.

Definition tt : t := ((1, Some tt), O).
