Module Sets.
Definition full {A : Type} : A -> Prop := fun _ => True.
Definition empty {A : Type} : A -> Prop := fun _ => False.
Definition union {A : Type} (X Y : A -> Prop) : A -> Prop := fun a => X a \/ Y a.
Definition intersect {A : Type} (X Y : A -> Prop) : A -> Prop := fun a => X a /\ Y a.
Definition omega_union {A : Type} (X : nat -> A -> Prop) : A -> Prop := fun a => exists n, X n a.
End Sets.

Module BinRel.
Definition id {A : Type} : A -> A -> Prop := fun x y => x = y.
Definition empty {A : Type} : A -> A -> Prop := fun x y => False.
Definition concat {A : Type} (r1 r2 : A -> A -> Prop) : A -> A -> Prop := fun x z => exists y, r1 x y /\ r2 y z.
Definition union {A : Type} (r1 r2 : A -> A -> Prop) : A -> A -> Prop := fun x y => r1 x y \/ r2 x y.
Definition intersection {A : Type} (r1 r2 : A -> A -> Prop) : A -> A -> Prop := fun x y => r1 x y /\ r2 x y.
Definition testrel {A : Type} (r : A -> Prop) := fun x y => x = y /\ r x.
Definition omega_union {A : Type} (r : nat -> A -> A -> Prop) : A -> A -> Prop := fun x y => exists n, r n x y.
Definition dia {A : Type} (r : A -> A -> Prop) (s : A -> Prop) : A -> Prop := fun x => exists y, r x y /\ s y.
End BinRel.
