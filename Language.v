Require Import Coq.Lists.List.
Require Import Toy.Imp.
Require Import Toy.UnifySL.implementation.
Import T.
Open Scope Z.

Inductive aexp : Type :=
  | ANum (n : Z)
  | AId (X : var)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
  | ADiv (a1 a2 : aexp)
  | ADeref (a : aexp).

Module Denote_Aexp.

Definition add_sem (da1 da2 : state -> option Z) : state -> option Z :=
  fun st =>
    match da1 st, da2 st with
      | Some v1, Some v2 => Some (v1 + v2)
      | _, _ => None
    end. 

Definition sub_sem (da1 da2 : state -> option Z) : state -> option Z :=
  fun st =>
    match da1 st, da2 st with
      | Some v1, Some v2 => Some (v1 - v2)
      | _, _ => None
    end.

Definition mul_sem (da1 da2 : state -> option Z) : state -> option Z :=
  fun st =>
    match da1 st, da2 st with
      | Some v1, Some v2 => Some (v1 * v2)
      | _, _ => None
    end.
  
Definition div_sem (da1 da2 : state -> option Z) : state -> option Z :=
  fun st =>
    match da1 st, da2 st with
      | Some v1, Some v2 =>
          if Z.eq_dec v2 0 then None else Some (v1 / v2)
      | _, _ => None
    end.

Definition deref_sem (da : state -> option Z) : state -> option Z :=
  fun st =>
    match da st with
      | Some v => match snd st v with
        | Some v' => Some v'
        | _ => None
      end
      | _ => None
    end.

Fixpoint aeval (a : aexp) : state -> option Z :=
  match a with
    | ANum n => fun _ =>  Some n
    | AId X => fun st => Some (fst st X)
    | APlus a1 a2 => add_sem (aeval a1) (aeval a2)
    | AMinus a1 a2 => sub_sem (aeval a1) (aeval a2)
    | AMult a1 a2 => mul_sem (aeval a1) (aeval a2)
    | ADiv a1 a2 => div_sem (aeval a1) (aeval a2)
    | ADeref a => deref_sem (aeval a)
  end.

End Denote_Aexp.

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Record bexp_denote : Type := {
  true_set : state -> Prop;
  false_set : state -> Prop;
  error_set : state -> Prop; }.

Definition opt_test (R : Z -> Z -> Prop) (X Y : state -> option Z) : bexp_denote :=
{|
  true_set := fun st =>
    match X st, Y st with
      | Some n1, Some n2 => R n1 n2
      | _, _ => False
    end;
  false_set := fun st =>
    match X st, Y st with
      | Some n1, Some n2 => ~ R n1 n2
      | _, _ => False
    end;
  error_set := fun st =>
    match X st, Y st with
      | Some n1, Some n2 => False
      | _, _ => True 
    end; |}.

Module Sets.

Definition union {A : Type} (X Y : A -> Prop) : A -> Prop :=
  fun a => X a \/ Y a.
    
Definition omega_union {A} (X : nat -> A -> Prop) : A -> Prop :=
  fun a => exists n, X n a.
    
End Sets.

Module Denote_Bexp.
Import Denote_Aexp.

Fixpoint beval (b : bexp) : bexp_denote :=
  match b with
    | BTrue =>
        {| true_set := Sets.full;
           false_set := Sets.empty;
           error_set := Sets.empty; |}
    | BFalse =>
        {| true_set := Sets.empty;
           false_set := Sets.full;
           error_set := Sets.empty; |}
    | BEq a1 a2 =>
        opt_test Z.eq (aeval a1) (aeval a2)
    | BLe a1 a2 => 
        opt_test Z.le (aeval a1) (aeval a2)
    | BNot b =>
        {| true_set := false_set (beval b);
           false_set := true_set (beval b);
           error_set := error_set (beval b); |}
           | BAnd b1 b2 =>
           {| true_set := Sets.intersect (true_set (beval b1)) (true_set (beval b2));
              false_set := Sets.union (false_set (beval b1))
                                      (Sets.intersect (true_set (beval b1))
                                                      (false_set (beval b2)));
              error_set := Sets.union (error_set (beval b1))
                                      (Sets.intersect (true_set (beval b1))
                                                      (error_set (beval b2))); |}
       end.

End Denote_Bexp.

Inductive com : Type :=
  | CSkip
  | CBreak
  | CCont
  | CAss_load (X : var) (a : aexp)
  | CAss_store (a1 : aexp) (a2 : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CFor (c1 c2 : com).

Record com_denote : Type := {
  com_normal : state -> state -> Prop;
  com_break : state -> state -> Prop;
  com_cont : state -> state -> Prop;
  com_error : state -> Prop }.

Module Denote_Com.
Import Denote_Aexp.
Import Denote_Bexp.

Definition skip_sem : com_denote := {|
  com_normal := fun st1 st2 => st1 = st2;
  com_break := fun st1 st2 => False;
  com_cont := fun st1 st2 => False;
  com_error := fun st => False; |}.

Definition break_sem : com_denote := {|
  com_normal := fun st1 st2 => False;
  com_break := fun st1 st2 => st1 = st2;
  com_cont := fun st1 st2 => False;
  com_error := fun st => False; |}.

Definition cont_sem : com_denote := {|
  com_normal := fun st1 st2 => False;
  com_break := fun st1 st2 => False;
  com_cont := fun st1 st2 => st1 = st2;
  com_error := fun st => False; |}.

Definition load_sem (X : var) (DA : state -> option Z) : com_denote := {|
  com_normal := fun st1 st2 => match DA st1 with
    | Some n => (fst st2 X = n) /\ (forall Y, Y <> X -> fst st2 Y = fst st1 Y) /\ (snd st1 = snd st2)
    | None => False
  end;
  com_break := fun st1 st2 => False;
  com_cont := fun st1 st2 => False;
  com_error := fun st => (DA st) = None; |}.
  
Definition store_sem (DAL DAR : state -> option Z) : com_denote := {|
  com_normal := fun st1 st2 => match DAL st1, DAR st1 with
    | Some p, Some v => (snd st1 p <> None) /\ (snd st2 p = Some v) /\
        (forall p', p <> p' -> snd st2 p' = snd st1 p') /\ (fst st1 = fst st2)
    | _, _ => False 
  end;
  com_break := fun st1 st2 => False;
  com_cont := fun st1 st2 => False;
  com_error := fun st => match DAL st, DAR st with
    | Some p, Some v => snd st p = None
    | _, _ => True 
  end; |}.

  Definition seq_sem (DC1 DC2 : com_denote) : com_denote := {|
  com_normal := fun st1 st2 =>
    exists st3, com_normal DC1 st1 st3 /\ com_normal DC2 st3 st2;
  com_break := fun st1 st2 =>
    (com_break DC1 st1 st2) \/
    (exists st3, com_normal DC1 st1 st3 /\ com_break DC2 st3 st2);
  com_cont := fun st1 st2 =>
    (com_cont DC1 st1 st2) \/
    (exists st3, com_normal DC1 st1 st3 /\ com_cont DC2 st3 st2);
  com_error := fun st =>
    (com_error DC1 st) \/ (exists st', com_normal DC1 st st' /\ com_error DC2 st'); |}.
  
Definition if_sem (DB : bexp_denote) (DC1 DC2 : com_denote) : com_denote := {|
  com_normal := fun st1 st2 => 
    (true_set DB st1 /\ com_normal DC1 st1 st2) \/
    (false_set DB st1 /\ com_normal DC2 st1 st2);
  com_break := fun st1 st2 =>
    (true_set DB st1 /\ com_break DC1 st1 st2) \/
    (false_set DB st1 /\ com_break DC2 st1 st2);
  com_cont := fun st1 st2 =>
    (true_set DB st1 /\ com_cont DC1 st1 st2) \/
    (false_set DB st1 /\ com_cont DC2 st1 st2);
  com_error := fun st =>
    (error_set DB st) \/
    (true_set DB st /\ com_error DC1 st) \/
    (false_set DB st /\ com_error DC2 st); |}.

Fixpoint iter_loop_body (DC1 DC2 : com_denote) (n : nat) : com_denote :=
  match n with
  | O => {|
      com_normal := fun st1 st2 =>
        (com_break DC1 st1 st2) \/
        (exists st3, com_normal DC1 st1 st3 /\ com_break DC2 st3 st2);
      com_break := fun st1 st2 => False;
      com_cont := fun st1 st2 => False;
      com_error := fun st =>
        (com_error DC1 st) \/
        (exists st', com_normal DC1 st st' /\ com_error DC2 st') |}
  | S n' => {|
      com_normal := fun st1 st2 => exists st3,
        ((exists st4, com_normal DC1 st1 st4 /\ com_normal DC2 st4 st3) \/
        (exists st4, com_cont DC1 st1 st4 /\ com_normal DC2 st4 st3)) /\
        (com_normal (iter_loop_body DC1 DC2 n') st3 st2);
      com_break := fun st1 st2 => False;
      com_cont := fun st1 st2 => False;
      com_error := fun st => exists st',
        ((exists st2, com_normal DC1 st st2 /\ com_normal DC2 st2 st') \/
        (exists st2, com_cont DC1 st st2 /\ com_normal DC2 st2 st')) /\
        (com_error (iter_loop_body DC1 DC2 n') st') |}
  end.

Definition for_sem (DC1 DC2 : com_denote) : com_denote := {|
  com_normal := fun st1 st2 =>
    exists n, com_normal (iter_loop_body DC1 DC2 n) st1 st2;
  com_break := fun st1 st2 => False;
  com_cont := fun st1 st2 => False;
  com_error := fun st =>
    exists n, com_error (iter_loop_body DC1 DC2 n) st |}.

Fixpoint ceval (c : com) : com_denote :=
  match c with
  | CSkip => skip_sem
  | CBreak => break_sem
  | CCont => cont_sem
  | CAss_load X a => load_sem X (aeval a)
  | CAss_store a1 a2 => store_sem (aeval a1) (aeval a2)
  | CSeq c1 c2 => seq_sem (ceval c1) (ceval c2)
  | CIf b c1 c2 => if_sem (beval b) (ceval c1) (ceval c2)
  | CFor c1 c2 => for_sem (ceval c1) (ceval c2)
  end.

End Denote_Com.
