(* Require Import Toy.UnifySL.implementation. *)
Require Import ZArith.
Require Import QArith.
Require Import Toy.lib.
Require Import Toy.type.
Open Scope Z.

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
  fun st => match da st with
    | Some p => match snd st p with
      | Some (inl (q, v)) => if (Qlt_le_dec 0%Q q) then Some v else None 
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

Module Denote_Term.
Import Denote_Aexp.

Definition add_term (a b : option Z) : option Z :=
  match a, b with 
  | Some n1, Some n2 => Some (n1 + n2)
  | _, _ => None
  end.

Definition sub_term (a b : option Z) : option Z :=
  match a, b with
  | Some n1, Some n2 => Some (n1 - n2)
  | _, _ => None
  end. 

Definition mul_term (a b : option Z) : option Z :=
  match a, b with
  | Some n1, Some n2 => Some (n1 * n2)
  | _, _ => None
  end.

Definition div_term (a b : option Z) : option Z :=
  match a, b with
  | Some n1, Some n2 => if (Z.eq_dec n2 0) then None else Some (n1 / n2)
  | _, _ => None
  end.

Definition deref_term (a : option Z) (st : state) : option Z :=
  match a with
  | Some p => match snd st p with
    | Some (inl (q, z)) => Some z 
    | _ => None
  end
  | _ => None
  end.

Fixpoint term_denote (t : term) : state -> option Z :=
  fun st => match t with
  | TNum n => Some n
  | TDenote a => aeval a st 
  | TPlus t1 t2 => add_term (term_denote t1 st) (term_denote t2 st)
  | TMinus t1 t2 => sub_term (term_denote t1 st) (term_denote t2 st)
  | TMult t1 t2 => mul_term (term_denote t1 st) (term_denote t2 st)
  | TDiv t1 t2 => div_term (term_denote t1 st) (term_denote t2 st)
  | TDeref t => deref_term (term_denote t st) st
  end.

End Denote_Term.

Module Denote_Assertion_D.
Import Denote_Term.
Import Denote_Bexp.

Fixpoint Assertion_Denote (d : Assertion_D) (st : state) : Prop :=
  match d with
  | DLe t1 t2 => match (term_denote t1 st), (term_denote t2 st) with
    | Some n1, Some n2 => n1 <= n2
    | _, _ => False
  end
  | DLt t1 t2 => match (term_denote t1 st), (term_denote t2 st) with
    | Some n1, Some n2 => n1 < n2
    | _, _ => False
  end
  | DEq t1 t2 => match (term_denote t1 st), (term_denote t2 st) with
    | Some n1, Some n2 => n1 = n2
    | _, _ => False
  end
  | DInj b => true_set (beval b) st 
  | DProp P => P
  | DOr d1 d2 => (Assertion_Denote d1 st) \/ (Assertion_Denote d2 st)
  | DAnd d1 d2 => (Assertion_Denote d1 st) /\ (Assertion_Denote d2 st)
  | DNot d => ~ (Assertion_Denote d st) 
  | DMapsto pt vt => match (term_denote pt st), (term_denote vt st) with
    | Some p, Some v => match snd st p with
      | Some (inl (q, z)) => z = v
      | _ => False 
    end
    | _, _ => False
  end
  | DHasLock L pi R => match snd st L with
    | Some (inr ((q, None), r)) => (Qeq q pi) /\ r = R 
    | _ => False 
  end
  | DReadytoRel L pi R => match snd st L with
    | Some (inr ((q, Some tt), r)) => (Qeq q pi) /\ r = R 
    | _ => False 
  end 
end.

End Denote_Assertion_D.

Module Denote_Com.
Import Denote_Aexp.
Import Denote_Bexp.
Import Denote_Assertion_D.

Definition skip_sem : com_denote := {|
  com_normal := BinRel.id;
  com_break := BinRel.empty;
  com_cont := BinRel.empty;
  com_error := Sets.empty |}.

Definition break_sem : com_denote := {|
  com_normal := BinRel.empty;
  com_break := BinRel.id;
  com_cont := BinRel.empty;
  com_error := Sets.empty |}.

Definition cont_sem : com_denote := {|
  com_normal := BinRel.empty;
  com_break := BinRel.empty;
  com_cont := BinRel.id;
  com_error := Sets.empty |}.

Definition set_sem (X : var) (DA : state -> option Z): com_denote := {|
  com_normal := fun st1 st2 => match DA st1 with
    | Some v => fst st2 X = v /\ (forall Y, Y <> X -> fst st2 Y = fst st1 Y) /\ snd st2 = snd st1
    | _ => False
  end;
  com_break := BinRel.empty;
  com_cont := BinRel.empty;
  com_error := fun st => DA st = None |}.

Definition store_sem (DAL DAR : state -> option Z) : com_denote := {|
  com_normal := fun st1 st2 => match (DAL st1), (DAR st1) with
    | Some p, Some v => match (snd st1 p), (snd st2 p) with
      | Some (inl (q1, z1)), Some (inl (q2, z2)) => q1 = 1%Q /\ q2 = 1%Q /\ z2 = v /\
          (forall p', p' <> p -> snd st2 p' = snd st1 p') /\ fst st1 = fst st2
      | _, _ => False
    end
    | _, _ => False
  end;
  com_break := BinRel.empty;
  com_cont := BinRel.empty;
  com_error := fun st => match (DAL st), (DAR st) with
    | Some p, Some v => match snd st p with
      | Some (inl (q, z)) => ~(Qeq q 1%Q)
      | _ => True 
    end
    | _, _ => True
  end |}.

Definition seq_sem (DC1 DC2 : com_denote) : com_denote := {|
  com_normal := BinRel.concat (com_normal DC1) (com_normal DC2);
  com_break := BinRel.union (com_break DC1) (BinRel.concat (com_normal DC1) (com_break DC2));
  com_cont := BinRel.union (com_cont DC1) (BinRel.concat (com_normal DC1) (com_cont DC2));
  com_error := Sets.union (com_error DC1) (BinRel.dia (com_normal DC1) (com_error DC2)) |}.

Definition if_sem (DB : bexp_denote) (DC1 DC2 : com_denote) : com_denote := {|
  com_normal := BinRel.union (BinRel.concat (BinRel.testrel (true_set DB)) (com_normal DC1))
    (BinRel.concat (BinRel.testrel (false_set DB)) (com_normal DC2));
  com_break := BinRel.union (BinRel.concat (BinRel.testrel (true_set DB)) (com_break DC1))
    (BinRel.concat (BinRel.testrel (false_set DB)) (com_break DC2));
  com_cont := BinRel.union (BinRel.concat (BinRel.testrel (true_set DB)) (com_cont DC1))
    (BinRel.concat (BinRel.testrel (false_set DB)) (com_cont DC2));
  com_error := Sets.union (error_set DB) 
    (Sets.union (Sets.intersect (true_set DB) (com_error DC1)) (Sets.intersect (false_set DB) (com_error DC2)))|}.

Fixpoint iter_loop_body (DC1 DC2 : com_denote) (n : nat) : com_denote := match n with
  | O => {|
      com_normal := BinRel.union (com_break DC1) (BinRel.concat (com_normal DC1) (com_break DC2));
      com_break := BinRel.empty;
      com_cont := BinRel.empty;
      com_error := Sets.union (com_error DC1) (BinRel.dia (com_normal DC1) (com_error DC2)) |}
  | S n' => {|
      com_normal := BinRel.concat 
        (BinRel.union (BinRel.concat (com_normal DC1) (com_normal DC2)) 
          (BinRel.concat (com_cont DC1) (com_normal DC2))) 
        (com_normal (iter_loop_body DC1 DC2 n'));
      com_break := BinRel.empty;
      com_cont := BinRel.empty;
      com_error := BinRel.dia 
        (BinRel.union (BinRel.concat (com_normal DC1) (com_normal DC2)) 
          (BinRel.concat (com_cont DC1) (com_normal DC2))) 
        (com_error (iter_loop_body DC1 DC2 n')) |}
end.

Definition for_sem (DC1 DC2 : com_denote) : com_denote := {|
  com_normal := BinRel.omega_union (fun n => com_normal (iter_loop_body DC1 DC2 n));
  com_break := BinRel.empty;
  com_cont := BinRel.empty;
  com_error := Sets.omega_union (fun n => com_error (iter_loop_body DC1 DC2 n)) |}.

Definition new_sem (X : var) : com_denote := {|
  com_normal := fun st1 st2 =>
    exists p, fst st2 X = p /\ snd st1 p = None /\ snd st2 p = Some (inl (1%Q, 0)) /\
      (forall p', p' <> p -> snd st2 p = snd st1 p) /\
      (forall Y, Y <> X -> fst st2 Y = fst st1 Y);
  com_break := BinRel.empty;
  com_cont := BinRel.empty;
  com_error := Sets.empty |}.

Definition delete_sem (X : var) : com_denote := {|
  com_normal := fun st1 st2 => match fst st1 X with
    | p => exists z, snd st1 p = Some (inl (1%Q, z)) /\ snd st2 p = None /\ 
        (forall p', p' <> p -> snd st2 p' = snd st1 p') /\ fst st1 = fst st2
  end;
  com_break := BinRel.empty;
  com_cont := BinRel.empty;
  com_error := fun st => match snd st (fst st X) with
    | Some (inl (q, z)) => ~(Qeq q 1%Q) 
    | _ => True 
  end |}.

Definition make_sem (p : addr) (Q : Assertion_D) : com_denote := {|
  com_normal := fun st1 st2 => match snd st1 p with
    | Some (inl (1%Q, z)) => snd st2 p = Some (inr ((1%Q, None), Q)) /\
        (forall p', p' <> p -> snd st2 p' = snd st1 p') /\ fst st1 = fst st2
    | Some (inr ((1%Q, x), Q')) => snd st2 p = Some (inr ((1%Q, None), Q)) /\
        (forall p', p' <> p -> snd st2 p' = snd st1 p') /\ fst st1 = fst st2
    | _ => False 
  end;
  com_break := BinRel.empty;
  com_cont := BinRel.empty;
  com_error := fun st => match snd st p with
    | Some (inl (q, z)) => ~(Qeq q 1%Q)
    | Some (inr ((q, x), Q')) => ~(Qeq q 1%Q)
    | _ => True 
  end |}.

Definition acquire_sem (p : addr) : com_denote := {|
  com_normal := fun st1 st2 => match snd st1 p with
    | Some (inr ((q, None), Q)) => Qlt 0%Q q /\ snd st2 p = Some (inr ((q, Some tt), Q)) /\
        (forall p', p' <> p -> snd st2 p = snd st1 p) /\ (fst st1 = fst st2)
    | _ => False 
  end;
  com_break := BinRel.empty;
  com_cont := BinRel.empty;
  com_error := fun st => match snd st p with
    | Some (inr ((q, None), Q)) => Qeq q 0%Q 
    | _ => True 
  end |}.

Definition release_sem (p : addr) : com_denote := {|
  com_normal := fun st1 st2 => match snd st1 p with
    | Some (inr ((q, Some tt), Q)) => snd st2 p = Some (inr ((q, None), Q)) /\
        (forall p', p' <> p -> snd st2 p = snd st1 p) /\ (fst st1 = fst st2)
    | _ => False 
  end;
  com_break := BinRel.empty;
  com_cont := BinRel.empty;
  com_error := fun st => match snd st p with 
    | Some (inr ((q, Some tt), Q)) => False 
    | _ => True 
  end |}.

Definition finalize_sem (p : addr) : com_denote := {|
  com_normal := fun st1 st2 => match snd st1 p with
    | Some (inr ((1%Q, x), Q)) => snd st2 p = Some (inl (1%Q, 0)) /\
        (forall p', p' <> p -> snd st2 p = snd st1 p) /\ (fst st1 = fst st2)
    | _ => False 
  end;
  com_break := BinRel.empty;
  com_cont := BinRel.empty;
  com_error := fun st => match snd st p with
    | Some (inr ((1%Q, x), Q)) => False 
    | _ => True 
  end |}.

Fixpoint ceval (c : com) : com_denote :=
  match c with
  | CSkip => skip_sem
  | CBreak => break_sem 
  | CCont => cont_sem 
  | CSet X a => set_sem X (aeval a)
  | CStore a1 a2 => store_sem (aeval a1) (aeval a2)
  | CSeq c1 c2 => seq_sem (ceval c1) (ceval c2)
  | CIf b c1 c2 => if_sem (beval b) (ceval c1) (ceval c2)
  | CFor c1 c2 => for_sem (ceval c1) (ceval c2)
  | CNew X => new_sem X 
  | CDelete X => delete_sem X
  | CMake p Q => make_sem p Q 
  | CAcquire p => acquire_sem p 
  | CRelease p => release_sem p 
  | CFinalize p => finalize_sem p 
  end.

End Denote_Com.
