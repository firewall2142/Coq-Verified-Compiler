Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Lists.List.
Require Import Sequences.
(*From Coq Require Import Arith.EqNat.*)
(*From Coq Require Import omega.Omega.*)
(*From Coq Require Import Init.Nat.*)
Import ListNotations.



Reserved Notation "c1 '/' st '\\' st'"
                  (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      SKIP / st \\ st
  | E_Ass  : forall st a1 n x,
      aeval st a1 = n ->
      (x ::= a1) / st \\ (t_update st x n)
  | E_Seq : forall c1 c2 st st' st'',
      c1 / st  \\ st' ->
      c2 / st' \\ st'' ->
      (c1 ;; c2) / st \\ st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      c1 / st \\ st' ->
      (IFB b THEN c1 ELSE c2 FI) / st \\ st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      c2 / st \\ st' ->
      (IFB b THEN c1 ELSE c2 FI) / st \\ st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      (WHILE b DO c END) / st \\ st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      c / st \\ st' ->
      (WHILE b DO c END) / st' \\ st'' ->
      (WHILE b DO c END) / st \\ st''

  where "c1 '/' st '\\' st'" := (ceval c1 st st').
(* ===================== *)
Inductive id : Type :=
  | Id : string -> id.

Definition beq_id x y :=
  match x,y with
    | Id n1, Id n2 => if string_dec n1 n2 then true else false
  end.

Theorem beq_id_refl : forall id, true = beq_id id id.
Proof.
  intros [n]. simpl. destruct (string_dec n n).
  - reflexivity.
  - destruct n0. reflexivity.
Qed.

Theorem beq_id_true_iff : forall x y : id,
  beq_id x y = true <-> x = y.
Proof.
   intros [n1] [n2].
   unfold beq_id.
   destruct (string_dec n1 n2).
   - subst. split. reflexivity. reflexivity.
   - split.
     + intros contra. inversion contra.
     + intros H. inversion H. subst. destruct n. reflexivity.
Qed.

Theorem beq_id_false_iff : forall x y : id,
  beq_id x y = false
  <-> x <> y.
Proof.
  intros x y. rewrite <- beq_id_true_iff.
  rewrite not_true_iff_false. reflexivity. Qed.

Theorem false_beq_id : forall x y : id,
   x <> y
   -> beq_id x y = false.
Proof.
  intros x y. rewrite beq_id_false_iff.
  intros H. apply H. Qed.
(* ====================================================== *)

Inductive aexp : Type :=
| ANum : nat -> aexp
| AId : id -> aexp
| APlus (a1 a2: aexp)
| AMinus (a1 a2: aexp)
| AMul (a1 a2: aexp).

Inductive bexp : Type :=
| BTrue : bexp
| BFalse : bexp
| BEq : aexp -> aexp -> bexp
| BLe : aexp -> aexp -> bexp
| BNot : bexp -> bexp
| BAnd : bexp -> bexp -> bexp.
  
Inductive com : Type :=
| CSkip
| CAss (x : string) (a : aexp)
| CSeq (c1 c2 : com)
| CIf (b : bexp) (c1 c2 : com)
| CWhile (b : bexp) (c : com).

Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).


Inductive instruction: Type :=
| Iconst (n:nat)                (*Push integer 'n' to stack*)
| Iget (i:nat)                  (*push value of the i-th stack slot*)
| Iset (i:nat)                  (*Pop an integer, assign it to the i-th stack slot*)
| Iadd                          (*pop n2, pop n1 and push back n1+n2*)
| Isub                          (*pop n2, pop n1, push back n1-n2*)
| Imul                          (* pop n2, pop n1, push back n1*n2 *)
| Ibranch_forward (ofs:nat)     (*skip ofs instructions forward*)
| Ibranch_backward (ofs:nat)    (*skip ofs instructions backward*)
| Ibeq(ofs:nat)                 (*pop n2, pop n1, skip ofs if n1=n2*)
| Ibne(ofs:nat)                 (*pop n2, pop n1, skip ofs if n1<>n2*)
| Ible(ofs:nat)                 (*pop n2, pop n1, skip ofs if n1<=n2*)
| Ibgt(ofs:nat)                 (*pop n2, pop n1, skip ofs if n1>n2*)
| Ihalt                         (*terminate execution successfully*)
.

Definition code := list instruction.
Definition stack := list nat.
Definition configuration := (nat * stack)%type.

Fixpoint code_at (C:code) (pc: nat) : option instruction :=
  match C, pc with
  | nil, _ => None
  | i::C', O => Some i
  | i::C', S pc' => code_at C' pc'
  end.

Fixpoint get_nth_slot (s:stack) (n:nat) : option nat :=
  match s, n with
  | nil, _ => None
  | v::s', O => Some v
  | v :: s', S n' => get_nth_slot s' n'
  end.

Fixpoint set_nth_slot (s:stack) (n:nat) (v:nat): option stack :=
  match s, n with
  | nil, _ => None
  | u :: s', O => Some (v :: s')
  | u :: s', S n' =>
    match set_nth_slot s' n' v with
    | None => None
    | Some ns' => Some (u :: ns')
    end
  end.


Inductive transition (C: code): configuration -> configuration -> Prop :=
  
| trans_const: forall pc stk n, code_at C pc = Some(Iconst n) ->
                                transition C (pc, stk) (pc + 1, n :: stk)
                                           
| trans_get: forall pc stk n v, code_at C pc = Some(Iget n) ->
                                get_nth_slot stk n = Some v ->
                                transition C (pc, stk) (pc + 1, v :: stk)
                                           
| trans_set: forall pc stk n v stk', code_at C pc = Some(Iset n) ->
                                     set_nth_slot stk n v = Some stk' ->
                                     transition C (pc, v :: stk) (pc + 1, stk')
                                                
| trans_add: forall pc stk n1 n2,  code_at C pc = Some(Iadd) ->
                                   transition C (pc, n2 :: n1 :: stk) (pc + 1, (n1 + n2) :: stk)
                                              
| trans_sub: forall pc stk n1 n2, code_at C pc = Some(Isub) ->
                                  transition C (pc, n2 :: n1 :: stk) (pc + 1, (n1 - n2) :: stk)
                                             
| trans_mul: forall pc stk n1 n2, code_at C pc = Some(Imul) ->
                                  transition C (pc, n2 :: n1 :: stk) (pc + 1, (n1 * n2) :: stk)
                                             
| trans_branch_forward: forall pc stk ofs pc', code_at C pc = Some(Ibranch_forward ofs) ->
                                               pc' = pc + 1 + ofs ->
                                               transition C (pc, stk) (pc', stk)

| trans_branch_backward: forall pc stk ofs pc', code_at C pc = Some(Ibranch_backward ofs) ->
                                                pc' = pc + 1 - ofs ->
                                                transition C (pc, stk) (pc', stk)

| trans_beq: forall pc stk ofs n1 n2 pc', code_at C pc = Some(Ibeq ofs) ->
                                          pc' = (if beq_nat n1 n2 then pc + 1 + ofs else pc + 1) ->
                                          transition C (pc, n2 :: n1 :: stk) (pc', stk)

| trans_bne: forall pc stk ofs n1 n2 pc', code_at C pc = Some(Ibne ofs) ->
                                          pc' = (if beq_nat n1 n2 then pc + 1 else pc + 1 + ofs) ->
                                          transition C (pc, n2 :: n1 :: stk) (pc', stk)

| trans_ble: forall pc stk ofs n1 n2 pc', code_at C pc = Some(Ible ofs) ->
                                          pc' = (if leb n1 n2 then pc + 1 + ofs else pc + 1) ->
                                          transition C (pc, n2 :: n1 :: stk) (pc', stk)

| trans_bgt: forall pc stk ofs n1 n2 pc', code_at C pc = Some(Ibgt ofs) ->
                                          pc' = (if leb n1 n2 then pc + 1 else pc + 1 + ofs) ->
                                          transition C (pc, n2 :: n1 :: stk) (pc', stk).


Definition varlist := list string.

Fixpoint find (var : id) (vlist : varlist) : option nat :=
  match vlist with
  | nil => None
  | u::vlist' => if beq_id (Id u) var then
               Some O
             else
               match find var vlist' with
               | None => None
               | Some n => Some (S n)
               end
  end.



Fixpoint gen_vlist (c:com) (ivlist: varlist): varlist :=
  match c with
  | c1 ;; c2 => let v1 := gen_vlist c1 ivlist in
                gen_vlist c2 v1
  | IFB b THEN c1 ELSE c2 FI => let v1 := gen_vlist c1 ivlist in
                                gen_vlist c2 v1
  | WHILE b DO c1 END => gen_vlist c1 ivlist
  | x ::= a => match find (Id x) ivlist with
                | None => x::ivlist
                | _ => ivlist
                end
  | CSkip => ivlist
  end.

Definition get_vlist (c:com): varlist :=
  gen_vlist c nil.
    
Definition X := ("X"%string).
Definition Y := ("Y"%string).
Definition Z := ("Z"%string).


Definition mycode :=
  (
     X ::= ANum 3 ;; WHILE BTrue DO Y ::= AId (Id X) END
  ).

Compute (find (Id Z) (get_vlist mycode)).

Fixpoint compile_aexp (stklen: nat) (vlist : varlist) (a:aexp): code :=
  match a with
  | ANum n => Iconst n :: nil
  | AId x => match find x vlist with
             | None => Iconst 0 :: nil
             | Some n => Iget (stklen-(length vlist)+n) :: nil
             end
  | APlus a1 a2 => let code1 := compile_aexp stklen vlist a1 in
                   let code2 := compile_aexp (stklen+1) vlist a2 in
                   code1 ++ code2 ++ Iadd::nil
  | AMul a1 a2 => let code1 := compile_aexp stklen vlist a1 in
                   let code2 := compile_aexp (stklen+1) vlist a2 in
                   code1 ++ code2 ++ Imul::nil
  | AMinus a1 a2 => let code1 := compile_aexp stklen vlist a1 in
                   let code2 := compile_aexp (stklen+1) vlist a2 in
                   code1 ++ code2 ++ Isub::nil
  end.


Fixpoint compile_bexp (stklen: nat) (vlist : varlist) (b:bexp) (cond:bool) (ofs:nat): code :=
  match b with
  | BTrue => if cond then Ibranch_forward ofs :: nil else nil
  | BFalse => if cond then nil else Ibranch_forward ofs :: nil
  | BEq a1 a2 =>
    let code1 := compile_aexp stklen vlist a1 in
    let code2 := compile_aexp (stklen+1) vlist a2 in
    code1 ++ code2 ++
               (if cond then Ibeq ofs :: nil else Ibne ofs :: nil)
  | BLe a1 a2 =>
    let ans1 := compile_aexp stklen vlist a1 in
    let ans2 := compile_aexp (stklen+1) vlist a2 in
    ans1 ++ ans2 ++
               (if cond then Ible ofs :: nil else Ibgt ofs :: nil)
  | BNot b1 =>
    compile_bexp stklen vlist b1 (negb cond) ofs
  | BAnd b1 b2 =>
    let code2 := compile_bexp stklen vlist b2 cond ofs in
    let code1 := compile_bexp stklen vlist b1 false (if cond then length code2
                                     else ofs + (length code2)) in
     code1 ++ code2
  end.


Fixpoint compile_com (vlist: varlist) (c:com): code :=
  let stklen := length vlist in
  match c with
  | SKIP => nil
  | c1 ;; c2 => (compile_com vlist c1) ++ (compile_com vlist c2)
  | IFB b THEN ifso ELSE ifnot FI =>
    let code_ifso := compile_com vlist ifso in
    let code_ifnot := compile_com vlist ifnot in
    compile_bexp stklen vlist b false (length code_ifso + 1)
                 ++ code_ifso
                 ++ Ibranch_forward (length code_ifnot)
                 :: code_ifnot
  | WHILE b DO body END =>
    let code_body := compile_com vlist body in
    let code_test := compile_bexp stklen vlist b false (length code_body + 1) in
    code_test
      ++ code_body
      ++ Ibranch_backward (length code_test + length code_body + 1)
      :: nil
  | var ::= a =>
            match find (Id var) vlist with
            | Some n =>
              compile_aexp stklen vlist a
                           ++ Iset n ::nil
            | _ => nil
            end
  end.

          
Definition compile_program (p: com): code :=
  compile_com (get_vlist p) p ++ Ihalt::nil.

Definition test_prog0 := X ::= ANum 3;; Y ::= AId (Id X).
Definition test_prog1 := WHILE BTrue DO SKIP END.
Definition test_prog2 :=
  X ::= ANum 3 ;;
  Y ::= AId (Id X) ;;
  WHILE BLe (ANum O) (AId (Id X)) DO Y ::= APlus (AId (Id Y)) (AId (Id X)) ;; X ::= AMinus (AId (Id X)) (ANum 1)  END.

Print test_prog2.
Compute (get_vlist test_prog2).
Compute (compile_program test_prog0). 
Compute (compile_program test_prog1).
Compute (compile_program test_prog2).


Definition mach_terminates (C: code) (stk_init stk_fin: stack) :=
  exists pc,
  code_at C pc = Some Ihalt /\
  star (transition C) (0, stk_init) (pc, stk_fin).

Theorem compile_program_correct_terminating:
  forall c st,
    c / empty_state \\ st ->
    exists stk,
      mach_terminates (compile_program c) nil stk
      /\ True.
Proof.
  
  
             

                                               
            
          

            
          
          
          
