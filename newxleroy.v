Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Lists.List.
(*From Coq Require Import Arith.EqNat.*)
(*From Coq Require Import omega.Omega.*)
(*From Coq Require Import Init.Nat.*)
(*Import ListNotations.*)

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
Definition varmap := id -> option nat. 

Definition empty_varmap : varmap := fun _ => None.
Definition update_varmap (f : varmap) (varname : id) (abspos : nat) : varmap :=
  fun t:id => if beq_id t varname then Some abspos else (f t).

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

Fixpoint prog_vmap (c : com) (v : varmap) (size: nat): (varmap*nat)%type :=
  match c with
  | c1 ;; c2  =>  let vn := prog_vmap c1 v size in
                  prog_vmap c2 (fst vn) (snd vn)
  | x ::= a1  =>  (update_varmap v (Id x) size , size+1)
  | _ => (v, size)
  end.

Fixpoint find (l : list string) (s : string): option nat :=
  match l with
  | nil     => None
  | v::l'    => if string_dec v s then Some O else
               match find l' s with
               | None =>  None
               | Some n => Some (S n)
               end
  end.


Fixpoint varlist (c: com) (l : list string): list string :=
  match c with
  | SKIP                      =>  l
  | x ::= a                   =>  match find l x with | None => x :: l | Some _ => l end
  | c1 ;; c2                  =>  varlist c2 (varlist c1 l)
  | IFB b THEN c1 ELSE c2 FI  =>  varlist c2 (varlist c1 l)
  | WHILE b DO c1 END         =>  varlist c1 l
  end.

Definition sample_code := (
  "X" ::= ANum 3 ;; "X" ::= ANum 69 ;; IFB BTrue THEN "Y" ::= ANum 3 ELSE SKIP FI
).

Print sample_code.
Compute (varlist sample_code nil).

Fixpoint compile_aexp (a: aexp) (vmp : varmap) (stk_size : nat): code :=
  match a with
  | ANum n => Iconst n :: nil
  | AId x =>  match vmp x with
              | None => Iconst 0 :: nil
              | Some n => Iget (stk_size - n - 1) :: nil
              end
  | APlus a1 a2 =>  (compile_aexp a1 vmp stk_size) ++ (compile_aexp a2 vmp (stk_size+1)) ++ (Iadd :: nil)
  | AMinus a1 a2 => (compile_aexp a1 vmp stk_size) ++ (compile_aexp a2 vmp (stk_size+1)) ++ (Isub :: nil)
  | AMul a1 a2 =>   (compile_aexp a1 vmp stk_size) ++ (compile_aexp a2 vmp (stk_size+1)) ++ (Imul :: nil)
  end.

Fixpoint compile_bexp (b: bexp) (vmp: varmap) (stk_size : nat) (cond:bool) (ofs: nat): code :=
  match b with
  | BTrue =>        if cond then (Ibranch_forward ofs :: nil) else nil
  | BFalse =>       if cond then nil else (Ibranch_forward ofs :: nil)
  | BEq a1 a2 =>    (compile_aexp a1 vmp stk_size) ++ (compile_aexp a2 vmp (stk_size+1)) ++
                    (if cond then (Ibeq ofs)::nil else (Ibne ofs)::nil)
  | BLe a1 a2 =>    (compile_aexp a1 vmp stk_size) ++ (compile_aexp a2 vmp (stk_size+1)) ++
                    (if cond then (Ible ofs)::nil else (Ibgt ofs)::nil)
  | BNot b1 =>      compile_bexp b1 vmp stk_size (negb cond) ofs
  | BAnd b1 b2 =>   let c2 := (compile_bexp b2 vmp (stk_size+1) cond ofs) in
                    let ofsc1:nat := if cond then (length c2) else (ofs + length c2) in
                    let c1 := (compile_bexp b1 vmp stk_size false ofsc1) in
                    (c1 ++ c2)
  end.

Definition test_vmap :=
  fun t:id => if beq_id t (Id "X") then Some 0
              else if beq_id t (Id "Y") then Some 1
              else None.

Definition X := AId (Id "X").
Definition Y := AId (Id "Y").
Definition Z := AId (Id "Z").
Definition W := AId (Id "W").
(*)
(* X + (X + Y)*)
Definition testexp1 := (APlus (X) (APlus (X) (Y)) ).
Compute (compile_aexp testexp1 test_vmap 2).

(* Y + (X + Y)*)
Definition testexp2 := (APlus (Y) (APlus (X) (Y)) ).
Compute (compile_aexp testexp2 test_vmap 2).


Definition test_vmap3 := 
  fun t:id => if beq_id t (Id "Z") then Some 2 else test_vmap t.

(* Z + (2 + Y)*)
Definition testexp3 := (APlus (Z) (APlus (X) (Y)) ).
Compute (compile_aexp testexp3 test_vmap3 3).

(* (X*X - 2*X*Y) + Y*)
Definition testexp4 := (APlus (AMinus (AMul X X) (AMul (ANum 2) (AMul X Y))) Y ).
Compute (  compile_aexp testexp4 test_vmap 2  ).


(* compile com * init_stack * varmap -> code * stack * varmap*)
Fixpoint compile_com (c : com) (stack_len : nat)(v : varmap): (code * (nat * varmap)) :=
  match c with
  | SKIP                             => (nil , (stack_len, v))
  | c1 ;; c2                         => let comp1 := (compile_com c1 stack_len v) in
                                        let comp2 := (compile_com c2 (fst (snd comp1)) (snd (snd comp1)) ) in
                                        (((fst comp1) ++ (fst comp2)), snd comp2)
  | x ::= a                          => match v (Id x) with
                                        | None =>  (    compile_aexp a v (stack_len)   ,
                                                      ( stack_len + 1 , update_varmap v (Id x) stack_len )      )
                                        | Some pos => (   (compile_aexp a v (stack_len)) ++ (Iset (stack_len-(pos+1))::nil ),
                                                      ( stack_len, v)  )
                                        end
                                        
  | IFB b THEN ifso ELSE ifnotso FI  => let code_ifso := (compile_com ifso stack_len v) in
                                        let code_ifnotso := (compile_com ifnotso stack_len v) in
                                        let ifelse_code := (compile_bexp b v stack_len false ((length (fst code_ifso)) + 1))
                                          ++ (fst code_ifso)
                                          ++ (Ibranch_forward (length (fst code_ifnotso)) :: nil)
                                          ++ (fst code_ifnotso)
                                        in
                                        (ifelse_code, ())
  | WHILE b DO body END              => let code_body := (compile_com body stack_len v) in
                                        let code_test := compile_bexp b false (length code_body + 1) in
                                        code_test
                                          ++ code_body
                                          ++ Ibranch_backward (length code_test + length code_body + 1) :: nil
  end.                                          
*)
                                             
                                                 
                                                            
                                                            
                                             
  
                                  

































