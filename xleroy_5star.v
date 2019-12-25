
Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Lists.List.
Require Export Sequences.
Require Export Maps.
Require Import Omega.
(*From Coq Require Import Arith.EqNat.*)
(*From Coq Require Import omega.Omega.*)
(*From Coq Require Import Init.Nat.*)

Ltac normalize :=
  repeat rewrite app_length in *;
  repeat rewrite plus_assoc in *;
  repeat rewrite plus_0_r in *;
  repeat rewrite Nat.sub_0_r in *;
  simpl in *.

Ltac normalize2 :=
  repeat rewrite app_length in *;
  repeat rewrite plus_assoc in *;
  repeat rewrite plus_0_r in *;
  repeat rewrite Nat.sub_0_r in *;
  repeat rewrite Nat.add_1_r in *;
  repeat rewrite Nat.add_0_r in *;
  simpl in *.

(* ========== Maps  =========== *)
Inductive id : Type :=
  | Id : string -> id.

Theorem id_inj: forall u v, Id u = Id v <-> u = v.
Proof. intros. split; intros; [inversion H | rewrite H]; auto.
Qed.

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


Definition total_map (A:Type) := id -> A.

(** Intuitively, a total map over an element type [A] is just a
    function that can be used to look up [id]s, yielding [A]s. *)

(** The function [t_empty] yields an empty total map, given a default
    element; this map always returns the default element when applied
    to any id. *)

Definition t_empty {A:Type} (v : A) : total_map A :=
  (fun _ => v).

(** More interesting is the [update] function, which (as before) takes
    a map [m], a key [x], and a value [v] and returns a new map that
    takes [x] to [v] and takes every other key to whatever [m] does. *)

Definition t_update {A:Type} (m : total_map A)
                    (x : id) (v : A) :=
  fun x' => if beq_id x x' then v else m x'.

Search "eq".

Theorem if_string_dec_eqb : forall s1 s2,
    (if string_dec s1 s2 then true else false) =
    String.eqb s1 s2.
Proof.
  intros.
  destruct (string_dec s1 s2). rewrite e. auto using String.eqb_refl.
  
  destruct (s1 =? s2)%string eqn:E. 
  apply String.eqb_eq in E. unfold not in n. destruct (n E). reflexivity.
Qed.
(* ======================= Imp =============================== *)

Definition state := total_map nat.

Definition empty_state : state :=
  t_empty 0.


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

Definition X := ("X"%string).
Definition Y := ("Y"%string).
Definition Z := ("Z"%string).
Definition W := ("W"%string).


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

Coercion Id : string >-> id.
Coercion AId : id >-> aexp.
Coercion ANum : nat >-> aexp.
Definition bool_to_bexp (b : bool) : bexp :=
  if b then BTrue else BFalse.
Coercion bool_to_bexp : bool >-> bexp.
Bind Scope imp_scope with aexp.
Bind Scope imp_scope with bexp.
Delimit Scope imp_scope with imp.
Notation "x + y" := (APlus x y) (at level 50, left associativity) : imp_scope.
Notation "x - y" := (AMinus x y) (at level 50, left associativity) : imp_scope.
Notation "x * y" := (AMul x y) (at level 40, left associativity) : imp_scope.
Notation "x <= y" := (BLe x y) (at level 70, no associativity) : imp_scope.
Notation "x = y" := (BEq x y) (at level 70, no associativity) : imp_scope.
Notation "x && y" := (BAnd x y) (at level 40, left associativity) : imp_scope.
Notation "'~' b" := (BNot b) (at level 75, right associativity) : imp_scope.
Definition example_aexp := (3 + (X * 2))%imp : aexp.
Definition example_bexp := (true && ~(X <= 4))%imp : bexp.




(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><*)

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


(* ======================= codeseq =============================== *)


Fixpoint code_at (C:code) (pc: nat) : option instruction :=
  match C, pc with
  | nil, _ => None
  | i::C', O => Some i
  | i::C', S pc' => code_at C' pc'
  end.


Inductive codeseq_at: code -> nat -> code -> Prop :=
  | codeseq_at_intro: forall C1 C2 C3 pc,
      pc = length C1 ->
      codeseq_at (C1 ++ C2 ++ C3) pc C2.

Lemma code_at_app:
  forall i c2 c1 pc,
  pc = length c1 ->
  code_at (c1 ++ i :: c2) pc = Some i.
Proof.
  induction c1; simpl; intros; subst pc; auto.
Qed.

Lemma codeseq_at_head:
  forall C pc i C',
  codeseq_at C pc (i :: C') ->
  code_at C pc = Some i.
Proof.
  intros. inversion H. simpl. apply code_at_app. auto.
Qed.

Lemma codeseq_at_tail:
  forall C pc i C',
  codeseq_at C pc (i :: C') ->
  codeseq_at C (pc + 1) C'.
Proof.
  intros. inversion H. 
  change (C1 ++ (i :: C') ++ C3)
    with (C1 ++ (i :: nil) ++ C' ++ C3).
  rewrite <- app_ass. constructor. rewrite app_length. auto.
Qed. 

Lemma codeseq_at_app_left:
  forall C pc C1 C2,
  codeseq_at C pc (C1 ++ C2) ->
  codeseq_at C pc C1.
Proof.
  intros. inversion H. rewrite app_ass. constructor. auto.
Qed.

Lemma codeseq_at_app_right:
  forall C pc C1 C2,
  codeseq_at C pc (C1 ++ C2) ->
  codeseq_at C (pc + length C1) C2.
Proof.
  intros. inversion H. rewrite app_ass. rewrite <- app_ass. constructor. rewrite app_length. auto.
Qed.

Lemma codeseq_at_app_right2:
  forall C pc C1 C2 C3,
  codeseq_at C pc (C1 ++ C2 ++ C3) ->
  codeseq_at C (pc + length C1) C2.
Proof.
  intros. inversion H. repeat rewrite app_ass. rewrite <- app_ass. constructor. rewrite app_length. auto.
Qed.

Hint Resolve code_at_app codeseq_at_head codeseq_at_tail codeseq_at_app_left codeseq_at_app_right codeseq_at_app_right2 Nat.add_0_r Nat.add_1_r Nat.add_assoc Nat.add_comm :codeseq.


(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><*)

Fixpoint get_nth_slot (stk:stack) (n:nat) : option nat :=
  match stk with
  | nil => None
  | v :: stk' =>
    match n with
    | O => Some v
    | S n' => get_nth_slot stk' n'
    end
  end.

Fixpoint set_nth_slot (stk:stack) (n:nat) (val:nat): option stack :=
  match stk with
  | nil => None
  | s :: stk'  =>
    match n with
    | O => Some (val :: stk')
    | S n' => match set_nth_slot stk' n' val with
              | None => None
              | Some ans => Some (s :: ans)
              end
    end
  end.
    
Import ListNotations.

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
    

Definition mycode :=
  (
     X ::= ANum 3 ;; WHILE BTrue DO Y ::= AId (Id X) END
  ).

Compute (find (Id Z) (gen_vlist mycode nil)).

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


Fixpoint compile_com (stklen : nat) (vlist: varlist) (c:com): code :=
  match c with
  | SKIP => nil
  | c1 ;; c2 => (compile_com stklen
                   vlist c1) ++ (compile_com stklen vlist c2)
  | IFB b THEN ifso ELSE ifnot FI =>
    let code_ifso := compile_com stklen vlist ifso in
    let code_ifnot := compile_com stklen vlist ifnot in
    compile_bexp stklen vlist b false (length code_ifso + 1)
                 ++ code_ifso
                 ++ Ibranch_forward (length code_ifnot)
                 :: code_ifnot
  | WHILE b DO body END =>
    let code_body := compile_com stklen vlist body in
    let code_test := compile_bexp stklen vlist b false (length code_body + 1) in
    code_test
      ++ code_body
      ++ Ibranch_backward (length code_test + length code_body + 1)
      :: nil
  | var ::= a =>
            match find (Id var) vlist with
            | Some n =>
              compile_aexp stklen vlist a
                           ++ Iset (stklen - length vlist + n) ::nil
            | _ => nil
            end
  end.


Fixpoint initialize_vars (l : varlist): code :=
  match l with
  | nil => nil
  | v :: l' => (Iconst O) :: initialize_vars l'
  end.


Fixpoint zerostk_of_len (n: nat) : stack :=
  match n with | O => nil | S n' => O :: zerostk_of_len n' end.

Definition compile_program (p: com): code :=
  let vlist := gen_vlist p nil in
  initialize_vars vlist
  ++ compile_com (length vlist) vlist p
  ++ Ihalt::nil.

Definition test_prog0 := X ::= ANum 3;; Y ::= AId (Id X).
Definition test_prog1 := WHILE BTrue DO SKIP END.
Definition test_prog2 :=
  X ::= ANum 3 ;;
  Y ::= AId (Id X) ;;
  WHILE BLe (ANum O) (AId (Id X)) DO Y ::= APlus (AId (Id Y)) (AId (Id X)) ;; X ::= AMinus (AId (Id X)) (ANum 1)  END.

Print test_prog2.
Compute (gen_vlist test_prog2 nil).
Compute (compile_program test_prog0). 
Compute (compile_program test_prog1).
Compute (compile_program test_prog2).

Fixpoint aeval (st : state) (a:aexp): nat :=
  match a with
  | ANum n => n
  | AId x => st x
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2 => (aeval st a1) - (aeval st a2)
  | AMul a1 a2 => (aeval st a1) * (aeval st a2)
  end.


Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => beq_nat (aeval st a1) (aeval st a2)
  | BLe a1 a2   => leb (aeval st a1) (aeval st a2)
  | BNot b1     => negb (beval st b1)
  | BAnd b1 b2  => andb (beval st b1) (beval st b2)
  end.



Fixpoint aeval_stk (v:varlist) (stk: stack) (a:aexp): nat :=
  match a with
  | ANum n => n
  | AId x => match find x v with
             | Some n =>
               match get_nth_slot stk ((length stk) - (length v) + n) with
               | Some val => val
               | _ => 0
               end
             | _ => 0
             end
  | APlus a1 a2 => (aeval_stk v stk a1) + (aeval_stk v ((aeval_stk v stk a1) ::stk) a2)
  | AMinus a1 a2 => (aeval_stk v stk a1) - (aeval_stk v ((aeval_stk v stk a1) ::stk) a2)
  | AMul a1 a2 => (aeval_stk v stk a1) * (aeval_stk v ((aeval_stk v stk a1) ::stk) a2)
  end.

Fixpoint beval_stk (v:varlist) (stk: stack) (b:bexp): bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => beq_nat (aeval_stk v stk a1) (aeval_stk v stk a2)
  | BLe a1 a2 => leb (aeval_stk v stk a1) (aeval_stk v stk a2)
  | BNot b1 => negb (beval_stk v stk b1)
  | BAnd b1 b2 => andb (beval_stk v stk b1) (beval_stk v stk b2)
  end.





(*<><><><><><><><><> HELPER <><><><><><><><><><><*)





Fact string_dec_refl:
  forall x, (if string_dec x x then true else false) = true.
Proof.
  intros. destruct string_dec; auto.
Qed.

Fact get_nth_success: forall stk u, u < length stk -> exists v,
      get_nth_slot stk u = Some v.
Proof.
  induction stk.
  simpl. intros. omega.
  intros u.
  destruct u.
  - subst. intros.
    exists a. reflexivity.
  - simpl. intros. apply IHstk. omega.
Qed.

Fact find_list_length:
  forall vlist i n,
    find i vlist = Some n -> n < length vlist.
Proof.
  induction vlist as [| v vl].
  - intros. discriminate.
  - destruct i as [i]. simpl. rewrite if_string_dec_eqb.
    destruct (v =? i)%string eqn:E.
    + intros. injection H. omega.
    + destruct (find (Id i) vl) as [m|] eqn:Q.
      intros. injection H.
      pose (H1 := IHvl _ _ Q). omega.
      intros. discriminate.
Qed.

Theorem find_get_ofs: forall (i:id) vlist n stk,
    length stk >= length vlist ->
    find i vlist = Some n ->
    exists m,
      get_nth_slot stk (length stk - length vlist + n) = Some m.
Proof.
  intros.
  apply find_list_length in H0.
  apply get_nth_success.
  omega.
Qed.


Theorem set_nth_success:
  forall stk pos val,
    pos < length stk ->
  exists stk',
      set_nth_slot stk pos val = Some stk'.
Proof.
  induction stk.
  - intros. simpl in H. omega.
  - intros. destruct pos as [| pos]. simpl. eauto.
    simpl in H.
    cut (pos < length stk). simpl. intros.
    destruct (IHstk pos val H0) as [ stk' hstk'].
    rewrite hstk'. eauto.
    omega.
Qed.




Definition agree (v : varlist) (stk : stack) (st : state) :=
  length stk = length v /\
  (forall i,
    (forall n, find i v = Some n ->
               (get_nth_slot stk (length stk - length v + n) = Some (st i)) )
    /\
    (find i v = None -> st i = O))
.


Theorem get_set_eq : forall pos l l' val,
    set_nth_slot l pos val = Some l' ->
    get_nth_slot l' pos = Some val.
Proof.
  induction pos.
  - destruct l.
    + discriminate.
    + intros. simpl in H. inversion H. subst. reflexivity.
  - intros. destruct l; try discriminate.
    simpl in H.
    destruct (set_nth_slot l pos val) eqn:E; try discriminate.
    inversion H. simpl. eapply IHpos. apply E.
Qed.

Theorem get_other_set : forall val l' l n' n,
    set_nth_slot l n val = Some l' ->
    n' <> n ->
    get_nth_slot l' n' = get_nth_slot l n'.
Proof.
  induction l'.
  - intros. induction l. reflexivity.
    simpl in *. destruct n. discriminate.
    destruct (set_nth_slot l n val); discriminate.
  - intros.
    destruct l. {simpl in *. discriminate. }
    destruct n.
    + simpl in H. inversion H. subst.
      destruct n'. omega.
      simpl. reflexivity.
    + simpl in H.
      destruct (set_nth_slot l n val) eqn:E; try discriminate.
      inversion H. subst.
      destruct n'.
      * simpl. reflexivity.
      * simpl. eapply IHl'. apply E.
        omega.
Qed.

Fact set_nth_length: forall stk' stk p v,
    set_nth_slot stk p v = Some stk' ->
    length stk = length stk'.
Proof.
  induction stk'.
  - intros. simpl in H.
    destruct stk; simpl in *. discriminate.
    destruct p. discriminate. destruct (set_nth_slot stk p v); discriminate.
  - intros. destruct stk.
    + simpl in *. discriminate.
    + simpl. destruct p; simpl in *. inversion H. subst. reflexivity.
      destruct (set_nth_slot stk p v) eqn:E; try discriminate.
      inversion H. subst. eauto.
Qed.

Theorem find_inj :
  forall x y vl n,
    find x vl = Some n ->
    (find y vl = find x vl <-> x = y).
Proof.
  induction vl.
  {intros. split; intros; simpl in *; discriminate. }
  intros. split;intros.
  destruct (beq_id a x) eqn:E.
  - simpl in H. remember E as t. unfold beq_id in t. rewrite t in H.
    inversion H. clear Heqt t. rewrite beq_id_true_iff in E. subst.
    simpl in H0. rewrite string_dec_refl in H0.
    destruct (beq_id a y) eqn:E.
    + apply beq_id_true_iff in E. assumption.
    + unfold beq_id in E. rewrite E in H0. destruct (find y vl); discriminate.
  - destruct x as [ x'].
    unfold beq_id in E.
    destruct (beq_id a y) eqn:E'.
    + apply beq_id_true_iff in E'. rewrite H in H0.
      destruct y as [y'].
      simpl in H0. inversion E'. clear E'.
      rewrite H2 in H0. rewrite string_dec_refl in H0. inversion H0.
      subst.
      simpl in H.
      destruct (if string_dec y' x' then true else false); try discriminate.
      destruct (find x' vl); discriminate.
    + destruct (if string_dec a x' then true else false) eqn:Ex; try discriminate.
      * clear E. destruct y  as [y']. unfold beq_id in E'.
        rewrite H in H0. simpl in H, H0. rewrite Ex in H. rewrite E' in H0.
        destruct (find x' vl); try discriminate.
        destruct (find y' vl); try discriminate.
        inversion H. inversion H0.
        eapply IHvl. destruct n. discriminate.
        auto. rewrite <- H2 in H3. auto.
  - subst. reflexivity.
Qed.

Theorem find_inj2 :
  forall vl x y n1 n2,
    find x vl = Some n1 ->
    find y vl = Some n2 ->
    (x = y <-> n1 = n2).
Proof.
  intros. split; intros.
  - subst. rewrite H in H0. inversion H0. reflexivity.
  - pose (Inj := find_inj _ y _ _ H).
    rewrite <- Inj. rewrite <- H1 in H0. rewrite H0. auto.
Qed.


Theorem aeval_stk_appended: forall (v : varlist) (a:aexp) (stk: stack) (s : nat) ,
    length v <= length stk ->
    aeval_stk v stk a = aeval_stk v (s::stk) a.
Proof.
  assert (G: forall (n s:nat) stk (v:varlist),
             length stk >= length v ->
             get_nth_slot (s :: stk) (length (s :: stk) - length v + n)
             =
             get_nth_slot stk (length stk - length v + n)). 
  {
    intros.
    assert (t: length (s::stk) - length v = S (length stk - length v)).
    { simpl. destruct (length v). omega. omega. }
    rewrite t.
    simpl. reflexivity.
  }

  induction a.
  - simpl. reflexivity.
  - intros. unfold aeval_stk.
    destruct (find i v) eqn:E; try auto.
    rewrite G. reflexivity. omega.
  - intros. simpl. rewrite (IHa1 stk s H).
    cut (aeval_stk v (aeval_stk v (s :: stk) a1 :: stk) a2 =
         aeval_stk v (aeval_stk v (s :: stk) a1 :: s ::  stk) a2). omega.
    assert (P1: aeval_stk v (s :: stk) a2 = aeval_stk v stk a2).
    { symmetry. auto.  }
    assert (P2: aeval_stk v (s :: stk) a2
                =
                aeval_stk v (aeval_stk v (s :: stk) a1 :: s :: stk) a2).
    { apply IHa2. simpl. omega. }
    
    assert (P3: aeval_stk v (stk) a2
                =
                aeval_stk v (aeval_stk v (s :: stk) a1 :: stk) a2).
    { apply IHa2. simpl. omega. }
    omega.
  - intros. simpl. rewrite (IHa1 stk s H).
    cut (aeval_stk v (aeval_stk v (s :: stk) a1 :: stk) a2 =
         aeval_stk v (aeval_stk v (s :: stk) a1 :: s ::  stk) a2). omega.
    assert (P1: aeval_stk v (s :: stk) a2 = aeval_stk v stk a2).
    { symmetry. auto.  }
    assert (P2: aeval_stk v (s :: stk) a2
                =
                aeval_stk v (aeval_stk v (s :: stk) a1 :: s :: stk) a2).
    { apply IHa2. simpl. omega. }
    assert (P3: aeval_stk v (stk) a2
                =
                aeval_stk v (aeval_stk v (s :: stk) a1 :: stk) a2).
    { apply IHa2. simpl. omega. }
    omega.
  - intros. simpl. rewrite (IHa1 stk s H).
    cut (aeval_stk v (aeval_stk v (s :: stk) a1 :: stk) a2 =
         aeval_stk v (aeval_stk v (s :: stk) a1 :: s ::  stk) a2).
    intros.
    rewrite H0. reflexivity.
    assert (P1: aeval_stk v (s :: stk) a2 = aeval_stk v stk a2).
    { symmetry. auto.  }
    assert (P2: aeval_stk v (s :: stk) a2
                =
                aeval_stk v (aeval_stk v (s :: stk) a1 :: s :: stk) a2).
    { apply IHa2. simpl. omega. }
    assert (P3: aeval_stk v (stk) a2
                =
                aeval_stk v (aeval_stk v (s :: stk) a1 :: stk) a2).
    { apply IHa2. simpl. omega. }
    omega.  
Qed.
(*<><><><><><><><><> HELPER END<><><><><><><><><><><*)






Fact agree_aeval (v : varlist) (stk : stack) (st: state) :
  forall (a:aexp),
    agree v stk st -> aeval st a = aeval_stk v stk a.
Proof.
  unfold agree.
  induction a; intros; destruct H.
  - reflexivity.

  - simpl. destruct (H0 i).
    destruct (find i v) eqn:E.
    rewrite H1. auto. auto. auto.
    
  - simpl. rewrite IHa1. rewrite IHa2.
    simpl. rewrite <- aeval_stk_appended. reflexivity. omega.
    split. omega. intros. auto. auto.

  - simpl. rewrite IHa1. rewrite IHa2.
    simpl. rewrite <- aeval_stk_appended. reflexivity. omega.
    split. omega. intros. auto. auto.

  - simpl. rewrite IHa1. rewrite IHa2.
    simpl. rewrite <- aeval_stk_appended. reflexivity. omega.
    split. omega. intros. auto. auto.

Qed.
  
Fact agree_beval (v : varlist) (stk : stack) (st: state) :
  forall (b:bexp),
    agree v stk st -> beval st b = beval_stk v stk b.
Proof.
  induction b; simpl; intros; eauto using agree_aeval.
  - rewrite (IHb H). reflexivity.
  - rewrite (IHb1 H). rewrite (IHb2 H). reflexivity.
Qed.
    
Reserved Notation "c1 '/' st '\\' st'"
                  (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      SKIP / st \\ st
  | E_Ass  : forall st a1 n x,
      aeval st a1 = n ->
      (x ::= a1) / st \\ (t_update st (Id x) n)
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




Lemma compile_aexp_correct:
  forall (a:aexp) (C:code) (stk:stack) (pc:nat) (vlist:varlist),
    forall (ineq : length stk >= length vlist), 
    codeseq_at C pc (compile_aexp (length stk) vlist a) ->
    star (transition C) (pc, stk)
         (pc + length(compile_aexp (length stk) vlist a),
          (aeval_stk vlist stk a)::stk).
Proof.
  induction a.
  - intros. apply star_one. apply trans_const. eauto with codeseq. 
  - intros.
    apply star_one.
    simpl in *.
    destruct (find i vlist) as [| n] eqn:E.
    + simpl. eapply trans_get. eauto with codeseq.
      
      destruct (find_get_ofs _ _ _  stk ineq E) as [m mH].
      rewrite mH. reflexivity.
    + simpl. apply trans_const. eauto with codeseq.
  
  - intros. simpl. eapply star_trans.
    apply (IHa1 C stk pc vlist ineq). eauto with codeseq.
    eapply star_trans. apply (IHa2 _ _ _ vlist). simpl. omega. simpl in H.
    rewrite plus_comm in H. simpl in H. eauto with codeseq.
    apply star_one. repeat (rewrite app_length || simpl).
    rewrite plus_assoc. rewrite (Nat.add_1_r (length stk)).
    rewrite plus_assoc with (p := 1).
    apply trans_add. simpl in H. rewrite Nat.add_1_r in H. eauto with codeseq.
  - intros. simpl. eapply star_trans.
    apply (IHa1 C stk pc vlist ineq). eauto with codeseq.
    eapply star_trans. apply (IHa2 _ _ _ vlist). simpl. omega. simpl in H.
    rewrite plus_comm in H. simpl in H. eauto with codeseq.
    apply star_one. repeat (rewrite app_length || simpl).
    rewrite plus_assoc. rewrite (Nat.add_1_r (length stk)).
    rewrite plus_assoc with (p := 1).
    apply trans_sub. simpl in H. rewrite Nat.add_1_r in H. eauto with codeseq.
  - intros. simpl. eapply star_trans.
    apply (IHa1 C stk pc vlist ineq). eauto with codeseq.
    eapply star_trans. apply (IHa2 _ _ _ vlist). simpl. omega. simpl in H.
    rewrite plus_comm in H. simpl in H. eauto with codeseq.
    apply star_one. repeat (rewrite app_length || simpl).
    rewrite plus_assoc. rewrite (Nat.add_1_r (length stk)).
    rewrite plus_assoc with (p := 1).
    apply trans_mul. simpl in H. rewrite Nat.add_1_r in H. eauto with codeseq.
  
Qed.

Lemma compile_bexp_correct:
  forall (b:bexp) (C:code) (stk:stack) (pc:nat) (vlist:varlist) (cond:bool) (ofs:nat),
    length stk >= length vlist ->
    codeseq_at C pc (compile_bexp (length stk) vlist b cond ofs) ->
  star (transition C)
       (pc, stk)
       (pc + length (compile_bexp (length stk) vlist b cond ofs) +
        if eqb (beval_stk vlist stk b) cond then ofs else 0, stk).
Proof.
  induction b.
  - simpl in *. intros. destruct cond eqn:E.
    apply star_one. eapply trans_branch_forward. eauto with codeseq.
    simpl. auto. simpl. normalize. apply star_refl.
  - simpl in *. intros. destruct cond; simpl.
    normalize. apply star_refl.
    apply star_one. eapply trans_branch_forward. eauto with codeseq. auto.
  - intros. simpl in *.
    destruct cond.
    + simpl. eapply star_trans. apply compile_aexp_correct. apply H. eauto with codeseq.
      eapply star_trans. apply compile_aexp_correct. simpl.
      cut( S (Datatypes.length stk) >= Datatypes.length vlist). intros. apply H1. omega.
      simpl. rewrite Nat.add_1_r in H0. eauto with codeseq. normalize.
      apply star_one. eapply trans_beq. rewrite Nat.add_1_r in *. eauto with codeseq.
      pose (av := aeval_stk_appended vlist a0 stk (aeval_stk vlist stk a)).
      rewrite <- av.
      destruct (aeval_stk vlist stk a =? aeval_stk vlist stk a0) eqn:E;
        simpl; normalize2; reflexivity. omega.
    + simpl. eapply star_trans. apply compile_aexp_correct. apply H. eauto with codeseq.
      eapply star_trans. apply compile_aexp_correct. simpl.
      cut( S (Datatypes.length stk) >= Datatypes.length vlist). intros. apply H1. omega.
      simpl. rewrite Nat.add_1_r in H0. eauto with codeseq. normalize.
      apply star_one. eapply trans_bne. rewrite Nat.add_1_r in *. eauto with codeseq.
      pose (av := aeval_stk_appended vlist a0 stk (aeval_stk vlist stk a)).
      rewrite <- av.
      destruct (aeval_stk vlist stk a =? aeval_stk vlist stk a0) eqn:E;
        simpl; normalize2; reflexivity. omega.
  - intros. simpl in *.
    destruct cond.
    + simpl. eapply star_trans. apply compile_aexp_correct. apply H. eauto with codeseq.
      eapply star_trans. apply compile_aexp_correct. simpl.
      cut( S (Datatypes.length stk) >= Datatypes.length vlist). intros. apply H1. omega.
      simpl. rewrite Nat.add_1_r in H0. eauto with codeseq. normalize.
      apply star_one. eapply trans_ble. rewrite Nat.add_1_r in *. eauto with codeseq.
      pose (av := aeval_stk_appended vlist a0 stk (aeval_stk vlist stk a)).
      rewrite <- av.
      destruct (aeval_stk vlist stk a <=? aeval_stk vlist stk a0) eqn:E;
        simpl; normalize2; reflexivity. omega.
    + simpl. eapply star_trans. apply compile_aexp_correct. apply H. eauto with codeseq.
      eapply star_trans. apply compile_aexp_correct. simpl.
      cut( S (Datatypes.length stk) >= Datatypes.length vlist). intros. apply H1. omega.
      simpl. rewrite Nat.add_1_r in H0. eauto with codeseq. normalize.
      apply star_one. eapply trans_bgt. rewrite Nat.add_1_r in *. eauto with codeseq.
      pose (av := aeval_stk_appended vlist a0 stk (aeval_stk vlist stk a)).
      rewrite <- av.
      destruct (aeval_stk vlist stk a <=? aeval_stk vlist stk a0) eqn:E;
        simpl; normalize2; reflexivity. omega.
  - intros. simpl in *. eapply star_trans. apply IHb. apply H. eauto with codeseq.
    destruct cond; simpl; destruct (beval_stk vlist stk b); simpl; apply star_refl. 
  - intros. simpl in *.
    destruct cond; normalize2.
    + eapply star_trans. apply IHb1. apply H. eauto with codeseq.
      destruct (beval_stk vlist stk b1); normalize2; try apply star_refl.
      apply IHb2. auto. eauto with codeseq.
    + eapply star_trans. apply IHb1. apply H. eauto with codeseq.
      destruct (beval_stk vlist stk b1);repeat normalize2.
      * apply IHb2. auto. eauto with codeseq. 
      * set (pc1 := (pc +
                     Datatypes.length
                       (compile_bexp (Datatypes.length stk) vlist b1 false
                                     (ofs + Datatypes.length
                                              (compile_bexp (Datatypes.length stk)
                                                            vlist b2 false ofs))) +
                     ofs + Datatypes.length (compile_bexp (Datatypes.length stk) vlist
                                                          b2 false ofs)))
          in *.
        set (pc2 := (pc +
                     Datatypes.length
                       (compile_bexp (Datatypes.length stk) vlist b1 false
                                     (ofs + Datatypes.length
                                              (compile_bexp (Datatypes.length stk)
                                                            vlist b2 false ofs))) +
                     Datatypes.length (compile_bexp (Datatypes.length stk)
                                                    vlist b2 false ofs) + ofs))
          in *.
        assert (H' : pc1 = pc2).
        { unfold pc1, pc2. omega.  }
        rewrite H'.
        apply star_refl.
Qed.

Definition mach_terminates (C: code) (stk_init stk_fin: stack) :=
  exists pc,
  code_at C pc = Some Ihalt /\
  star (transition C) (0, stk_init) (pc, stk_fin).

Search "agree".



Definition test_prog3 :=
  (Z ::= X;;
       Y ::= 1;;
       WHILE ~(Z = 0) DO
         Y ::= Y * Z;;
         Z ::= Z - 1
      END)%imp.

Import ListNotations.
Compute (compile_program test_prog3).                     

Fixpoint varlist_contains_all (c:com) (vlist : varlist) : Prop :=
  match c with
  | (c1 ;; c2) => (varlist_contains_all c1 vlist /\ varlist_contains_all c2 vlist)
  | IFB b THEN c1 ELSE c2 FI => (varlist_contains_all c1 vlist /\ varlist_contains_all c2 vlist)
  | WHILE b DO c1 END => varlist_contains_all c1 vlist
  | SKIP => True
  | x ::= a => (exists n, find x vlist = Some n)
  end.



Lemma compile_com_correct_terminating:
  forall (c : com) (st st': state),
    c / st \\ st' ->
    forall (C:code) (stk:stack) (vlist:varlist) (pc:nat),
    varlist_contains_all c vlist ->
    codeseq_at C pc (compile_com (length stk) vlist c) ->
    agree vlist stk st ->
  exists stk',
     star (transition C) (pc, stk) (pc + length (compile_com (length stk) vlist c), stk')
     /\ agree vlist stk' st'.
Proof.
  induction 1.
  {
    intros.
    exists stk. simpl. split. rewrite Nat.add_0_r. apply star_refl.
    inversion H. subst. assumption.
  }
  {
    intros. simpl in H0. destruct H0 as [m H0].
    remember H2 as ag.
    destruct H2 as [H2 H2'].
    
    assert (Nstk : exists stk', set_nth_slot stk m n = Some stk').
    { apply set_nth_success. rewrite H2. eapply find_list_length. eauto. }
    destruct Nstk as [stk' Nstk].
    
    eexists. simpl. normalize. rewrite H0 in *.
    split.
    {
      eapply star_trans. apply compile_aexp_correct.
      Search "ge".
      assert (lenIneq : length stk >= length vlist). omega.
      apply lenIneq.
      eauto with codeseq.
      apply star_one. normalize. eapply trans_set. eauto with codeseq.
      rewrite H2. rewrite Nat.sub_diag. simpl.
      Search "aeval".
      rewrite <- (agree_aeval _ _ _ a1 ag). rewrite H. apply Nstk.
    }
    {
      
      
      Search "set_".
      assert (f: length stk' = length vlist).
      {
        rewrite <- H2.
        symmetry.
        eapply set_nth_length with (stk' := stk'). apply Nstk.
      }
      unfold agree. split. assumption.
      intros. split.
      - intros. unfold t_update.
        destruct (H2' i) as [h2 h2'].
        destruct (beq_id x i) eqn:E. try apply beq_id_true_iff in E. 
        + rewrite <- E in H3. rewrite H0 in H3. inversion H3. rewrite <- H5.
          Search "get_set".
          eapply get_set_eq. rewrite f. rewrite Nat.sub_diag. simpl.
          apply Nstk.
        + rewrite f. rewrite H2 in h2.
          Search "get_other".
          rewrite <- (h2 n0 H3).
          eapply get_other_set. apply Nstk.
          rewrite Nat.sub_diag. simpl. apply beq_id_false_iff in E.
          Search "find".
          destruct (find_inj2 _ _ _ _ _ H0 H3) as [contra contra']. auto.
      - intros. destruct (H2' i) as [h2 h2'].
        unfold t_update.
        destruct (beq_id x i) eqn:E; apply beq_id_true_iff in E || apply beq_id_false_iff in E.
        + subst. rewrite H3 in H0. discriminate.
        + auto.
      
    }
  }
  {
    intros. simpl in *.
    destruct H1 as [h1 h2].
    assert (C1: codeseq_at C pc (compile_com (Datatypes.length stk) vlist c1)).
    {eauto with codeseq. }
    assert (C2: codeseq_at C (pc+length (compile_com (Datatypes.length stk) vlist c1))
                           (compile_com (Datatypes.length stk) vlist c2)).
    {eauto with codeseq. }
    
    destruct (IHceval1 C stk vlist pc h1 C1 H3) as [stk' [ih1 ih1']].
    remember ih1' as t.
    destruct t as [ih1'' h1'''].
    remember H3 as t.
    destruct t as [H3' H3''].
    assert (stkE: length stk' = length stk).
    { omega. }
    rewrite <- stkE in C2.
    destruct (IHceval2 C stk' vlist _ h2 C2 ih1') as [stk'' [ih2 ih2']].    
    eexists. split.
    - eapply star_trans. apply ih1. normalize. repeat rewrite stkE in ih2. apply ih2.
    - assumption.
  }
  {
    intros. simpl in H2.

    assert (Ct : codeseq_at C pc
       (compile_bexp (Datatypes.length stk) vlist b false
                     (Datatypes.length (compile_com (Datatypes.length stk) vlist c1) + 1))).
    { eauto with codeseq. }

    set (code_test := (compile_bexp (Datatypes.length stk) vlist b false
                                    (Datatypes.length
                                       (compile_com (Datatypes.length stk) vlist c1) + 1)))
      in *.
    set (code_ifso := compile_com (length stk) vlist c1).
    set (code_ifnot := compile_com (length stk) vlist c2).
    
    assert (C1 : codeseq_at C (pc + Datatypes.length code_test)
                            (compile_com (Datatypes.length stk) vlist c1)). {eauto with codeseq. }
    assert (C2: codeseq_at C (pc + length code_test + length code_ifso + 1) code_ifnot).
    { eauto with codeseq. }
    
    pose (btest := compile_bexp_correct b C stk pc vlist false
                                        (length (code_ifso) + 1) Ct).
    
    destruct H1 as [H1' H1].
    destruct (IHceval C stk _ _ H1' C1 H3) as [stk' [ih ih']].
    
    eexists. split.
    Check agree_beval.
    - eapply star_trans. apply btest. rewrite <- (agree_beval _ _ _ b H3). rewrite H. simpl.
      fold code_ifso code_ifnot code_test in ih |- *. normalize.
      eapply star_trans. apply ih.
      apply star_one. unfold code_ifso. unfold code_ifnot. eapply trans_branch_forward.
      eauto with codeseq. unfold code_ifso, code_test, code_ifnot. omega.
    - assumption.
  }
  {
    intros. simpl in H2.

    assert (Ct : codeseq_at C pc
       (compile_bexp (Datatypes.length stk) vlist b false
                     (Datatypes.length (compile_com (Datatypes.length stk) vlist c1) + 1))).
    { eauto with codeseq. }

    set (code_test := (compile_bexp (Datatypes.length stk) vlist b false
                                    (Datatypes.length
                                       (compile_com (Datatypes.length stk) vlist c1) + 1)))
      in *.
    set (code_ifso := compile_com (length stk) vlist c1) in code_test.
    set (code_ifnot := compile_com (length stk) vlist c2) in code_test.
    
    assert (C1 : codeseq_at C (pc + Datatypes.length code_test)
                            (compile_com (Datatypes.length stk) vlist c1)). {eauto with codeseq. }
    assert (C2: codeseq_at C (pc + length code_test + length code_ifso + 1) code_ifnot).
    { eauto with codeseq. }
    
    pose (btest := compile_bexp_correct b C stk pc vlist false
                                        (length (code_ifso) + 1) Ct).
    
    destruct H1 as [H1' H1].
    destruct (IHceval C stk _ _ H1 C2 H3) as [stk' [ih ih']].

    eexists. split.
    Check agree_beval.
    - eapply star_trans. apply btest. rewrite <- (agree_beval _ _ _ b H3). rewrite H. simpl.
      fold code_ifso code_ifnot code_test in ih |- *. normalize.
      rewrite <- Nat.add_1_l with (length code_ifnot). normalize. apply ih.
    - assumption.
  }
  {
    simpl in *. intros.
    set (code_body := compile_com (Datatypes.length stk) vlist c) in *.
    set (code_test := compile_bexp (Datatypes.length stk) vlist b false
                                   (Datatypes.length code_body + 1)) in *.
    assert (Cb : codeseq_at C (pc + length code_test)
                             (compile_com (Datatypes.length stk) vlist c)).
    { eauto with codeseq. }
    assert (Ct : codeseq_at C pc (compile_bexp (Datatypes.length stk) vlist b false
                                               (Datatypes.length code_body + 1))).
    { eauto with codeseq. }
    
    pose (jump:= compile_bexp_correct  _ _ _ _ _ _ _ Ct).
    rewrite <- (agree_beval _ _ _ b H2) in jump.
    eexists.
    split. 2 : apply H2.
    normalize.
    rewrite H in jump. simpl in jump. normalize.
    fold code_test in jump. assumption.    
  }
  {
    intros.
    set (code_body := compile_com (Datatypes.length stk) vlist c) in *.
    set (code_test := compile_bexp (Datatypes.length stk) vlist b false
                                   (Datatypes.length code_body + 1)) in *.
    assert (Cb : codeseq_at C (pc + length code_test)
                             (compile_com (Datatypes.length stk) vlist c)).
    { eauto with codeseq. }
    assert (Ct : codeseq_at C pc (compile_bexp (Datatypes.length stk) vlist b false
                                               (Datatypes.length code_body + 1))).
    { eauto with codeseq. }
    
    pose (jump:= compile_bexp_correct  _ _ _ _ _ _ _ Ct).
    rewrite <- (agree_beval _ _ _ b H4) in jump.
    simpl. fold code_body code_test.
    simpl in H2.
    destruct (IHceval1 C stk vlist _ H2 Cb H4) as [stk' [ihb ihb']]. 
    assert (V: varlist_contains_all (WHILE b DO c END) vlist).
    {simpl. auto. }

    assert (L : length stk' = length stk).
    { destruct H4. destruct ihb'. omega. }          

    pose (Ihc2 := IHceval2 C stk' _ pc V).
    rewrite L in Ihc2.
    destruct (Ihc2 H3 ihb') as [stk'' ihc].
    eexists. split.
    eapply star_trans. apply jump.
    rewrite H. simpl. fold code_body code_test. normalize. simpl.
    eapply star_trans. apply ihb. fold code_body code_test.
    eapply star_trans. apply star_one. eapply trans_branch_backward. eauto with codeseq.
    2 : {
      fold code_body code_test in ihc. normalize.
      apply ihc.
    }
    fold code_body code_test. normalize. omega.
    apply ihc.
  }
Qed.
