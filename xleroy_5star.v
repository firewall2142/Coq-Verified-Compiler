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

Hint Resolve code_at_app codeseq_at_head codeseq_at_tail codeseq_at_app_left codeseq_at_app_right codeseq_at_app_right2: codeseq.


(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><*)

Fixpoint get_nth_slot (s:stack) (n:nat) : option nat :=
  match s, n with
  | nil, _ => None
  | v::s', O => Some v
  | v :: s', S n' => get_nth_slot s' n'
  end.

Fixpoint set_nth_slot (s:stack) (n:nat) (val:nat): option stack :=
  match s, n with
  | nil, _ => None
  | u :: s', O => Some (val :: s')
  | u :: s', S n' =>
    match set_nth_slot s' n' val with
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
    
Definition X := ("X"%string).
Definition Y := ("Y"%string).
Definition Z := ("Z"%string).


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


Fixpoint compile_com (stk: stack) (vlist: varlist) (c:com): code :=
  let stklen := length vlist in
  match c with
  | SKIP => nil
  | c1 ;; c2 => (compile_com stk
                   vlist c1) ++ (compile_com stk vlist c2)
  | IFB b THEN ifso ELSE ifnot FI =>
    let code_ifso := compile_com stk vlist ifso in
    let code_ifnot := compile_com stk vlist ifnot in
    compile_bexp stklen vlist b false (length code_ifso + 1)
                 ++ code_ifso
                 ++ Ibranch_forward (length code_ifnot)
                 :: code_ifnot
  | WHILE b DO body END =>
    let code_body := compile_com stk vlist body in
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
  ++ compile_com (zerostk_of_len (length vlist)) vlist p
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

Theorem find_get_ofs: forall i vlist n stk,
    find i vlist = Some n ->
    exists m,
      get_nth_slot stk (length stk - length vlist + n) = Some m.
Proof.
Admitted.


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
  forall i,
    (forall n, find i v = Some n ->
               (get_nth_slot stk (length stk - length v + n) = Some (st i)))
    /\
    (find i v = None -> st i = O).


Theorem agree_length_prop : forall vl stk st,
    agree vl stk st -> length stk >= length vl.
Proof.
  induction vl.
  - intros. simpl. omega.
  - intros.
Admitted.






(*<><><><><><><><><> HELPER END<><><><><><><><><><><*)






Fact agree_aeval (v : varlist) (stk : stack) (st: state) :
  forall (a:aexp),
    agree v stk st -> aeval st a = aeval_stk v stk a.
Proof.
  intros.
  unfold agree in *.
  induction a.
  - simpl. reflexivity.
  - simpl. Check find_get_ofs.
    destruct (H i) as [H1 H2].
    destruct (find i v) as [n | ] eqn:E.
Admitted.




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
    codeseq_at C pc (compile_aexp (length stk) vlist a) ->
    star (transition C) (pc, stk)
         (pc + length(compile_aexp (length stk) vlist a),
          (aeval_stk vlist stk a)::stk).
Proof.
  induction a.
  { intros. apply star_one. apply trans_const. eauto with codeseq. }
  {
    intros.
    apply star_one.
    simpl in *.
    destruct (find i vlist) as [| n] eqn:E.
    - simpl. eapply trans_get. eauto with codeseq.
      Check find_get_ofs.
      destruct (find_get_ofs _ _ _ stk E) as [m mH].
      rewrite mH. reflexivity.
    - simpl. apply trans_const. eauto with codeseq.
  }
  {
    intros. simpl. eapply star_trans.
    apply (IHa1 C stk pc vlist). eauto with codeseq.
    eapply star_trans. apply (IHa2 _ _ _ vlist). simpl in H.
    rewrite plus_comm in H. simpl in H. eauto with codeseq.
    apply star_one. repeat (rewrite app_length || simpl).
    rewrite plus_assoc. rewrite (Nat.add_1_r (length stk)).
    rewrite plus_assoc with (p := 1).
    apply trans_add. simpl in H. rewrite Nat.add_1_r in H. eauto with codeseq.
  }

  (* DIY just replace trans_add*)
Admitted.


Definition mach_terminates (C: code) (stk_init stk_fin: stack) :=
  exists pc,
  code_at C pc = Some Ihalt /\
  star (transition C) (0, stk_init) (pc, stk_fin).

Search "agree".

Lemma compile_com_correct_terminating:
  forall (C:code) (c : com) (st st': state),
  c / st \\ st' ->
  forall (stk:stack) (vlist:varlist) (pc:nat),
    codeseq_at C pc (compile_com stk vlist c) ->
    agree vlist stk st ->
  exists stk',
     star (transition C) (pc, stk) (pc + length (compile_com stk vlist c), stk')
     /\ agree vlist stk st'.
Proof.
  intros.
  induction c.
  {
    exists stk. simpl. split. rewrite Nat.add_0_r. apply star_refl.
    inversion H. subst. assumption.
  }
  {
    unfold compile_com. simpl in H0.
    destruct (find (Id x) vlist) as [n | ] eqn:E.
    - Check agree_length_prop.
      assert (E' : n < length stk).
      {
        pose (E''' := agree_length_prop _ _ _ H1).
        pose (E'' := find_list_length _ _ _ E).
        omega.
      }

      Check set_nth_success.
      destruct (set_nth_success _ _ (aeval st a) E') as [stk' Hstk'].
      exists stk'. simpl in H0.
      split.
      + eapply star_trans. apply compile_aexp_correct. eauto with codeseq.
  }
Qed.

























(*
Theorem compile_program_correct_terminating:
  forall c st,
    c / empty_state \\ st ->
    exists stk,
      mach_terminates (compile_program c) nil stk
      /\ True.
Proof.
  intros c st H.
  induction H.
  {
    unfold mach_terminates.
    exists nil.
    split. 2 : { exact I. }
    exists 0. split. trivial.
    apply star_refl.
  }
  {
    exists ((aeval st a1) :: nil).
    split. 2:{ exact I. }
    unfold mach_terminates.
    exists (length(compile_program (x ::= a1)) - 1).
    split.
    - unfold compile_program. simpl. rewrite string_dec_refl.
      rewrite app_length. simpl.
      rewrite Nat.add_1_r. simpl. eauto with codeseq.
    - unfold compile_program. unfold gen_vlist. simpl. rewrite string_dec_refl.
      eapply star_trans. apply star_one. apply trans_const. simpl. auto.
      
  }
  (*
  {
    unfold mach_terminates.
    exists (aeval empty_state a1 :: nil).
    split. 2 : { trivial. } 
    exists (length (Iconst 0::nil ++ compile_aexp 1 (x::nil) a1 ++ Iset 0 ::nil)).
    split.
    - unfold compile_program. simpl. rewrite string_dec_refl. auto with codeseq.
    - unfold compile_program. unfold gen_vlist. simpl. rewrite string_dec_refl.
      eapply star_trans. apply star_one. apply trans_const. reflexivity.
      repeat rewrite app_length. simpl.
      Check compile_aexp_correct.
  }*)
  
    
             

                                               
            
          

            
          
          
          
