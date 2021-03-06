Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Lists.List.
From StorelessMachine Require Import Sequences.
From StorelessMachine Require Import Maps.
From StorelessMachine Require Import Imp.
From StorelessMachine Require Import Facts.
Import ListNotations.
Require Import Omega.

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


Theorem length_initialize_vars : forall l,
    length (initialize_vars l) = length l.
Proof. induction l; simpl; auto. Qed.

Fixpoint zerostk_of_len (n: nat) : stack :=
  match n with | O => nil | S n' => O :: zerostk_of_len n' end.

Definition compile_program (p: com): code :=
  let vlist := gen_vlist p nil in
  initialize_vars vlist
  ++ compile_com (length vlist) vlist p
  ++ Ihalt::nil.


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



Inductive varlist_contains_all : com -> varlist -> Prop :=
| Vseq : forall c1 c2 vlist,
    varlist_contains_all c1 vlist ->
    varlist_contains_all c2 vlist ->
    varlist_contains_all (c1 ;; c2) vlist
| Vifb : forall c1 c2 vlist b,
    varlist_contains_all c1 vlist ->
    varlist_contains_all c2 vlist ->
    varlist_contains_all (IFB b THEN c1 ELSE c2 FI) vlist
| Vwhile: forall c vlist b,
    varlist_contains_all c vlist ->
    varlist_contains_all (WHILE b DO c END) vlist
| Vskip : forall vlist, varlist_contains_all SKIP vlist
| Vass : forall  vlist x a,
    (exists n, find (Id x) vlist = Some n) ->
    varlist_contains_all (x ::= a) vlist.



Theorem extend_gen_vlist:
  forall a x l,
    varlist_contains_all a l ->
    varlist_contains_all a (x::l).
Proof.
  induction a.
  - constructor.
  - intros. inversion H. subst.
    apply Vass.
    destruct (if string_dec x0 x then true else false) eqn:E.
    + simpl. rewrite E.  exists 0. reflexivity.
    + simpl. rewrite E. destruct H3. rewrite H0. exists (S x1).
      reflexivity.
  - intros. inversion H. subst. apply Vseq; auto.
  - intros. inversion H. subst. apply Vifb; auto.
  - intros. inversion H. subst. apply Vwhile. auto.
Qed.

Theorem gen_gen_vlist:
  forall b a l ,
    varlist_contains_all a l ->
    varlist_contains_all a (gen_vlist b l).
Proof.
  induction b.
  - simpl. auto.
  - intros. simpl. destruct (find x l) eqn:E. assumption.
    apply extend_gen_vlist. assumption.
  - simpl. intros. cut (varlist_contains_all a (gen_vlist b1 l)); intuition.
  - simpl. intros. cut (varlist_contains_all a (gen_vlist b2 l)); intuition.
  - simpl. intros. auto.
Qed.



Theorem gen_vlist_contains_all :
  forall c l, varlist_contains_all c (gen_vlist c l).
Proof.
  induction c.
  - simpl. constructor.
  - intros. simpl. apply Vass. simpl.
    destruct (find x l) eqn:E.
    + rewrite E. exists n. reflexivity. 
    + simpl. rewrite string_dec_refl. exists 0. reflexivity.
  - simpl. intros. apply Vseq. apply gen_gen_vlist. auto. auto.
  - simpl. intros. apply Vifb. apply gen_gen_vlist. auto. auto.
  - simpl. intros. apply Vwhile. auto.
Qed.


Definition agree (v : varlist) (stk : stack) (st : state) :=
  length stk = length v /\
  (forall i,
    (forall n, find i v = Some n ->
               (get_nth_slot stk (length stk - length v + n) = Some (st i)) )
    /\
    (find i v = None -> st i = O))
.


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
    destruct (find i vlist) eqn:E.
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
    intros. inversion H0. subst. clear H0. rename H6 into H0. destruct H0 as [m H0].
    set ( n := aeval st a1). assert (H : n = aeval st a1). auto.
    remember H2 as ag.
    destruct H2 as [H2 H2'].
    
    assert (Nstk : exists stk', set_nth_slot stk m n = Some stk').
    { apply set_nth_success. rewrite H2. eapply find_success_list_length. eauto. }
    destruct Nstk as [stk' Nstk].
    
    eexists. simpl. normalize. rewrite H0 in *.
    split.
    {
      eapply star_trans. apply compile_aexp_correct.
      assert (lenIneq : length stk >= length vlist). omega.
      apply lenIneq.
      eauto with codeseq.
      apply star_one. normalize. eapply trans_set. eauto with codeseq.
      rewrite H2. rewrite Nat.sub_diag. simpl.
      rewrite <- (agree_aeval _ _ _ a1 ag). rewrite H. apply Nstk.
    }
    {
      
      
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
          eapply get_set_eq. rewrite f. rewrite Nat.sub_diag. simpl.
          apply Nstk.
        + rewrite f. rewrite H2 in h2.
          rewrite <- (h2 n0 H3).
          eapply get_other_set. apply Nstk.
          rewrite Nat.sub_diag. simpl. apply beq_id_false_iff in E.
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
    inversion H1. subst. rename H6 into h1. rename H8 into h2.
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

    remember H3 as t. destruct t as [H3' H3'']. clear Heqt.
    assert (Hineq : length stk >= length vlist). omega.
    pose (btest := compile_bexp_correct b C stk pc vlist false
                                        (length (code_ifso) + 1) Hineq Ct).
    inversion H1. subst. rename H8 into H1'. clear H1. rename H9 into H1.
    destruct (IHceval C stk _ _ H1' C1 H3) as [stk' [ih ih']].
    
    eexists. split.
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

    remember H3 as t. destruct t as [H3' H3'']. clear Heqt.
    assert (Hineq : length stk >= length vlist). omega.
    pose (btest := compile_bexp_correct b C stk pc vlist false
                                        (length (code_ifso) + 1) Hineq Ct).
    
    inversion H1. subst. rename H8 into H1'. clear H1. rename H9 into H1.
    destruct (IHceval C stk _ _ H1 C2 H3) as [stk' [ih ih']].

    eexists. split.
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

    remember H2 as t. destruct t as [H2' H2'']. clear Heqt.
    assert (Hineq : length stk >= length vlist). omega.
    
    pose (jump:= compile_bexp_correct  _ _ _ _ _ _ _ Hineq Ct).
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

    
    remember H4 as t. destruct t as [H4' H4'']. clear Heqt.
    assert (Hineq : length stk >= length vlist). omega.
    
    pose (jump:= compile_bexp_correct  _ _ _ _ _ _ _ Hineq Ct).

    rewrite <- (agree_beval _ _ _ b H4) in jump.
    simpl. fold code_body code_test.
    inversion H2. subst. rename H2 into H2o. rename H8 into H2.
    destruct (IHceval1 C stk vlist _ H2 Cb H4) as [stk' [ihb ihb']]. 
    assert (V: varlist_contains_all (WHILE b DO c END) vlist).
    {auto. }

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


Theorem initialize_vars_comm: forall vlist,
    ( Iconst 0 ):: (initialize_vars vlist) = (initialize_vars vlist) ++ [ Iconst 0 ].
Proof.
  induction vlist.
  - reflexivity.
  - simpl. rewrite IHvlist. reflexivity.
Qed.

  
Theorem initialize_correct : forall C vlist pc,
    codeseq_at C pc (initialize_vars vlist) ->
    exists stk,
      star (transition C) (pc, nil) (pc + length vlist, stk)
      /\ agree vlist stk empty_state.
Proof.
  induction vlist.
  {
    intros. simpl. normalize. eexists.
    split. apply star_refl.
    split; simpl; auto.
    intros. split. intros. discriminate.
    intros. cbv delta. reflexivity.
  }
  {
    simpl in *. intros.
    destruct (IHvlist pc). rewrite initialize_vars_comm in H.
    eauto with codeseq. destruct H0.
    eexists. split.
    - eapply star_trans. apply H0.
      assert (pc + S (length vlist) = (pc + length vlist) + 1). omega.
      rewrite H2. apply star_one. apply trans_const.
      rewrite initialize_vars_comm in H.
      assert (forall vlist, length vlist = length (initialize_vars vlist)).
      { intros v. induction v; simpl; auto. }
      rewrite H3.  eauto with codeseq.
    - destruct H1. split. simpl. auto. intros. split;
      destruct i;
        destruct (if string_dec a s then true else false) eqn:E; simpl; rewrite E; intros.
        * inversion H3. rewrite H5. rewrite H1.
          rewrite Nat.sub_diag. simpl. rewrite <- H5. unfold empty_state.
          unfold t_empty. reflexivity.
        * rewrite H1. rewrite Nat.sub_diag. simpl. destruct (find s vlist) eqn:E'.
          pose (ih := H2 (Id s)). destruct ih. rewrite H1 in *.
          rewrite Nat.sub_diag in *. simpl in *.
          { destruct n. cbv delta. simpl. reflexivity.
            apply H2. inversion H3. rewrite <- H7. assumption. 
          }
          discriminate.
        * discriminate.
        * cbv delta. reflexivity.
  }
Qed.


Definition mach_terminates (C: code) (stk_init stk_fin: stack) :=
  exists pc,
  code_at C pc = Some Ihalt /\
  star (transition C) (0, stk_init) (pc, stk_fin).


Theorem compile_program_correct_terminating:
  forall c st,
  c / empty_state \\ st ->
  exists stk,
     mach_terminates (compile_program c) nil stk
  /\ agree (gen_vlist c []) stk st.
Proof.
  intros.
  set (C := compile_program c). unfold compile_program in C.
  assert (C0: codeseq_at ([]++C++[]) 0 C). {constructor. reflexivity. }
  rewrite app_nil_r in C0. simpl in C0.                                           
  pose (C1 := codeseq_at_app_left _ 0 _ _ C0).
  destruct (initialize_correct _ _ _ C1) as [stk0 [H1 [H2 H3]]].
  pose (CC := compile_com_correct_terminating _ _ _ H C stk0 (gen_vlist c [])
                                              (length ( initialize_vars (gen_vlist c [])))).
  destruct CC as [stk' [H4 H5]].
  apply gen_vlist_contains_all.
  rewrite H2. unfold C. pose (h := codeseq_at_app_right _ _ _ _ C0).
  apply codeseq_at_app_left in h. apply h.
  split; assumption.
  rewrite length_initialize_vars in H4. rewrite <- H2 in *.
  simpl. destruct H5. eauto with codeseq.

  eexists. split. unfold mach_terminates.
  + eexists. split. eauto with codeseq.
    eapply star_trans. apply H1.
    normalize2. rewrite length_initialize_vars. rewrite <- H2. apply H4.
  + split; auto.
Qed.


(* and its FINALLY correct! *)
