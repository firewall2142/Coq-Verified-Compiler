(** This file contains results about 
[find], [codeseq_at], [code_at], [get_nth_slot] and [set_nth_slot]*)

From Coq Require Export Strings.String.
From Coq Require Export Arith.Arith.
From Coq Require Export Lists.List.
From Coq Require Export Bool.Bool.
Require Import Omega.
From StorelessMachine Require Import Maps.
From StorelessMachine Require Import Imp.

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

Hint Resolve code_at_app codeseq_at_head codeseq_at_tail codeseq_at_app_left
     codeseq_at_app_right codeseq_at_app_right2 Nat.add_0_r Nat.add_1_r
     Nat.add_assoc Nat.add_comm :codeseq.



Fact find_success_list_length:
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



Theorem find_get_ofs: forall (i:id) vlist n stk,
    length stk >= length vlist ->
    find i vlist = Some n ->
    exists m,
      get_nth_slot stk (length stk - length vlist + n) = Some m.
Proof.
  intros.
  apply find_success_list_length in H0.
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







