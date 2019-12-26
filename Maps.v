From Coq Require Export Strings.String.
From Coq Require Export Arith.Arith.
From Coq Require Export Lists.List.
From Coq Require Export Bool.Bool.

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

Fact string_dec_refl:
  forall x, (if string_dec x x then true else false) = true.
Proof.
  intros. destruct string_dec; auto.
Qed.
