Set Implicit Arguments.

Require Export Arith.Arith.

Section SEQUENCES.

Variable A: Type. (* the type of states *)
Variable R: A -> A -> Prop. (* the transition relation, from one state to the next *)


Inductive star: A -> A -> Prop :=
  | star_refl: forall a,
      star a a
  | star_step: forall a b c,
      R a b -> star b c -> star a c.

Lemma star_one:
  forall (a b: A), R a b -> star a b.
Proof.
  eauto using star.
Qed.

Lemma star_trans:
  forall (a b: A), star a b -> forall c, star b c -> star a c.
Proof.
  induction 1; eauto using star.
Qed.


Inductive plus: A -> A -> Prop :=
  | plus_left: forall a b c,
      R a b -> star b c -> plus a c.

Lemma plus_one:
  forall a b, R a b -> plus a b.
Proof.
  eauto using star, plus.
Qed.

Lemma plus_star:
  forall a b,
  plus a b -> star a b.
Proof.
  intros. inversion H. eauto using star.
Qed.

Lemma plus_star_trans:
  forall a b c, plus a b -> star b c -> plus a c.
Proof.
  intros. inversion H. eauto using plus, star_trans.
Qed.

Lemma star_plus_trans:
  forall a b c, star a b -> plus b c -> plus a c.
Proof.
  intros. inversion H0. inversion H; eauto using plus, star, star_trans.
Qed.

Lemma plus_right:
  forall a b c, star a b -> R b c -> plus a c.
Proof.
  eauto using star_plus_trans, plus_one.
Qed.

Definition all_seq_inf (a: A) : Prop :=
  forall b, star a b -> exists c, R b c.


Search "add".

Hint Resolve star_one star_trans Nat.add_comm Nat.add_assoc Nat.add_1_r : star_hints.

End SEQUENCES.
