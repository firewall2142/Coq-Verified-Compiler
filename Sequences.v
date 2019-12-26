(** A library of relation operators defining sequences of transitions
  and useful properties about them. *)

Set Implicit Arguments.

Section SEQUENCES.

Variable A: Type.                 (**r the type of states *)
Variable R: A -> A -> Prop.       (**r the transition relation, from one state to the next *)

(** ** Finite sequences of transitions *)

(** Zero, one or several transitions: reflexive, transitive closure of [R]. *)

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

End SEQUENCES.  


