(** Here is provided some examples of label-structured modal
    transition systems for weighted modal automata. They can
    be found in the article _Extending Modal Transition Systems
    with Structured Labels_, by Sebastian S. Bauer, Line Juhl,
    Kim G. Larsen, Axel Legay, and Jiri Srba, and published in
    2012 in the journal _Mathematical Structures in Computer
    Science_, volume 22, pages 581-617. *)


Require Import ZArith.
Require Import Coq.Classes.RelationClasses.
Open Scope Z_scope.


(** A label is either an integer interval or the empty set [WMA_bottom]. *)

Inductive WMA_labels : Set :=
    |   WMA_interval (x : Z) (y : Z) (le_xy : x <= y)
    |   WMA_bottom.


Definition WMA_refines (l1 l2 : WMA_labels) : Prop :=
    match (l1, l2) with
    |   (WMA_interval x1 y1 _, WMA_interval x2 y2 _) => x2 <= x1 /\ y1 <= y2
    |   (WMA_bottom, _) => True
    |   _ => False
    end.


Lemma WMA_refines_PreOrder :
    PreOrder WMA_refines.
Proof.
    split.
    - unfold Reflexive.
      intro x ; case x ; simpl.
      unfold WMA_refines.
      intros.
      split ; omega.
      unfold WMA_refines.
      auto.
    - unfold Transitive.
      intros.
      destruct x ; destruct y ; destruct z ; unfold WMA_refines in * ; auto ; split ; omega.
Qed.

Close Scope Z_scope.

