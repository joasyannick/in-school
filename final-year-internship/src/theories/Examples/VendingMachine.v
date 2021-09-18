(** Here is provided some examples of label-structured modal
    transition systems that model vending machines. They can be
    found in the article _Extending Modal Transition Systems
    with Structured Labels_, by Sebastian S. Bauer, Line Juhl,
    Kim G. Larsen, Axel Legay, and Jiri Srba, and published in
    2012 in the journal _Mathematical Structures in Computer
    Science_, volume 22, pages 581-617. *)


Add LoadPath "..".
Require Import Coq.Classes.RelationClasses.
Require Import LabelSet.


(** There are seven labels. They represent the following events:
    - [VM_drink]: the machine delivers a drink;
    - [VM_coffee]: the machine delivers a coffee;
    - [VM_tea]: the machine delivers a tea;
    - [VM_coin]: the user inserts a coin;
    - [VM_1EUR]: the user inserts 1 EUR;
    - [VM_2EUR]: the user inserts 2 EUR;
    - [VM_bottom]: the least element. *)

Inductive VM_labels : Set :=
    VM_drink | VM_coffee | VM_tea | VM_coin | VM_1EUR | VM_2EUR | VM_bottom.


(** [VM_refines] is the refinement relation, i.e. a partial order,
    on [VM_labels]. [VM_coffee] and [VM_tea] refine [VM_drink],
    and [VM_1EUR] and [VM_2EUR] refine [VM_coin]. [VM_bottom]
    refines all labels. *)

Definition VM_refines (l1 l2 : VM_labels) : Prop :=
    match l1 with
    |   VM_drink => l2 = VM_drink
    |   VM_coffee => l2 = VM_coffee \/ l2 = VM_drink
    |   VM_tea => l2 = VM_tea \/ l2 = VM_drink
    |   VM_coin => l2 = VM_coin
    |   VM_1EUR => l2 = VM_1EUR \/ l2 = VM_coin
    |   VM_2EUR => l2 = VM_2EUR \/ l2 = VM_coin
    |   VM_bottom => True
    end.


(** [VM_refines] is a preoder on [VM_labels]. *)

Lemma VM_refines_PreOrder :
    PreOrder VM_refines.
Proof.
    split.
    - unfold Reflexive.
      intro x ; case x ; simpl ; try left ; reflexivity.
    - unfold Transitive.
      intros x y z Hxy Hyz.
      unfold VM_refines in *; destruct x; destruct y; destruct z; subst; auto; try discriminate; try (destruct Hxy; discriminate).
Qed.


(** The set [VM_labels] of labels is a label-set. *)

Lemma VM_LabelSet :
    LabelSet VM_refines_PreOrder VM_bottom.
Proof.
    split.
    - admit.
    - intro l ; destruct l ; simpl ; apply I.
    - intros l1 H. specialize H with VM_bottom.
    destruct l1 ; unfold VM_refines in H ; auto ; try discriminate ; destruct H ; discriminate.
Qed.