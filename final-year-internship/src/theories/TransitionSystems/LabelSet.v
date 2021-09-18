(** This library provides an implementation of the notion of
    _label-set_, defined in the article _Extending Modal Transition
    Systems with Structured Labels_ by Sebastian S. Bauer,
    Line Juhl, Kim G. Larsen, Axel Legay, and Jiri Srba, and
    published in 2012 in the journal _Mathematical Structures in
    Computer Science_, volume 22, pages 581-617. *)


Add LoadPath ".." as LSMTS.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Import LSMTS.Sets.NaiveSet.
Require Import LSMTS.Classes.DecidableRelation.
Require Import LSMTS.Classes.Order.
Require Import LSMTS.Classes.DecidableOrder.


(****************************)
(** * Well-Formed Label-Set *)
(****************************)


(** A _label-set_ consists of: (1) a set [label] of _labels_,
    (2) a partial order [precedes] on [label]; and (3) a
    least label [bottom]. *)

Class LSet_LabelSet
    {label : Type}
    (precedes : relation label)
    (bottom : label)
    : Type
    :=
        LSet_buildLabelSet {

(** There is a getter for each parameter. *)

            LSet_label := label;
            LSet_precedes := precedes;
            LSet_bottom := bottom;

(** The field [LSet_QuasiOrder] is the proof that [precedes] is a
    quasi-order on [labels]. *)

            LSet_QuasiOrder : QO_QuasiOrder precedes;

(** *)

            LSet_Decidable : QO_Decidable LSet_QuasiOrder;

(** The predicate [LSet_eq] defines the equality of two labels. *)

            LSet_eq : relation label := QO_eq LSet_QuasiOrder;

(** *)

            LSet_eq_Decidable : DRel_Decidable LSet_eq := QO_eq_Decidable LSet_Decidable;

(** The method [LSet_Equivalence] returns the proof that [LSet_eq]
    is an equivalence relation on [labels]. *)

            LSet_Equivalence : Equivalence LSet_eq := QO_Equivalence LSet_QuasiOrder;

(** The method [LSet_PartialOrder] returns the proof that [precedes]
    is a partial order on [labels], i.e. it is an antisymmetric
    preorder with respect to the equivalence relation [LSet_eq]. *)

            LSet_PartialOrder : PO_PartialOrder LSet_eq precedes := QO_PartialOrder LSet_QuasiOrder;

(** The field [LSet_bottom_least] is the proof that [bottom] is the
    least label. *)

            LSet_bottom_least : PO_least LSet_PartialOrder (Nv_full label) bottom;

(** *)

            LSet_bottom_uniqueness := PO_uniqueness_of_least LSet_PartialOrder (Nv_full label);

(** The predicate [LSet_Implementation] defines the set of
    _implementation labels_. The implementation labels are the direct
    successors of [bottom]. *)

            LSet_Implementation : Nv_naiveSet label :=
                fun (i : label) => ~(LSet_eq i bottom) /\
                    (forall l : label,  ~(LSet_eq l bottom) -> precedes l i -> LSet_eq l i);

(** Given a label [l], the method [Lset_PrecedingImplementations]
    returns the set of implementation labels that precedes [l]. *)

            LSet_PrecedingImplementations (l : label) : Nv_naiveSet label :=
                fun (i : label) => precedes i l /\ LSet_Implementation i
        }.


(** The fields [LSet_PreOrder] and [Lset_bottom_least] are the only
    arguments needed explicitly to build a label-set. *)

Arguments LSet_buildLabelSet {_ _ _ _} _ _.


(** We prefer to have the label-set explicit in every method. *)

Arguments LSet_label {_ _ _} _.
Arguments LSet_precedes {_ _ _} _ _ _.
Arguments LSet_bottom {_ _ _} _.
Arguments LSet_QuasiOrder {_ _ _} _.
Arguments LSet_Decidable {_ _ _} _.
Arguments LSet_eq {_ _ _} _ _ _.
Arguments LSet_eq_Decidable {_ _ _} _.
Arguments LSet_Equivalence {_ _ _} _.
Arguments LSet_PartialOrder {_ _ _} _ _ _.
Arguments LSet_bottom_least {_ _ _} _.
Arguments LSet_bottom_uniqueness {_ _ _} _ _ _ _ _.
Arguments LSet_Implementation {_ _ _} _ _.
Arguments LSet_PrecedingImplementations {_ _ _} _ _ _.


(** The three parameters can be automatically generated and declared
    implicit with [`(..)] or [`{..}]. *)

Generalizable Variables label precedes bottom.


(** A label-set can be interpreted as a partially ordered set. *)

Coercion LSet_PartialOrder : LSet_LabelSet >-> PO_PartialOrder.


(** Some notations. *)

Notation "l1 ≼ l2  '[LSet'  L ']'" := (LSet_precedes L l1 l2) (at level 70, no associativity).
Notation "l1 == l2  '[LSet'  L ']'" := (LSet_eq L l1 l2) (at level 70, no associativity).
Notation "l1 <> l2  '[LSet'  L ']'" := (~(LSet_eq L l1 l2)) (at level 70, no associativity).


(** *)

Definition LSet_lift
    `(L : LSet_LabelSet)
    (E1 E2 : Nv_naiveSet L)
    :=
        forall e1, e1 ∈ E1 -> exists e2, e2 ∈ E2 /\ e1 ≼ e2 [LSet L].

Notation "E1 ≼ E2  '[Set'  L ']'" := (LSet_lift L E1 E2) (at level 70, no associativity).

(* Demontrer l'instanciation de quasi-order *)

(** This one comes from the article. *)

Notation "〚 l 〛" := (LSet_PrecedingImplementations _ l) (at level 35, right associativity).


(** A label-set [L] is well-formed if and only if every label, except
    [LSet_bottom L], has an implementation label among its
    predecessors. *)

Class LSet_WellFormed
    `(L : LSet_LabelSet)
    : Prop
    :=
        LSet_buildWellFormed {

(** The getter [LSet_WellFormed_LabelSet] returns the proof that
    [L] is a label-set *)

            LSet_WellFormed_LabelSet := L;

(** The field [LSet_WellFormed_intro] is the proof of well-formedness. *)

            LSet_WellFormed_intro :
                forall l : L, l <> LSet_bottom L [LSet _] ->
                    exists i : L, i ∈ 〚l〛
    }.


(** The parameter [L] and the field [LSet_WellFormed_intro] are the
    only explicit arguments needed to build a transition. *)

Arguments LSet_buildWellFormed {_ _ _} _ _.


(** We prefer to have the well-formed label-set explicit in every
    method. *)

Arguments LSet_WellFormed_LabelSet {_ _ _ _} _.
Arguments LSet_WellFormed_intro {_ _ _ _} _ _ _.


(** The parameter [L] can be automatically generated and declared
    implicit with [`(..)] or [`{..}]. *)

Generalizable Variables L.


(** A well-formed label-set can be interpreted as a label-set. *)

Coercion LSet_WellFormed_LabelSet : LSet_WellFormed >-> LSet_LabelSet.


(****************************)
(** * Product of Label-Sets *)
(****************************)


(** The set of labels that results from the product of two label-sets
    [L1] and [L2], contains a special element [LSet_bottomPair] (the
    least product label), and ordered pairs [(l1, l2)] such that
    [l1 <> bottom1] and [l2 <> bottom2]. *)

Inductive LSet_prod
    `(L1 : LSet_LabelSet)
    `(L2 : LSet_LabelSet)
    : Type
    :=
        |   LSet_bottomPair : LSet_prod L1 L2
        |   LSet_pair :
                forall (l1 : L1) (l2 : L2),
                    (l1 <> LSet_bottom L1 [LSet _]) -> l2 <> LSet_bottom L2 [LSet _] -> LSet_prod L1 L2.

Arguments LSet_bottomPair {_ _ _ _ _ _ _ _}.
Arguments LSet_pair {_ _ _ _ _ _ _ _} _ _ _ _.


(** The observer [LSet_isBottomPair] indicates whether a term of type
    [LSet_prod] has been built with the constructor [LSet_bottomPair]. *)

Definition LSet_isBottomPair
    `{L1 : LSet_LabelSet}
    `{L2 : LSet_LabelSet}
    (p : LSet_prod L1 L2)
    : Prop
    :=
        match p with
        |   LSet_bottomPair => True
        |   LSet_pair _ _ _ _ => False
        end.

Arguments LSet_isBottomPair {_ _ _ _ _ _ _ _} _.


(** The observer [LSet_isPair] indicates whether a term of type
    [LSet_prod] has been built with the constructor [LSet_pair]. *)

Definition LSet_isPair
    `{L1 : LSet_LabelSet}
    `{L2 : LSet_LabelSet}
    (p : LSet_prod L1 L2)
    : Prop
    :=
        match p with
        |   LSet_bottomPair => False
        |   LSet_pair _ _ _ _ => True
        end.

Arguments LSet_isPair {_ _ _ _ _ _ _ _} _ .


(** The getter [LSet_fst] returns the first label of an ordered pair
    of labels. *)

Definition LSet_fst
    `{L1 : LSet_LabelSet}
    `{L2 : LSet_LabelSet}
    {p : LSet_prod L1 L2}
    (isPair : LSet_isPair p)
    : LSet_label L1
    :=
        match p return LSet_isPair p -> LSet_label L1 with
        |   LSet_bottomPair => fun pre : False => match pre with end
        |   LSet_pair l1 _ _ _  => fun _ => l1
        end isPair.

Arguments LSet_fst {_ _ _ _ _ _ _ _ _} _.


(** The getter [LSet_snd] returns the second label of an ordered pair
    of labels. *)

Definition LSet_snd
    `{L1 : LSet_LabelSet}
    `{L2 : LSet_LabelSet}
    {p : LSet_prod L1 L2}
    (isPair : LSet_isPair p)
    : LSet_label L2
    :=
        match p return LSet_isPair p -> LSet_label L2 with
        |   LSet_bottomPair => fun pre : False => match pre with end
        |   LSet_pair _ l2 _ _  => fun _ => l2
        end isPair.

Arguments LSet_snd {_ _ _ _ _ _ _ _ _} _.


(** The function [LSet_toPair] converts a product label into an
    ordinary ordered pair. *)

Definition LSet_toPair
    `{L1 : LSet_LabelSet}
    `{L2 : LSet_LabelSet}
    (p : LSet_prod L1 L2)
    : L1 * L2
    :=
        match p with
        |   LSet_bottomPair => (LSet_bottom L1, LSet_bottom L2)
        |   LSet_pair l1 l2 _ _ => (l1, l2)
        end.

Arguments LSet_toPair {_ _ _ _ _ _ _ _} _.


(** The function [LSet_prodSet] converts a set of ordinary ordered
    pairs into a set of product labels. *)

Definition LSet_prodSet
    `{L1 : LSet_LabelSet}
    `{L2 : LSet_LabelSet}
    (P : Nv_naiveSet (L1 * L2))
    : Nv_naiveSet (LSet_prod L1 L2)
    :=
        fun (p : LSet_prod L1 L2) => (LSet_toPair p) ∈ P.

Arguments LSet_prodSet {_ _ _ _ _ _ _ _} _ _.


(** The partial order [LSet_prodOrder] on the product of two label-sets
    is such that [LSet_bottomPair] is the least element, and [(l1, l2)]
    precedes [(l1', l2')] if and only if [l1] precedes [l1'] and [l2]
    precedes [l2']. *)

Definition LSet_prodOrder
    `(L1 : LSet_LabelSet)
    `(L2 : LSet_LabelSet)
    (p1 : LSet_prod L1 L2)
    (p2 : LSet_prod L1 L2)
    : Prop
    :=
        match (p1, p2) with
        |   (LSet_bottomPair, _) => True
        |   (LSet_pair l1 l2 _ _, LSet_pair l1' l2' _ _) =>
                l1 ≼ l1' [LSet L1] /\ l2 ≼ l2' [LSet L2]
        |   _ => False
        end.

Arguments LSet_prodOrder {_ _ _} _ {_ _ _} _ _ _.


(** *)

Instance LSet_prodOrder_Decidable
    `(L1 : LSet_LabelSet)
    `(L2 : LSet_LabelSet)
    : DRel_Decidable (LSet_prodOrder L1 L2).
(* begin hide *)
Proof.
    split.
    intros p1 p2.
    destruct p1 as [ | p1l1 p1l2 p1l1_not_bottom p1l2_not_bottom],
        p2 as [ | p2l1 p2l2 p2l1_not_bottom p2l2_not_bottom].
    now left.
    now left.
    now right.
    elim (DRel_decidable (QO_decidable (LSet_Decidable L1)) p1l1 p2l1).
    -   elim (DRel_decidable (QO_decidable (LSet_Decidable L2)) p1l2 p2l2).
        left; now split.
        right; intro p1_precedes_p2; now destruct p1_precedes_p2.
    -   right; intro p1_precedes_p2; now destruct p1_precedes_p2.
Defined.
(* end hide *)


(** The relation [LSet_prodOrder] is a quasi-order on [LSet_prod L1 L2]. *)

Instance LSet_prod_QuasiOrdered
    `(L1 : LSet_LabelSet)
    `(L2 : LSet_LabelSet)
    : QO_QuasiOrder (LSet_prodOrder L1 L2).
(* begin hide *)
Proof.
    split.
    -   intro p.
        destruct p as [ | l1 l2 l1_not_bottom l2_not_bottom].
        now apply I.
        split.
        now apply (reflexivity (Reflexive := QO_Reflexive L1)).
        now apply (reflexivity (Reflexive := QO_Reflexive L2)).
    -   intros p1 p2 p3 p1_precedes_p2 p2_precedes_p3.
        destruct p1 as [ | p1l1 p1l2 p1l1_not_bottom p1l2_not_bottom],
            p2 as [ | p2l1 p2l2 p2l1_not_bottom p2l2_not_bottom],
            p3 as [ | p3l1 p3l2 p3l1_not_bottom p3l2_not_bottom];
        try assumption;
        destruct p1_precedes_p2, p2_precedes_p3.
        split.
        now apply (transitivity (Transitive := (QO_Transitive L1)) (y := p2l1)).
        now apply (transitivity (Transitive := (QO_Transitive L2)) (y := p2l2)).
Qed.
(* end hide *)


(** *)

Instance LSet_prod_Decidable
    `(L1 : LSet_LabelSet)
    `(L2 : LSet_LabelSet)
    : QO_Decidable (LSet_prod_QuasiOrdered L1 L2).
(* begin hide *)
Proof.
    split.
    now apply LSet_prodOrder_Decidable.
Qed.
(* end hide *)


(** The product [LSet_prod L1 L2] together with the relation
    [LSet_prodOrder] and the least label [LSet_bottomPair] is a
    label-set. *)

Program Instance LSet_prod_LabelSet
    `(L1 : LSet_LabelSet)
    `(L2 : LSet_LabelSet)
    : LSet_LabelSet (LSet_prodOrder L1 L2) LSet_bottomPair
    :=
        LSet_buildLabelSet (LSet_prod_Decidable L1 L2) _.
(* begin hide *)
Next Obligation.
    now unfold LSet_prodOrder.
Qed.
(* end hide *)


(** Here is the notation used in the article for the product of
    label-sets. *)

Notation "L1 ⊗ L2" := (LSet_prod_LabelSet L1 L2) (at level 40, left associativity).


(** Equality of product labels. *)

Lemma LSet_pair_equality
    `(L1 : LSet_LabelSet)
    `(L2 : LSet_LabelSet)
    : forall (l1 l1' : L1) (l2 l2' : L2),
          l1 == l1' [LSet L1] -> l2 == l2' [LSet L2] ->
              forall l1nb l2nb l1'nb l2'nb,
                  (LSet_pair l1 l2 l1nb l2nb) == (LSet_pair l1' l2' l1'nb l2'nb) [LSet L1 ⊗ L2].
(* begin hide *)
Proof.
    intros l1 l1' l2 l2' l1_eq_l1' l2_eq_l2' l1_not_bottom l2_not_bottom
        l1'_not_bottom l2'_not_bottom.
    destruct l1_eq_l1' as [l1_precedes_l1' l1'_precedes_l1],
        l2_eq_l2' as [l2_precedes_l2' l2'_precedes_l2].
    split;
    now split.
Qed.
(* end hide *)


Lemma LSet_pair_equality_converse
    `(L1 : LSet_LabelSet)
    `(L2 : LSet_LabelSet)
    : forall (l1 l1' : L1) (l2 l2' : L2) l1nb l2nb l1'nb l2'nb,
          (LSet_pair l1 l2 l1nb l2nb) == (LSet_pair l1' l2' l1'nb l2'nb) [LSet L1 ⊗ L2] ->
              l1 == l1' [LSet L1] /\ l2 == l2' [LSet L2].
(* begin hide *)
Proof.
    intros l1 l1' l2 l2' l1_not_bottom l1'_not_bottom
        l2_not_bottom l2'_not_bottom l1_l2_eq_l1'_l2'.
    destruct l1_l2_eq_l1'_l2' as [[l1_precedes_l1' l2_precedes_l2'] [l1'_precedes_l1 l2'_precedes_l2]].
    split;
    now split.
Qed.
(* end hide *)  


(** Substitutions. *)

Lemma LSet_prodOrder_substl
    `(L1 : LSet_LabelSet)
    `(L2 : LSet_LabelSet)
    : forall (p1 p1' p2 : L1 ⊗ L2),
          p1 == p1' [LSet _] -> (p1 ≼ p2 [LSet _] <-> p1' ≼ p2 [LSet _]).
(* begin hide *)
Proof.
    intros p1 p1' p2 p1_eq_p1'.
    destruct p1_eq_p1' as [p1_precedes_p1' p1'_precedes_p1].
    split.
    now intro p1_precedes_p2; transitivity p1.
    now intro p1'_precedes_p2; transitivity p1'.
Qed.
(* end hide *)


Lemma LSet_prodOrder_substr
    `(L1 : LSet_LabelSet)
    `(L2 : LSet_LabelSet)
    : forall (p1 p2 p2' : L1 ⊗ L2),
          p2 == p2' [LSet _] -> (p1 ≼ p2 [LSet _] <-> p1 ≼ p2' [LSet _]).
(* begin hide *)
Proof.
    intros p1 p2 p2' p2_eq_p2'.
    destruct p2_eq_p2' as [p2_precedes_p2' p2'_precedes_p2].
    split.
    now intro p1_precedes_p2; transitivity p2.
    now intro p1_precedes_p2'; transitivity p2'.
Qed.
(* end hide *)


(** If [W1] and [W2] are two well-formed label-set, then so is their
    product [L1 ⊗ L2]. *)

Instance LSet_prod_WellFormed
    `(W1 : LSet_WellFormed)
    `(W2 : LSet_WellFormed)
    : LSet_WellFormed (W1 ⊗ W2).
(* begin hide *)
Proof.
    split.
    intros p p_not_bottomPair.
    destruct p as [ | l1 l2 l1_not_bottom l2_not_bottom].
    now exfalso; now apply p_not_bottomPair.
    assert (exists i1 : W1, i1 ∈ 〚l1〛) as exists_i1.
    now apply (LSet_WellFormed_intro W1 l1 l1_not_bottom).
    assert (exists i2 : W2, i2 ∈ 〚l2〛) as exists_i2.
    now apply (LSet_WellFormed_intro W2 l2 l2_not_bottom).
    destruct exists_i1 as [i1 i1_implementation], exists_i2 as [i2 i2_implementation].
    destruct i1_implementation as [i1_precedes_l1 i1_implementation],
        i2_implementation as [i2_precedes_l2 i2_implementation].
    destruct i1_implementation as [i1_not_bottom i1_after_bottom],
        i2_implementation as [i2_not_bottom i2_after_bottom].
    exists (LSet_pair i1 i2 i1_not_bottom i2_not_bottom).
    split.
    now split.
    split.
    now trivial.
    intro p'.
    destruct p' as [ | l1' l2' l1'_not_bottom l2'_not_bottom].
    now intro absurdum; exfalso; now apply absurdum.
    intros l1'_l2'_not_bottomPair l1'_precedes_i1_l2'_i2.
    destruct l1'_precedes_i1_l2'_i2 as [l1'_precedes_i1 l2'_precedes_i2].
    split; split; try assumption.
    now elim (i1_after_bottom l1' l1'_not_bottom l1'_precedes_i1); now trivial.
    now elim (i2_after_bottom l2' l2'_not_bottom l2'_precedes_i2); now trivial.
Qed.
(* end hide *)


(** Given two label-sets [L1] and [L2], the elements in the cartesian
    product of [LSet_Implementation L1] and [LSet_Implementation L2]
    are exactly the implementation labels of the product of [L1] and
    [L2]. *)


Lemma LSet_prod_Implementation
    `(L1 : LSet_LabelSet)
    `(L2 : LSet_LabelSet)
    : (LSet_Implementation (L1 ⊗ L2)) ==
          (LSet_prodSet ((LSet_Implementation L1) × (LSet_Implementation L2))) [Nv].
(* begin hide *)
Proof.
    split; intros p p_implementation.
    -   destruct p as [ | l1 l2 l1_not_bottom l2_not_bottom].
        now destruct p_implementation as [absurdum _]; exfalso; now apply absurdum.
        split.
        +   split; try assumption.
            destruct p_implementation as [l1_l2_not_bottomPair l1_l2_after_bottomPair].
            intros l l_not_bottom l_precedes_l1.
            generalize (l1_l2_after_bottomPair (LSet_pair l l2 l_not_bottom l2_not_bottom)).
            intro maybe_l_l2_eq_l1_l2.
            assert (l_l2_eq_l1_l2 : LSet_eq (L1 ⊗ L2)
                (LSet_pair l l2 l_not_bottom l2_not_bottom)
                (LSet_pair l1 l2 l1_not_bottom l2_not_bottom)).
            apply maybe_l_l2_eq_l1_l2; try now trivial.
            split; try now trivial.
            apply (reflexivity (Reflexive := (QO_Reflexive L2))).
            clear maybe_l_l2_eq_l1_l2.
            clear l1_l2_after_bottomPair.
            destruct l_l2_eq_l1_l2 as [_ l1_l2_precedes_l_l2].
            destruct l1_l2_precedes_l_l2 as [l1_precedes_l _].
            now split.
        +   split; try assumption.
            destruct p_implementation as [l1_l2_not_bottomPair l1_l2_after_bottomPair].
            intros l l_not_bottom l_precedes_l2.
            generalize (l1_l2_after_bottomPair (LSet_pair l1 l l1_not_bottom l_not_bottom)).
            intro maybe_l1_l_eq_l1_l2.
            assert (l1_l_eq_l1_l2 : LSet_eq (L1 ⊗ L2)
                (LSet_pair l1 l l1_not_bottom l_not_bottom)
                (LSet_pair l1 l2 l1_not_bottom l2_not_bottom)).
            apply maybe_l1_l_eq_l1_l2; try now trivial.
            split.
            apply (reflexivity (Reflexive := (QO_Reflexive L1))).
            assumption.
            clear maybe_l1_l_eq_l1_l2.
            clear l1_l2_after_bottomPair.
            destruct l1_l_eq_l1_l2 as [_ l1_l2_precedes_l1_l].
            destruct l1_l2_precedes_l1_l as [_ l2_precedes_l].
            now split.
    -   destruct p as [ | l1 l2 l1_not_bottom l2_not_bottom];
        inversion p_implementation as [i1 i2 implementation1 implementation2];
        clear i1 i2 H0 H1.
        +   split.
            destruct implementation1 as [absurdum _].
            now intro; now apply absurdum.
            intros p p_not_bottomPair p_precedes_bottomPair.
            split; try assumption.
            apply (LSet_bottom_least (L1 ⊗ L2)).
            apply Nv_full_intro.
        +   split.
            now intro absurdum; destruct absurdum as [absurdum _]; destruct absurdum.
            intros p' p'_not_bottomPair p'_precedes_l1_l2.
            destruct p' as [ | l1' l2' l1'_not_bottom l2'_not_bottom];
            unfold LSet_eq;
            unfold QO_eq;
            unfold QO_precedes in *;
            unfold LSet_prodOrder in *.
            split.
            now trivial.
            now destruct p'_not_bottomPair.
            destruct p'_precedes_l1_l2 as [l1'_precedes_l1 l2'_precedes_l2].
            destruct implementation1 as [_ l1_after_bottom].
            destruct implementation2 as [_ l2_after_bottom].
            generalize (l1_after_bottom l1' l1'_not_bottom l1'_precedes_l1).
            intro l1'_eq_l1.
            clear l1_after_bottom.
            generalize (l2_after_bottom l2' l2'_not_bottom l2'_precedes_l2).
            intro l2'_eq_l2.
            clear l2_after_bottom.
            destruct l1'_eq_l1 as [_ l1_precedes_l1'].
            destruct l2'_eq_l2 as [_ l2_precedes_l2'].
            now split; split.
Qed.
(* end hide *)