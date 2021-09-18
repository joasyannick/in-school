(** This library is about quasi-orders, also known as _preorders_,
    strict orders, and partial orders. *)


Add LoadPath ".." as LSMTS.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Setoids.Setoid.
Require Import LSMTS.Sets.NaiveSet.


(*****************************************)
(** * Quasi-, Strict, and Partial Orders *)
(*****************************************)


(** The standard library already has an implementation for preorders.
    Nevertheless, some people like to call them _quasi-orders_. *)

Notation QO_QuasiOrder := PreOrder.
Notation QO_buildQuasiOrder := Build_PreOrder.
Notation QO_Reflexive := PreOrder_Reflexive.
Notation QO_Transitive := PreOrder_Transitive.


(** A _quasi-ordered set_ consists of: (1) a set [set], and (2) a
    relation [precedes] on [set] that is reflexive and transitive.
    The components [set] and [precedes] are given as parameters—[set]
    being implicit—and are accessible with the getters [QO_set] and
    [QO_precedes]. *)

Definition QO_set
    {set : Type}
    {precedes : relation set}
    (Q : QO_QuasiOrder precedes)
    :=
        set.

Definition QO_precedes
    {set : Type}
    {precedes : relation set}
    (Q : QO_QuasiOrder precedes)
    :=
        precedes.

Notation "x ≼ y  '[QO'  Q ']'" := (QO_precedes Q x y) (at level 70, no associativity).


(** A quasi-ordered set can be interpreted as a set. *)

Coercion QO_set : QO_QuasiOrder >-> Sortclass.


(** The proofs [QO_Reflexive] and [QO_Transitive] of reflexivity and
    transitivity, respectively, are the only arguments needed
    explicitly to build a quasi-order. *)
    
Arguments QO_buildQuasiOrder {_ _} _ _.


(** We prefer to have the quasi-order explicit in every method. *)

Arguments QO_Reflexive {_ _} _ _.
Arguments QO_Transitive {_ _} _ _ _ _ _ _.


(** Given a quasi-ordered set [Q], and two objects [x y : Q],
    [x] is said to precede _strictly_ [y], written [x ≺ y], if and
    only if [x ≼ y] but [~(y ≼ x)]. *)

Definition QO_strictlyPrecedes
    `(Q : PreOrder)
    : relation Q
    :=
        fun x y : Q => x ≼ y [QO Q] /\ ~(y ≼ x [QO Q]).

Notation "x ≺ y  '[QO'  Q ']'" := (QO_strictlyPrecedes Q x y) (at level 70, no associativity).


(** The standard library also has an implementation for strict orders. *)

Notation SO_StrictOrder := StrictOrder.
Notation SO_buildStrictOrder := Build_StrictOrder.
Notation SO_Irreflexive := StrictOrder_Irreflexive.
Notation SO_Transitive := StrictOrder_Transitive.


(** A _strict order_ is irreflexive and transitive. Two getters,
    [SO_set] and [SO_precedes], are available. They respectively return
    the set on which the strict order is defined, and the relation
    thereon. *)

Definition SO_set
    {set : Type}
    {precedes : relation set}
    (S : SO_StrictOrder precedes)
    :=
        set.

Definition SO_precedes
    {set : Type}
    {precedes : relation set}
    (S : SO_StrictOrder precedes)
    :=
        precedes.

Notation "x ≺ y  '[SO'  S ']'" := (SO_precedes S x y) (at level 70, no associativity).


(** A strictly ordered set can be interpreted as a set. *)

Coercion SO_set : SO_StrictOrder >-> Sortclass.


(** The proofs [SO_Irreflexive] and [SO_Transitive] of irreflexivity
    and transitivity, respectively, are the only arguments needed
    explicitly to build a strict order. *)
    
Arguments SO_buildStrictOrder {_ _} _ _.


(** We prefer to have the strict order explicit in every method. *)

Arguments SO_Irreflexive {_ _} _ _ _.
Arguments SO_Transitive {_ _} _ _ _ _ _ _.


(** The relation [QO_strictlyPrecedes] is a strict order. *)

Instance QO_StrictOrder
    `(Q : PreOrder)
    : SO_StrictOrder (QO_strictlyPrecedes Q).
(* begin hide *)
Proof.
    split.
    -   unfold Irreflexive.
        unfold Reflexive, complement.
        unfold QO_strictlyPrecedes.
        intros x x_strictly_precedes_x.
        destruct x_strictly_precedes_x as [x_precedes_x x_not_precedes_x].
        now apply x_not_precedes_x.
    -   unfold Transitive.
        intros x y z x_strictly_precedes_y y_strictly_precedes_z.
        destruct x_strictly_precedes_y as [x_precedes_y y_not_precedes_x],
            y_strictly_precedes_z as [y_precedes_z z_not_precedes_y].
        split.
        now transitivity y.
        intro z_precedes_x.
        assert (inconsistency : y ≼ x [QO Q]).
        now transitivity z.
        now apply y_not_precedes_x.
Qed.
(* end hide *)


(** The _reflexive closure_ of a strict order [≺] is the relation [≼]
    such that [x ≼ y] if and only if [x ≺ y] or [x = y]. Since [x = x],
    [x ≼ x]; so, reflexivity is enforced. *)

Definition SO_reflexiveClosure
    `(S : StrictOrder)
    : relation S
    :=
        fun x y : S => x ≺ y [SO S] \/ x = y.


(** The reflexive closure is a quasi-order. *)

Instance SO_QuasiOrder
    `(S : StrictOrder)
    : QO_QuasiOrder (SO_reflexiveClosure S).
(* begin hide *)
Proof.
    split.
    -   intro x.
        unfold SO_reflexiveClosure.
        right.
        reflexivity.
    -   intros x y z x_precedes_y y_precedes_z.
        unfold SO_reflexiveClosure in *.
        destruct x_precedes_y as [x_strictly_precedes_y | x_eq_y],
            y_precedes_z as [y_strictly_precedes_z | y_eq_z].
        +   left.
            now transitivity y.
        +   rewrite <- y_eq_z.
            now left.
        +   rewrite x_eq_y.
            now left.
        +   rewrite <- y_eq_z.
            now right.
Qed.
(* end hide *)


(** The standard library provides an implementation for partial orders. *)

Notation PO_PartialOrder := PartialOrder.
Notation PO_PartialOrder_intro := partial_order_equivalence.


(** The class [PO_PartialOrder] has five parameters: [set], [eq], [Eq],
    [precedes], and [Q]. As usal, [set] is the set on which the
    relation [precedes] is defined. [Q] is the proof that [precedes]
    is a reflexive and transitive quasi-order on [set]. To be a _partial
    order_, [precedes] must be additionally antisymmetric with respect
    to an equivalence relation [eq]. The component [Eq] proves that
    [eq] is indeed an equivalence relation. Here are the getters to
    access these five components. *)

Definition PO_set
    {set : Type}
    {eq : relation set}
    {Eq : Equivalence eq}
    {precedes : relation set}
    {Q : QO_QuasiOrder precedes}
    (P : PO_PartialOrder eq precedes)
    :=
        set.

Definition PO_eq
    {set : Type}
    {eq : relation set}
    {Eq : Equivalence eq}
    {precedes : relation set}
    {Q : QO_QuasiOrder precedes}
    (P : PO_PartialOrder eq precedes)
    :=
        eq.

Notation "x == y  '[PO'  P ']'" := (PO_eq P x y) (at level 70, no associativity).
Notation "x <> y  '[PO'  P ']'" := (~(PO_eq P x y)) (at level 70, no associativity).

Definition PO_Equivalence
    {set : Type}
    {eq : relation set}
    {Eq : Equivalence eq}
    {precedes : relation set}
    {Q : QO_QuasiOrder precedes}
    (P : PO_PartialOrder eq precedes)
    :=
        Eq.

Definition PO_precedes
    {set : Type}
    {eq : relation set}
    {Eq : Equivalence eq}
    {precedes : relation set}
    {Q : QO_QuasiOrder precedes}
    (P : PO_PartialOrder eq precedes)
    :=
        precedes.

Notation "x ≼ y  '[PO'  P ']'" := (PO_precedes P x y) (at level 70, no associativity).
 
Definition PO_QuasiOrder
    {set : Type}
    {eq : relation set}
    {Eq : Equivalence eq}
    {precedes : relation set}
    {Q : QO_QuasiOrder precedes}
    (P : PO_PartialOrder eq precedes)
    :=
        Q.


(** A partially ordered set can be interpreted as a quasi-ordered set. *)

Coercion PO_QuasiOrder : PO_PartialOrder >-> QO_QuasiOrder.


(** A partial order is reflexive, antisymmetric, and transitive. *)

Instance PO_Reflexive
    `(P : PartialOrder)
    : Reflexive (PO_precedes P).
(* begin hide *)
Proof.
    apply (QO_Reflexive (PO_QuasiOrder P)).
Qed.
(* end hide *)

Instance PO_Transitive
    `(P : PartialOrder)
    : Transitive (PO_precedes P).
(* begin hide *)
Proof.
    apply (QO_Transitive (PO_QuasiOrder P)).
Qed.
(* end hide *)

Notation PO_Antisymmetric := partial_order_antisym.


(** Two objects [x] and [y] of a partially ordered set are _comparable_
    if and only if [x ≼ y] or [y ≼ x]. *)

Definition PO_comparable
    `(P : PartialOrder)
    : relation P
    :=
        fun x y : P => x ≼ y [PO P] \/ y ≼ x [PO P].


(** Let [P] be a partially ordered set, and [S ⊆ P] a subset of [P].
    An object [x ∈ S] is the _unique_ element of [S] if and only if
    every element of [S] is equivalent to [x]. *)

Definition PO_unique
    `(P : PartialOrder)
    (S : Nv_naiveSet P)
    (x : P)
    : Prop
    :=
        x ∈ S /\ (forall x' : P, x' ∈ S -> x' == x [PO P]).


(** A subset [S] of a partially ordered set [P] satisfies the
    uniqueness property if and only if all its elements are
    equivalent. *)

Definition PO_uniqueness
    `(P : PartialOrder)
    (S : Nv_naiveSet P)
    : Prop
    :=
        forall x y : P, x ∈ S-> y ∈ S -> x == y [PO P].


(** Every subset [S] of a partially ordered set [P] with a unique
    element satisfies the uniqueness property. *)

Lemma PO_uniqueness_of_unique
    `(P : PartialOrder)
    (S : Nv_naiveSet P)
    : PO_uniqueness P (PO_unique P S).
(* begin hide *)
Proof.
    unfold PO_uniqueness; intros x y x_unique y_unique.
    destruct x_unique as [x_in_S others_eq_x],
        y_unique as [y_in_S others_eq_y].
    now apply (others_eq_y x).
Qed.
(* end hide *)


(** A partial order induces a strict order [≺] such that [x ≺ y] if
    and only if [x ≼ y] but [~(x == y)]. *)

Definition PO_strictlyPrecedes
    `(P : PartialOrder)
    : relation P
    :=
        fun x y : P => x ≼ y [PO P] /\ ~(x == y [PO P]).

Instance PO_StrictOrder
    `(P : PartialOrder)
    : SO_StrictOrder (PO_strictlyPrecedes P).
(* begin hide *)
Proof.
    split.
    -   intros x x_strictly_precedes_y.
        destruct x_strictly_precedes_y as [x_precedes_y x_not_eq_y].
        apply x_not_eq_y.
        now apply antisymmetry.
    -   intros x y z x_strictly_precedes_y y_strictly_precedes_z.
        destruct x_strictly_precedes_y as [x_precedes_y x_not_eq_y],
            y_strictly_precedes_z as [y_precedes_z y_not_eq_z].
        split.
        now transitivity y.
        intro x_eq_z.
        rewrite x_eq_z in x_precedes_y.
        assert (y_eq_z : y == z [PO P]).
        now apply antisymmetry.
        now apply y_not_eq_z.
Qed.
(* end hide *)

Notation "x ≺ y  '[PO'  P ']'" := (PO_strictlyPrecedes P x y) (at level 70, no associativity).


(** The strict order induced by a partial order is the same as
    the one induced by this partial order seen as a quasi-order. *)

Lemma PO_QO_StrictOrder
    `(P : PartialOrder)
    : forall x y : P, x ≺ y [PO P] -> x ≺ y [QO P].
(* begin hide *)
Proof.
    intros x y x_strictly_precedes_y.
    destruct x_strictly_precedes_y as [x_precedes_y x_not_eq_y].
    split; try assumption.
    intro y_precedes_x.
    assert (x_eq_y : x == y [PO P]).
    now apply antisymmetry.
    now apply x_not_eq_y.
Qed.
(* end hide *)


(** The predicate [QO_eq] defines the equality relation [==] induced
    by a quasi-order. By definition, [x == y] if and only if [x ≼ y]
    and [y ≼ x]. *)

Definition QO_eq
    `(Q : PreOrder)
    : relation Q
    :=
        fun x y : Q => x ≼ y [QO Q] /\ y ≼ x [QO Q].

Notation "x == y  '[QO'  Q ']'" := (QO_eq Q x y) (at level 70, no associativity).
Notation "x <> y  '[QO'  Q ']'" := (~(QO_eq Q x y)) (at level 70, no associativity).


(** The equality [QO_eq] is an equivalence relation. *)

Instance QO_Equivalence
    `(Q : PreOrder)
    : Equivalence (QO_eq Q).
(* begin hide *)
Proof.
    split.
    -   intro x.
        unfold QO_eq.
        split;
        reflexivity.
    -   intros x y eq_x_y.
        unfold QO_eq in *.
        destruct eq_x_y as [precedes_x_y precedes_y_x].
        now split.
    -   intros x y z eq_x_y eq_y_z.
        unfold QO_eq in *.
        destruct eq_x_y as [precedes_x_y precedes_y_x],
            eq_y_z as [precedes_y_z precedes_z_y].
        split;
        now transitivity y.
Qed.
(* end hide *)


(** A quasi-order induces a partial order. *)

Instance QO_PartialOrder
    `(Q : PreOrder)
    : PO_PartialOrder (QO_eq Q) (QO_precedes Q).
(* begin hide *)
Proof.
    unfold PartialOrder.
    unfold relation_equivalence, relation_conjunction, Basics.flip;
    unfold predicate_equivalence, predicate_intersection;
    unfold pointwise_lifting, pointwise_extension.
    unfold QO_eq.
    intros x y.
    split;
    trivial.
Qed.
(* end hide *)


(*****************************************)
(** * Extrema in a Partially Ordered Set *)
(*****************************************)


(** Given a part [S] of a partially ordered set [P], the _least element_
    of [S] is the one that precedes all the others. *)

Definition PO_least
    `(P : PartialOrder)
    (S : Nv_naiveSet P)
    (l : P)
    : Prop
    :=
        l ∈ S /\ (forall x : P, x ∈ S -> l ≼ x [PO P]).


(** A set may have a least element. *)

Definition PO_has_least
    `(P : PartialOrder)
    (S : Nv_naiveSet P)
    : Type
    :=
        {l : P | PO_least P S l}.


(** If there is a least element, we can get it. *)

Definition PO_getLeast
    `(P : PartialOrder)
    (S : Nv_naiveSet P)
    (H : PO_has_least P S)
    : P
    := 
        projT1 H.


(** And the object we get is indeed the least element. *)

Lemma PO_is_least
    `(P : PartialOrder)
    (S : Nv_naiveSet P)
    (H : PO_has_least P S)
    : PO_least P S (PO_getLeast P S H).
(* begin hide *)
Proof.
    exact (projT2 H).
Qed.
(* end hide *)


(** A _minimal element_ of [S] is an element of [S] without any
    predecessor. *)

Definition PO_Minimal
    `(P : PartialOrder)
    (S : Nv_naiveSet P)
    : Nv_naiveSet P
    :=
        fun m : P => m ∈ S /\ (forall x : P, x ∈ S -> x ≼ m [PO P] -> x == m [PO P]).


(** A set may have a minimal element. *)

Definition PO_has_minimal
    `(P : PartialOrder)
    (S : Nv_naiveSet P)
    : Type
    :=
        {m : P | PO_Minimal P S m}.


(** If there is a minimal element, we can get it. *)

Definition PO_getMinimal
    `(P : PartialOrder)
    (S : Nv_naiveSet P)
    (H : PO_has_minimal P S)
    : P
    :=
        projT1 H.


(** And the object we get is indeed a minimal element. *)

Lemma PO_is_minimal
    `(P : PartialOrder)
    (S : Nv_naiveSet P)
    (H : PO_has_minimal P S)
    : PO_Minimal P S (PO_getMinimal P S H).
(* begin hide *)
Proof.
   exact (projT2 H).
Qed.
(* end hide *)


(** The least element, when it exists, is a minimal element. *)

Lemma PO_least_is_minimal
    `(P : PartialOrder)
    : forall (S : Nv_naiveSet P) (l : P),
          PO_least P S l -> l ∈ (PO_Minimal P S).
(* begin hide *)
Proof.
    intros S l l_least.
    destruct l_least as [l_in_S l_least].
    split.
    assumption.
    intros x x_in_S x_precedes_l.
    apply antisymmetry.
    assumption.
    apply (l_least x x_in_S).
Qed.
(* end hide *)


(** An element of [S] is its _minimum_ if and only if it is its unique
    minimal element. *)

Definition PO_minimum
    `(P : PartialOrder)
    (S : Nv_naiveSet P)
    (m : P)
    : Prop
    :=
        PO_unique P (fun x => x ∈ (PO_Minimal P S)) m.


(** A set may have a minimum. *)

Definition PO_has_minimum
    `(P : PartialOrder)
    (S : Nv_naiveSet P)
    : Type
    :=
        {m : P | PO_minimum P S m}.


(** If there is a minimum, we can get it. *)

Definition PO_getMinimum
    `(P : PartialOrder)
    (S : Nv_naiveSet P)
    (H : PO_has_minimum P S)
    : P
    :=
        projT1 H.


(** And the object we get is indeed the minimum. *)

Lemma PO_is_minimum
    `(P : PartialOrder)
    (S : Nv_naiveSet P)
    (H : PO_has_minimum P S)
    : PO_minimum P S (PO_getMinimum P S H).
(* begin hide *)
Proof.
    exact (projT2 H).
Qed.
(* end hide *)


(** The least element, when it exits, is the minimum. *)

Lemma PO_least_is_minimum
    `(P : PartialOrder)
    : forall (S : Nv_naiveSet P) (l : P),
          PO_least P S l -> PO_minimum P S l.
(* begin hide *)
Proof.
    intros S l l_least.
    split.
    now apply PO_least_is_minimal.
    intros x x_minimal.
    destruct l_least as [l_in_S l_least].
    destruct x_minimal as [x_in_S x_minimal].
    symmetry.
    apply (x_minimal l l_in_S (l_least x x_in_S)).
Qed.
(* end hide *)


(** When it exists, the minimum is unique. *)

Lemma PO_uniqueness_of_minimum
    `(P : PartialOrder)
    : forall (S : Nv_naiveSet P), PO_uniqueness P (fun x => PO_minimum P S x).
(* begin hide *)
Proof.
    intro S; now apply PO_uniqueness_of_unique.
Qed.
(* end hide *)


(** Thus, when it exists, the least element is unique too. *)

Corollary PO_uniqueness_of_least
    `(P : PartialOrder)
    : forall (S : Nv_naiveSet P), PO_uniqueness P (fun x => PO_least P S x).
(* begin hide *)
Proof.
    intros S l l' l_least l'_least.
    now apply (PO_uniqueness_of_minimum P S l l');
    apply (PO_least_is_minimum).
Qed.
(* end hide *)


(** Given a part [S] of a partially ordered set [P], the _greatest
    element_ of [S] is the one that succeeds all the others. *)

Definition PO_greatest
    `(P : PartialOrder)
    (S : Nv_naiveSet P)
    (g : P)
    : Prop
    :=
        g ∈ S /\ (forall x : P, x ∈ S -> x ≼ g [PO P]).


(** A set may have a greatest element. *)

Definition PO_has_greatest
    `(P : PartialOrder)
    (S : Nv_naiveSet P)
    : Type
    :=
        {g : P | PO_greatest P S g}.


(** If there is a greatest element, we can get it. *)

Definition PO_getGreatest
    `(P : PartialOrder)
    (S : Nv_naiveSet P)
    (H : PO_has_greatest P S)
    : P
    := 
        projT1 H.


(** And the object we get is indeed the greatest element. *)

Lemma PO_is_greatest
    `(P : PartialOrder)
    (S : Nv_naiveSet P)
    (H : PO_has_greatest P S)
    : PO_greatest P S (PO_getGreatest P S H).
(* begin hide *)
Proof.
    exact (projT2 H).
Qed.
(* end hide *)


(** A _maximal element_ of [S] is an element of [S] without any
    successor. *)

Definition PO_Maximal
    `(P : PartialOrder)
    (S : Nv_naiveSet P)
    : Nv_naiveSet P
    :=
        fun m : P => m ∈ S /\ (forall x : P, x ∈ S -> m ≼ x [PO P] -> m == x [PO P]).


(** A set may have a maximal element. *)

Definition PO_has_maximal
    `(P : PartialOrder)
    (S : Nv_naiveSet P)
    : Type
    :=
        {m : P | PO_Maximal P S m}.


(** If there is a maximal element, we can get it. *)

Definition PO_getMaximal
    `(P : PartialOrder)
    (S : Nv_naiveSet P)
    (H : PO_has_maximal P S)
    : P
    :=
        projT1 H.


(** And the object we get is indeed a maximal element. *)

Lemma PO_is_maximal
    `(P : PartialOrder)
    (S : Nv_naiveSet P)
    (H : PO_has_maximal P S)
    : PO_Maximal P S (PO_getMaximal P S H).
(* begin hide *)
Proof.
   exact (projT2 H).
Qed.
(* end hide *)


(** The greatest element, when it exists, is a maximal element. *)

Lemma PO_greatest_is_maximal
    `(P : PartialOrder)
    : forall (S : Nv_naiveSet P) (g : P),
          PO_greatest P S g -> g ∈ (PO_Maximal P S).
(* begin hide *)
Proof.
    intros S g g_greatest.
    destruct g_greatest as [g_in_S g_greatest].
    split.
    assumption.
    intros x x_in_S g_precedes_x.
    apply antisymmetry.
    assumption.
    apply (g_greatest x x_in_S).
Qed.
(* end hide *)


(** An element of [S] is its _maximum_ if and only if it is its unique
    maximal element. *)

Definition PO_maximum
    `(P : PartialOrder)
    (S : Nv_naiveSet P)
    (m : P)
    : Prop
    :=
        PO_unique P (fun x => x ∈ (PO_Maximal P S)) m.


(** A set may have a maximum. *)

Definition PO_has_maximum
    `(P : PartialOrder)
    (S : Nv_naiveSet P)
    : Type
    :=
        {m : P | PO_maximum P S m}.


(** If there is a maximum, we can get it. *)

Definition PO_getMaximum
    `(P : PartialOrder)
    (S : Nv_naiveSet P)
    (H : PO_has_maximum P S)
    : P
    :=
        projT1 H.


(** And the object we get is indeed the maximum. *)

Lemma PO_is_maximum
    `(P : PartialOrder)
    (S : Nv_naiveSet P)
    (H : PO_has_maximum P S)
    : PO_maximum P S (PO_getMaximum P S H).
(* begin hide *)
Proof.
    exact (projT2 H).
Qed.
(* end hide *)


(** The greatest element, when it exits, is the maximum. *)

Lemma PO_greatest_is_maximum
    `(P : PartialOrder)
    : forall (S : Nv_naiveSet P) (g : P),
          PO_greatest P S g -> PO_maximum P S g.
(* begin hide *)
Proof.
    intros S g g_greatest.
    split.
    now apply PO_greatest_is_maximal.
    intros x x_maximal.
    destruct g_greatest as [g_in_S g_greatest].
    destruct x_maximal as [x_in_S x_maximal].
    apply (x_maximal g g_in_S (g_greatest x x_in_S)).
Qed.
(* end hide *)


(** When it exists, the maximum is unique. *)

Lemma PO_uniqueness_of_maximum
    `(P : PartialOrder)
    : forall (S : Nv_naiveSet P), PO_uniqueness P (fun x => PO_maximum P S x).
(* begin hide *)
Proof.
    intro S; now apply PO_uniqueness_of_unique.
Qed.
(* end hide *)


(** Thus, when it exists, the greatest element is unique too. *)

Corollary PO_greatest_uniqueness
    `(P : PartialOrder)
    : forall (S : Nv_naiveSet P), PO_uniqueness P (fun x => PO_greatest P S x).
(* begin hide *)
Proof.
    intros S g g' g_greatest g'_greatest.
    now apply (PO_uniqueness_of_maximum P S g g');
    apply (PO_greatest_is_maximum).
Qed.
(* end hide *)


(** Given a part [S] of a partially ordered set [P], the function
    [PO_LowerBound] returns the set of predecessors that all
    the elements of [S] have in common. *)

Definition PO_LowerBound
    `(P : PartialOrder)
    (S : Nv_naiveSet P)
    : Nv_naiveSet P
    :=
        fun l : P => forall x : P, x ∈ S -> l ≼ x [PO P].


(** It is natural to look for the _greatest lower bound_ (GLB). *)

Definition PO_glb
    `(P : PartialOrder)
    (S : Nv_naiveSet P)
    (glb : P)
    : Prop
    :=
        let L := (PO_LowerBound P S)
        in glb ∈ L /\ PO_greatest P L glb.

(** A set may have a greatest lower bound. *)

Definition PO_has_glb
    `(P : PartialOrder)
    (S : Nv_naiveSet P)
    : Type
    :=
        {glb : P | PO_glb P S glb}.


(** If there is a greatest lower bound, we can get it. *)

Definition PO_getGlb
    `(P : PartialOrder)
    (S : Nv_naiveSet P)
    (H : PO_has_glb P S)
    : P
    :=
        projT1 H.


(** And the object we get is indeed the greatest lower bound. *)

Lemma PO_is_glb
    `(P : PartialOrder)
    (S : Nv_naiveSet P)
    (H : PO_has_glb P S)
    : PO_glb P S (PO_getGlb P S H).
(* begin hide *)
Proof.
   exact (projT2 H).
Qed.
(* end hide *)


(** Given a part [S] of a partially ordered set [P], the function
    [PO_UpperBound] returns the set of successors that all
    the elements of [S] have in common. *)

Definition PO_UpperBound
    `(P : PartialOrder)
    (S : Nv_naiveSet P)
    : Nv_naiveSet P
    :=
        fun u : P => forall x : P, x ∈ S -> x ≼ u [PO P].


(** It is natural to look for the _least upper bound_ (LUB) too. *)

Definition PO_lub
    `(P : PartialOrder)
    (S : Nv_naiveSet P)
    (lub : P)
    : Prop
    :=
        let U := (PO_UpperBound P S)
        in lub ∈ U /\ PO_least P U lub.


(** A set may have a least lower bound. *)

Definition PO_has_lub
    `(P : PartialOrder)
    (S : Nv_naiveSet P)
    : Type
    :=
        {lub : P | PO_lub P S lub}.


(** If there is a least upper bound, we can get it. *)

Definition PO_getLub
    `(P : PartialOrder)
    (S : Nv_naiveSet P)
    (H : PO_has_lub P S)
    : P
    :=
        projT1 H.


(** And the object we get is indeed the least upper bound. *)

Lemma PO_is_lub
    `(P : PartialOrder)
    (S : Nv_naiveSet P)
    (H : PO_has_lub P S)
    : PO_lub P S (PO_getLub P S H).
(* begin hide *)
Proof.
   exact (projT2 H).
Qed.
(* end hide *)