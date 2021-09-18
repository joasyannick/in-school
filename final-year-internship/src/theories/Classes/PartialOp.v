(** *)


Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Setoids.Setoid.


(** *)

Class POp_PartialOp
    {set : Type}
    (defined : relation set)
    {eq : relation set}
    (Eq : Equivalence eq)
    :=
        POp_buildPartialOp {

(** *)

            POp_set := set;
            POp_defined := defined;
            POp_eq := eq;
            POp_Equivalence := Eq;

(** *)

            POp_operator : forall x y : set, defined x y -> set
        }.


(** *)

Arguments POp_buildPartialOp {_ _ _} _ _ .


(** *)

Arguments POp_set {_ _ _ _} _ .
Arguments POp_defined {_ _ _ _} _ _ _.
Arguments POp_eq {_ _ _ _} _ _ _.
Arguments POp_Equivalence {_ _ _ _} _.
Arguments POp_operator {_ _ _ _} _ _ _ _.


(** *)

Generalizable Variables set defined eq Eq.


(** *)

Coercion POp_operator : POp_PartialOp >-> Funclass.


(** *)

Lemma POp_irrelevance
    `(Op : POp_PartialOp)
    : forall x y xy xy',
          POp_eq Op (Op x y xy) (Op x y xy').
(* begin hide *)
Proof.
    intros x y x_y_defined x_y_defined'.
    assert (irrelevance : x_y_defined = x_y_defined').
    now apply proof_irrelevance.
    now rewrite irrelevance.
Qed.
(* end hide *)


(** *)

Class POp_Commutative
    `(Op : POp_PartialOp)
    : Prop
    :=
        POp_buildCommutative {

(** *)

            POp_Commutative_PartialOp := Op;

(** *)

            POp_commutativity1 :
                forall x y,
                    POp_defined Op x y -> POp_defined Op y x;

(** *)

            POp_commutativity2 :
                forall x y,
                    POp_defined Op y x -> POp_defined Op x y;

(** *)

            POp_commutativity3 :
                forall x y xy,
                    POp_eq _ (Op x y xy) (Op y x (POp_commutativity1 x y xy))
        }.


(** *)

Arguments POp_buildCommutative {_ _ _ _} _ _ _ _.


(** *)

Arguments POp_Commutative_PartialOp {_ _ _ _ _} _.
Arguments POp_commutativity1 {_ _ _ _ _} _ _ _ _.
Arguments POp_commutativity2 {_ _ _ _ _} _ _ _ _.
Arguments POp_commutativity3 {_ _ _ _ _} _ _ _ _.


(** *)


Generalizable Variables Op.


(** *)

Coercion POp_Commutative_PartialOp : POp_Commutative >-> POp_PartialOp.


(** *)

Class POp_Associative
    `(Op : POp_PartialOp)
    : Prop
    :=
        POp_buildAssociative {

(** *)

            POp_Associative_PartialOp := Op;

(** *)

            POp_associativity1 :
                forall x y z xy, POp_defined _ (Op x y xy) z ->
                    forall yz, POp_defined _ x (Op y z yz);         


            POp_associativity2 :
                forall x y z yz, POp_defined _ x (Op y z yz) ->
                    forall xy, POp_defined _ (Op x y xy) z;         

(** *)

            POp_associativity3 :
              forall x y z xy yz xyz,
                      POp_eq _ (Op x (Op y z yz) xyz)
                          (Op (Op x y xy) z (POp_associativity2 x y z yz xyz xy))
        }.