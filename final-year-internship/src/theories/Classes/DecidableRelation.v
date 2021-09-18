(** This library is about _decidable_ relations, i.e. relations that
    can be tested with a pattern matching or an if-then-else. *)


Require Import Coq.Relations.Relation_Definitions.


(** A relation [related] on a set [set] is _decidable_ when there
    exists an algorithm that says, for each [x y : set], whether
    or not [related x y]. *)

Class DRel_Decidable
    {set : Type}
    (related : relation set)
    : Type
    :=
        DRel_buildDecidable {

(** There is a getter for each parameter. *)

              DRel_set := set;
              DRel_related : set -> set -> Prop := related;

(** The field [DRel_decidable] is the decision algorithm. *)

              DRel_decidable : forall x y : set, {related x y} + {~related x y}
        }.


(** Only the relation [related] and its decision algorithm
    [DRel_decidable] are explicitly required to build an instance of
    a decidable relation. *)

Arguments DRel_buildDecidable {_} _ _.


(** We prefer to have the decidable relation explicit in every method. *)

Arguments DRel_set {_ _} _.
Arguments DRel_related {_ _} _ _ _.
Arguments DRel_decidable {_ _} _ _ _.


(** The parameters can be automatically generated and declared
    implicit with [`(..)] or [`{..}]. *)

Generalizable Variables set related.


(** A decidable relation is a relation. *)

Coercion DRel_related : DRel_Decidable >-> Funclass.