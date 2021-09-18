(** *)


Add LoadPath ".." as LSMTS.
Require Import Coq.Classes.RelationClasses.
Require Import LSMTS.Classes.DecidableRelation.
Require Import LSMTS.Classes.Order.


(** *)

Class QO_Decidable
    `(Q : PreOrder)
    : Type
    :=
        QO_buildDecidable {

(** *)

            QO_Decidable_QuasiOrder := Q;

(** *)

            QO_decidable : DRel_Decidable (QO_precedes Q)
        }.


(** *)

Arguments QO_buildDecidable {_ _} _ _.


(** *)

Arguments QO_Decidable_QuasiOrder {_ _ _} _.
Arguments QO_decidable {_ _ _} _.


(** *)

Generalizable Variable Q.


(** *)

Coercion QO_Decidable_QuasiOrder : QO_Decidable >-> QO_QuasiOrder.


(** *)

Class SO_Decidable
    `(S : StrictOrder)
    : Type
    :=
        SO_buildDecidable {

(** *)

            SO_Decidable_StrictOrder := S;

(** *)

            SO_decidable : DRel_Decidable (SO_precedes S)
        }.


(** *)

Arguments SO_buildDecidable {_ _} _ _.


(** *)

Arguments SO_Decidable_StrictOrder {_ _ _} _.
Arguments SO_decidable {_ _ _} _.


(** *)

Generalizable Variable S.


(** *)

Coercion SO_Decidable_StrictOrder : SO_Decidable >-> SO_StrictOrder.


(** *)

Class PO_Decidable
    `(P : PartialOrder)
    : Type
    :=
        PO_buildDecidable {

(** *)

            PO_Decidable_PartialOrder := P;

(** *)

            PO_decidable : DRel_Decidable (PO_precedes P);

(** *)

            PO_eq_Decidable : DRel_Decidable (PO_eq P)
        }.


(** *)

Arguments PO_buildDecidable {_ _ _ _ _} _ _ _.


(** *)

Arguments PO_Decidable_PartialOrder {_ _ _ _ _ _} _ _ _.
Arguments PO_decidable {_ _ _ _ _ _} _.
Arguments PO_eq_Decidable {_ _ _ _ _ _} _.


(** *)

Generalizable Variable P.


(** *)

Coercion PO_Decidable_PartialOrder : PO_Decidable >-> PO_PartialOrder.


(** *)

Instance QO_eq_Decidable
    `(Q : QO_Decidable)
    : DRel_Decidable (QO_eq Q).
(* begin hide *)
Proof.
    split.
    intros x y.
    elim (DRel_decidable (QO_decidable Q) x y).
    -   elim (DRel_decidable (QO_decidable Q) y x).
        intros y_precedes_x x_precedes_y.
        left; now split.
        intros y_not_precedes_x x_precedes_y.
        right; intro x_eq_y; now destruct x_eq_y.
    -   intros x_not_precedes_y.
        right; intro x_eq_y; now destruct x_eq_y.
Qed.
(* end hide *)


(** *)

Instance QO_PartialOrder_Decidable
    `(Q : QO_Decidable)
    : PO_Decidable (QO_PartialOrder Q).
(* begin hide *)
Proof.
    split.
    now destruct Q.
    now apply (QO_eq_Decidable Q).
Qed.
(* end hide *)