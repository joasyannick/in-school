(** This library provides some examples of label-structured modal
    transition systems built with boolean labels. They can be found in
    the article _Extending Modal Transition Systems with Structured
    Labels_, by Sebastian S. Bauer, Line Juhl, Kim G. Larsen, Axel Legay,
    and Jiri Srba, and published in 2012 in the journal _Mathematical
    Structures in Computer Science_, volume 22, pages 581-617. *)


Add LoadPath "..".
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.RelationClasses.
Require Import LabelSet.


(** The binary relation [leb] on [bool] is a preorder.  *)

Instance leb_PreOrder :
    PreOrder leb.
(* begin hide *)
Proof.
    split.
    - unfold Reflexive;
      destr_bool.
    - unfold Transitive;
      destr_bool.
Qed.
(* end hide *)


(** The set [bool] together with the preorder [leb] and the least
    boolean [false] is a label-set. *)

Program Instance bool_LabelSet : LabelSet leb false :=
    Build_LabelSet leb false leb_PreOrder _.


(** The boolean [true] is an implementation label. *)

Lemma implementation_true : LabS_implementation true.
(* begin hide *)
Proof.
    unfold LabS_implementation.
    split;
    try discriminate.
    destr_bool.
    apply (reflexivity (Reflexive := Equivalence_Reflexive (Equivalence := LabS_eqrel))).
    exfalso;
    apply H;
    reflexivity.
Qed.
(* end hide *)


(** The set [bool] together with the preorder [leb] and the least
    boolean [false] is a well-formed label-set. *)

Instance bool_WFLabelSet : WFLabelSet bool_LabelSet.
(* begin hide *)
Proof.
    split.
    destr_bool;
    exists true;
    split;
    apply implementation_true;
    simpl;
    trivial.
Qed.
(* end hide *)


(*
Inductive configurations1
    : Set
    := i0 | i1.


Definition may1
    (pre : configurations1)
    (l : bool)
    (post : configurations1)
    : Prop
    :=
        match (pre, l, post) with
        |   (i0, true, i1) => True
        |   (i1, true, i0) => True
        | _ => False
        end.


Lemma booleanLSMTS1_incl :
    forall (pre : configurations1) (l : bool) (post : configurations1),
        may1 pre l post -> may1 pre l post.
Proof.
    trivial.
Qed.


Instance booleanLSMTS1 : LSMTS bool_WFLabelSet i0 may1 may1.
Proof.
    apply (Build_LSMTS bool_WFLabelSet i0 may1 may1 booleanLSMTS1_incl).
Qed.
*)