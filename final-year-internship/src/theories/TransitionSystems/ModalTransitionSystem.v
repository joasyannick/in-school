(** This library provides an implementation of _label-structured modal
    transition systems_ (LSMTS), a notion defined in the article
    _Extending Modal Transition Systems with Structured Labels_ by
    Sebastian S. Bauer, Line Juhl, Kim G. Larsen, Axel Legay, and Jiri
    Srba, and published in 2012 in the journal _Mathematical
    Structures in Computer Science_, volume 22, pages 581-617. *)


Add LoadPath ".." as LSMTS.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Import LSMTS.Sets.NaiveSet.
Require Import LSMTS.Classes.PartialOp.
Require Import LSMTS.TransitionSystems.Transition.
Require Import LSMTS.Classes.Order.
Require Import LSMTS.Contracts.Contract.
Require Import LSMTS.TransitionSystems.LabelSet.
Require Import LSMTS.TransitionSystems.LabelOp.
Require Import LSMTS.TransitionSystems.TransitionSystem.


(************************************************)
(** * Label-Structured Modal Transition Systems *)
(************************************************)


(** A _label-structured modal transition system_ can be viewed as
    a transition system where each transition has a _modality_. *)


Class MTS_TransitionSystem
    `(Event : LSet_WellFormed)
    `(Modal : LSet_LabelSet)
    : Type
    :=
        MTS_buildTransitionSystem {

(** There is a getter for each parameter. *)

            MTS_Event := Event;
            MTS_Modal := Modal;

(** *)

            MTS_state : Type;
(** *)

            MTS_initial : MTS_state;

(** *)

            MTS_System : TS_TransitionSystem (Nv_singleton MTS_initial) Event;

(** *)

            MTS_Modality : TS_Transition MTS_System -> Nv_naiveSet Modal;

(** *)

            MTS_inheritance :
                forall t m m',
                    m ∈ (MTS_Modality t) -> m ≼ m' [LSet _] -> m' ∈ (MTS_Modality t)
        }.


(** *)

Arguments MTS_buildTransitionSystem {_ _ _ _} _ {_ _ _} _ {_ _} _ {_} _.


(** We prefer to have the LSMTS explicit in every method. *)

Arguments MTS_Event {_ _ _ _ _ _ _ _ _} _.
Arguments MTS_Modal {_ _ _ _ _ _ _ _ _} _.
Arguments MTS_state {_ _ _ _ _ _ _ _ _} _.
Arguments MTS_initial {_ _ _ _ _ _ _ _ _} _.
Arguments MTS_System {_ _ _ _ _ _ _ _ _} _.
Arguments MTS_Modality {_ _ _ _ _ _ _ _ _} _ _ _.
Arguments MTS_inheritance {_ _ _ _ _ _ _ _ _} _ _ _ _ _ _.


(** The parameters can be automatically generated and declared
    implicit with [`(..)] or [`{..}]. *)

Generalizable Variables Event Modal.


(** A LSMTS can be interpreted as a transition system. *)

Coercion MTS_System : MTS_TransitionSystem >-> TS_TransitionSystem.


(** *)

Class MTS_Implementation
    `(M : MTS_TransitionSystem)
    : Prop
    :=
        MTS_buildImplementation {

(** *)

            MTS_Implementation_System := M;

(** *)

            MTS_inheritance_converse :
                forall t m m',
                    m' ∈ (MTS_Modality M t) -> m ≼ m' [LSet _] -> m ∈ (MTS_Modality M t);

(** *)

            MTS_implementation :
                forall t : TS_Transition M,
                    (TS_label t) ∈ (LSet_Implementation (MTS_Event M))
        }.


(** *)

Arguments MTS_buildImplementation {_ _ _ _ _ _ _ _ _} _ _ _.


(** *)

Arguments MTS_Implementation_System {_ _ _ _ _ _ _ _ _ _} _.
Arguments MTS_inheritance_converse {_ _ _ _ _ _ _ _ _ _} _ _ _ _ _ _.
Arguments MTS_implementation {_ _ _ _ _ _ _ _ _ _} _ _.


(** *)

Coercion MTS_Implementation_System : MTS_Implementation >-> MTS_TransitionSystem.


(** *)

Generalizable Variables M.


(*****************)
(** * Refinement *)
(*****************)


(** Relations over modal transition systems. *)

Definition MTS_relation
    `(M1 : MTS_TransitionSystem)
    (M2 : MTS_TransitionSystem (MTS_Event M1) (MTS_Modal M1))
    : Type
    :=
        (TS_state M1) -> (TS_state M2) -> Prop.


(** *)

Definition MTS_identity
    `(M : MTS_TransitionSystem)
    : MTS_relation M M
    :=
        fun s s' : TS_state M => s = s'.


(** *)

Definition MTS_inverse
    `{M1 : MTS_TransitionSystem}
    {M2 : MTS_TransitionSystem (MTS_Event M1) (MTS_Modal M1)}
    (refines : MTS_relation M1 M2)
    : MTS_relation M2 M1
    :=
        fun (s2 : TS_state M2) (s1 : TS_state M1) =>
            refines s1 s2.


(** *)

Definition MTS_composition
    `{M1 : MTS_TransitionSystem}
    {M2 : MTS_TransitionSystem (MTS_Event M1) (MTS_Modal M1)}
    {M3 : MTS_TransitionSystem (MTS_Event M1) (MTS_Modal M1)}
    (refines1 : MTS_relation M1 M2)
    (refines2 : MTS_relation M2 M3)
    : MTS_relation M1 M3
    :=
        fun (s1 : TS_state M1) (s3 : TS_state M3) =>
            exists s2 : TS_state M2, refines1 s1 s2 /\ refines2 s2 s3.


(** *)

Class MTS_ModalRefinement
    `{M1 : MTS_TransitionSystem}
    {M2 : MTS_TransitionSystem (MTS_Event M1) (MTS_Modal M1)}
    (refines : MTS_relation M1 M2)
    : Prop
    :=
        MTS_buildModalRefinement {

(** *)

            MTS_refining := M1;
            MTS_refined := M2;
            MTS_refines := refines;

(** *)

            MTS_modal_refinement0 : refines (MTS_initial M1) (MTS_initial M2);
 
(** *)

            MTS_modal_refinement1 :
                forall t1 s2,
                    refines (TS_source t1) s2 ->
                            exists t2,
                                TS_source t2 = s2 /\
                                    refines (TS_target t1) (TS_target t2) /\
                                         (TS_label t1) ≼ (TS_label t2) [LSet _] /\
                                                 (MTS_Modality M1 t1) ≼ (MTS_Modality M2 t2) [Set _];

(** *)

            MTS_modal_refinement2 :
                forall s1 t2, refines s1 (TS_source t2) -> 
                        forall m2 : MTS_Modal M2, m2 ∈ (MTS_Modality M2 t2) -> m2 ∈ (LSet_Implementation _) ->
                            exists t1,
                                TS_source t1 = s1 /\
                                    refines (TS_target t1) (TS_target t2) /\
                                        TS_label t1 ≼ TS_label t2 [LSet _] /\
                                            m2 ∈ MTS_Modality M1 t1
    }.


(** *)

Arguments MTS_buildModalRefinement {_ _ _ _ _ _ _ _ _ _ _} _ _ _ _.


(** *)

Arguments MTS_refining {_ _ _ _ _ _ _ _ _ _ _ _} _.
Arguments MTS_refined {_ _ _ _ _ _ _ _ _ _ _ _} _.
Arguments MTS_refines {_ _ _ _ _ _ _ _ _ _ _ _} _ _ _.
Arguments MTS_modal_refinement0 {_ _ _ _ _ _ _ _ _ _ _ _} _.
Arguments MTS_modal_refinement1 {_ _ _ _ _ _ _ _ _ _ _ _} _ _ _ _.
Arguments MTS_modal_refinement2 {_ _ _ _ _ _ _ _ _ _ _ _} _ _ _ _ _ _ _.


(** *)

Generalizable Variables refines.


(** *)

Instance MTS_identitity_ModalRefinement
    `(M : MTS_TransitionSystem)
    : MTS_ModalRefinement (MTS_identity M).
(* begin hide *)
Admitted.
(*
Proof.
    split.
    -   reflexivity.
    -   intros s s' s_eq_s' t s_source_of_t m m_modality_of_t .
        exists t.
        rewrite s_eq_s' in s_source_of_t.
        repeat split; auto.
        now apply (reflexivity (Reflexive := (PO_Reflexive L))).
        exists m.
        split; try assumption.
        now apply (reflexivity (Reflexive := (PO_Reflexive Modal))).
    -   intros s s' s_eq_s' t s'_source_of_t m m_modality_of_t m_implementation.
        exists t.
        rewrite s_eq_s'.
        repeat split; auto.
        now apply (reflexivity (Reflexive := (PO_Reflexive L))).
Qed.
*)
(* end hide *)


(** *)

Instance MTS_inverse_ModalRefinement
    `{I1 : MTS_Implementation}
    {M2 : MTS_TransitionSystem (MTS_Event I1) (MTS_Modal I1)}
    {I2 : MTS_Implementation M2}     
    {refines : MTS_relation I1 I2}
    (R : MTS_ModalRefinement refines)
    : MTS_ModalRefinement (MTS_inverse refines).
(* begin hide *)
Admitted.
(*
Proof.
    split.
    -   apply (MTS_modal_refinement0 R).
    -   intros s2 s1 s2_refines_s1 t2 s2_source_of_t2 m2 m2_modality_of_t2.
        admit. (*
        elim (MTS_modal_refinement1 R s1 s2 s2_refines_s1); intros.
        destruct H as [s1_source_of_t1 [H1 [H2 H3]]].
        exists x.
        repeat split; auto.
        destruct H1; auto.
        generalize (MTS_implementation I2 t2); intro.
        destruct H.
        elim (H0 (Tsn_label (projT1 x))); auto.
        elim (MTS_implementation I1 x); intros; auto.
        assumption. *)
    -   admit.
Qed.
*)
(* end hide *)


(** *)

Instance MTS_composition_ModalRefinement
    `{M1 : MTS_TransitionSystem}
    {M2 : MTS_TransitionSystem (MTS_Event M1) (MTS_Modal M1)}
    {M3 : MTS_TransitionSystem (MTS_Event M1) (MTS_Modal M1)}
    {refines1 : MTS_relation M1 M2}
    (refinement1 : MTS_ModalRefinement refines1)
    {refines2 : MTS_relation M2 M3}
    (refinement2 : MTS_ModalRefinement refines2)
    : MTS_ModalRefinement (MTS_composition refines1 refines2).
(* begin hide *)
Admitted.
(*
Proof.
    split.
    -   exists (MTS_initial M2).
        split.
        apply (MTS_modal_refinement0 refinement1).
        apply (MTS_modal_refinement0 refinement2).
    -   intros s1 s3 s1_refines_s3 t1 s1_source_of_t1 m1 m1_modality_of_t1.
        destruct s1_refines_s3 as [s2 [s1_refines_s2 s2_refines_s3]].
        elim (MTS_modal_refinement1 refinement1 s1 s2 s1_refines_s2 t1 s1_source_of_t1 m1 m1_modality_of_t1).
        intros t2 t1_refines_t2.
        destruct t1_refines_t2 as [s2_source_of_t2 [s1'_refines_s2' [l1_precedes_l2 [m2 [m2_modality_of_t2 m1_precedes_m2]]]]].
        elim (MTS_modal_refinement1 refinement2 s2 s3 s2_refines_s3 t2 s2_source_of_t2 m2 m2_modality_of_t2).
        intros t3 t2_refines_t3.
        destruct t2_refines_t3 as [s3_source_of_t3 [s2'_refines_s3' [l3_precedes_l3 [m3 [m3_modality_of_t3 m2_precedes_m3]]]]].
        exists t3.
        repeat split.
        assumption.
        exists (Tsn_target (projT1 t2)).
        now split.
        now apply (transitivity (Transitive := PO_Transitive L) (y := Tsn_label (projT1 t2))).
        exists m3.
        split; try assumption.
        now apply (transitivity (Transitive := PO_Transitive Modal) (y := m2)).
    -   intros s1 s3 s1_refines_s3 t3 s3_source_of_t3 m3 m3_modality_of_t3 m3_implementation.
        destruct s1_refines_s3 as [s2 [s1_refines_s2 s2_refines_s3]].
        elim (MTS_modal_refinement2 refinement2 s2 s3 s2_refines_s3 t3 s3_source_of_t3 m3 m3_modality_of_t3 m3_implementation).
        intros t2 t2_refines_t3.
        destruct t2_refines_t3 as [s2_source_of_t2 [s2'_refines_s3' [l2_refines_l3 m3_modality_of_t2]]].
        elim (MTS_modal_refinement2 refinement1 s1 s2 s1_refines_s2 t2 s2_source_of_t2 m3 m3_modality_of_t2 m3_implementation).
        intros t1 t1_refines_t2.
        destruct t1_refines_t2 as [s1_source_of_t1 [s1'_refines_s2' [l1_refines_l2 m3_modality_of_t1]]].
        exists t1.
        repeat split.
        assumption.
        exists (Tsn_target (projT1 t2)).
        now split.
        now apply (transitivity (Transitive := PO_Transitive L) (y := Tsn_label (projT1 t2))).
        assumption.
Qed.
*)
(* end hide *)


(** *)

Definition MTS_modallyRefines
    `(M1 : MTS_TransitionSystem)
    (M2 : MTS_TransitionSystem (MTS_Event M1) (MTS_Modal M1))
    : Prop
    :=
        exists refines : MTS_relation M1 M2, MTS_ModalRefinement refines.

Notation "M1 ≼m M2  '[MTS]'" := (MTS_modallyRefines M1 M2) (at level 70, no associativity).


(** *)

Definition MTS_ImplementationSemantics
    `(M : MTS_TransitionSystem)
    : Nv_naiveSet (MTS_TransitionSystem (MTS_Event M) (MTS_Modal M))
    :=
        fun I : MTS_TransitionSystem (MTS_Event M) (MTS_Modal M) =>
            I ≼m M [MTS] /\ MTS_Implementation I.

Notation "〚 M 〛" := (MTS_ImplementationSemantics M) (at level 35, right associativity).


(** *)

Instance MTS_modallyRefines_QuasiOrder
    `{Event : LSet_WellFormed}
    `{Modal : LSet_LabelSet}
    : QO_QuasiOrder (MTS_modallyRefines (Event := Event) (Modal := Modal)).
(* begin hide *)
Proof.
    split.
    -   intro M.
        exists (MTS_identity M).
        apply (MTS_identitity_ModalRefinement M).
    -   intros M1 M2 M3 M1_refines_M2 M2_refines_M3.
        destruct M1_refines_M2 as [refines1 refinement1],
            M2_refines_M3 as [refines2 refinement2].
        exists (MTS_composition refines1 refines2).
        apply (MTS_composition_ModalRefinement refinement1 refinement2).
Qed.
(* end hide *)


(** *)

Lemma MTS_Implementation_Symmetric
    `{I1 : MTS_Implementation}
    {M2 : MTS_TransitionSystem (MTS_Event I1) (MTS_Modal I1)}
    {I2 : MTS_Implementation M2}
    : I1 ≼m I2 [MTS] -> I2 ≼m I1 [MTS].
(* begin hide *)
Proof.
    intro I1_refines_I2.
    destruct I1_refines_I2 as [refines refinement].
    exists (MTS_inverse refines).
    now apply MTS_inverse_ModalRefinement.
Qed.
(* end hide *)


(** *)

Definition MTS_thoroughlyRefines
    `(M1 : MTS_TransitionSystem)
    (M2 : MTS_TransitionSystem (MTS_Event M1) (MTS_Modal M1))
    : Prop
    :=
        〚M1〛 ⊆ 〚M2〛.

Notation "M1 ≼t M2  '[MTS]'" := (MTS_thoroughlyRefines M1 M2) (at level 70, no associativity).


(** *)

Lemma MTS_Soundness
    `(M1 : MTS_TransitionSystem)
    (M2 : MTS_TransitionSystem (MTS_Event M1) (MTS_Modal M1))
    : M1 ≼m M2 [MTS] -> M1 ≼t M2 [MTS].
(* begin hide *)
Proof.
    intro M1_refines_M2.
    destruct M1_refines_M2 as [refines refinement].
    intros I I_implementation.
    destruct I_implementation as [I_precedes_M1 I_implementation].
    split.
    apply (transitivity (Transitive := QO_Transitive MTS_modallyRefines_QuasiOrder) (y := M1)).
    assumption.
    now exists refines.
    assumption.
Qed.
(* end hide *)


(***************************)
(** * Parallel Composition *)
(***************************)


(** *)

(*
Inductive MTS_CompTsn 
    `(M1 : MTS_TransitionSystem)
    (M2 : MTS_TransitionSystem (MTS_Event M1) (MTS_Modal M1))
    `(Op : LOp_Operation (MTS_Event M1))
    : ((MTS_state M1) * (MTS_state M2))%type -> (MTS_Event M1) -> ((MTS_state M1) * (MTS_state M2))%type -> Prop
    := 
        MTS_CompTsn_intro : forall s s' t t' k l kl m,
            MTS_PostByEvent M1 s k s' -> MTS_PostByEvent M2 t k t' -> Op k l kl == m [LSet _] ->
                MTS_CompTsn M1 M2 Op (s, t) m (s', t').
 *)

(*
Inductive MTS_CompTsn 
    `(M1 : MTS_TransitionSystem)
    (M2 : MTS_TransitionSystem (MTS_Event M1) (MTS_Modal M1))
    `(Op : LOp_Operation (MTS_Event M1))
    : Nv_naiveSet (Tsn_Transition ((MTS_state M1) * (MTS_state M2))%type (MTS_Event M1))
    := 
        MTS_CompTsn_intro : forall t1 t2 m kl, t1 ∈ TS_Transition M1 -> t2 ∈ TS_Transition M2 ->
           m == Op (Tsn_label t1) (Tsn_label t2) kl [LSet _] ->
               {| Tsn_source := (Tsn_source t1, Tsn_source t2);                   
                  Tsn_label := m;
                  Tsn_target := (Tsn_target t1, Tsn_target t2) |} ∈ MTS_CompTsn M1 M2 Op. 
*)

(** *)



(** *)

Record MTS_ProdTsn
    `(M1 : MTS_TransitionSystem)
    (M2 : MTS_TransitionSystem (MTS_Event M1) (MTS_Modal M1))
    `(Op : LOp_Operation (MTS_Event M1))
    :=
        MTS_buildProdTsn {
            MTS_leftTsn : TS_Transition M1;
            MTS_rightTsn : TS_Transition M2;
            MTS_compatTsn : POp_defined Op (TS_label MTS_leftTsn) (TS_label MTS_rightTsn) }.

Definition MTS_getProdTsn
     `(M1 : MTS_TransitionSystem)
    (M2 : MTS_TransitionSystem (MTS_Event M1) (MTS_Modal M1))
    `(Op : LOp_Operation (MTS_Event M1))
    (t : MTS_ProdTsn M1 M2 Op)
  := {|
         Tsn_source := (TS_source (MTS_leftTsn _ _ _ t), TS_source (MTS_rightTsn _ _ _ t));
         Tsn_target := (TS_target (MTS_leftTsn _ _ _ t), TS_target (MTS_rightTsn _ _ _ t));
         Tsn_label := Op (TS_label (MTS_leftTsn _ _ _ t)) (TS_label (MTS_rightTsn _ _ _ t)) (MTS_compatTsn _ _ _ t)
      |}.
          
Program Instance MTS_Composition
    `(M1 : MTS_TransitionSystem)
    (M2 : MTS_TransitionSystem (MTS_Event M1) (MTS_Modal M1))
    `(Op : LOp_Operation (MTS_Event M1))
    : MTS_TransitionSystem (MTS_Event M1) (MTS_Modal M1)
    :=
        {|
          MTS_System := TS_buildTransitionSystem (Nv_singleton (MTS_initial M1, MTS_initial M2))
                                                 (MTS_Event M1)
                                                 (MTS_ProdTsn M1 M2 Op) (MTS_getProdTsn M1 M2 Op );
          MTS_Modality t := ((MTS_Modality M1 (MTS_leftTsn _ _ _ t)) ∩ (MTS_Modality M2 (MTS_rightTsn _ _ _ t)))
        |}.
(*Next Obligation.*)
(*    generalize m m0 X0; intros s1 s2 e; clear m m0 X0.
    exact (
        fun s' : prod (MTS_state M1) (MTS_state M2) =>
            match s' with (s1', s2') =>
                forall (t1 : TS_transition M1) (t2 : TS_transition M2) k l, 
                    Tsn_source (projT1 t1) = s1 ->
                    Tsn_label (projT1 t1) = k ->
                    Tsn_target (projT1 t1) = s1' ->
                    Tsn_source (projT1 t2) = s2 ->
                    Tsn_label (projT1 t2) = l ->
                    Tsn_target (projT1 t2) = s2' ->
                    forall kl, (Op k l kl) == e [LSet _]
            end
        ).*)
(*Defined.*)
Next Obligation.
    inversion t.
    admit.
(*    intro mod.
    inversion h.
    inversion x.
    exact ((MTS_Modality M1 t1) ∩ (MTS_Modality M2 t2)).*)
Defined.
     