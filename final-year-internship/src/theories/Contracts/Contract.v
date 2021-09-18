(** *)



Add LoadPath ".." as LSMTS.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Import LSMTS.Sets.NaiveSet.
Require Import LSMTS.Classes.PartialOp.
Require Import LSMTS.Classes.Order.


(** *)

Class Cct_Theory
    (contract : Type)
    {design : Type}
    {design_eq : relation design}
    (design_Equivalence : Equivalence design_eq)
    (legal : design -> Prop)
    {defined : relation design}
    (designComp : POp_PartialOp defined design_Equivalence)
    (implements : design -> contract -> Prop)
    :=
        Cct_buildTheory {

(** *)

            Cct_contract := contract;
            Cct_design := design;
            Cct_design_eq := design_eq;
            Cct_design_Equivalence := design_Equivalence;
            Cct_legal := legal;
            Cct_designComp := designComp;
            Cct_implements := implements;

(** *)

            Cct_Implementation (C : contract) : Nv_naiveSet design :=
                fun D : design => implements D C;

(** *)

            Cct_refines (C1 C2 : contract) : Prop :=
                Cct_Implementation C1 ⊆ Cct_Implementation C2


(** *)
               

(** *)

                                   
        }.


Generalizable Variables contract design design_eq design_Equivalence legal designComp implements.

Instance Cct_refines_QuasiOrder
    `(Th : Cct_Theory)
    : QO_QuasiOrder Cct_refines.
Admitted.

Instance Cct_refines_PartialOrder
    `(Th : Cct_Theory)
    : PO_PartialOrder (QO_eq (Cct_refines_QuasiOrder _)) Cct_refines
    := QO_PartialOrder (Cct_refines_QuasiOrder _).





(*
Instance CCT_conjunction
    `(Th : CCT_Theory)
    :  PF_PartialOperation (CCT_refines_PartialOrder Th) :=
                {| PF_domain x y := PO_has_glb _ Nv{x, y};
                   PF_operator x y h := PO_getGlb _ Nv{x, y} h |}.

Definition CCT_prodSpec
    `(Th : CCT_Theory)
    (C1 C2 : CCT_contract)
    : Nv_naiveSet contract
    :=
      fun C : (CCT_contract (CCT_Theory := Th)) =>
        forall (M1 M2 : CCT_design (CCT_Theory := Th)) h, CCT_implements M1 C1 -> CCT_implements M2 C2 ->
            CCT_implements (CCT_designProd (CCT_Theory := Th) M1 M2 h) C.

           
 Instance CCT_contractProd
    `(Th : CCT_Theory)
    :  PF_PartialOperation (CCT_refines_PartialOrder Th) :=
                {| PF_domain x y := PO_has_least _ (CCT_prodSpec Th x y);
                   PF_operator x y h := PO_getLeast _ (CCT_prodSpec Th x y) h |}.

*)