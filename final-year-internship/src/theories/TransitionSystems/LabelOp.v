(** *)


Add LoadPath ".." as LSMTS.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Setoids.Setoid.
Require Import LSMTS.Classes.DecidableRelation.
Require Import LSMTS.Classes.PartialOp.
Require Import LSMTS.Classes.Order.
Require Import LSMTS.TransitionSystems.LabelSet.


(***********************)
(** * Label Operations *)
(***********************)


(** *)

Class LOp_Operation
    `(L : LSet_LabelSet)
    (defined : relation L)
    : Type
    :=
        LOp_buildOperation {

(** *)

            LOp_LabelSet := L;
            LOp_defined := defined;

(** *)

            LOp_Op : POp_PartialOp defined (LSet_Equivalence L)
        }.


(** *)

Arguments LOp_buildOperation {_ _ _} _ _ _.


(** *)

Arguments LOp_LabelSet {_ _ _ _ _} _.
Arguments LOp_defined {_ _ _ _ _} _ _ _.
Arguments LOp_Op {_ _ _ _ _} _.


(** *)

Generalizable Variables L defined.


(** *)

Coercion LOp_Op : LOp_Operation >-> POp_PartialOp.


(** *)

Definition LOp_prod_defined
    `(Op1 : LOp_Operation)
    `(Op2 : LOp_Operation)
    : relation (LOp_LabelSet Op1 ⊗ LOp_LabelSet Op2)
    :=
        fun (p1 p2 : (LOp_LabelSet Op1) ⊗ (LOp_LabelSet Op2)) =>
            match (p1, p2) with
            |   (LSet_bottomPair, _) => True 
            |   (_, LSet_bottomPair) => True 
            |   (LSet_pair k1 k2 _ _, LSet_pair l1 l2 _ _) =>
                    LOp_defined Op1 k1 l1 /\ LOp_defined Op2 k2 l2
            end.  


(** *)

Instance LOp_prod
    `(Op1 : LOp_Operation)
    `(Op2 : LOp_Operation)
    : LOp_Operation _ (LOp_prod_defined Op1 Op2).
(* begin hide *)
Proof.
    repeat split.
    exact (fun p1 p2 =>
        match (p1, p2) as p return (LOp_prod_defined Op1 Op2) (fst p) (snd p) -> _ with
            |   (LSet_bottomPair, _) => fun _ => LSet_bottomPair
            |   (_, LSet_bottomPair) => fun _ => LSet_bottomPair
            |   (LSet_pair k1 k2 k1nb k2nb, LSet_pair l1 l2 l1nb l2nb) => fun H =>
                    match DRel_decidable (LSet_eq_Decidable L) (Op1 k1 l1 (proj1 H)) (LSet_bottom _) with
                    |   left _ => LSet_bottom _
                    |   right h1 =>
                            match DRel_decidable (LSet_eq_Decidable L0) (Op2 k2 l2 (proj2 H)) (LSet_bottom _) with
                            |   left _ => LSet_bottom _
                            |   right h2 => LSet_pair _ _ h1 h2
                            end
                    end
        end).
Defined.
(* end hide *)


(** *)

Class LOp_Commutative
    `(Op : LOp_Operation)
    : Prop
    :=
        LOp_buildCommutative {

(** *)

            LOp_Commutative_Operation := Op;

(** *)

            LOp_commutativity : POp_Commutative (LOp_Op Op)
        }.


(** *)

Arguments LOp_buildCommutative {_ _ _ _ _ _} _.


(** *)

Arguments LOp_commutativity {_ _ _ _ _ _} _.


(** *)

Generalizable Variables Op.


(** *)

Coercion LOp_Commutative_Operation : LOp_Commutative >-> LOp_Operation.


(** *)

Instance LOp_prod_Commutative
    `(Op1 : LOp_Commutative)
    `(Op2 : LOp_Commutative)
    : LOp_Commutative (LOp_prod Op1 Op2).
(* begin hide *)
Admitted.
(*
Next Obligation.
    repeat intro.
    destruct x, y; simpl in *; auto; destruct H; split; auto; apply (POp_commutativity1); auto.
    destruct x, y; simpl in *; auto; destruct H; split; auto; apply (LOp_commutable); auto.
Qed.
Next Obligation.
  intros; destruct x,y; simpl; try reflexivity.
  do 3 (match goal with
      |- context [match ?cnd with _ => _ end] => destruct cnd; simpl; auto; try reflexivity
  end).                                                               
  rewrite (LOp_commutativity Op1) in l.
  exfalso.
  rewrite <- l in n3.
  apply n3.
  rewrite (proof_irrelevance _ _ (proj1 (LOp_commutable Op1 l1 l0) (proj1 pre))).
  reflexivity.
  (match goal with
      |- context [match ?cnd with _ => _ end] => destruct cnd; simpl; auto; try reflexivity
  end).                                                               
  rewrite (LOp_commutativity Op2) in l.
  exfalso.
  rewrite <- l in n5.
  apply n5.
  rewrite (proof_irrelevance _ _ (proj1 (LOp_commutable Op2 l2 l3) (proj2 pre))).
  reflexivity.
  rewrite (LOp_commutativity Op1) in l.
  exfalso.
  rewrite <- l in n3.
  apply n3.
  symmetry.
  rewrite (proof_irrelevance _ _ (proj1 pre) ).
  reflexivity.
  (match goal with
      |- context [match ?cnd with _ => _ end] => destruct cnd; simpl; auto; try reflexivity
  end).                                                               
  rewrite (LOp_commutativity Op2) in l.
  exfalso.
  rewrite <- l in n4.
  apply n4.
  symmetry.
  rewrite (proof_irrelevance _ _ (proj2 pre) ).
  reflexivity.
  apply LSet_pair_equality; auto.
  rewrite (LOp_commutativity Op1 l0 l1).
  symmetry; rewrite (proof_irrelevance _ _ (proj1 pre) ); reflexivity.
  rewrite (LOp_commutativity Op2 l3 l2).
  symmetry; rewrite (proof_irrelevance _ _ (proj2 pre) ); reflexivity.
Qed.
*)
(* end hide *)


(** *)

Class LOp_Associative
    `(Op : LOp_Operation)
    : Prop
    :=
        LOp_buildAssociative {

(** *)

            LOp_Associative_Operation := Op;

(** *)

            LOp_associativity : POp_Associative (LOp_Op Op)
        }.


(** *)

Arguments LOp_buildAssociative {_ _ _ _ _ _} _.


(** *)

Arguments LOp_associativity {_ _ _ _ _ _} _.


(** *)

Coercion LOp_Associative_Operation : LOp_Associative >-> LOp_Operation.


(** *)

Instance LOp_prod_Associative
    `(Op1 : LOp_Commutative)
    `(Op2 : LOp_Commutative)
    : LOp_Associative (LOp_prod Op1 Op2).
(* begin hide *)
Admitted.
(* end hide *)


(** *)

Class LOp_Compositional
    `(Op : LOp_Operation)
    : Prop
    :=
        LOp_buildCompositional {

(** *)

            LOp_Compositional_Operation := Op;

(** *)

            LOp_compositionality1 :
                forall k l k' l', k ≼ k' [LSet _] -> l ≼ l' [LSet _] ->
                    POp_defined Op k l -> POp_defined Op k' l';

(** *)

            LOp_compositionality2 :
                forall k l k' l', k ≼ k' [LSet _] -> l ≼ l' [LSet _] ->
                    POp_defined Op k' l' -> POp_defined Op k l;

(** *)

            LOp_compositionality3 :
                forall k k' l l' kk' ll' kl,
                    (Op k l kl) ≼ (Op k' l' (LOp_compositionality1 k l k' l' kk' ll' kl)) [LSet _]
        }.


(** *)

Arguments LOp_buildCompositional {_ _ _ _ _ _} _ _ _.


(** *)

Arguments LOp_Compositional_Operation {_ _ _ _ _ _} _.
Arguments LOp_compositionality1 {_ _ _ _ _ _} _ _ _ _ _ _ _ _.
Arguments LOp_compositionality2 {_ _ _ _ _ _} _ _ _ _ _ _ _ _.
Arguments LOp_compositionality3 {_ _ _ _ _ _} _ _ _ _ _ _ _ _.


(** *)

Coercion LOp_Compositional_Operation : LOp_Compositional >-> LOp_Operation.


(** *)

Instance LOp_prod_Compositional
    `(Op1 : LOp_Compositional)
    `(Op2 : LOp_Compositional)
    : LOp_Compositional (LOp_prod Op1 Op2).
(* begin hide *)
Admitted.
(* end hide *)
