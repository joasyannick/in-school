(** This library extends the standard library [Coq.Sets.Ensembles],
    and provides the usual mathematical notations of naive set
    theories. *)


Add LoadPath ".." as LSMTS.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.


(****************)
(** * Notations *)
(****************)


(** [naiveSet] is a better name than [Ensemble]. *)

Notation Nv_naiveSet := Ensemble.


(** Some other renamings. *)

Notation Nv_in := In.
Notation Nv_included := Included.
Notation Nv_empty := Empty_set.
Notation Nv_full := Full_set.
Notation Nv_full_intro := Full_intro.
Notation Nv_singleton := Singleton.
Notation Nv_singleton_intro := In_singleton.
Notation Nv_union := Union.
Notation Nv_union_introl := Union_introl.
Notation Nv_union_intror := Union_intror.
Notation Nv_add := Add.
Notation Nv_intersection := Intersection.
Notation Nv_intersection_intro := Intersection_intro.
Notation Nv_couple := Couple.
Notation Nv_couple_introl := Couple_l.
Notation Nv_couple_intror := Couple_r.
Notation Nv_triple := Triple.
Notation Nv_triple_introl := Triple_l.
Notation Nv_triple_introm := Triple_m.
Notation Nv_triple_intror := Triple_r.
Notation Nv_complement := Complement.
Notation Nv_difference := Setminus.
Notation Nv_subtract := Subtract.
Notation Nv_disjoint := Disjoint.
Notation Nv_disjoint_intro := Disjoint_intro.
Notation Nv_notEmpty := Inhabited.
Notation Nv_notEmpty_intro := Inhabited_intro.
Notation Nv_strictlyIncluded := Strict_Included.
Notation Nv_eq := Same_set.
Notation Nv_extensionality := Extensionality_Ensembles.
Notation Nv_finite := Finite.
Notation Nv_empty_finite := Empty_is_finite.
Notation Nv_finite_union := Union_is_finite.
Notation Nv_cardinal := cardinal.
Notation Nv_cardinal_empty := card_empty.
Notation Nv_cardinal_add:= card_add.
Notation Nv_cardinal_invert := cardinal_invert.
Notation Nv_cardinal_elim := cardinal_elim.


(** In most cases, the universe can be considered implicit. *)

Arguments Nv_in {_} _ _.
Arguments Nv_included {_} _ _.
Arguments Nv_empty {_} _.
Arguments Nv_full _ _.
Arguments Nv_full_intro {_} _.
Arguments Nv_singleton {_} _ _.
Arguments Nv_singleton_intro {_} _.
Arguments Nv_union {_} _ _ _.
Arguments Nv_union_introl {_} _ _ _ _.
Arguments Nv_union_intror {_} _ _ _ _.
Arguments Nv_add {_} _ _ _.
Arguments Nv_intersection {_} _ _ _.
Arguments Nv_intersection_intro {_} _ _ _ _ _.
Arguments Nv_couple {_} _ _ _.
Arguments Nv_couple_introl {_} _ _.
Arguments Nv_couple_intror {_} _ _.
Arguments Nv_triple {_} _ _ _ _.
Arguments Nv_triple_introl {_} _ _ _.
Arguments Nv_triple_introm {_} _ _ _.
Arguments Nv_triple_intror {_} _ _ _.
Arguments Nv_complement {_} _ _.
Arguments Nv_difference {_} _ _ _.
Arguments Nv_subtract {_} _ _ _.
Arguments Nv_disjoint {_} _ _.
Arguments Nv_disjoint_intro {_} _ _ _.
Arguments Nv_notEmpty {_} _.
Arguments Nv_notEmpty_intro {_} _ _ _.
Arguments Nv_strictlyIncluded {_} _ _.
Arguments Nv_eq {_} _ _.
Arguments Nv_extensionality {_} _ _ _.
Arguments Nv_finite {_} _.
Arguments Nv_empty_finite {_}.
Arguments Nv_finite_union {_} _ _ _ _.
Arguments Nv_cardinal {_} _ _.
Arguments Nv_cardinal_empty {_}.
Arguments Nv_cardinal_add {_} _ _ _ _ _.
Arguments Nv_cardinal_invert {_} _ _ _.
Arguments Nv_cardinal_elim {_} _ _ _.


(** Let us take advantage of Unicode. *)

Notation "x ∈ E" := (Nv_in E x) (at level 70, no associativity).
Notation "x ∉ E" := (~(Nv_in E x)) (at level 70, no associativity).
Notation "S ⊆ T" := (Nv_included S T) (at level 70, no associativity).
Notation "S ⊈ T" := (~(Nv_included S T)) (at level 70, no associativity).
Notation "∅" := Nv_empty.
Notation "'Nv{' x , .. , y '}'" := (Nv_add .. (Nv_add ∅ x) .. y).
Notation "S ∪ T" := (Nv_union S T) (at level 50, left associativity).
Notation "S ∩ T" := (Nv_intersection S T) (at level 40, left associativity).
Notation "∁ S" := (Nv_complement S) (at level 35, right associativity).
Notation "S \ T" := (Nv_difference S T) (at level 50, left associativity).
Notation "S ⊂ T" := (Nv_strictlyIncluded S T) (at level 70, no associativity).
Notation "S == T  '[Nv]'" := (Nv_eq S T) (at level 70, no associativity).


(**************************)
(** * Product of Two Sets *)
(**************************)


Inductive Nv_product
    {U V : Type}
    (S : Nv_naiveSet U)
    (T : Nv_naiveSet V)
    : Nv_naiveSet (U * V)
    :=
        Nv_product_intro : forall (x : U) (y : V),
            x ∈ S -> y ∈ T -> (x, y) ∈ (Nv_product S T).

Notation "S × T" := (Nv_product S T) (at level 40, left associativity).