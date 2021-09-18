(** This library provides an implementation of the theory of
    _transition systems_, an important tool to model the behaviors
    of computing systems. *)


Add LoadPath ".." as LSMTS.
Require Import LSMTS.Sets.NaiveSet.
Require Import LSMTS.TransitionSystems.Transition.


(*************************)
(** * Transition Systems *)
(*************************)


(** A _transition system_ models a system whose _state_ is influenced
    by some _events_. It consists of: (1) a set [state] of _states_;
    (2) a subset [Initial] of _initial states_; (3) a set [event] of
    _events_; and (4) a _transition relation_ [PostByEvent] which can
    be viewed as a function that returns the set of _direct successor
    states_ reachable in one step from a given state by a given event. *)

Class TS_TransitionSystem
    {state : Type}
    (Initial : Nv_naiveSet state)
    (event : Type)
    : Type
    :=
        TS_buildTransitionSystem {

(** There is a getter for each parameter. *)

            TS_state := state;
            TS_Initial := Initial;
            TS_event := event;

(** *)

            TS_Transition : Type;

(** *)

            TS_getTransition : TS_Transition -> Tsn_Transition state event;
            TS_source t := Tsn_source (TS_getTransition t);
            TS_label t := Tsn_label (TS_getTransition t);
            TS_target t := Tsn_target (TS_getTransition t);

(** *)
            
            TS_PostByEvent : state -> event -> Nv_naiveSet state :=
                    fun s e s' => exists t,
                        TS_source t = s /\ TS_label t = e /\ TS_target t = s';
                                    
(** The method [TS_PreByEvent] returns the set of states that are
    the _direct predecessors_ of a state [s'] with respect to an
    event [e]. *)

            TS_PreByEvent (e : event) (s' : state) : Nv_naiveSet state :=
                fun (s : state) => exists t,
                    TS_source t = s /\ TS_label t = e /\ TS_target t = s';

(** The method [TS_Post] returns the set of states that are the
    direct successors of a state [s]. *)

            TS_Post (s : state) : Nv_naiveSet state :=
                fun (s' : state) =>
                    exists e : event, s' ∈ (TS_PostByEvent s e);

(** The method [TS_Pre] returns the set of states that are the direct
    predecessors of a state [s']. *)

            TS_Pre (s' : state) : Nv_naiveSet state :=
                fun (s : state) =>
                    exists e : event, s ∈ (TS_PreByEvent e s');


(** The method [TS_PostByEventAndTransitions] returns the set of
    states that are the direct successors of a state [s], with
    respect to an event [e] and a set of transitions [T]. *)
(*
            TS_PostByEventAndTransitions
                (s : state)
                (e : event)
                (T : Nv_naiveSet (Tsn_Transition state event))
                (T_subset : T ⊆ TS_Transition)
                : Nv_naiveSet state
                :=
                    fun (s' : state) =>
                        (Tsn_buildTransition s e s') ∈ T;
*)
(** The method [TS_PreByEventAndTransitions] returns the set of
    states that are the direct predecessors of a state [s'], with
    respect to an event [e] and a set of transitions [T]. *)
(*
            TS_PreByEventAndTransitions
                (e : event)
                (s' : state)
                (T : Nv_naiveSet (Tsn_Transition state event))
                (T_subset : T ⊆ TS_Transition)
                : Nv_naiveSet state
                :=
                    fun (s : state) =>
                        (Tsn_buildTransition s e s') ∈ T;
*)
(** The method [TS_postByTransitions] returns the set of states that
    are the direct successors of a state [s], with respect to a set
    of transitions [T]. *)
(*
            TS_PostByTransitions
                (s : state)
                (T : Nv_naiveSet (Tsn_Transition state event))
                (T_subset : T ⊆ TS_Transition)
                : Nv_naiveSet state
                :=
                    fun (s' : state) => exists e : event,
                        s' ∈ (TS_PostByEventAndTransitions s e T T_subset);
*)
(** The method [TS_PreByTransitions] returns the set of states that
    are the direct predecessors of a state [s'], with respect to a
    set of transitions [T]. *)
(*
            TS_PreByTransitions
                (s' : state)
                (T : Nv_naiveSet (Tsn_Transition state event))
                (T_subset : T ⊆ TS_Transition)
                : Nv_naiveSet state
                :=
                    fun (s : state) => exists e : event,
                        s ∈ (TS_PreByEventAndTransitions e s' T T_subset);
*)
(** Given a set of transitions [T], the method [TS_Target] returns
    the set of state that are the targets of a transition belonging
    to [T]. *)
(*
            TS_Target
                (T : Nv_naiveSet (Tsn_Transition state event))
                (T_subset : T ⊆ TS_Transition)
                : Nv_naiveSet state
                :=
                    fun (s' : state) => exists s : state,
                        s' ∈ (TS_PostByTransitions s T T_subset);
*)
(** Given a set of transitions [T], the method [TS_Source] returns
    the set of state that are the sources of a transition belonging
    to [T]. *)
(*
            TS_Source
                (T : Nv_naiveSet (Tsn_Transition state event))
                (T_subset : T ⊆ TS_Transition)
                : Nv_naiveSet state
                :=
                    fun (s : state) => exists s' : state,
                        s ∈ (TS_PreByTransitions s' T T_subset);
*)
(** The method [TS_Outgoing] returns the set of transitions whose
    sources are in a given set of states [S]. *)

            TS_Outgoing
                (S : Nv_naiveSet state)
                : Nv_naiveSet (Tsn_Transition state event)
                :=
                    fun (t : Tsn_Transition state event) =>
                        (Tsn_source t) ∈ S;

(** The method [TS_Incoming] returns the set of transitions whose
    targets are in a given set of states [S]. *)

            TS_Incoming
                (S : Nv_naiveSet state)
                : Nv_naiveSet (Tsn_Transition state event)
                :=
                    fun (t : Tsn_Transition state event) =>
                        (Tsn_target t) ∈ S;

(** The method [TS_Terminal] returns the set of _terminal states_.
    A _terminal state_ is a state without any outgoing transitions. *)

            TS_Terminal : Nv_naiveSet state :=
                fun (s : state) =>
                    forall (e : event) (s' : state), s' ∉ (TS_PostByEvent s e);

(** The method [TS_Deterministic] defines the set of
    _deterministic states_. A _deterministic state_ is a state
    with at most one outgoing transition per event. *)

            TS_Deterministic : Nv_naiveSet state :=
                fun (s : state) =>
                    forall (e : event) (n : nat),
                        Nv_cardinal (TS_PostByEvent s e) n -> n <= 1;

(** The predicate [TS_deterministic] defines the notion of
    _deterministic transition systems_. A _deterministic transition
    system_ has at most one initial state, and is such that all its
    states states are deterministic. *)

            TS_deterministic : Prop :=
                (forall (n : nat), Nv_cardinal Initial n -> n <= 1) /\
                    (forall (s : state), s ∈ TS_Deterministic)

        }.


(** *)

Arguments TS_buildTransitionSystem {_} _ _ _ _.


(** We prefer to have the transition system explicit in every method. *)

Arguments TS_state {_ _ _} _.
Arguments TS_Initial {_ _ _} _ _.
Arguments TS_event {_ _ _} _.
Arguments TS_Transition {_ _ _} _.
Arguments TS_source {_ _ _ _} _.
Arguments TS_label {_ _ _ _} _.
Arguments TS_target {_ _ _ _} _.
Arguments TS_PostByEvent {_ _ _} _ _ _ _.
Arguments TS_PreByEvent {_ _ _} _ _ _ _.
Arguments TS_Post {_ _ _} _ _ _.
Arguments TS_Pre {_ _ _} _ _ _.
Arguments TS_Outgoing {_ _ _} _ _ _.
Arguments TS_Incoming {_ _ _} _ _ _.
Arguments TS_Terminal {_ _ _} _ _.
Arguments TS_Deterministic {_ _ _} _ _.
Arguments TS_deterministic {_ _ _} _.


(** The four parameters can be automatically generated and declared
    implicit with [`(..)] or [`{..}]. *)

Generalizable Variables Initial event.


(****************)
(** * Behaviors *)
(****************)


(** The type [TS_sequence] is the type of possibly infinite
    alternating sequence of states and events. If the sequence is
    finite, it ends with a state. *)

CoInductive TS_sequence
    `(M : TS_TransitionSystem)
    : Type
    :=
        |   TS_end (s : TS_state M)
        |   TS_seq (s : TS_state M) (e : TS_event M) (next : TS_sequence M).

Arguments TS_end {_ _ _ _} _.
Arguments TS_seq {_ _ _ _} _ _ _.


(** The function [TS_start] returns the starting state of a
    [TS_sequence]. *)

Definition TS_start
    `{M : TS_TransitionSystem}
    (ς : TS_sequence M)
    : state
    :=
        match ς with
        |   TS_end s => s
        |    TS_seq s _ _ => s
        end.


(** The predicate [TS_fragmentFrom] says whether a [TS_sequence]
    describes a _behavior fragment_ of the transition system [M].
    A _behavior fragment_ is a finite [TS_sequence] shaped according
    to the transition relation [PostByEvent]. *)

Inductive TS_fragmentFrom
    `(M : TS_TransitionSystem)
    (s : state)
    : TS_sequence M -> Prop
    :=
        |   TS_fragment_end : TS_fragmentFrom M s (TS_end s)
        |   TS_fragment_seq :
                forall (e : TS_event M) (s' : TS_state M) (ς : TS_sequence M),
                    s' ∈ (TS_PostByEvent M s e) -> TS_fragmentFrom M s' ς ->
                        TS_fragmentFrom M s (TS_seq s e ς).


(** The predicate [TS_fragment] says whether a [TS_sequence]
    is an _initial_ behavior fragment, that is, a behavior fragment
    whose starting state is an initial state. *)

Inductive TS_fragment
    `(M : TS_TransitionSystem)
    (ς : TS_sequence M)
    : Prop
    :=
        TS_initial_fragment :
            (TS_start ς) ∈ (TS_Initial M) -> TS_fragmentFrom M (TS_start ς) ς ->
                TS_fragment M ς.


(** The predicate [TS_behaviorFrom] defines the notion of _maximal_
    behavior fragment. A _maximal_ behavior fragment is either a
    finite behavior fragment whose last state is terminal, or
    an infinite behavior fragment. *)

CoInductive TS_behaviorFrom
    `(M : TS_TransitionSystem)
    (s : state)
    : TS_sequence M -> Prop
    :=
        |   TS_behavior_end : s ∈ (TS_Terminal M) -> TS_behaviorFrom M s (TS_end s)
        |   TS_behavior_seq :
                forall (e : TS_event M) (s' : TS_state M) (ς : TS_sequence M),
                    s' ∈ (TS_PostByEvent M s e) -> TS_behaviorFrom M s' ς ->
                        TS_behaviorFrom M s (TS_seq s e ς).


(** The predicate [TS_behavior] says whether a [TS_sequence]
    is an initial and maximal behavior fragment. *)

Inductive TS_behavior
    `(M : TS_TransitionSystem)
    (ς : TS_sequence M)
    : Prop
    :=
        TS_initial_behavior :
            (TS_start ς) ∈ (TS_Initial M) -> TS_behaviorFrom M (TS_start ς) ς ->
                TS_behavior M ς.
