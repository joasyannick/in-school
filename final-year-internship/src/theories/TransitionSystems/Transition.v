(** This library provides an implementation of the notion of
    _transition_. Within a _transition system_ [M], a _transition_ is
    a triple [(source, label, target)] which means that the system
    modelled by [M] moves to the _state_ [target] if the _event_
    [label] occurs while it is in the _state_ [source]. *)

Class Tsn_Transition
    (state event : Type)
    : Type
    :=
        Tsn_buildTransition {

(** There is a getter for each parameter. *)

            Tsn_state := state;
            Tsn_event := event;

(** The field [Tsn_source] is the _source_ of the transition. *)
            
            Tsn_source : state;

(** The field [Tsn_label] is the _label_ of the transition. *)
            
            Tsn_label : event;

(** The field [Tsn_target] is the _target_ of the transition. *)

            Tsn_target : state
        }.


(** The fields [Tsn_source], [Tsn_label], and [Tsn_target] are the
    only arguments needed explicitly to build a transition. *)

Arguments Tsn_buildTransition {_ _} _ _ _.


(** We prefer to have the transition explicit in every method. *)

Arguments Tsn_state {_ _} _.
Arguments Tsn_event {_ _} _.
Arguments Tsn_source {_ _} _.
Arguments Tsn_label {_ _} _.
Arguments Tsn_target {_ _} _.


(** The two parameters [state] and [event] can be automatically
    generated and declared implicit with [`(..)] or [`{..}]. *)

Generalizable Variables state event.