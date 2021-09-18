type comparator (t : Type) =
      Equals (test : t -> t -> Prop)
    | Greater (test : t -> t -> Prop)
    | Lesser (test : t -> t -> Prop)
