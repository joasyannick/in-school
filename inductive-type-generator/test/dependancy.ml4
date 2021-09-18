type dependancy (s : Type) (t : Type) =
    Without (first : s) (second : t)
  | With (first : Type) (second : first)
