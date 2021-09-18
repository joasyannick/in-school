type tree (t : Type) =
    Leaf
  | Node (node : tree t * t * tree t)
