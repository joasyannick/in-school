type stack (t : Type) =
      Empty
    | Push (top : t) (pop : stack t)
