Module CoColor.
	CoInductive color  :=
		  Color (red : nat) (green : nat) (blue : nat).


	Definition isColor  (__input : color) : Prop :=
		match __input with
			  Color _ _ _ => True
		end.


	Definition getColorRed  (__input : color) : isColor __input -> nat :=
		match __input with
			  Color red _ _ => fun __precondition => red
		end.


	Definition getColorGreen  (__input : color) : isColor __input -> nat :=
		match __input with
			  Color _ green _ => fun __precondition => green
		end.


	Definition getColorBlue  (__input : color) : isColor __input -> nat :=
		match __input with
			  Color _ _ blue => fun __precondition => blue
		end.
End CoColor.





Module Color.
	Parameter Label : Type.

	CoInductive color  :=
		  Color (red : nat) (green : nat) (blue : nat)
		| Labeled (__tag : Label) (__data : color)
		| Reference (__tag : Label).


	Definition isColor  (__input : color) : Prop :=
		match __input with
			  Color _ _ _ => True
			| _ => False
		end.


	Definition isLabeled  (__input : color) : Prop :=
		match __input with
			  Labeled _ _ => True
			| _ => False
		end.


	Definition isReference  (__input : color) : Prop :=
		match __input with
			  Reference _ => True
			| _ => False
		end.


	Definition getColorRed  (__input : color) : isColor __input -> nat :=
		match __input with
			  Color red _ _ => fun __precondition => red
			| _ => fun __precondition => match __precondition with end
		end.


	Definition getColorGreen  (__input : color) : isColor __input -> nat :=
		match __input with
			  Color _ green _ => fun __precondition => green
			| _ => fun __precondition => match __precondition with end
		end.


	Definition getColorBlue  (__input : color) : isColor __input -> nat :=
		match __input with
			  Color _ _ blue => fun __precondition => blue
			| _ => fun __precondition => match __precondition with end
		end.


	Definition getLabeled__tag  (__input : color) : isLabeled __input -> Label :=
		match __input with
			  Labeled __tag _ => fun __precondition => __tag
			| _ => fun __precondition => match __precondition with end
		end.


	Definition getLabeled__data  (__input : color) : isLabeled __input -> color :=
		match __input with
			  Labeled _ __data => fun __precondition => __data
			| _ => fun __precondition => match __precondition with end
		end.


	Definition getReference__tag  (__input : color) : isReference __input -> Label :=
		match __input with
			  Reference __tag => fun __precondition => __tag
			| _ => fun __precondition => match __precondition with end
		end.


	Inductive subterm  (__root : color) : color -> Type :=
		  SubRoot : subterm __root __root
		| SubLabeled : forall __tag __data, subterm __root (Labeled  __tag __data) -> subterm __root __data.
End Color.