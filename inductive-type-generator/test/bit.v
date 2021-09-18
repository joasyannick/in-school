Module CoBit.
	CoInductive bit  :=
		  Zero 
		| One .


	Definition isZero  (__input : bit) : Prop :=
		match __input with
			  Zero  => True
			| _ => False
		end.


	Definition isOne  (__input : bit) : Prop :=
		match __input with
			  One  => True
			| _ => False
		end.


	


	
End CoBit.





Module Bit.
	Parameter Label : Type.

	CoInductive bit  :=
		  Zero 
		| One 
		| Labeled (__tag : Label) (__data : bit)
		| Reference (__tag : Label).


	Definition isZero  (__input : bit) : Prop :=
		match __input with
			  Zero  => True
			| _ => False
		end.


	Definition isOne  (__input : bit) : Prop :=
		match __input with
			  One  => True
			| _ => False
		end.


	Definition isLabeled  (__input : bit) : Prop :=
		match __input with
			  Labeled _ _ => True
			| _ => False
		end.


	Definition isReference  (__input : bit) : Prop :=
		match __input with
			  Reference _ => True
			| _ => False
		end.


	


	


	Definition getLabeled__tag  (__input : bit) : isLabeled __input -> Label :=
		match __input with
			  Labeled __tag _ => fun __precondition => __tag
			| _ => fun __precondition => match __precondition with end
		end.


	Definition getLabeled__data  (__input : bit) : isLabeled __input -> bit :=
		match __input with
			  Labeled _ __data => fun __precondition => __data
			| _ => fun __precondition => match __precondition with end
		end.


	Definition getReference__tag  (__input : bit) : isReference __input -> Label :=
		match __input with
			  Reference __tag => fun __precondition => __tag
			| _ => fun __precondition => match __precondition with end
		end.


	Inductive subterm  (__root : bit) : bit -> Type :=
		  SubRoot : subterm __root __root
		| SubLabeled : forall __tag __data, subterm __root (Labeled  __tag __data) -> subterm __root __data.
End Bit.