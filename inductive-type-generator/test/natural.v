Module CoNatural.
	CoInductive natural  :=
		  Zero 
		| Successor (predecessor : natural).


	Definition isZero  (__input : natural) : Prop :=
		match __input with
			  Zero  => True
			| _ => False
		end.


	Definition isSuccessor  (__input : natural) : Prop :=
		match __input with
			  Successor _ => True
			| _ => False
		end.


	


	Definition getSuccessorPredecessor  (__input : natural) : isSuccessor __input -> natural :=
		match __input with
			  Successor predecessor => fun __precondition => predecessor
			| _ => fun __precondition => match __precondition with end
		end.
End CoNatural.





Module Natural.
	Parameter Label : Type.

	CoInductive natural  :=
		  Zero 
		| Successor (predecessor : natural)
		| Labeled (__tag : Label) (__data : natural)
		| Reference (__tag : Label).


	Definition isZero  (__input : natural) : Prop :=
		match __input with
			  Zero  => True
			| _ => False
		end.


	Definition isSuccessor  (__input : natural) : Prop :=
		match __input with
			  Successor _ => True
			| _ => False
		end.


	Definition isLabeled  (__input : natural) : Prop :=
		match __input with
			  Labeled _ _ => True
			| _ => False
		end.


	Definition isReference  (__input : natural) : Prop :=
		match __input with
			  Reference _ => True
			| _ => False
		end.


	


	Definition getSuccessorPredecessor  (__input : natural) : isSuccessor __input -> natural :=
		match __input with
			  Successor predecessor => fun __precondition => predecessor
			| _ => fun __precondition => match __precondition with end
		end.


	Definition getLabeled__tag  (__input : natural) : isLabeled __input -> Label :=
		match __input with
			  Labeled __tag _ => fun __precondition => __tag
			| _ => fun __precondition => match __precondition with end
		end.


	Definition getLabeled__data  (__input : natural) : isLabeled __input -> natural :=
		match __input with
			  Labeled _ __data => fun __precondition => __data
			| _ => fun __precondition => match __precondition with end
		end.


	Definition getReference__tag  (__input : natural) : isReference __input -> Label :=
		match __input with
			  Reference __tag => fun __precondition => __tag
			| _ => fun __precondition => match __precondition with end
		end.


	Inductive subterm  (__root : natural) : natural -> Type :=
		  SubRoot : subterm __root __root
		| SubLabeled : forall __tag __data, subterm __root (Labeled  __tag __data) -> subterm __root __data
		| SubSuccessorPredecessor : forall predecessor, subterm __root (Successor  predecessor) -> subterm __root predecessor.
End Natural.