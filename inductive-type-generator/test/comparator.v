Module CoComparator.
	CoInductive comparator (t : Type) :=
		  Equals (test : t -> t -> Prop)
		| Greater (test : t -> t -> Prop)
		| Lesser (test : t -> t -> Prop).


	Definition isEquals {t: Type} (__input : comparator t) : Prop :=
		match __input with
			  Equals _ => True
			| _ => False
		end.


	Definition isGreater {t: Type} (__input : comparator t) : Prop :=
		match __input with
			  Greater _ => True
			| _ => False
		end.


	Definition isLesser {t: Type} (__input : comparator t) : Prop :=
		match __input with
			  Lesser _ => True
			| _ => False
		end.


	Definition getEqualsTest {t: Type} (__input : comparator t) : isEquals __input -> t -> t -> Prop :=
		match __input with
			  Equals test => fun __precondition => test
			| _ => fun __precondition => match __precondition with end
		end.


	Definition getGreaterTest {t: Type} (__input : comparator t) : isGreater __input -> t -> t -> Prop :=
		match __input with
			  Greater test => fun __precondition => test
			| _ => fun __precondition => match __precondition with end
		end.


	Definition getLesserTest {t: Type} (__input : comparator t) : isLesser __input -> t -> t -> Prop :=
		match __input with
			  Lesser test => fun __precondition => test
			| _ => fun __precondition => match __precondition with end
		end.
End CoComparator.





Module Comparator.
	Parameter Label : Type.

	CoInductive comparator (t : Type) :=
		  Equals (test : t -> t -> Prop)
		| Greater (test : t -> t -> Prop)
		| Lesser (test : t -> t -> Prop)
		| Labeled (__tag : Label) (__data : comparator t)
		| Reference (__tag : Label).


	Definition isEquals {t: Type} (__input : comparator t) : Prop :=
		match __input with
			  Equals _ => True
			| _ => False
		end.


	Definition isGreater {t: Type} (__input : comparator t) : Prop :=
		match __input with
			  Greater _ => True
			| _ => False
		end.


	Definition isLesser {t: Type} (__input : comparator t) : Prop :=
		match __input with
			  Lesser _ => True
			| _ => False
		end.


	Definition isLabeled {t: Type} (__input : comparator t) : Prop :=
		match __input with
			  Labeled _ _ => True
			| _ => False
		end.


	Definition isReference {t: Type} (__input : comparator t) : Prop :=
		match __input with
			  Reference _ => True
			| _ => False
		end.


	Definition getEqualsTest {t: Type} (__input : comparator t) : isEquals __input -> t -> t -> Prop :=
		match __input with
			  Equals test => fun __precondition => test
			| _ => fun __precondition => match __precondition with end
		end.


	Definition getGreaterTest {t: Type} (__input : comparator t) : isGreater __input -> t -> t -> Prop :=
		match __input with
			  Greater test => fun __precondition => test
			| _ => fun __precondition => match __precondition with end
		end.


	Definition getLesserTest {t: Type} (__input : comparator t) : isLesser __input -> t -> t -> Prop :=
		match __input with
			  Lesser test => fun __precondition => test
			| _ => fun __precondition => match __precondition with end
		end.


	Definition getLabeled__tag {t: Type} (__input : comparator t) : isLabeled __input -> Label :=
		match __input with
			  Labeled __tag _ => fun __precondition => __tag
			| _ => fun __precondition => match __precondition with end
		end.


	Definition getLabeled__data {t: Type} (__input : comparator t) : isLabeled __input -> comparator t :=
		match __input with
			  Labeled _ __data => fun __precondition => __data
			| _ => fun __precondition => match __precondition with end
		end.


	Definition getReference__tag {t: Type} (__input : comparator t) : isReference __input -> Label :=
		match __input with
			  Reference __tag => fun __precondition => __tag
			| _ => fun __precondition => match __precondition with end
		end.


	Inductive subterm {t: Type} (__root : comparator t) : comparator t -> Type :=
		  SubRoot : subterm __root __root
		| SubLabeled : forall __tag __data, subterm __root (Labeled t __tag __data) -> subterm __root __data.
End Comparator.