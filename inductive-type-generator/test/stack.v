Module CoStack.
	CoInductive stack (t : Type) :=
		  Empty 
		| Push (top : t) (pop : stack t).


	Definition isEmpty {t: Type} (__input : stack t) : Prop :=
		match __input with
			  Empty  => True
			| _ => False
		end.


	Definition isPush {t: Type} (__input : stack t) : Prop :=
		match __input with
			  Push _ _ => True
			| _ => False
		end.


	


	Definition getPushTop {t: Type} (__input : stack t) : isPush __input -> t :=
		match __input with
			  Push top _ => fun __precondition => top
			| _ => fun __precondition => match __precondition with end
		end.


	Definition getPushPop {t: Type} (__input : stack t) : isPush __input -> stack t :=
		match __input with
			  Push _ pop => fun __precondition => pop
			| _ => fun __precondition => match __precondition with end
		end.
End CoStack.





Module Stack.
	Parameter Label : Type.

	CoInductive stack (t : Type) :=
		  Empty 
		| Push (top : t) (pop : stack t)
		| Labeled (__tag : Label) (__data : stack t)
		| Reference (__tag : Label).


	Definition isEmpty {t: Type} (__input : stack t) : Prop :=
		match __input with
			  Empty  => True
			| _ => False
		end.


	Definition isPush {t: Type} (__input : stack t) : Prop :=
		match __input with
			  Push _ _ => True
			| _ => False
		end.


	Definition isLabeled {t: Type} (__input : stack t) : Prop :=
		match __input with
			  Labeled _ _ => True
			| _ => False
		end.


	Definition isReference {t: Type} (__input : stack t) : Prop :=
		match __input with
			  Reference _ => True
			| _ => False
		end.


	


	Definition getPushTop {t: Type} (__input : stack t) : isPush __input -> t :=
		match __input with
			  Push top _ => fun __precondition => top
			| _ => fun __precondition => match __precondition with end
		end.


	Definition getPushPop {t: Type} (__input : stack t) : isPush __input -> stack t :=
		match __input with
			  Push _ pop => fun __precondition => pop
			| _ => fun __precondition => match __precondition with end
		end.


	Definition getLabeled__tag {t: Type} (__input : stack t) : isLabeled __input -> Label :=
		match __input with
			  Labeled __tag _ => fun __precondition => __tag
			| _ => fun __precondition => match __precondition with end
		end.


	Definition getLabeled__data {t: Type} (__input : stack t) : isLabeled __input -> stack t :=
		match __input with
			  Labeled _ __data => fun __precondition => __data
			| _ => fun __precondition => match __precondition with end
		end.


	Definition getReference__tag {t: Type} (__input : stack t) : isReference __input -> Label :=
		match __input with
			  Reference __tag => fun __precondition => __tag
			| _ => fun __precondition => match __precondition with end
		end.


	Inductive subterm {t: Type} (__root : stack t) : stack t -> Type :=
		  SubRoot : subterm __root __root
		| SubLabeled : forall __tag __data, subterm __root (Labeled t __tag __data) -> subterm __root __data
		| SubPushPop : forall top pop, subterm __root (Push t top pop) -> subterm __root pop.
End Stack.