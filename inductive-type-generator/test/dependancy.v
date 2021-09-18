Module CoDependancy.
	CoInductive dependancy (s : Type) (t : Type) :=
		  Without (first : s) (second : t)
		| With (first : Type) (second : first).


	Definition isWithout {s: Type} {t: Type} (__input : dependancy s t) : Prop :=
		match __input with
			  Without _ _ => True
			| _ => False
		end.


	Definition isWith {s: Type} {t: Type} (__input : dependancy s t) : Prop :=
		match __input with
			  With _ _ => True
			| _ => False
		end.


	Definition getWithoutFirst {s: Type} {t: Type} (__input : dependancy s t) : isWithout __input -> s :=
		match __input with
			  Without first _ => fun __precondition => first
			| _ => fun __precondition => match __precondition with end
		end.


	Definition getWithoutSecond {s: Type} {t: Type} (__input : dependancy s t) : isWithout __input -> t :=
		match __input with
			  Without _ second => fun __precondition => second
			| _ => fun __precondition => match __precondition with end
		end.


	Definition getWithFirst {s: Type} {t: Type} (__input : dependancy s t) : isWith __input -> Type :=
		match __input with
			  With first _ => fun __precondition => first
			| _ => fun __precondition => match __precondition with end
		end.


	Definition getWithSecond {s: Type} {t: Type} (__input : dependancy s t) : forall (__precondition : isWith __input), getWithFirst __input __precondition :=
		match __input return forall (__precondition : isWith __input), getWithFirst __input __precondition with
			  With _ second => fun __precondition => second
			| _ => fun __precondition => match __precondition with end
		end.
End CoDependancy.





Module Dependancy.
	Parameter Label : Type.

	CoInductive dependancy (s : Type) (t : Type) :=
		  Without (first : s) (second : t)
		| With (first : Type) (second : first)
		| Labeled (__tag : Label) (__data : dependancy s t)
		| Reference (__tag : Label).


	Definition isWithout {s: Type} {t: Type} (__input : dependancy s t) : Prop :=
		match __input with
			  Without _ _ => True
			| _ => False
		end.


	Definition isWith {s: Type} {t: Type} (__input : dependancy s t) : Prop :=
		match __input with
			  With _ _ => True
			| _ => False
		end.


	Definition isLabeled {s: Type} {t: Type} (__input : dependancy s t) : Prop :=
		match __input with
			  Labeled _ _ => True
			| _ => False
		end.


	Definition isReference {s: Type} {t: Type} (__input : dependancy s t) : Prop :=
		match __input with
			  Reference _ => True
			| _ => False
		end.


	Definition getWithoutFirst {s: Type} {t: Type} (__input : dependancy s t) : isWithout __input -> s :=
		match __input with
			  Without first _ => fun __precondition => first
			| _ => fun __precondition => match __precondition with end
		end.


	Definition getWithoutSecond {s: Type} {t: Type} (__input : dependancy s t) : isWithout __input -> t :=
		match __input with
			  Without _ second => fun __precondition => second
			| _ => fun __precondition => match __precondition with end
		end.


	Definition getWithFirst {s: Type} {t: Type} (__input : dependancy s t) : isWith __input -> Type :=
		match __input with
			  With first _ => fun __precondition => first
			| _ => fun __precondition => match __precondition with end
		end.


	Definition getWithSecond {s: Type} {t: Type} (__input : dependancy s t) : forall (__precondition : isWith __input), getWithFirst __input __precondition :=
		match __input return forall (__precondition : isWith __input), getWithFirst __input __precondition with
			  With _ second => fun __precondition => second
			| _ => fun __precondition => match __precondition with end
		end.


	Definition getLabeled__tag {s: Type} {t: Type} (__input : dependancy s t) : isLabeled __input -> Label :=
		match __input with
			  Labeled __tag _ => fun __precondition => __tag
			| _ => fun __precondition => match __precondition with end
		end.


	Definition getLabeled__data {s: Type} {t: Type} (__input : dependancy s t) : isLabeled __input -> dependancy s t :=
		match __input with
			  Labeled _ __data => fun __precondition => __data
			| _ => fun __precondition => match __precondition with end
		end.


	Definition getReference__tag {s: Type} {t: Type} (__input : dependancy s t) : isReference __input -> Label :=
		match __input with
			  Reference __tag => fun __precondition => __tag
			| _ => fun __precondition => match __precondition with end
		end.


	Inductive subterm {s: Type} {t: Type} (__root : dependancy s t) : dependancy s t -> Type :=
		  SubRoot : subterm __root __root
		| SubLabeled : forall __tag __data, subterm __root (Labeled s t __tag __data) -> subterm __root __data.
End Dependancy.