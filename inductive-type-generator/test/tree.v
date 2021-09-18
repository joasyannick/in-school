Module CoTree.
	CoInductive tree (t : Type) :=
		  Leaf 
		| Node (node : tree t * t * tree t).


	Definition isLeaf {t: Type} (__input : tree t) : Prop :=
		match __input with
			  Leaf  => True
			| _ => False
		end.


	Definition isNode {t: Type} (__input : tree t) : Prop :=
		match __input with
			  Node _ => True
			| _ => False
		end.


	


	Definition getNodeNode {t: Type} (__input : tree t) : isNode __input -> tree t * t * tree t :=
		match __input with
			  Node node => fun __precondition => node
			| _ => fun __precondition => match __precondition with end
		end.
End CoTree.





Module Tree.
	Parameter Label : Type.

	CoInductive tree (t : Type) :=
		  Leaf 
		| Node (node : tree t * t * tree t)
		| Labeled (__tag : Label) (__data : tree t)
		| Reference (__tag : Label).


	Definition isLeaf {t: Type} (__input : tree t) : Prop :=
		match __input with
			  Leaf  => True
			| _ => False
		end.


	Definition isNode {t: Type} (__input : tree t) : Prop :=
		match __input with
			  Node _ => True
			| _ => False
		end.


	Definition isLabeled {t: Type} (__input : tree t) : Prop :=
		match __input with
			  Labeled _ _ => True
			| _ => False
		end.


	Definition isReference {t: Type} (__input : tree t) : Prop :=
		match __input with
			  Reference _ => True
			| _ => False
		end.


	


	Definition getNodeNode {t: Type} (__input : tree t) : isNode __input -> tree t * t * tree t :=
		match __input with
			  Node node => fun __precondition => node
			| _ => fun __precondition => match __precondition with end
		end.


	Definition getLabeled__tag {t: Type} (__input : tree t) : isLabeled __input -> Label :=
		match __input with
			  Labeled __tag _ => fun __precondition => __tag
			| _ => fun __precondition => match __precondition with end
		end.


	Definition getLabeled__data {t: Type} (__input : tree t) : isLabeled __input -> tree t :=
		match __input with
			  Labeled _ __data => fun __precondition => __data
			| _ => fun __precondition => match __precondition with end
		end.


	Definition getReference__tag {t: Type} (__input : tree t) : isReference __input -> Label :=
		match __input with
			  Reference __tag => fun __precondition => __tag
			| _ => fun __precondition => match __precondition with end
		end.


	Inductive subterm {t: Type} (__root : tree t) : tree t -> Type :=
		  SubRoot : subterm __root __root
		| SubLabeled : forall __tag __data, subterm __root (Labeled t __tag __data) -> subterm __root __data.
End Tree.