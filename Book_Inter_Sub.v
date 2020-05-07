Load Coq_book_ontology.

Parameter Irish: Human -> Prop. 
Record Irishhuman: CN:= mkirishhuman 
    {h:> Human; I: Irish h}.
Record Irishdelegate: CN:= mkirishdelegate 
    {d :> Delegate; I2 : Irish d}.
Parameter Skillful: forall A: CN, A -> Prop.
(** Skillful as a polymorphic type*)
Record Skillfulman : CN := mkskillfulman 
	{ m :> Man; S: Skillful Man m}.
Record Skillfulhuman : CN := mkskillfuluman 
    {h2 :> Human; S2 : Skillful Human h2}.
Parameter walk: Human -> Prop. 

Theorem delegate1: 
    (some Irishdelegate) walk -> (some Delegate) walk.
    cbv. firstorder. Qed.
	
Theorem delegate2: 
    (some Man) Irish -> (some Human) Irish. 
    cbv.  firstorder. Qed.
	
Theorem skill1: 
    (some Skillfulman) Irish -> (some Man) Irish. 
    cbv. firstorder. Qed.
	
Theorem skill2: 
    (some Surgeon) (Skillful Surgeon) -> (some Man)( Skillful Man).
    cbv. firstorder. Abort all.