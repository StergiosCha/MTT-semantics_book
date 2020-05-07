Load Coq_book_ontology.
(** Dealing with multidimensional adjectives. Health as an inductive type
 where  the dimensions are enumerated. This is just an enumerated type*)
Definition   Degree:= Set. 
Inductive Health: Degree:= Heart|Blood|Cholesterol.
Parameter Healthy: Health->Human->Prop.
Definition sick:=fun y : Human => ~ (forall x : Health, Healthy x y).
Definition healthy:= fun y : Human => forall x : Health, Healthy x y.

Theorem HEALTHY:
    healthy John -> Healthy Heart John /\ Healthy Blood John
    /\ Healthy Cholesterol John.
    cbv. intros. split. apply H.
    split. apply H. apply H. Qed.

Theorem HEALTHY2:
    healthy John -> not (sick John).
    cbv. firstorder. Qed.

Theorem HEALTHY3:
    (exists x: Health, Healthy x John) -> healthy John.
    cbv. firstorder. Abort.

Theorem HEALTHY4:
    (exists x: Health, not (Healthy x John)) -> healthy John.
    cbv. firstorder. Abort.

Theorem HEALTHY5:  
    (exists x: Health, not (Healthy x John))  -> sick John.
  cbv. firstorder.  Qed.

Inductive art: Degree:= a1|a2|a3|a4.
Parameter F: art -> nat. 
Definition DIM_CN := fun  h: Human => fun a: art => F a.
Parameter STND_art: nat. 
Record Artist: Set:= mkartist{h:> Human; EI :  forall a: art, gt (DIM_CN h a) STND_art }.