Load Coq_book_ontology. 
Parameter Manner: Set.
Parameter Agent : CN. 
Parameter illegible_m: Manner -> Prop.
Parameter illegible_ma: Manner -> Agent -> Prop. 
Inductive Evt_m : Manner -> Type:=  EVT_m : forall m : Manner, Evt_m m.
Inductive Evt_ma : Manner -> Agent -> Type:=  EVT_ma : forall m : Manner, forall a: Agent,  Evt_ma m a.

Unset Implicit Arguments. 
Parameter write: forall m: Manner,  Human -> Evt_m m -> Prop.
Set Implicit Arguments. 
Definition illegibly_m:= fun (m: Manner)(A:CN)(P: A -> Evt_m m -> Prop) 
    (x: A) (E: Evt_m m) => P x E /\ illegible_m m.
Parameter m: Manner.
Parameter u: Evt_m m. 
Theorem MANNER: 
    exists m : Manner,  exists e : Evt_m m, illegibly_m (write m)
    John e -> illegible_m (m). 
    exists m. exists u. cbv. firstorder. Qed. 
    
Definition illegibly_a:= fun (m: Manner)(a : Agent)(A:CN)(P: A -> Evt_ma m a  -> Prop) 
    (x: A) (E: Evt_ma m a) => P x E /\ illegible_ma m a.