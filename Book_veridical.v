Load Coq_book_ontology.
Parameter walk: Human -> Prop. 
Definition  VER_PROP (Q: Prop):= forall P: Prop, P -> Q.  
Definition fortunately:= VER_PROP.

Theorem VER1:
    fortunately (walk John) -> walk John.
    cbv. firstorder. apply H with (fortunately (walk John)).
    cbv. firstorder. Qed.

Theorem VER3: forall Q: Prop, VER_PROP Q -> Q.
  cbv.  firstorder.  apply H  with (VER_PROP Q).
  cbv. assumption.  Qed.

Theorem VER4 (P: Prop):
    forall Q: Prop, (P -> Q) -> (P ->  VER_PROP Q).
    cbv. firstorder. Qed. 