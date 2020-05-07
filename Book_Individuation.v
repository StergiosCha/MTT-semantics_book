Require Import Setoid.
(**DomCN is the old CN, the universe of common nouns**)
Definition DomCN:=Set.

(**Equiv is an equivalence relation on elements of DomCN**)
Record Equiv (A:DomCN): Type:= mkEquiv 
    {eq1:> A->A->Prop; _eq2: reflexive A(eq1) /\ symmetric A eq1 /\ transitive A eq1}.
Record Equiv_K (A:DomCN): Type:= mkEquiv_K 
    {eq2:> A->A->Prop; _eq3: reflexive A(eq2)/\ symmetric A eq2}.
	
(**CN is a setoid, here expressed as a record, 
second projection is the equiv relation on the type**)
Record CN := mkCN
    {D:> DomCN; E:Equiv D}.
Record CN_K := mkCN_K
    {D2:> DomCN; E2:Equiv_K D2}.
	
(**Types in DomCN**)
Parameter Human  Man: DomCN.
Parameter John: Human.
Axiom mh: Man->Human. Coercion mh: Man>->Human.

(**IC for Human**)
Parameter IC_Human: Equiv(Human).

(**This is the CN type in Capitals as a setoid**)
Definition HUMAN:= mkCN Human IC_Human.

(**Given the IC for man as being inherited from human**)
Definition AIC_Man:= fun x: Man=>fun y:Man=> IC_Human(x)(y).

(** We prove the equivalence of AIC_Man**)
Theorem EQ: 
    reflexive  Man  AIC_Man /\  symmetric Man AIC_Man /\  
    transitive Man AIC_Man. 
    cbv. destruct  IC_Human. destruct _eq4. destruct H0. 
    split. intro. unfold reflexive in H.  apply H. split. intro. 
    unfold symmetric in H0. intuition. intro. unfold transitive in H1.
    intro. intro. intros. apply H1 with y. assumption. assumption. Qed.

(**A first definition of three, prety standard but takes into account
 the IC, B and B2 are the two respective projections**)
Definition three_f:= fun A:CN => fun P:A.(D)->Prop=> 
    exists x:A.(D),P(x)/\exists y:A.(D), P(y)/\ exists z:A.(D), P(z) /\ 
    not((A.(E))(x)(y)) /\ not((A.(E))(y)(z)) /\ not((A.(E))(x)(z)).

(** Similarly for some**)
Definition some:=fun A:CN=> fun P:A.(D)->Prop=> exists x:A.(D), P(x).

(**Predicates are functions from the first projection of the CN to Prop**)
Parameter walk: HUMAN.(D)->Prop.
Check walk John.
Check (three_f HUMAN) walk.

(** Defining the IC for man and then MAN**)
Definition IC_Man:=  mkEquiv Man AIC_Man EQ.
Definition MAN:= mkCN Man IC_Man.

(**A proof that if three men walk, three humans walk**)
Theorem MANWALK:
    (three_f MAN) walk-> (three_f HUMAN) walk.
    cbv. intros. destruct H. destruct H. destruct H0.
    destruct H0. destruct H1. destruct H1. destruct H2.
    destruct H3. exists x. split. intuition. exists x0.
    split. intuition. exists x1. split. intuition. intuition.
    Qed.



(** Defining the dot for PhyInfo and type book**)
Parameters Phy : DomCN. 
Parameter Info: DomCN.
Set Implicit Arguments.

(** Defining the dot type  PhyInfo and declaring the coercions**)
Record PhyInfo: DomCN := mkPhyInfo 
    {p :> Phy; i :> Info}.
Parameter Book: DomCN.
Axiom bf: Book-> PhyInfo. Coercion bf: Book >-> PhyInfo.

(** IC for Phy, Info and PhyInfo**)
Parameter IC_Phy: Equiv(Phy).
Parameter IC_Info: Equiv(Info).
Definition PHY:= mkCN Phy IC_Phy.
Definition INFO:= mkCN Info IC_Info.

Definition AIC_PhyInfo := fun a1: (PhyInfo)=>fun b1: ( PhyInfo) =>
    IC_Phy(a1.(p))( b1.(p)) \/ IC_Info(a1.(i))( b1.(i)).
	
Theorem EQ1: 
    reflexive  PhyInfo  AIC_PhyInfo /\  symmetric PhyInfo  AIC_PhyInfo.
    cbv. destruct IC_Phy. firstorder. destruct IC_Info. firstorder. Qed. 
	
Definition IC_PhyInfo:=  mkEquiv_K PhyInfo  AIC_PhyInfo EQ1.
Definition PHYINFO:= mkCN_K PhyInfo IC_PhyInfo.

(** Defining the IC criteria for book**)
Definition AIC_Book1 := fun x: Book=>fun y:Book=> IC_Phy(x)(y).
Definition AIC_Book2 := fun x: Book=>fun y:Book=> IC_Info(x)(y).

Theorem EQ2: 
    reflexive  Book  AIC_Book1 /\  symmetric Book AIC_Book1 
    /\  transitive Book AIC_Book1. 
    cbv. destruct  IC_Phy. destruct _eq4. destruct H0. split.
    intro. unfold reflexive in H.  apply H. split. intro. unfold symmetric in H0.
    intuition. intro. unfold transitive in H1. intro. intro. intros. apply H1 with y.
    assumption. assumption. Qed.

Theorem EQ3: 
    reflexive  Book  AIC_Book2 /\  symmetric Book AIC_Book2 
    /\ transitive Book AIC_Book2. 
    cbv. destruct  IC_Info. destruct _eq4. destruct H0. split. intro. 
    unfold reflexive in H.  apply H. split. intro. unfold symmetric in H0.
    intuition. intro. unfold transitive in H1. intro. intro. intros. apply H1 with y.
    assumption. assumption. Qed.

Definition IC_Book1:=  mkEquiv Book  AIC_Book1 EQ2.
Definition IC_Book2:=  mkEquiv  Book  AIC_Book2 EQ3.
Definition BOOK1:= mkCN Book IC_Book1.
Definition BOOK2:= mkCN Book IC_Book2.

Parameter picked_up: Human->Phy->Prop.
Parameter mastered: Human->Info->Prop.

Definition three_c:= fun A : DomCN => fun P : (PhyInfo) -> Prop =>
    exists x y z : Book, not(IC_PhyInfo((x))((y))) /\
    not((IC_PhyInfo)((y))((z)))/\not((IC_PhyInfo)((x))((z))) 
	/\ P x /\ P y /\ P z.
Unset Implicit Arguments. 
Definition and:= fun A:DomCN=> fun P: A->Prop=>fun Q: A->Prop=> 
    fun x: A=>  P(x)/\Q(x).

Theorem copred_dd1: 
    (three_c Book )(and PhyInfo(picked_up John )(mastered John)) -> 
    (three_f PHY) (picked_up John) /\ (three_f INFO) (mastered John).
    cbv. intros.  destruct IC_Phy. destruct IC_Info. firstorder. Qed.                                                                                

Theorem copred_dd2: 
    (three_c Book )(and PhyInfo(picked_up John )(mastered John)) -> 
    exists x y z : Book, not((PHY.(E))((x))((y))) /\ not((PHY.(E))((y))((z))) /\ 
    not((PHY.(E))((x))((z))) /\ picked_up John (x) /\ picked_up John y
    /\ picked_up John z /\ not((INFO.(E))((x))((y)))/\not((INFO.(E))((y))((z)))
    /\not((INFO.(E))((x))((z))) /\ mastered  John (x) /\ mastered John y 
    /\ mastered John z.
    cbv. firstorder. Qed.

Parameter Heavy: Phy->Prop. 
Record Heavybook :DomCN := mkheavybook { b1 :> Book; b2 : Heavy b1 }.

Definition AIC_HBook1 := fun x: Heavybook=>fun y:Heavybook=> IC_Book1(x)(y).

Theorem EQ4: 
    reflexive  Heavybook  AIC_HBook1 /\ symmetric Heavybook AIC_HBook1
    /\ transitive Heavybook AIC_HBook1. 
    cbv. destruct  IC_Phy. destruct _eq4. destruct H0. split. intro.
    unfold reflexive in H.  apply H. split. intro. unfold symmetric in H0. 
    intuition. intro. unfold transitive in H1. intro. intro. intros. apply H1 with y.
    assumption. assumption. Qed.

Definition IC_HBook1:=  mkEquiv Heavybook  AIC_HBook1 EQ4.
Definition HBOOK1:= mkCN Heavybook IC_HBook1.

Definition AIC_HBook2 := fun x: Heavybook=>fun y:Heavybook=> IC_Book2(x)(y).

Theorem EQ5: 
    reflexive  Heavybook  AIC_HBook2 /\ symmetric Heavybook AIC_HBook2 
    /\ transitive Heavybook AIC_HBook2. 
    cbv. destruct  IC_Info. destruct _eq4. destruct H0. split.
    intro. unfold reflexive in H.  apply H. split. intro. 
    unfold symmetric in H0. intuition. intro. unfold transitive in H1. 
    intro. intro. intros. apply H1 with y. assumption. assumption. Qed.

Definition IC_HBook2:=  mkEquiv Heavybook  AIC_HBook2 EQ5.
Definition HBOOK2:= mkCN Heavybook IC_HBook2.

Theorem HEAVYBOOK: 
    (some HBOOK2) ( mastered John)-> (some INFO)( mastered John). 
    firstorder. Qed.

Theorem HEAVYBOOK1: 
    (some HBOOK1) (picked_up John)-> (some PHY)( picked_up John).
    firstorder. Qed.

Theorem HEAVYBOOK2: 
    (three_f HBOOK1) (picked_up John)-> (three_f PHY)( picked_up John).
    cbv.  firstorder. Qed.

Theorem HEAVYBOOK3: 
    (three_f HBOOK2) ( mastered John)-> (three_f INFO)( mastered John). 
    cbv. intros. firstorder. Qed.

Parameter Informative: Info->Prop.
Record Heavyinfobook: DomCN:= mkheavyinfobook
    {l4 :>Heavybook; _ : Informative l4}.
Definition AIC_HIBook1:= fun x: Heavyinfobook=> fun y:  Heavyinfobook=> IC_HBook1(x)(y).

Theorem EQ6: 
    reflexive  Heavyinfobook  AIC_HIBook1 /\ symmetric Heavyinfobook AIC_HIBook1 
    /\ transitive Heavyinfobook AIC_HIBook1. 
    cbv. destruct  IC_Phy. destruct _eq4. destruct H0. split.
    intro. unfold reflexive in H.  apply H. split. intro.
    unfold symmetric in H0. intuition. intro. unfold transitive in H1.
    intro. intro. intros. apply H1 with y. assumption. assumption. Qed.

Definition IC_HIBook1:=  mkEquiv Heavyinfobook  AIC_HIBook1 EQ6.
Definition HIBOOK1:= mkCN Heavyinfobook IC_HIBook1.

Definition AIC_HIBook2:= fun x: Heavyinfobook=>fun y: Heavyinfobook=> IC_HBook2(x)(y).

Theorem EQ7: 
    reflexive  Heavyinfobook  AIC_HIBook2/\  symmetric Heavyinfobook AIC_HIBook2 
    /\ transitive Heavyinfobook AIC_HIBook2. 
    cbv. destruct  IC_Info. destruct _eq4. destruct H0. split. intro. 
    unfold reflexive in H.  apply H. split. intro. unfold symmetric in H0.
    intuition. intro. unfold transitive in H1. intro. intro. intros. apply H1 with y.
    assumption. assumption. Qed.
	
Definition IC_HIBook2:=  mkEquiv Heavyinfobook  AIC_HIBook2 EQ7.
Definition HIBOOK2:= mkCN Heavyinfobook IC_HIBook2.


Theorem HEAVYIBOOK2:
    (three_f HBOOK1) (picked_up John)-> (three_f PHY)( picked_up John). 
    cbv. firstorder. Qed.

Theorem HEAVYIBOOK3: 
    (three_f HIBOOK2) ( mastered John)-> (three_f INFO)( mastered John). 
    cbv. intros. firstorder. Qed.

Theorem HEAVYIBOOK4: 
    (three_f HIBOOK1) (picked_up John)-> (three_f HBOOK1)( picked_up John). 
    cbv. firstorder. Qed.
	
Theorem HEAVYIBOOK5: 
    (three_f HIBOOK2) ( mastered John) -> (three_f HBOOK2)( mastered John).
    cbv. intros. firstorder. Qed.

Parameter OTS: Phy -> Prop.
Parameter WL: Info -> Prop.
Parameter WaP: Book.
Definition one:= fun A:CN => fun P:A.(D)->Prop=> 
    exists x: A.(D),P(x).
Check exists x: Book,  OTS x /\ ( ( x = WaP)/\(WL x)).
Set Implicit Arguments. 
Check exists x: BOOK1.(D),  OTS x /\ BOOK2.(E) x x /\ ( ( x = WaP) /\ (WL x)).

Theorem threedf: 
    three_f PHY  (OTS) -> (one  PHY) OTS . 
    cbv. firstorder. Qed. 