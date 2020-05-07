Definition CN:= Set. 

(** Common Nouns as Types *)
Parameters Bank Manager Accountant Car Meeting  City Nobel_prize Distance Mammal Report Student Diamond Delegate    Mouse Survey Swede Scandinavian Contract Door Window Institution Phy Info Factory Woman Man Object President Surgeon Animal Human: CN.

(* *Book as a Sigma Type encoding Pustejovsky's qualias structure. The first projection is a coercion, thus Book is a subtype of phy.info The and dot
Record PhyInfo : CN := mkPhyInfo { phy :> Phy; info :> Info }.
(* Book as Sigma-type with PhyInfo & BookQualia *)
Parameter Hold : Phy->Info->Prop.
Parameter R1 : PhyInfo->Prop.
Parameter W : Human->PhyInfo->Prop.
Record BookQualia (A:PhyInfo) : Set :=
mkBookQualia { Formal : Hold A A;
Telic : R1 A;
Agent : exists h: Human, W h A }.
Record Book : Set := mkBook { Arg :> PhyInfo; Qualia : BookQualia Arg }.*)

     (** Subtyping relations. Coercion ensures that in every situation requiring an object of type b, an object of type a can be used (with a<b) *)
Axiom do: Diamond->Object. Coercion do: Diamond >-> Object.
Axiom sw: Surgeon -> Human. Coercion sw: Surgeon >-> Human.
Axiom mo2: Meeting->Object. Coercion mo2: Meeting>->Object.
Axiom mh2: Manager->Human. Coercion mh2: Manager >-> Human.
Axiom co3: Car->Object. Coercion co3: Car>-> Object.
Axiom co2: City->Object. Coercion co2: City>-> Object.
Axiom maa: Mammal->Animal. Coercion maa: Mammal >-> Animal.
Axiom no1: Nobel_prize ->Object. Coercion no1: Nobel_prize>->Object.
Axiom sh1: Student->Human. Coercion sh1: Student>->Human.
Axiom dh:  Delegate->Human. Coercion dh: Delegate>->Human.
Axiom ma: Mouse ->Animal. Coercion ma:Mouse>->Animal.
Axiom mh : Man->Human. Coercion mh : Man >-> Human.
Axiom wh : Woman->Human. Coercion wh : Woman >-> Human.
Axiom ha: Human-> Animal. Coercion ha: Human>-> Animal.
Axiom ao: Animal->Object. Coercion ao: Animal>-> Object.
Axiom ss:Swede->Scandinavian. Coercion ss: Swede>-> Scandinavian.
Axiom bi: Bank -> Institution. Coercion bi: Bank>-> Institution.
(** Some quantifiers *)
Definition some:= fun A:CN=> fun P:A->Prop=> exists x:A, P(x). 
Definition all:= fun A:CN=> fun P:A->Prop=> forall x:A, P(x).
Definition no:= fun A:CN=> fun P:A->Prop=> forall x:A, not(P(x)).
Definition A:= some.
Definition each:=all.
Parameters John George : Man.
Parameters Mary Helen : Woman.