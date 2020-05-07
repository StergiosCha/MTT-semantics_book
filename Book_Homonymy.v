Load Coq_book_ontology.


(* Simple Homonymy by Overloading in Coercive Subtyping *)
Set Implicit Arguments.

(* unit type for "run" *)
Inductive Onerun : Set := run.
Definition T1:= Human->Prop.
Definition T2:= Human->Institution->Prop.
Parameter run1: T1.
Parameter run2: T2.
Definition r1 (r:Onerun): T1:= run1. Coercion r1: Onerun >-> T1.
Definition r2 (r:Onerun): T2:= run2. Coercion r2: Onerun >-> T2.

(* John runs quickly *)
Parameter quickly: forall (A: CN), (A -> Prop) -> (A -> Prop).
Definition john_runs_quickly:= quickly (run:T1) John.
(* John runs a bank *)
Definition john_runs_a_bank:= exists b: Bank, (run: T2) John b.