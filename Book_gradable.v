(* Degree is type of names of degrees -- d : Degree corresponds to type D(d) *)
(* So, Degree is a Tarski universe! *)
(* Here is an example with three degrees. *)
Require Import Omega.
Inductive Degree: Set:= HEIGHT | AGE | IDIOCY.
Definition D (d: Degree):= nat.
Definition Height:= D(HEIGHT).
Check Height.
Definition Age:= D(AGE).
Definition Idiocy:= D(IDIOCY).

(* Universe CN_G of indexed CNs *)
Definition CN_G (_:Degree) := Set.
Parameter Human: CN_G(HEIGHT).
Parameter John Mary Kim : Human.
Parameter height: Human->Height.

(** Type of physical objects indexed with a degree**)
Parameter PHY : forall d: Degree, CN_G(d).

(* ADJ(D,A) of syntax of adjectives whose domain is A : CN_G(d) *)
Parameter ADJ: forall d:Degree, CN_G(d)->Set.
Parameter TALL SHORT: ADJ HEIGHT Human.
Parameter IDIOTIC: ADJ IDIOCY Human.
Parameter ENORMOUS: forall d: Degree,  ADJ d  (PHY(d)).

(* STND *)
Parameter STND: forall d:Degree, forall A:CN_G(d), ADJ d A -> D(d).

(* semantics of tall, taller_than *)
Definition tall (h:Human):= ge (height h) (STND HEIGHT Human TALL).
Definition taller_than (h1:Human) (h2:Human) := gt (height h2) (height h1).

(*Some simple theorems*)
Theorem TALLER:
    taller_than Mary John /\ height Mary = 170 -> gt (height John) 170.
    cbv. intro. omega. Qed.

Theorem trans:
    taller_than Mary John /\ taller_than Kim Mary -> taller_than Kim John.
    cbv. intro. omega. Qed.

(**Definition for Idiot**)
Parameter IHuman : Idiocy -> CN_G(IDIOCY).
Definition Idiot:=  sigT(fun x: Idiocy=> (sigT (fun y: (IHuman x) => (gt x (STND IDIOCY Human IDIOTIC))))).
Definition enormous  (d:Degree)(A:CN_G(d))(d1: D d) := fun P: A =>  gt (d1)  (STND  d (PHY(d))(ENORMOUS d)).
Check enormous.
Section Enormous. 
Variable STND_order: forall d: Degree, forall C: CN_G(d),  forall A: ADJ d C,  STND d (PHY(d))(ENORMOUS d) > STND d C A. 
Set Implicit Arguments.
Record enormousidiot: Set:= mkeidiot
  {h:> Idiot; EI: enormous IDIOCY (IHuman(projT1(h)))(projT1(h))(projT1(projT2(h))) /\  ge  (STND  IDIOCY (PHY(IDIOCY))(ENORMOUS IDIOCY))(STND IDIOCY Human IDIOTIC) }.
Record enormousidiot1: Set:= mkeidiot1
                               {h1:> Idiot; EI1: enormous IDIOCY (IHuman(projT1(h1)))(projT1(h1))(projT1(projT2(h1)))/\  ge  (STND  IDIOCY (PHY(IDIOCY))(ENORMOUS IDIOCY))(STND IDIOCY Human IDIOTIC) }.
Theorem  ENORMOUS1:
  enormousidiot -> exists H: Idiot,   projT1(H) > STND IDIOCY (PHY IDIOCY) (ENORMOUS IDIOCY).
  cbv. firstorder. Qed.
Theorem EI2:
  enormousidiot -> exists H: Idiot,   projT1(H) > STND IDIOCY (PHY IDIOCY) (ENORMOUS IDIOCY) /\ projT1(H) >  (STND IDIOCY Human IDIOTIC).
  cbv. firstorder. unfold Idiot in h0. exists h0. firstorder.
  unfold enormous in H. firstorder. elim  h0. intros. destruct p.
  omega. Qed.
Theorem EI3:
  enormousidiot -> exists H: Idiot,   projT1(H) > STND IDIOCY (PHY IDIOCY) (ENORMOUS IDIOCY) /\ projT1(H) >
  (STND IDIOCY Human IDIOTIC) /\  STND IDIOCY (PHY IDIOCY) (ENORMOUS IDIOCY) > (STND IDIOCY Human IDIOTIC).
   cbv. firstorder. unfold Idiot in h0. exists h0. firstorder.
  unfold enormous in H. firstorder. elim  h0. intros. destruct p.
  omega. Qed.


