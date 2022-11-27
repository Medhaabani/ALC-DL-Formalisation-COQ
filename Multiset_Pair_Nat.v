Add Rec LoadPath "~/color82" as CoLoR.	
Require Import RelExtras.
Require Import MultisetList.
Require Import MultisetTheory.
Require Import MultisetListOrder.
Require Export DecidableTypeEx.

Module PairNat.
   Definition A :=    (nat * nat)%type .
 End PairNat.

Module NatPairSet <: Eqset := Eqset_def PairNat.

Module NatPairSet_dec.
 
   Module Eq := NatPairSet.
   Export Eq.
 
   Lemma eqA_dec : forall x y :(nat *nat), { x = y}+ { x<> y}.
Proof.
intros.
repeat decide equality.
Qed.
 End NatPairSet_dec.
 
Module MSetCore := MultisetList.MultisetList NatPairSet_dec.
 
 Module MSetTheory := MultisetTheory.Multiset MSetCore.
 Notation "'XXX'" := I : sets_scope.
 Export MSetTheory.
 
 Module MSetOrd := MultisetOrder.MultisetOrder MSetCore  .
 Export MSetOrd.


(**************** Exemples sur l'ordre des multisets de type na t******)
Definition gtA x y := gt (fst x ) (fst y ) \/ ( (fst x) = (fst y) /\ gt (snd x)(snd y)).
Definition   ltA := transp gtA.
 Definition leA x y := ~gtA x y.
 Definition gtA_trans := clos_trans gtA.
 Definition  geA x y := gtA x y \/ eqA x y.
Hint Unfold gtA ltA leA gtA_trans : sets.
Require Export List.


Definition M1 :=   (((0,0)::(1,1)::nil)).
Definition M2 :=   (((2,2)::nil)).
Definition M3 :=   (((2,2)::(3,3)::nil)).

(*Definition M4 := (2,2) ::(empty :: (3,3) ).*)



(*********************** Exemple 1  M2 >mul M1 ******)
Lemma example1_onestep :MultisetRedGt   gtA M2 M1.
Proof.
apply (MSetRed  gtA (A0 :=  ({{(2,2)}} +  empty))
 (B :=  ({{(0,0)}} + ({{(1,1)}} + empty))) (X:= empty) (a := (2,2))(Y := {{(0,0)}} + ({{(1,1)}} ))  ).
auto with *.
solve_meq.
intros.
generalize  (member_union H) ; clear H; intro.
inversion_clear H; generalize (member_singleton H0); clear H0; intro H;  inversion_clear H;
auto with *.
Qed.

Lemma example1_multstep :MultisetGt   gtA M2 M1.
Proof.
hnf.
apply t_step.
exact example1_onestep.
Qed.
Lemma need1: forall x x' y y' : nat * nat , x = x' -> y = y' -> gtA x  y -> gtA x'  y'.
Proof.
intros.
rewrite <- H .  rewrite <-H0.
auto.
Qed.

Lemma need0: forall x x' y y' : nat * nat, x = x' -> y = y' -> ltA x  y -> ltA x' y'.
Proof.
intros.
rewrite <- H .  rewrite <-H0.
auto.

Qed.
Lemma need02:  forall (a b:  nat ), {gt a  b}+{~ gt a  b}.
Proof.
double induction   a b   .
right.
omega.
intros.
inversion H.
auto with *.
auto with *.
auto with *.
intuition.
generalize (H0 n).
intros.
inversion_clear H1.
left.
omega.
right.
omega.
Qed.

(*************************************************************)
Lemma need2:  forall (a b:  nat*nat ), {gtA a  b}+{~ gtA a  b}.
Proof.
intros.
unfold gtA.
case (need02 (fst a) (fst b)).
intros.
left.
left.
auto.
intros.
case (OrderedTypeEx.Nat_as_OT.eq_dec (fst a) (fst b)).
intros.
case (need02 (snd a) (snd b)).
intros.
left.
auto.
intros.
right.
intro.
inversion H.
auto.
inversion_clear H0.
auto.
intros.
right.
intro.
inversion H.
auto.
inversion_clear H0.
auto.
Qed.

Lemma decidable_GT  :forall M N, { MultisetGT gtA M N}+{~  MultisetGT gtA M N}.
Proof.
intros.
apply (mOrd_dec  gtA need1   need2 M N). 
Qed.

Lemma example46 :MultisetLT  gtA  M1 M2.
Proof.
compute.
apply   (MSetGT gtA  (M := M2)  (N:= M1)(X:= {{(2,2)}} ) (Y := ({{(0,0)}} + {{(1,1)}} ))(Z:= empty)).
auto with *.
solve_meq.
hnf.
solve_meq.
intuition.
exists (2,2).
auto with *.
apply member_union in H.
inversion_clear H.
 (apply  (member_singleton ) in H0 ;inversion_clear H0; 
auto).
auto with *.
(apply  (member_singleton ) in H0 ;inversion_clear H0; 
auto).
auto with *.
Qed.
