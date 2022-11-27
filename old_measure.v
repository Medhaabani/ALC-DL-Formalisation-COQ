Require Export Tableau_decidability.
Require Export  Relations.

Require Export FSetEqProperties.
Module Import FactP := WEqProperties_fun  Fact_as_DT fsetsfact.
Module  NiP := WEqProperties_fun  NI_as_DT fsetsni.

Require Export FSetDecide. 
Module  NiD := WDecide_fun  NI_as_DT fsetsni.
Module Export FiD := WDecide_fun  Fact_as_DT fsetsfact.

Require Export FSetProperties.
Module Import FP := WProperties_fun  Fact_as_DT fsetsfact.
Module  NP := WProperties_fun  NI_as_DT fsetsni.

Definition clos_trans_succ   := clos_trans Abox succ  .  
Definition is_expansion A B  := clos_trans_succ  B A.  

Definition is_instance (f :fact) :  bool := match f with 
| inst _ _  => true 
| _         => false end .

Definition is_instance_x  (x: NI) (f :fact) :  bool := match f with 
| inst  y  _  => match NI_as_DT.eq_dec  y x with left _ => true |right _ => false end   
| _         => false end .

Definition set_of_instance (AB : Abox)  := (  filter is_instance AB).
Definition set_of_x_instance (x: NI ) (AB : Abox)  := (  filter (is_instance_x x) AB).

Definition construct_set_ni_as_instance_in_fact  (f:fact) (A :Setni) : Setni :=  match f with 
| inst  x c  =>  fsetsni.add   x A
| _ => A end.

Definition set_ni_as_instance_in_abox (AB : Abox) : Setni :=(   fold construct_set_ni_as_instance_in_fact  AB fsetsni.empty ).

Definition set_ni_as_instance_in_abox1 (AB : Abox) : Setni :=set_ni_in_abox (  filter is_instance AB).

(**************************************************)

Definition is_expansion_intial :=  is_expansion Abox_intial.

(****************************************************)
Lemma comp : compat_op Fact_as_DT.eq  fsetsni.eq construct_set_in_fact.
Proof.
unfold compat_op,  fsetsni.eq.
intros.

inversion_clear H.
induction x'. simpl. red.
unfold fsetsni.Equal in H0.
intuition.
generalize (H0 a); intros; clear H0.
inversion_clear H1.
 NiD.fsetdec.
generalize (H0 a); intros; clear H0. NiD.fsetdec.
simpl. red.
NiD.fsetdec.
simpl. red.
NiD.fsetdec.
Qed.
(******************************************)
Lemma comp1: transpose fsetsni.Equal construct_set_in_fact.
Proof.
unfold transpose.
 double induction  x y;
 intros ; simpl; 
NiD.fsetdec.
Qed.
(******************************************)
Lemma comp3 : ~   In (inst x_0 C)   empty.
Proof.
intuition.
FiD.fsetdec.

Qed.
(***************************************************)
Lemma fold_addf : forall f, ~   In f   empty->  fsetsni.Equal
 (  fold construct_set_in_fact (  add f   empty ) fsetsni.empty)
(construct_set_in_fact f  (  fold construct_set_in_fact   empty  fsetsni.empty)).
Proof.

apply fold_add.
auto with *.
apply comp.

exact comp1.
Qed.
(******************************************************************************************)

Lemma set_ni_in_abox_intial : fsetsni.eq  (set_ni_in_abox Abox_intial ) (fsetsni.singleton x_0).
Proof.
unfold set_ni_in_abox , Abox_intial.  
generalize ( fold_equal (A:=Setni)(eqA := fsetsni.eq)_ (f:=construct_set_in_fact)  comp  comp1 fsetsni.empty  (singleton_equal_add  (inst x_0 C))) .
intros.
rewrite H; clear H.
generalize (fold_addf (inst x_0 C) comp3).
intros.
rewrite H; clear H.
rewrite fold_empty .
simpl.
 rewrite <- NP.singleton_equal_add.
auto with *.
Qed.

(******************************************************************************************)


Lemma add_not_change : forall x  A c, fsetsni.In x A -> fsetsni.Equal  (construct_set_in_fact  (inst  x c)  A ) A.
Proof.
intuition.
simpl.
auto with *.
Qed.

Lemma  same_adding : forall x  A c c1 c2,  fsetsni.Equal  (construct_set_in_fact (inst  x c)  A )(construct_set_in_fact  (inst  x (AndC c1 c2))  A ) .

Proof.
intros.
auto with *.
Qed.

Lemma r1 : forall x c1 c2 AB1 ,  ~  In(inst x c2) AB1->   In (inst x c1) AB1-> ~  In (inst x c2)  (  add (inst x c1) AB1).
Proof.
intros.
eauto with *.
Qed.

Lemma add_add_x : forall x s, fsetsni.eq (fsetsni.add x (fsetsni.add x s )) (fsetsni.add x s ). 
Proof.
simpl.
intros.
unfold fsetsni.eq.
NiD.fsetdec.

Qed.
Lemma add_add_f : forall x s,   eq (  add x (  add x s )) (  add x s ). 
Proof.
simpl. intros.
unfold   eq.

FiD.fsetdec.
Qed.

Lemma in_add : forall x AB,   In x (  add x AB).
Proof.
intuition.

Qed.

Lemma r2 : forall x c1 c2 AB1 , (inst x c1)<>(inst x c2) -> ~  In(inst x c2) AB1-> ~  In (inst x c1) AB1-> ~  In (inst x c2)  (  add (inst x c1) AB1).
Proof.
intros.

intro.

generalize (   add_3 H H2).
trivial.
Qed.

(**************************************************)

Lemma and_rule_preserve_ni : forall AB1 AB2,  Andrule AB1 AB2 -> fsetsni.eq (set_ni_in_abox AB1)  (set_ni_in_abox AB2).
Proof.
intros.
inversion_clear H.
inversion_clear H0.
unfold set_ni_in_abox.
rewrite H1;  clear H1.
intuition.

(*********************************)
assert ( {  In (inst x c1) AB1}+ {~  In (inst x c1) AB1}).
apply In_dec.
inversion_clear H1.

(********************************************************)
(*********************************************************)
assert ( {  In (inst x c2) AB1}+ {~  In (inst x c2) AB1}).
apply In_dec.
inversion_clear H1.
tauto.
(*********un exist **************)
generalize (r1  x c1 c2 AB1 H3 H2).
intros.
rewrite  (fold_add _ (s:=   (  add (inst x c1) AB1)) comp comp1 fsetsni.empty H1).
simpl.
rewrite (add_fold _ (s:= AB1) comp comp1  fsetsni.empty H2).
intuition.
rewrite <- (remove_fold_1  _ (s:= AB1) comp comp1  fsetsni.empty H).
simpl.
rewrite add_add_x.
auto with *.
(***********************)

assert ( {  In (inst x c2) AB1}+ {~  In (inst x c2) AB1}).
apply In_dec.
inversion_clear H1.
(*****************************************)
(*************un exist ********************)

generalize (  add_2 (inst x c1)  H3 ).
intros.
rewrite (add_fold _ (s:= _ ) comp comp1  fsetsni.empty H1).
rewrite  (fold_add  _ (s:= _ ) comp comp1  fsetsni.empty H2).
simpl.
rewrite <- (remove_fold_1  _ (s:= AB1) comp comp1  fsetsni.empty H).
simpl.
rewrite add_add_x.
auto with *.
(******************************************)
(**********les deux nexist pas********************************)

assert ({c1 =c2 }+{c1<> c2}).
repeat decide equality.
inversion_clear H1.
rewrite H4.
(*************************************)
generalize (in_add (inst x c2) AB1); intros.
rewrite (add_fold _ (s:= _ ) comp comp1  fsetsni.empty H1).
rewrite  (fold_add  _ (s:= _ ) comp comp1  fsetsni.empty H3).
simpl.
rewrite <- (remove_fold_1  _ (s:= AB1) comp comp1  fsetsni.empty H).
simpl.
intuition.
rewrite add_add_x.
auto with *.
(******************************************)
assert ((inst x c1)<>(inst x c2)).
intuition.
inversion H1.
tauto.
(***************************)
generalize (r2 _ _ _ _ H1 H3 H2); intros.
rewrite  (fold_add  _ (s:= _ ) comp comp1  fsetsni.empty H5).
simpl.
rewrite  (fold_add  _ (s:= _ ) comp comp1  fsetsni.empty H2).
simpl.
rewrite <- (remove_fold_1  _ (s:= AB1) comp comp1  fsetsni.empty H).
simpl.
intuition.
rewrite add_add_x.
rewrite add_add_x. auto with *.
Qed.
(******************************************************************)
Lemma orleft_rule_preserve_ni : forall AB1 AB2,  Orruleleft AB1 AB2 -> fsetsni.eq (set_ni_in_abox AB1)  (set_ni_in_abox AB2).
Proof.
intuition.
inversion_clear H.
inversion_clear H0.
inversion_clear H2.
rewrite H1.
unfold set_ni_in_abox.
rewrite  (fold_add  _ (s:= _ ) comp comp1  fsetsni.empty H0).

simpl.
rewrite <- (remove_fold_1  _ (s:= AB1) comp comp1  fsetsni.empty H).
simpl.

rewrite add_add_x.
 auto with *.
Qed.
(******************************************************************)
Lemma orright_rule_preserve_ni : forall AB1 AB2,  Orruleright AB1 AB2 -> fsetsni.eq (set_ni_in_abox AB1)  (set_ni_in_abox AB2).
Proof.
intuition.
inversion_clear H.
inversion_clear H0.
inversion_clear H2.
rewrite H1.
unfold set_ni_in_abox.
rewrite  (fold_add  _ (s:= _ ) comp comp1  fsetsni.empty H3).

simpl.
rewrite <- (remove_fold_1  _ (s:= AB1) comp comp1  fsetsni.empty H).
simpl.

rewrite add_add_x.
 auto with *.
Qed.

(*******************************************)
Lemma add_add_xy : forall x y s, fsetsni.eq (fsetsni.add y  (fsetsni.add x (fsetsni.add y s) )) (fsetsni.add x (fsetsni.add y s) ). 
Proof.
simpl.
intros.
unfold fsetsni.eq.

NiD.fsetdec.
Qed.
(***********************************)
Lemma All_rule_preserve_ni : forall AB1 AB2,  Allrule AB1 AB2 -> fsetsni.eq (set_ni_in_abox AB1)  (set_ni_in_abox AB2).
Proof.

intuition.
inversion_clear H.
inversion_clear H0.
inversion_clear H2.
rewrite H1.
unfold set_ni_in_abox.

rewrite  (fold_add  _ (s:= _ ) comp comp1  fsetsni.empty ).

simpl.
rewrite <- (remove_fold_1  _ (s:= AB1) comp comp1  fsetsni.empty H0).
simpl.

rewrite add_add_xy.
 auto with *.
trivial.

Qed.



(**********************************************************)
(* for rule some , exist  new y that added.  we will do this nxt time ****)
(**********************************************************)











(**********************************************************)
(*16 mars *****)
(***********************************************************)



Lemma set_instance_abox_intial  :    eq  (set_of_x_instance  x_0   Abox_intial ) Abox_intial .
Proof.

unfold  set_of_x_instance , Abox_intial.
split.
apply   filter_1.
unfold compat_bool .
intros.
rewrite H.
trivial.
intro. 
assert (is_instance_x x_0  (inst x_0 C) = true ).
simpl.


unfold NiD.F.eqb.

case (NP.Dec.F.eq_dec x_0 x_0).
auto.
auto with *.


apply (  filter_3).
unfold compat_bool .
intros.
rewrite H1.
trivial.
trivial.
FiD.fsetdec.
Qed. 