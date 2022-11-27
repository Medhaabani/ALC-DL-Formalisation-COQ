Require Export Tableau.

(*** si AB2 est satisfiable Alors AB1 est satisfiable *)

Definition  sound  (r : Abox -> Abox -> Prop) := forall AB1 AB2 ,
                 r AB1 AB2 ->
                         abox_satisfiable AB2 ->abox_satisfiable AB1 .



Lemma  sound_extend_rstar :forall r, sound r -> sound (rstar_rule r).
Proof.
unfold sound . intros.
induction H0.
auto.
apply H with y.
auto.
tauto.
Qed.


Lemma sound_extend_disj  : forall   l : list (Abox ->Abox->Prop), (forall r,    List.In r l -> sound r) -> sound (disj_rule l).
Proof.

induction l.  intros.
red.
intros.
inversion H0.
intros.
red.
intros.
simpl in H0.
inversion H0.
assert ((List.In a (a :: l) )).
auto with *.
unfold sound in H.
apply ( H a H3 AB1 AB2 H2 H1).
red in IHl.
generalize H1.
generalize H2.
generalize AB2.
generalize AB1.
apply IHl.
intros.
apply H.
auto with *.
Qed.
(******************************)

Lemma and_sound :  sound Andrule.
Proof.
unfold sound, abox_satisfiable, is_model_Abox .
intros.
inversion_clear H0.
inversion_clear H.
exists x.
intros.
intuition.
apply H1.
rewrite H2.
eauto with *.
Qed.


(*** Si AB1 est satisfiable Alors AB2  est satisfiable *) 

Lemma and_sound2 : forall AB1 AB2 , Andrule AB1 AB2 -> abox_satisfiable AB1 ->abox_satisfiable AB2 .
Proof.
unfold abox_satisfiable, is_model_Abox .
intros.
inversion_clear H.
inversion_clear H0.
inversion_clear H1.
exists x0.
intros.
rewrite H2 in H1.
rewrite factFact.add_iff  in H1.
inversion_clear H1.

generalize (H _  H0).
intros.
unfold  inter_satisfies_fact in H1.
simpl   (interpC x0 (AndC c1 c2)) in H1.        
inversion H1.
intuition.
inversion_clear H4.
trivial.

rewrite factFact.add_iff  in H4.
inversion_clear  H4.
generalize (H _  H0).
intros.
unfold  inter_satisfies_fact in H4.
simpl   (interpC x0 (AndC c1 c2)) in H4.       
inversion H4.
inversion_clear H1.

trivial.
auto.

Qed.

(****************************** Or left    *************************************)

Lemma orleft_sound :  sound Orruleleft  .
Proof.
unfold  sound , abox_satisfiable, is_model_Abox .
intros.
inversion_clear H0.
inversion_clear H.
exists x.

intros.
intuition.
apply H1.
rewrite H2.
eauto with *.
Qed.

(****************           or right           **********************)

Lemma orright_sound : sound Orruleright .
Proof.
unfold sound , abox_satisfiable, is_model_Abox .
intros.
inversion_clear H0.
inversion_clear H.
exists x.
intros.
intuition.
apply H1.
rewrite H2.
eauto with *.
Qed.


(************ all sound ***********************************)

Lemma all_sound : sound Allrule .
Proof.
unfold sound,  abox_satisfiable, is_model_Abox .
intros.
inversion_clear H0.
inversion_clear H.
exists x.
intros.
intuition.
apply H1.
rewrite H2.
eauto with *.
Qed.

(*************    Some Sound ***********************)

Lemma some_sound : sound Somerule.
Proof.
unfold sound, abox_satisfiable, is_model_Abox .
intros.
inversion_clear H0.
inversion_clear H.
exists x.
intros.
intuition.
apply H1.
rewrite H2.
eauto with *.
Qed.


Hint Resolve and_sound orleft_sound orright_sound all_sound some_sound.


(***********************   rule is sound ***********************)


Lemma  rule_sound1 :  sound  ALC_rule.
Proof.
apply sound_extend_disj   .
intros; repeat  (inversion_clear H ; eauto with *;  inversion_clear H0;  eauto with *).
Qed.

Lemma  rule_sound :  sound rule.
Proof.
unfold sound.
intros ; repeat  (inversion_clear H ; eauto with *;  inversion_clear H1;  eauto with *).
Qed.

Hint Resolve rule_sound.

(**************************************************************************************)
(**************************************************************************************)
(**                                                    Proof of TR soundeness                            ***)
(**************************************************************************************)
(**************************************************************************************)

Lemma end_is_satisfiable_first_is_satisfiable : forall AB1 AB2 , 
			(Rstar Abox  rule  AB1 AB2) -> 
					abox_satisfiable AB2 ->
						abox_satisfiable AB1 .

Proof.
intros.
induction H.
trivial.
apply rule_sound with y.
trivial.
trivial.
intuition.
Qed.






















