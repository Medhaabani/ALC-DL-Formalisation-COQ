Require Export ABox.
Require Export Relations_2.
Require Export FSetFacts.

Module  factFact := WFacts_fun Fact_as_DT fsetsfact.
Export  fsetsfact.
(***********************Les Règles de transformation ***********************************)

Inductive  Andrule (b1: Abox) (b2 :Abox) :Prop  :=   
  mk_andrule:forall x c1 c2  ,
    In  (inst x  (AndC c1 c2)) b1 /\ ~ (In  (inst x c1) b1  /\  In (inst x c2 ) b1 )  ->  b2 = add   (inst x c2) ( add (inst x c1) b1) 
       -> Andrule (b1: Abox) (b2 :Abox).

Inductive Orruleleft (b1 : Abox) (b2: Abox) : Prop := 
    mk_orruleleft:forall x c1 c2  ,   In  (inst x  (OrC c1 c2)) b1 /\ ~ In (inst x c1) b1 /\ ~ In  (inst x c2 ) b1   ->  b2 = add   (inst x c1) b1
       -> Orruleleft (b1: Abox) (b2 :Abox).

Inductive Orruleright(b1 : Abox) (b2: Abox) : Prop := 
    mk_orruleright : forall x c1 c2  , In (inst x  (OrC c1 c2)) b1 /\ ~ In (inst x c1) b1 /\ ~ In  (inst x c2 ) b1   ->  b2 = add (inst x c2) b1
       -> Orruleright(b1: Abox) (b2 :Abox).

Inductive Allrule (b1 : Abox) (b2: Abox) : Prop := 
    mk_Alrule :forall x y r c1,   In   (inst x  (AllC  r c1 ))  b1 /\  In (rel x y r) b1  /\ ~ In  (inst y c1 ) b1    ->  b2 = add  (inst y c1) b1
       -> Allrule (b1: Abox) (b2 :Abox).

(******************************* La règle Some ***************************)

 Inductive Somerule (b1 : Abox) (b2: Abox) : Prop := 
    mk_Somerule :forall x  z r c1,   In  (inst x  (SomeC  r c1 )) b1  /\ (  forall y,
~ (In  (rel x y r)  b1 /\  In  (inst y c1 ) b1)) /\ ~ ( fsetsni.In  z (set_ni_in_abox  b1)) 
 -> b2 =add  (rel x z r) ( add  (inst z c1) b1) 
   ->  Somerule (b1: Abox) (b2 :Abox).


(******************************************************************************************)

Definition rule AB1 AB2 := (Andrule AB1 AB2) \/ 
                                             (Orruleleft AB1 AB2) \/ 
                                              (Orruleright AB1 AB2) \/
                                               (Somerule AB1 AB2) \/ 
                                                (Allrule AB1 AB2).
(******************************************************************************************)
Definition  rstar_rule   := Rstar Abox  .

Definition ALC_rules := Andrule :: Orruleleft :: Orruleright :: Allrule::Somerule::nil.

Fixpoint  disj_rule ( l : list (Abox -> Abox -> Prop)) : (Abox -> Abox -> Prop) := 
match l with
| nil  => (fun AB1 AB2 => False)
| r::rs => (fun AB1 AB2 => (r AB1 AB2) \/  (disj_rule rs AB1 AB2))
end.

Definition ALC_rule := disj_rule ALC_rules.
(*******************************************)

Definition contains_clash (AB : Abox) : Prop  := exists x , exists c, 
           (fsetsfact.In (inst x c) AB  /\  fsetsfact.In  (inst x (NotC c)) AB  )  \/ (fsetsfact.In  (inst x Bottom) AB ).  

Definition next  AB1 AB2: Prop := (~ contains_clash AB1) /\  (rule AB1 AB2).
Definition succ  AB2 AB1 := (~ contains_clash AB1) /\  (rule AB1 AB2).
Definition complete  AB := forall AB1 ,  ~ (ALC_rule AB AB1).

(**************************************************************************)



(*****************************************)
(************************************************************************************************************************)
Lemma first_is_nnf_nxt_is_nnf : forall AB1 AB2 , (  rule  AB1 AB2) -> is_Normal_Abox AB1 ->is_Normal_Abox AB2.
Proof.
intros.
inversion_clear H.
(**************************)
inversion_clear H1.
rewrite H2.
intuition.
generalize (H0  (inst x (AndC c1 c2)) H1).
intro.
red in H3.
simpl in H3.
intuition.
red.
intros.
cut ({ f =  (inst x c2)} +{~ f =  (inst x c2)}).
intros.
inversion_clear H6.
subst.
simpl.
trivial.
apply NNPP.
intro.
apply H7.
symmetry .
apply NNPP.
intro.
apply H6.
unfold not in H8.
generalize (add_3  H8 (y:= f) (s:=(fsetsfact.add (inst x c1) AB1) )).
intros.
generalize (H9 H3 ).
intros.
cut ({ f =  (inst x c1)} +{~ f =  (inst x c1)}).
intros.
inversion_clear H11.
subst.
simpl.
trivial.
apply NNPP.
intro.
apply H12.
symmetry .
apply NNPP.
intro.
apply H11.
generalize (add_3  H13 (y:= f) (s:= AB1 )).


intros.
generalize (H14  H10 ).
intros.
apply H0.
trivial.
auto with *.
auto.



(******************************)
inversion_clear H1.
inversion_clear H.
rewrite H2.
intuition.
generalize (H0  (inst x (OrC c1 c2)) H).
intro.

red in H3.
simpl in H3.
red.
intros.
intuition.

rewrite factFact.add_iff  in H5.
inversion H5.
inversion H3.
subst f.
red.
trivial.
apply H0.
trivial.


(********************************)
inversion_clear H.
inversion_clear H1.
rewrite H2.
intuition.
generalize (H0  (inst x (OrC c1 c2)) H1).
intro.
red in H3.
simpl in H3.
red.
intros. rewrite factFact.add_iff  in H5.
inversion_clear H5.

inversion_clear H6.
tauto.
auto.


(**************************************)
inversion_clear H1.
inversion_clear H.
rewrite H2.
intuition.
generalize (H0  (inst x (SomeC r c1 )) H).
intro.
red in H3.
simpl in H3.
red.
intros.
rewrite factFact.add_iff  in H5.
intuition.
inversion H6.
red.
trivial.
rewrite factFact.add_iff  in H6.
intuition.
inversion_clear H5.
trivial.

(************************************)
inversion_clear H.
inversion_clear H1.
rewrite H2.
intuition.
generalize (H0  (inst x (AllC r c1 )) H).
intros.
red in H3.
simpl in H3.
red.
intros. rewrite factFact.add_iff  in H5.
inversion_clear H5.

inversion_clear H6.
auto.
auto.
Qed.

(*************************************)
Lemma first_is_nnf_end_is_nnf : forall AB1 AB2 , ( Rstar Abox  rule  AB1 AB2) -> is_Normal_Abox AB1 ->is_Normal_Abox AB2.
Proof.
intros.
induction H.
auto.
apply IHRstar.
apply  first_is_nnf_nxt_is_nnf with x.
trivial.
trivial.
Qed.

