Require Export  Semantic.

(***********transformation de la négation ******************************)
Fixpoint  trans_neg  (a:concept)  : concept := match a with
		|  AtomC x=>  NotC (AtomC x)
		|Top  =>  Bottom
		|Bottom  =>  Top
		| NotC   c   =>    c
		| AndC   c d  => OrC (trans_neg  c) (trans_neg  d) 
		| OrC c d     => AndC (trans_neg  c) (trans_neg  d)
		| AllC r c         => SomeC r ( trans_neg  c)
		| SomeC r c     => AllC r  (trans_neg  c)
		end.



(********************************)
Lemma trans_neg_andc: forall c0 c1 , (trans_neg (AndC c0 c1))= OrC (trans_neg c0) (trans_neg c1).
intros.
auto.
Qed.
(**********La forme normale sans negation ******************)
Fixpoint NNF (a :concept) :concept := match a with 
 | NotC c1 =>  trans_neg (NNF c1)
|AtomC x => AtomC x
|Top => Top
|Bottom => Bottom
|AndC c1 c2 => AndC (NNF c1 ) (NNF c2)
|OrC c1 c2  => OrC (NNF c1) (NNF c2)
|AllC  r c => AllC r (NNF c)
|SomeC r c => SomeC r (NNF c)
end. 

(***************************************************)

Fixpoint  isNF  (a : concept) : Prop:=  match a with
|AtomC x => True
|Top => True
|Bottom => True 
|NotC c1 => exists x , c1 = (AtomC x)
|AndC c1 c2 => isNF c1 /\  isNF c2 
|OrC c1 c2 =>   isNF c1  /\  isNF c2
|AllC  r c => isNF c
|SomeC r c => isNF c
end .

Require Export Omega. 
Set Implicit Arguments.

(*****************************************************)
Lemma  sem_neg : forall i c, (interpC i (trans_neg c))  = (Complement (interpC i c)).
Proof.
intros.
elim c.
 intros.
   simpl .
    tauto.
simpl .
apply comp_empty_is_full .
   simpl .
apply comp_full_is_empty .

intros.
  simpl .
  symmetry  .
  apply Complement_Complement.
intros.
  simpl .
  rewrite H.
  rewrite H0.
  symmetry .
  apply comp_inters_as_union.
intros.
  simpl in |- *.
  rewrite H .
  rewrite H0 .
  symmetry  .
  apply comp_union_as_inters.
simpl ; intros.
  rewrite H .
  unfold Complement, In .

  apply Extensionality_Ensembles. 
  split; unfold Included, Ensembles.In ;intros.
 intro.
   inversion_clear H0.
    intuition.
apply not_all_ex_not in H0.
  inversion_clear H0.
  exists x0.
   apply imply_to_and in H1.
  assumption.
simpl ; intros.
  rewrite H .
  unfold Complement, In .
  apply Extensionality_Ensembles.
  split; unfold Included, Ensembles.In ; intros.
 intro.
   inversion_clear H1.
   inversion_clear H2.
   generalize H3.
   apply H0.
   trivial.
 intuition.
  apply H0.
  exists y.
  split.
 apply H1.
trivial.
Qed.

(****************************************************)
Lemma  semNFCC : forall i c , 
     (interpC i  c)  =  (interpC i  (NNF c)).
Proof.
intros.
elim c; intros;simpl; auto.

rewrite -> sem_neg .
apply f_equal .
trivial.
symmetry in H ; rewrite H.
symmetry in H0 ; rewrite H0.
trivial.
symmetry in H ; rewrite H.
symmetry in H0 ; rewrite H0.
trivial.
symmetry in H ; rewrite H.
trivial.
symmetry in H ; rewrite H.
trivial.
Qed.
(***************************************) 
Lemma isNF_to_NNF : forall c, isNF c -> (NNF c ) = c.
Proof.
induction  c ; simpl ; intros; auto.
 inversion_clear H; subst; auto.
inversion_clear H.
rewrite IHc1; auto.
rewrite IHc2; auto.
inversion_clear H.
rewrite IHc1; auto.
rewrite IHc2;auto.
rewrite IHc ; auto.
rewrite IHc ; auto.
Qed.
(******************************************)
Lemma isnf_trans_neg : forall c,  isNF c ->  isNF (trans_neg c).
Proof.
induction c; simpl ; intros; auto.
exists n; auto.
inversion_clear H ; subst ; simpl ; auto.
inversion H; auto.
inversion H; auto.
Qed.
(*****************************************)
Lemma isnf_nnf: forall c ,  isNF (NNF c ).
Proof.
induction c;simpl; auto.
apply  isnf_trans_neg; auto.
Qed.
(*****************************************)
Lemma isnf_eq_nnf : forall c, isNF c <-> (NNF c ) = c.
Proof.
split.
apply  isNF_to_NNF.
intro.
rewrite <- H.
 apply isnf_nnf.
Qed.

