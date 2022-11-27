Require Export Relations_1 .
Require Export Finite_sets .
Require Export Syntax.
Require Export  Othertheory.

(***********************************************************************)
Parameter NI: Set.

(****************               Interprétation des rôles    ******************) 
Fixpoint interpR  (D: Set) (interp_r : NR ->  Relation D) (r: role)
       : Relation D :=
    match r with
    | (AtomR b) => interp_r b
end .

Implicit Arguments interpR [D].
(****************    L'interprétation ***************************)
Record Interp : Type := {
	 D:Set; 
	interp_c : NC -> Ensemble D;
	interp_r : NR ->  Relation D;
	interp_inst : NI-> D}.

(****************               Interprétation des Concepts    ******************) 
Fixpoint interpC (i:Interp)(c : concept){struct c} : Ensemble (D i) :=  
      match c with
	| Bottom           =>   Empty_set _
	| Top                 =>   Full_set _
	|  AtomC a       =>   interp_c i a
	|  AndC c1 c2  =>   Intersection  (interpC i c1) (interpC  i c2)
	| OrC c1 c2     =>   Union  (interpC i c1) (interpC  i c2)
	|  NotC c          =>   Complement  (interpC  i c)
	|  AllC r c          =>   fun x => forall y, (interpR  (interp_r i) r x y) -> (interpC i c y)
	|  SomeC r c    =>  fun x => exists y, (interpR  (interp_r i) r x y) /\ (interpC  i c y)	end.

Lemma sem_and_commutative : forall (i:Interp)(c1 c2: concept) , 
 (interpC i  (AndC c1 c2)) =(interpC i  (AndC c2 c1)). 
Proof.
intros; simpl. 
apply Extensionality_Ensembles.
split ; unfold Included ; intros; inversion H; apply Intersection_intro; auto.
Qed.
Lemma sem_or_commutative : forall (i:Interp)(c1 c2: concept) , 
 (interpC i  (OrC c1 c2)) =(interpC i  (OrC c2 c1)). 
Proof.
intros; simpl. 
apply Extensionality_Ensembles.
split ;unfold Included ; intros; inversion H .
apply  Union_intror; auto.
apply  Union_introl; auto.
apply  Union_intror; auto.
apply  Union_introl; auto.
Qed.

(****************************************)
Lemma sem_and_or :  forall i c1 c2, 
	                          (interpC i  (AndC c1 c2)) =(interpC i  (NotC (OrC( NotC c1) (NotC c2)))).
Proof.
intros.
simpl.apply inters_is_comp_union.
Qed.

(*****************************************************************)
Lemma sem_or_and :forall  i  c1 c2 , 
                         (interpC i  (OrC c1 c2)) = (Complement (interpC i (AndC( NotC c1) (NotC c2)))).
Proof.
intros.
simpl.
apply union_as_comp_inters.
Qed.
(*******************************************************)
Lemma  interCnotC :  forall i  c1  , 
(interpC i (AndC  c1 (NotC c1)))  = Empty_set (D i).
Proof.
intros.
simpl .
apply Extensionality_Ensembles.
split. 
intro.
   intros.
   inversion_clear H.
    contradiction.
intro.
  intros.
   contradiction.
Qed.
(****************************************************************)
Lemma sem_all_some : forall i c r,  
(interpC i  (AllC r c)) = (interpC i  (NotC (SomeC  r (NotC c)))).

Proof.
  simpl; intros.
  unfold Complement, In.
  apply Extensionality_Ensembles.
  split; unfold Included, In; red; intros.
     inversion_clear H0.
    intuition.
    apply NNPP; intro.
    apply H; clear H.
    exists y; intuition.
Qed.
(**********************************************************)
(**********************************************************)

Definition subsumed c1 c2 := forall  i, 
Included  (D i) (interpC i c1) (interpC i c2).


Definition concept_satisfiable c := exists  i, 
~ ( (interpC i c) = Empty_set (D i)).

Definition is_model_concept  i c  :=
~ ( (interpC i c) = Empty_set _).

Definition concept_unsatisfiable c := forall  i,
interpC i c = Empty_set _.

(*****************************************)
Lemma bottom_unsttisfiable : concept_unsatisfiable  Bottom.
Proof.
intro.
intros.
trivial.
Qed.

(*************************************************)
Lemma concp_unst_is_not_sat : forall c , concept_unsatisfiable c -> ~ concept_satisfiable c   .
Proof.
intros.
intro.
inversion_clear H0.
unfold concept_unsatisfiable in H.
auto.
Qed.

(*************************************************)
Lemma Top_sub_all : forall c , subsumed c Top.
Proof.
intro. 
unfold subsumed ,Included . intros.
simpl.
apply Full_intro.
Qed.
(***********************************************************)










