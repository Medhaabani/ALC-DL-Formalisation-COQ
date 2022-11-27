(***********************************************)
Require Export Classical_sets.
(*****************************************)

Lemma all_not_ex_not:
  forall (U : Type) (P : U -> Prop),
  (forall n : U, P n) -> ~ (exists n : U, ~P n).
Proof.
intros.
apply all_not_not_ex.
auto.
Qed.


(*******  Des lemmes sur les ensembles ***** *)
Implicit Arguments Intersection [U].
Implicit Arguments Complement [U].
Implicit Arguments Union [U].
(* Set Printing Implicit. *)

Lemma   inters_is_comp_union : forall (D:Set)(E1 E2 : Ensemble D) , 
  (Intersection E1 E2 ) = (Complement  (Union  (Complement  E1) (Complement E2) )).
Proof.
intros.
apply Extensionality_Ensembles.
split; unfold Included, Complement, In; intros.
 intro.
   inversion_clear H.
   inversion_clear H0.
  auto.
 auto.
split; apply NNPP; intro; apply H.
 left.
   trivial.
right.
  trivial.
Qed.
(***************************************************************)
Lemma  union_as_comp_inters : forall (D:Set)(E1 E2 : Ensemble D) , (Union  E1 E2 ) =(Complement  (Intersection  (Complement  E1) (Complement  E2) )).
Proof.
intros.
apply Extensionality_Ensembles.
split; unfold Included, In in |- *; intros.
 intro.
   inversion_clear H0.
   inversion_clear H.
  auto.
 auto.
rewrite inters_is_comp_union in H.

 repeat  rewrite Complement_Complement in H.
  trivial.
Qed.
(**************************************************************)
Lemma  comp_inters_as_union :  forall (D:Set)(E1 E2 : Ensemble D) ,(Complement  (Intersection  E1 E2 )) = (Union  (Complement  E1) (Complement  E2) ).
Proof.
intros.
apply Extensionality_Ensembles.
split; unfold Included, Complement, In ; intros.
 rewrite inters_is_comp_union in H.
   unfold Complement, In in H.
   apply NNPP.
   trivial.
intro.
  inversion_clear H0.
  inversion_clear H.
 auto.
auto.
Qed.
(*******************************************************************)
Lemma comp_union_as_inters :  forall (D:Set)(E1 E2 : Ensemble D) , (Complement  (Union  E1 E2 )) = (Intersection  (Complement  E1) (Complement  E2) ).
Proof.
intros.
rewrite <- Complement_Complement .
apply f_equal .
apply union_as_comp_inters.
Qed.
(******************************************)
Lemma  comp_empty_is_full :  forall (D:Set),
Empty_set D   = Complement   (Full_set  D ).
Proof.
intros.
apply Extensionality_Ensembles.
unfold Complement.
split; unfold Included , Complement , In; intros.
tauto.
apply NNPP.
intro.
apply H.
apply Full_intro.
Qed.
(********************************)
Lemma  comp_full_is_empty :  forall (D:Set),
Full_set D   = Complement   ( Empty_set  D ).
Proof.
intros.
apply Extensionality_Ensembles.
unfold Complement.
split; unfold Included , Complement , In; intros.
tauto.
apply NNPP.
intro.
apply H0.
apply Full_intro.
Qed.