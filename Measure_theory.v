Add Rec LoadPath "~/color82" as CoLoR.	
Require Export Multiset_Pair_Nat.
Require Export Inverse_Image.
Require Export Measure.

(**************Measure Definition****************************)
Definition construct_Multiset  (A: Abox) (f:fact) M1 : Multiset :=  insert (mes_comp   A  f)  M1.
Definition  Measure2 A B : Multiset  := ( fold  (construct_Multiset  A )   B MSetCore.empty ).
Definition Measure_Abox AB := Measure2 AB AB.
  
(****************************************************************************)
(************************* Lemmas for rewriting *************************)
(****************************************************************************)

(****************** For set_some ******************************)
Lemma  Compat_som : forall x r   , compat_op (Fact_as_DT.eq ) Equal (Constract_set_som x r  ).
Proof.
unfold compat_op.
intros.
unfold Constract_set_som.
inversion_clear H.
FiD.fsetdec.
Qed.

Lemma Equivalence_Eq : Equivalence Equal.
Proof.
auto with *.
Qed.

Lemma  transp_som : forall x r  , transpose Equal (Constract_set_som x r ).
Proof.
unfold transpose.
intros.
unfold Constract_set_som.
FiD.fsetdec.
Qed.
(*************************************************************)
Lemma Eq_cr : Equivalence fsetsni.Equal.
Proof.
auto with *.
Qed.

Lemma compat_c  :forall  c,  compat_op Fact_as_DT.eq  fsetsni.Equal (construct_set_of_y_in_concept c).
Proof.
unfold compat_op ; intros.
inversion H.
subst; clear H. 
induction x' ; simpl . 
case(eq_dec_concept  c c0 ).
rewrite H0 ; auto with set .
auto with *.
auto with *.
auto with *.
Qed.

Lemma transp_c : forall   c , transpose fsetsni.Equal (construct_set_of_y_in_concept c ).
Proof.
intros.
unfold transpose .
double induction   x y ; unfold construct_set_of_y_in_concept  ;intros ; auto with set.
case (eq_dec_concept  c c0) ; intros.
case (eq_dec_concept  c  c1); 
auto with *.
auto with *.
Qed.

(*******************************************************)
Lemma compat_r : forall x r , compat_op Fact_as_DT.eq  fsetsni.Equal (construct_set_of_y_in_rel x r).
Proof.
unfold compat_op.
intros.
inversion_clear H.
case x' ;
simpl; 
auto with *.
intros; case ( eq_ni n x && eq_role r r0 ).
rewrite  H0.
auto with *.
auto.
Qed.

Lemma transp_r : forall x r, transpose fsetsni.Equal (construct_set_of_y_in_rel x r).
Proof. 
unfold transpose.
 double induction   x0 y  ;intros ; auto with set.
simpl.
case ( eq_ni  n2 x && eq_role r r1).
case( eq_ni n x && eq_role r r0).
auto with set.
auto with set.
auto with set.
Qed.

Lemma  compat_cm: forall s1,  compat_op Fact_as_DT.eq meq (construct_Multiset s1).
Proof.
unfold compat_op , construct_Multiset ; intros.
inversion H ;   subst .
  solve_meq.
Qed.

Lemma transp_cm : forall s1, transpose meq (construct_Multiset s1).
Proof.
unfold transpose ,  construct_Multiset ; intros ; solve_meq.
Qed.

Lemma Eq_meq : Equivalence meq.
Proof.
auto.
Qed.

Lemma  compat_css : forall s , compat_op Fact_as_DT.eq  Equal (Constract_set_som_r s).
Proof.
unfold compat_op ; intros.
inversion_clear H.
unfold Constract_set_som_r.
auto with *.
Qed.
Lemma transp_css : forall s , transpose Equal (Constract_set_som_r s).
Proof.
unfold  transpose ; intros.
unfold Constract_set_som_r .
FiD.fsetdec.
Qed.
(*****************************************************************************************)
Hint Resolve compat_cm  Eq_meq  transp_r  transp_cm  compat_r   transp_c compat_c 
                       Compat_som  Eq_cr  transp_som Equivalence_Eq compat_css transp_css.
(*********************************************************************************************)
(*********************************************************************************************)

(**********************************Measure lemmas**********************************************************)

Lemma measure_add_1 : forall f s2 AB , ~ In f s2-> (Measure2 AB (add f s2)) =mul= ( Measure2 AB  (add f empty ) ) +(Measure2 AB  s2 ).
Proof.
intros.
unfold Measure2.
rewrite (FP.fold_add) ; auto.
rewrite (FP.fold_add); auto  with set . 
rewrite ( FP.fold_empty);  simpl ; solve_meq.
Qed.
(**********************************************************)
Lemma measure_add_2 : forall f s2 AB ,  In f s2-> (Measure2 AB (add f s2)) =mul= (Measure2 AB  s2 ).
Proof.
intros ; unfold Measure2.
rewrite (FP.add_fold) ;
intuition.
Qed.

Lemma equal_mes_comp : forall f s1 s2 , s1 [=] s2 ->  (mes_comp s1 f ) = (mes_comp s2 f ).
Proof.
intros.
unfold mes_comp .
case f ; intros ; intuition. case c ;  intros ;  simpl ; intuition .
case (and_applicable_or_not (inst n (AndC c0 c1)) s1) ; intros.
case (and_applicable_or_not (inst n (AndC c0 c1)) s2); intros.
intuition.
apply False_ind; apply n0 ; clear n0.
inversion_clear a.
inversion_clear H0.
inversion H1.
rewrite H3, H4, H5 in *; clear H1 H3 H4 H5.
inversion_clear H2.
apply (App_and _ _ n c0 c1) .  
rewrite <- H ; auto with set.

(*********case (and_applicable_or_not (inst n (AndC c0 c1)) s2).********************************)
case (and_applicable_or_not (inst n (AndC c0 c1)) s2); intros ; intuition.
apply False_ind; apply n0 ; clear n0.
inversion_clear a.
inversion_clear H0.
inversion H1.
rewrite H3, H4, H5 in *; clear H1 H3 H4 H5.
inversion_clear H2.
apply (App_and _ _ n c0 c1) ; rewrite  H;  intuition .

(******************************************************)
case (or_applicable_or_not (inst n (OrC c0 c1)) s1) ;intros.
case (or_applicable_or_not (inst n (OrC c0 c1)) s2); intros.
 intuition.
apply False_ind; apply n0 ; clear n0.
inversion_clear o.
inversion_clear H0.
inversion H1.
rewrite H3, H4, H5 in *; clear H1 H3 H4 H5.
inversion_clear H2.
apply (App_or _ _ n c0 c1) ; rewrite <- H; intuition .
(****************************************)

case (or_applicable_or_not (inst n (OrC c0 c1)) s2); intros.
apply False_ind; apply n0 ; clear n0.
inversion_clear o.
inversion_clear H0.
inversion H1.
rewrite H3, H4, H5 in *; clear H1 H3 H4 H5.
inversion_clear H2.
apply (App_or _ _ n c0 c1) ; rewrite  H; intuition.
intuition.
(***************************************)

assert ((set_rel n c0 r s1) = (set_rel n c0 r s2)).
unfold set_rel.
apply  (NiP.equal_cardinal ). 
apply fsetsni.equal_1.
unfold set_y_in_abox.
rewrite   <-   ( FP.fold_equal Eq_cr (compat_r n r) (transp_r n r) _ H) ; auto.
unfold set_y_c_in_abox.
rewrite <-     ( FP.fold_equal Eq_cr (compat_c c0) (transp_c c0)  _ H) ; auto.
intuition . 

(**********************************************************)
assert (set_of_some_term n r s1 [=] (set_of_some_term n r s2)).
unfold set_of_some_term.
rewrite   (FactP.fold_compat  Abox  _  _ (Constract_set_som n r )(Constract_set_som n r )) ; auto.
apply   ( FP.fold_equal Equivalence_Eq); auto. 

(*****************added ***************************)
intros.
unfold Constract_set_som.
auto with *.
assert ((set_of_some_term_r n r s1) [=]set_of_some_term_r n r s2).
unfold set_of_some_term_r.



rewrite   (FactP.fold_compat Abox _ _ (Constract_set_som_r s1)(Constract_set_som_r s2)) ;auto.

apply   ( FP.fold_equal Equivalence_Eq) ; auto. 
intros.
unfold Constract_set_som_r .
unfold some_terme_reductble.
case (some_applicable_or_not_2 x s1); intro.
case (some_applicable_or_not_2 x s2); intro.
auto with *.
apply False_ind; apply n0 ;clear n0.
inversion_clear s.
inversion_clear H3.

apply (App_some_2  _ _ x0 r0 c1).
 split; auto.

intro; rewrite <- H ; apply H5.
case (some_applicable_or_not_2 x s2); intro.
apply False_ind; apply n0 ;clear n0.
inversion_clear s.
inversion_clear H3.

apply (App_some_2 _ _ x0 r0 c1).
 split; auto.

intro; rewrite  H ; apply H5.
auto with *.

(**************************************)
rewrite  H0 , H2.
intuition.
(************************************************************)
case(some_applicable_or_not (inst n (SomeC r c0)) s1) ; intros.
case(some_applicable_or_not (inst n (SomeC r c0)) s2) ; intros.
trivial.
apply False_ind.
apply n0 ; clear n0.
inversion_clear s.
inversion_clear H0.
inversion_clear H2.
inversion H1.
rewrite <-  H5 ,H6, H4 , H in *; clear   H5 H6 H4 H1.
apply (App_some   _ _ x  r c1 ).
intuition.
generalize (H3 y).
intro.
apply H1.
rewrite H.
intuition.

case(some_applicable_or_not (inst n (SomeC r c0)) s2) ; intros.

apply False_ind.
apply n0 ; clear n0.
inversion_clear s.
inversion_clear H0.
inversion_clear H2.
inversion H1.
rewrite  H5 ,H6, H4 in *; clear   H5 H6 H4 H1.
apply (App_some   _ _ x  r0 c1 ).
rewrite  H in *.
intuition.
generalize (H3 y).
intro.
apply H1.
rewrite <-  H.
intuition.
trivial.
Qed.

(************************************************************)
Lemma Mesure_equal_1  : forall s1 s2 s3 , s2 [=]s3 -> Measure2 s1 s2 =mul= Measure2 s1 s3.
Proof.
intros; unfold Measure2.
apply   (FP.fold_equal Eq_meq  (compat_cm s1) (transp_cm s1)  _ H  ). 
Qed.

(************************************************************)
Lemma measure_union  : forall s2  AB s1, Empty (inter s1 s2)-> ( Measure2 AB (union s1 s2)) =mul= (Measure2 AB  s1 ) +( Measure2 AB  s2 ).
Proof.
intros; unfold Measure2.
rewrite (FP.fold_union) ; auto.
fold  (Measure2  AB s2) ; fold   (Measure2  AB s1).

rewrite (FP.fold_rec_weak (A:= Multiset) (P:= fun s M =>(Measure2 AB s + Measure2 AB s2)=mul= M )
(f:= construct_Multiset AB)(i:=Measure2 AB s2 )).

intuition.
intros ; rewrite <- (Mesure_equal_1 AB _ _ H0) ; auto.
unfold Measure2 ;  rewrite (FP.fold_empty) ; solve_meq.
intros; rewrite   (measure_add_1 x  s AB H0 ).
assert ( Measure2  AB (add x empty) =mul= {{mes_comp AB x}}).
unfold Measure2.
rewrite (FP.fold_add) ;auto.
rewrite ( FP.fold_empty); auto.
solve_meq.
auto with set.
rewrite H2 ; unfold construct_Multiset ; rewrite <- H1.
solve_meq.
intro ; unfold Empty in H.
generalize (H x); intros.
FiD.fsetdec.
Qed.
(**************************************************************)
Lemma Measure_equal_2 : forall s1 s2 s3 , s1 [=]s2 -> Measure2 s1 s3 =mul= Measure2 s2  s3.
Proof.
intros; unfold Measure2.
apply  (FactP.fold_compat   _  _ Eq_meq (construct_Multiset s1) (construct_Multiset s2) (compat_cm s1) (transp_cm s1) (compat_cm s2) (transp_cm s2)).
intros; unfold construct_Multiset .
 rewrite (equal_mes_comp  x  s1 s2 H) ; intuition.
Qed.


(*************************** about MultisetGT ********************)
Lemma MultisetGT_equal  : forall M1 M2 M3, M2 =mul= M3 -> MultisetGT gtA M1 M2 -> MultisetGT gtA M1 M3.
Proof.
intros.
inversion H0.
assert (  M3 =mul= Z + Y).
rewrite <-  H.
auto.
apply (MSetGT gtA H1  H2 H5  H4). 
Qed.

Lemma MultisetGT_equal2  : forall M1 M2 M3, M2 =mul= M3 -> MultisetGT gtA M2 M1 -> MultisetGT gtA M3 M1.
Proof.
intros.
inversion H0.
assert (  M3 =mul= Z + X).
rewrite <-  H.
auto.
apply (MSetGT gtA H1  H5 H3  H4). 
Qed.

(**************************************************)
Lemma fst_comp_lq_sizec:  ( forall s x c , fst  (mes_comp s (inst x c))  <=  sizeC c).
intuition.
unfold mes_comp.
case (and_applicable_or_not (inst x c) s); intros ; unfold sizef.
case (or_applicable_or_not (inst x c) s) ; intros ; unfold sizef.
case (some_applicable_or_not (inst x c) s) ; intros ;unfold sizef. 

induction  c;  auto with *.
induction  c;  auto with *.
case c; 
auto with *.
intros.
case (some_applicable_or_not (inst x (SomeC r c0)) s).
intros.
auto with *.
intros.
auto with *.
case (or_applicable_or_not (inst x c) s) ; intros ; unfold sizef.
case (some_applicable_or_not (inst x c) s) ; intros ;unfold sizef. 
induction  c;  auto with *.
induction  c;  auto with *.
case (some_applicable_or_not (inst x c) s) ; intros ;unfold sizef. induction  c;  auto with *.
induction  c;  auto with *. 
Qed.


Lemma lq_lt_lt :forall a b c,  a <= b ->   b< c -> a < c.
intros.
omega.
Qed.


Lemma notin_inst_abox_notin_set: forall AB1 c1 y,  ~ In (inst y c1) AB1-> ~ fsetsni.In y (set_y_c_in_abox c1 AB1).
Proof.
intros.
unfold set_y_c_in_abox.
apply FP.fold_rec_nodep ; intros.
auto with set.
(******************************)
induction x ; simpl ; auto.
case(eq_dec_concept c1 c) ; intros.
rewrite(NiD.F.add_iff); intro.
inversion_clear H2 ; subst ;auto.
auto.
Qed.


Lemma notin_rel_abox_notin_set: forall n x r AB1, ~ In (rel x n r) AB1-> ~  fsetsni.In n (set_y_in_abox x r AB1).
Proof.
intros; unfold set_y_in_abox .
apply FP.fold_rec_nodep ;intros.
auto with set.

induction x0; simpl ; auto .

unfold eq_ni , eq_role.
case (NP.Dec.F.eq_dec n0 x) ;intro ;simpl ; auto .

case (eq_dec_role ); intro ; simpl ;auto .
inversion e.
subst.

rewrite(NiD.F.add_iff) ; intro.
inversion_clear H2 ;auto .
rewrite H3 in *; auto .
Qed.




