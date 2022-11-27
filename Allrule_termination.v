Add Rec LoadPath "~/color82" as CoLoR.	
Require Export Measure_theory.


Lemma compat_const :compat_op Fact_as_DT.eq  fsetsni.Equal construct_set_in_fact. 
Proof.
unfold compat_op.
intros.
inversion_clear H.
induction x'; simpl ;
 rewrite H0; 
intuition.
 Qed.


Lemma transp_const :   transpose fsetsni.Equal construct_set_in_fact  .
Proof.
unfold transpose.
double induction   x y  ;  intros ;  simpl  ;   NiD.fsetdec.
Qed.

Lemma dec_eq_gtA : forall a b, geA a b -> {gtA a b}+{a = b}. 
Proof.
intros.
case (eqA_dec a b); intro.
right ; auto.
left.
inversion_clear H.
auto with *.
tauto.
Qed.

 Lemma trois : forall s n c , In (inst n c) s ->   fsetsni.In n (set_ni_in_abox s).
Proof.
intros; unfold set_ni_in_abox .
rewrite  <-  ( FP.remove_fold_1 Eq_cr compat_const transp_const _ H).
simpl.
intuition.
Qed.

Lemma trois2:  forall s n c  , ~ fsetsni.In n (set_ni_in_abox s) ->~  In (inst n c) s.
Proof.
intros ; intro.
apply H; auto.
apply( trois s n c) ; auto.
Qed.

Lemma Quatre : forall s n r x , In (rel x n r) s ->   fsetsni.In n (set_ni_in_abox s).
Proof.
intros; unfold set_ni_in_abox .
rewrite  <-  ( FP.remove_fold_1 Eq_cr compat_const transp_const _ H).
simpl.
intuition.
Qed.

Lemma quatre2 : forall s n r x ,  ~  fsetsni.In n (set_ni_in_abox s) -> ~ In (rel x n r) s.
Proof.
intros.
intro ; apply H.
apply (Quatre s n r x  H0).
Qed.
Hint Resolve quatre2 Quatre trois2 trois.
Lemma union_empty :  forall a, union empty  a [=] a.
Proof.
auto with *.
Qed.

Hint Resolve  union_empty.

Lemma set_of_some_term_g_eq  : forall n r c s1 s2 ,  Allrule s2 s1 -> In (inst n (AllC r c)) s2  -> set_of_some_term n r s1[=]set_of_some_term n r s2.
Proof.
intros.
unfold set_of_some_term.
inversion_clear H.
inversion_clear H1.
inversion_clear H3.
subst.
rewrite FactP.MP.fold_add ;auto. unfold  Constract_set_som.
rewrite <-  ( FactP.MP.remove_fold_1  Equivalence_Eq  (Compat_som n r ) (transp_som n r) _ H ).
simpl. unfold  Constract_set_som.
simpl. FiD.fsetdec. 
Qed.

Lemma set_of_some_term_subs : forall n r c s1 s2 ,  Allrule s2 s1 -> In (inst n (AllC r c)) s2 -> set_of_some_term_r n r s1[<=]set_of_some_term_r n r s2.
Proof.
intros.
unfold set_of_some_term_r.
rewrite  (FP.fold_equal _ (compat_css s1)  (transp_css s1) empty (set_of_some_term_g_eq n r c s1 s2 H H0)) ; auto.
inversion_clear H.
inversion_clear H1.
inversion_clear H3.
rewrite (FP.fold_rel (g:= (Constract_set_som_r s2))(f:=(Constract_set_som_r s1) ) (j:= empty)).
auto with *.
auto with *.
intros.
unfold Constract_set_som_r .
unfold some_terme_reductble.
case(some_applicable_or_not_2 x0 s1);intro.
case(some_applicable_or_not_2 x0 s2); intro.
FiD.fsetdec. 
apply False_ind.
apply n0.
inversion_clear s.
inversion_clear H6.
apply (App_some_2 _ _ x1 r1 c0).
split.
auto with *.
intros.
intro.
apply (H8 y0).
inversion_clear H6.
split.
subst.
FiD.fsetdec.
subst.
FiD.fsetdec.
case(some_applicable_or_not_2 x0 s2); intro.
FiD.fsetdec.
FiD.fsetdec.
Qed.

(**********************************************************************)
Lemma set_of_some_term_cardinal  : forall n r c s1 s2 ,  Allrule s2 s1 -> In (inst n (AllC r c)) s2 -> cardinal (set_of_some_term_r n r s1) <= cardinal (set_of_some_term_r n r s2).
Proof.
intros.
apply (FP.subset_cardinal).
apply (set_of_some_term_subs n r c s1 s2) ;auto.
Qed.

Lemma transitif : forall a b c, b >= c -> geA (a,b) (a,c).
intros.
red.
unfold gtA.
simpl.
assert (  { b = c} + {b<> c}).
decide equality.
inversion_clear H0.
right.
inversion_clear H1.
intuition.
left.
omega.
Qed.

Lemma lah : forall a b c ,fsetsni.Subset  b  c -> fsetsni.Subset (fsetsni.diff a c) (fsetsni.diff a b). 
Proof.
intros.
NiD.fsetdec.
Qed.

Lemma set_of_xc_term_subs : forall n r c s1 s2 ,  Allrule s2 s1 -> In (inst n (AllC r c)) s2 -> fsetsni.Subset (set_y_c_in_abox c s2) (set_y_c_in_abox c s1).
Proof.
intros.
inversion_clear H.
inversion_clear H1.
inversion_clear H3.
unfold set_y_c_in_abox .
subst.
red.
intros.
rewrite FactP.MP.fold_add ;auto ;simpl.
case (eq_dec_concept c c1) ; intro ; auto with *.
Qed.

Lemma set_of_xyr_eq : forall n r c s1 s2 ,  Allrule s2 s1 -> In (inst n (AllC r c)) s2 ->  fsetsni.Equal (set_y_in_abox n r s2) (set_y_in_abox n r s1).
Proof.
intros.
inversion_clear H.
inversion_clear H1.
inversion_clear H3.
unfold set_y_in_abox .
subst. rewrite FactP.MP.fold_add ;auto ;simpl.
auto with *.
Qed.

(******* this the important lemma *****************)
Lemma mia : forall a d b c ,fsetsni.Equal  a  d -> (fsetsni.Subset b c) -> fsetsni.Subset  (fsetsni.diff a c )       (fsetsni.diff d  b).
intros.
NiD.fsetdec.
Qed.

Lemma measure_off_all : forall n r c s1 s2 ,  Allrule s2 s1 -> In (inst n (AllC r c)) s2 -> geA (mes_comp s2 (inst n (AllC r c))) (mes_comp s1 (inst n (AllC r c))).
Proof.
intros.
unfold mes_comp.
inversion H.
inversion_clear H1.
inversion_clear H4.
assert(set_rel n c r s2 >= set_rel n c r s1).
red.
apply NP.subset_cardinal.
apply mia.
symmetry.
apply  (set_of_xyr_eq  n r c s1 s2 ); auto. apply (set_of_xc_term_subs n r c s1 s2); auto.
generalize (set_of_some_term_cardinal  n r c s1 s2  H H0); intro.
red  in H4.
inversion H4.
inversion H6.
unfold geA.
right.
auto with *.
inversion H9.
left.
unfold gtA.
right.
simpl.
auto with *.
left.
unfold gtA.
right.
simpl.
auto with *.
left.
unfold gtA.
right.
simpl.
auto with *.
Qed.

Lemma first :  forall f s1 s2 ,Allrule s2 s1  -> In f s2 ->  geA  (mes_comp s2 f)  (mes_comp s1 f ).
Proof.
intros.
induction f.
induction c.
red  ; auto with *.
red  ; auto with *.
red  ; auto with *.
red  ; auto with *.
(***** cas  du And *********************)
simpl.
case (and_applicable_or_not (inst n (AndC c1 c2)) s2) ; intros.
case (and_applicable_or_not (inst n (AndC c1 c2)) s1); intros.
right.
auto with *.
left.
left.
simpl.
auto with *.
case (and_applicable_or_not (inst n (AndC c1 c2)) s1); intros.
apply False_ind.
apply n0.
inversion_clear a.
inversion_clear H1.
inversion_clear H3.
inversion_clear H.
clear IHc1 IHc2.
inversion H2.
subst. apply (App_and _ _  n c1 c2 ); split ; auto with *.
split ; auto with *.
intro. apply H4.
split.
inversion_clear H.
FiD.fsetdec.
inversion_clear H.
FiD.fsetdec.
unfold geA.
right.
auto with *.
simpl.
case (or_applicable_or_not (inst n (OrC c1 c2)) s2) ; intros.
case (or_applicable_or_not (inst n (OrC c1 c2)) s1); intros.
right. auto with *.
left.
left.
simpl.
auto with *.
case (or_applicable_or_not (inst n (OrC c1 c2)) s1); intros.
apply False_ind.
apply n0.
inversion_clear o.
inversion_clear H1.
inversion_clear H3.
inversion_clear H4.
clear IHc1 IHc2.
inversion H2.
subst. apply (App_or  _ _  n c1 c2 ); split ; auto with *.
split ; auto with *.
split.
inversion_clear H.
intro. apply H3.
subst.
FiD.fsetdec.
inversion_clear H.
intro.
apply H5.
subst.
FiD.fsetdec.
right.
auto with *.
(**********************************************)
apply (measure_off_all  n r c s1 s2); auto.
(******************************************)
simpl.
clear IHc.
case(some_applicable_or_not (inst n (SomeC r c)) s2) ; intro.
case(some_applicable_or_not (inst n (SomeC r c)) s1) ; intro.
right; auto.
auto with *.
left.
unfold gtA.
left.
simpl.
auto with *.
case(some_applicable_or_not (inst n (SomeC r c)) s1) ; intro.
apply False_ind.
apply n0; clear n0.
inversion_clear s.
inversion_clear H1.
inversion_clear H3.
inversion_clear H.
inversion H2.
subst.
clear H2.
apply (App_some _ _ x r0 c1).
split.
auto.
split.
auto.
intro. intro.
apply (H4 y0); clear H4.
inversion_clear H.
split.
FiD.fsetdec.
FiD.fsetdec.
right.
auto with *.
simpl.
right.
auto with *.
right.
auto with *.
Qed.

Lemma compat_flip: forall s,
compat_op Fact_as_DT.eq  (flip meq) (construct_Multiset s).
Proof.
 red; unfold flip ,construct_Multiset .
intros.
inversion_clear H.
solve_meq.
Qed.

Lemma transp_flip : forall s , transpose (flip meq) (construct_Multiset s).
Proof.
red.
unfold construct_Multiset , flip .
intros ; solve_meq.
Qed.

Hint Resolve compat_flip transp_flip.

Lemma dec_gt_eq_measure : forall f s1 s2 ,Allrule s2 s1  -> In f s2 ->  {gtA  (mes_comp s2 f)  (mes_comp s1 f )} + {(mes_comp s2 f)  =(mes_comp s1 f ) }.
Proof.
intros; apply dec_eq_gtA.
 apply first ; auto.
Qed.
(*****************************)
Lemma mo : forall a b c d , a>b -> c>=d -> a +c > b+ d.
Proof.
intros;  omega.
Qed.

Lemma poop: forall a b y ,  fsetsni.In y a -> fsetsni.In y b -> ~ fsetsni.In y (fsetsni.diff a b).
intros.
NiD.fsetdec.
Qed.

Lemma mah2 : forall a b c,   b <= c ->c < a -> b < a.
intros.
omega.
Qed.

Lemma allrule_decrease : forall  s1 s2,  Allrule s2 s1 ->MultisetLT gtA   (Measure2 s1  s1) (Measure2 s2 s2).
Proof.
intros.
unfold MultisetLT.
unfold transp.
inversion H.
inversion_clear H0.
inversion_clear H3.
(*************************************)
assert (s2 [=] add  (inst x (AllC r c1)) (remove (inst x (AllC r c1))  s2)). 
FiD.fsetdec.
assert ( Measure2 s2 s2 =mul=  (fold (construct_Multiset s2) (remove (inst x (AllC r c1)) s2)
    {{ (mes_comp s2 (inst x (AllC r c1))) }})).
generalize ( Mesure_equal_1 s2 _ _ H3) ;intro.
rewrite H5.
unfold Measure2.
rewrite( FP.fold_add); auto with *. 
rewrite  <-    (FP.fold_commutes) ; auto with * .
symmetry in H5.
apply (MultisetGT_equal2 _ _ _ H5).
clear H5.
(*****************************************)
assert ( Measure2 s1 s1 =mul=  fold (construct_Multiset s1) (remove (inst x (AllC r c1)) s2)
       ({{mes_comp s1 (inst x (AllC r c1))}} +
   ({{mes_comp s1 (inst y c1)}}  + MSetCore.empty))).
assert ( s1  [=]  (add (inst y c1) (add (inst x (AllC r c1)) (remove (inst x (AllC r c1))s2)))).
rewrite <- H3 ; rewrite H1; intuition.
generalize ( Mesure_equal_1 s1 _ _ H5) ;intro Hi ;
rewrite Hi; clear Hi H5 H3.
unfold Measure2.
rewrite( FP.fold_add); auto with *. 
rewrite  <-    (FP.fold_commutes) ; auto with * .
rewrite( FP.fold_add); auto with *. 
rewrite  <-    (FP.fold_commutes) ; auto with * .
rewrite (FP.add_remove).
auto.
auto.
symmetry in H5.
apply (MultisetGT_equal _ _ _ H5).
clear H5 H3.
(*******************************************)
apply (FP.fold_rel (A:= Multiset)( B:= Multiset) (R:=MultisetLT gtA)) .
(************************************)
apply  (MSetGT  _ (X:= {{mes_comp s2 (inst x (AllC r c1))}} )
      (Y:=({{mes_comp s1 (inst x (AllC r c1))}} +
   ({{mes_comp s1 (inst y c1)}} +
    MSetCore.empty))) 
(Z:=MSetCore.empty)).
auto with *.
auto with *.
auto with *.
intros.
exists (mes_comp s2 (inst x (AllC r c1))).
auto with *.
apply member_union in H3.
inversion_clear H3.
apply member_singleton in H5.
rewrite H5.
unfold mes_comp.
(*************************************)
unfold set_rel .
unfold gtA.
right.
simpl.
split.
auto with *.
apply mo.
Focus 2.
apply (set_of_some_term_cardinal  x r c1 s1 s2); auto.
rewrite <- (set_of_xyr_eq _ r c1 _ _ H H2).
assert (fsetsni.Equal (set_y_c_in_abox c1 s1) (fsetsni.add y (set_y_c_in_abox c1 s2) )).
unfold set_y_c_in_abox .
subst.
 rewrite( FP.fold_add); auto . simpl.
case (eq_dec_concept c1 c1); intro;
intuition.
rewrite H3.
red.
apply (NP.subset_cardinal_lt (x:=y)). apply mia ; auto with *.
apply fsetsni.diff_3.
unfold set_y_in_abox.
rewrite <- ( FP.remove_fold_1 _ (compat_r x r) (transp_r x r) _ H0).
simpl.
unfold eq_ni.
case(NP.Dec.F.eq_dec x x) ; intro. 
unfold eq_role.
case(eq_dec_role r r); intro. simpl.
auto with *.
tauto.
elim n.
auto with *.
unfold set_y_c_in_abox.
apply  FP.fold_rel.
auto with *.
induction  x0.
intros.
simpl.
case (eq_dec_concept c1 c).
intro.
case(NI_as_DT.eq_dec n y). intro.
inversion e0.
subst.
tauto.
intros.
NiD.fsetdec.
intros.
auto.
simpl.
auto with *.
simpl.
auto with *.
apply poop.
unfold set_y_in_abox. rewrite <- ( FP.remove_fold_1 _ (compat_r x r) (transp_r x r) _ H0).
simpl.
unfold eq_ni.
case(NP.Dec.F.eq_dec x x) ; intro. 
unfold eq_role.
case(eq_dec_role r r); intro. simpl.
auto with *.
tauto.
elim n.
auto with *.
auto with *.
(************************************************)
apply member_union in H5.
inversion_clear H5.
apply member_singleton in H3.
rewrite H3.
left. generalize (fst_comp_lq_sizec  s1  y  c1) ;intro. red. 
apply (mah2 (fst (mes_comp s2 (inst x (AllC r c1))) )(fst (mes_comp s1 (inst y c1)) ) (sizeC c1) H5).
simpl.
auto.
inversion H3.
(******************************************************************************************)
intros.
assert (In x0 s2).  FiD.fsetdec.
case (dec_gt_eq_measure x0 s1 s2 H H6); intro.
inversion_clear H5.
unfold construct_Multiset.
apply (MSetGT _ (X:= X + {{mes_comp s2 x0}})( Y:= Y+{{(mes_comp s1  x0) }})(Z := Z) ).
auto with *.
rewrite H8.
solve_meq.
rewrite H9.
solve_meq.
intros.
apply member_union in H5.
inversion_clear H5.
generalize  (H10 y0 H11); intro.
inversion_clear H5.
exists x1 ; intuition. exists (mes_comp s2 x0) .
auto with *.
apply member_singleton in H11.
inversion_clear H11.
auto.
inversion_clear H5.
(**********************************************)
apply (MSetGT _ (X:= X )( Y:= Y) (Z := Z+ {{mes_comp s2 x0}}) ).
intuition.
unfold construct_Multiset.
rewrite H8; solve_meq.
unfold construct_Multiset.
rewrite H9. rewrite e. solve_meq.
intro;  apply ( H10 y0).
Qed.