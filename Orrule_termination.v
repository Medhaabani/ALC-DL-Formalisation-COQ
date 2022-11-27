Add Rec LoadPath "color82" as CoLoR.	
Require Export Measure_theory.

Lemma some_same2 : forall x r n  c1 c2 AB1, In (inst n (OrC c1 c2)) AB1-> ~  In (inst n c1) AB1->
  (set_of_some_term x  r AB1) [=]  (set_of_some_term x  r (add (inst n c1) AB1)).
Proof.
intros.
unfold set_of_some_term.
rewrite ( FactP.MP.fold_add  Equivalence_Eq  (Compat_som x r ) (transp_som x r) _ H0).
unfold Constract_set_som .
rewrite  <- ((FP.remove_fold_1 Equivalence_Eq  (Compat_som x r) (transp_som x r)  empty H)).
unfold Constract_set_som.
simpl. intros. rewrite <-  (FP.union_assoc).
rewrite <-  (FP.union_assoc).
assert(Equal (union (some_term x r c1) (some_term x r c2)) 
(union (union (some_term x r c1) (some_term x r c1)) (some_term x r c2))).
FiD.fsetdec.
rewrite H1.
FiD.fsetdec.
Qed.

Lemma mes_all1 : forall x n c c1 r AB1  , 
In ( inst x (AllC r c))  AB1 ->In (inst n c1) AB1->
 (mes_comp   AB1 ( inst x (AllC r c))) =   (mes_comp  (add (inst n c1) AB1) ( inst x (AllC r c))).
Proof.
intros.
apply equal_mes_comp .
auto with *.
Qed.

Lemma some_same_r_O  : forall x r n  c1 c2 AB1, In (inst n (OrC c1 c2)) AB1-> ~  In (inst n c1) AB1->
 (Subset  (set_of_some_term_r  x  r (add (inst n c1) AB1)) (set_of_some_term_r x  r AB1)).
Proof.
intros ;unfold set_of_some_term_r.
generalize (some_same2 x r n  c1 c2 AB1 H H0); intro.
assert (fold (Constract_set_som_r (add (inst n c1) AB1)) (set_of_some_term x r (add (inst n c1) AB1)) empty  [=]fold (Constract_set_som_r (add (inst n c1) AB1))
  (set_of_some_term x r AB1) empty).
apply  (FP.fold_equal Equivalence_Eq) ;auto.
auto with *.
rewrite H2.
(******************************************************)
rewrite  (FP.fold_rel (f:= (Constract_set_som_r (add (inst n c1) AB1)))(g:=  (Constract_set_som_r AB1))(j:= empty)).
auto with *.
auto with *.
clear H1  H2.
intros.
unfold Constract_set_som_r.
unfold some_terme_reductble.
(*************************************)
case(some_applicable_or_not_2 x0 (add (inst n c1) AB1)); intro.
case(some_applicable_or_not_2 x0 AB1); intro.
FiD.fsetdec.
(************************************)
apply False_ind.
apply n0; clear n0.
inversion_clear s.
inversion_clear H3.
apply (App_some_2 _ _ x1 r0 c0).
split ; auto. intro.
generalize (H5 y); intro.
intro.
apply H3.
inversion_clear H6.
split.
auto with *.
auto with *.
(******************************************************)
case(some_applicable_or_not_2 x0 AB1); intro.
FiD.fsetdec.
FiD.fsetdec.
Qed.

Lemma some_gte_o  : forall x r n  c1 c2 AB1, In (inst n (OrC c1 c2)) AB1-> ~  In (inst n c1) AB1->
 (cardinal (set_of_some_term_r  x  r (add (inst n c1) AB1)) <= cardinal (set_of_some_term_r x  r AB1)).
Proof.
intros.
apply FP.subset_cardinal.
apply ( some_same_r_O x r n  c1 c2 AB1); auto.
Qed.

Lemma mes_all2 : forall x n c c1 c2 r AB1  , 
In ( inst x (AllC r c))  AB1 -> In (inst n (OrC c1 c2)) AB1-> ~  In (inst n c1) AB1->
{gtA (mes_comp   AB1 ( inst x (AllC r c)))   ((mes_comp   (add (inst n c1) AB1) ( inst x (AllC r c))))}
 + {(mes_comp   AB1 ( inst x (AllC r c))) =   (mes_comp  (add (inst n c1) AB1) ( inst x (AllC r c)))}.

Proof.
(***********************************************)
intros.
simpl.
(*********************************************************)
assert ({set_rel x  c r AB1 > (set_rel x  c r (add (inst n c1) AB1))}
+ 
{ set_rel x  c r AB1 =(set_rel x  c r (add (inst n c1) AB1) ) }).
(***********************************************)
case (eq_dec_concept c c1) ; intro.
subst.
case ( FactP.MP.In_dec  (rel x n r ) AB1  ); intro.
(***************************************************************)
(*************************Le premier cas *********************)
left ; unfold set_rel .
(********Assert 1******************************)
assert (fsetsni.Equal (set_y_in_abox x r AB1) (set_y_in_abox x r (add (inst n c1) AB1)  )).
unfold set_y_in_abox.
rewrite (FP.fold_add Eq_cr (compat_r x r) (transp_r x r) _ H1).
auto with *.
(********Assert 2*********************)
assert (fsetsni.Equal (set_y_c_in_abox c1 (add (inst n c1) AB1)) (fsetsni.add n (set_y_c_in_abox  c1 AB1))).
unfold set_y_c_in_abox.
rewrite (FP.fold_add Eq_cr (compat_c c1) (transp_c c1) _ H1 ).
simpl.
case (eq_dec_concept c1 c1) ;intros.
auto with set.
tauto.
(***************************)
rewrite <-   H2. 
rewrite  H3.
(******* Assert 3**********************)
assert (fsetsni.In  n (set_y_in_abox x r (add (inst n c1) AB1))).
unfold set_y_in_abox.
assert (In (rel x n r) (add (inst n c1) AB1)).
FiD.fsetdec.
rewrite <-  ( FP.remove_fold_1 Eq_cr (f:=(construct_set_of_y_in_rel x r) ) (compat_r x r)(transp_r  x r) fsetsni.empty H4 ).
simpl.
assert (eq_ni x x && eq_role r r = true).
unfold eq_ni.
unfold eq_role.
case(NP.Dec.F.eq_dec x x ); intros; intuition.
case(eq_dec_role r r  ) ;intros ; intuition.
rewrite H5 ;intuition.
(*************Assert 4 ***********************)
assert(fsetsni.cardinal (fsetsni.diff (set_y_in_abox x r AB1) (set_y_c_in_abox c1 AB1)) = S(fsetsni.cardinal
  (fsetsni.diff (set_y_in_abox x r AB1)
     (fsetsni.add n (set_y_c_in_abox c1 AB1))) )).
apply (NP.cardinal_2 ( x:= n)  ). 
NiD.fsetdec.
(*************************)
unfold NP.Add ; intros.
split.
(**********************)
intros.
case (NI_as_DT.eq_dec n y); intro.
inversion e.
left; auto.
right ; apply fsetsni.diff_3; NiD.fsetdec.
 intro.
inversion_clear H5.
subst.
apply fsetsni.diff_3.
NiD.fsetdec.
(******************************************)
apply (notin_inst_abox_notin_set  _ _ _ H1).
NiD.fsetdec.
rewrite H5 ; auto.
(****************************************************************)
(*********le deuxieme cas*******************************************************)
right.
unfold set_rel .
(******************Assert 1**************************)
unfold set_y_in_abox.
rewrite (FP.fold_add Eq_cr (compat_r x r) (transp_r x r) _ H1).
fold ( (set_y_in_abox x r AB1) ).
(*************************************)
apply  (NiP.equal_cardinal ). 
apply fsetsni.equal_1.
red.
split.
intros.
case (NI_as_DT.eq_dec n a).
intros.
inversion e.
subst.
generalize(notin_rel_abox_notin_set _ _ _   _ n0).
intros.
apply fsetsni.diff_1 in H2.
auto with *.
intros.
apply fsetsni.diff_3.
NiD.fsetdec.
unfold set_y_c_in_abox.
rewrite FP.fold_add ; auto.
simpl.
case (eq_dec_concept c1 c1 ).
intros.
fold (set_y_c_in_abox c1 AB1).
intro.
apply fsetsni.diff_2 in H2. 
apply H2.
NiD.fsetdec.
intro.
tauto.
intros.
apply fsetsni.diff_3.
NiD.fsetdec.
apply fsetsni.diff_2 in H2. 
intro.
apply H2.
unfold set_y_c_in_abox.
rewrite FP.fold_add ; auto.
simpl.
case (eq_dec_concept c1 c1 ). intros. NiD.fsetdec.
intro.
auto.
(***************last case***********************************)
intros.
right.
unfold set_rel .
unfold set_y_in_abox.
rewrite (FP.fold_add Eq_cr (compat_r x r) (transp_r x r) _ H1).
auto with *.
(*********************************************)
unfold set_y_c_in_abox. 
rewrite FP.fold_add ; auto.
simpl.
case (eq_dec_concept c c1); intro.
tauto.
intuition.
generalize  (some_gte_o  x  r n c1 c2 AB1 H0 H1); intro.
inversion_clear H2.
left.
unfold gtA.
right; simpl; intuition.
assert (forall a b,  a<= b -> a =b \/ a <b).
intros.
omega.
generalize (H2 _ _ H3).
intros.
assert ( {cardinal (set_of_some_term_r x r (add (inst n c1) AB1)) =
     cardinal (set_of_some_term_r x r AB1)} + {cardinal (set_of_some_term_r x r (add (inst n c1) AB1)) <>
     cardinal (set_of_some_term_r x r AB1)}).
auto with *.
inversion_clear H6.
right.
auto with *.
left.
unfold gtA.
right; simpl; intuition.
Qed. 

Lemma mes_all : forall x n c c1 c2 r AB1 , 
In ( inst x (AllC r c))  AB1 -> In (inst n (OrC c1 c2)) AB1-> 
{gtA (mes_comp   AB1 ( inst x (AllC r c)))   ((mes_comp   (add (inst n c1) AB1) ( inst x (AllC r c))))}
 + {(mes_comp   AB1 ( inst x (AllC r c))) =   (mes_comp  (add (inst n c1) AB1) ( inst x (AllC r c)))}.
Proof.
intros.
 case (FP.In_dec  (inst n c1) AB1).
intro.
right.
apply mes_all1.
auto.
auto.
intros. 
apply (mes_all2 x n c c1 c2 r AB1).
auto.
auto.
auto.
Qed.

Lemma dec_eq_gt_in_remov2  : forall  c1 c2 x s2 ,  In (inst x  (OrC c1 c2)) s2-> ~ In (inst x  c1) s2 ->~ In (inst x  c2) s2->
                                      forall f,  In f (remove (inst x (OrC c1 c2) ) s2) ->
             ({ gtA  (mes_comp s2 f)  (mes_comp ((add (inst x c1) s2))f )}
          +          {   (mes_comp s2 f)  =  (mes_comp ( (add (inst x c1)s2))f )}).

Proof.
intros.
induction f ; intros . 
case ( Fact_as_DT.eq_dec (inst x (OrC c1 c2)) (inst n  c ) ); intro.
rewrite e in H2.
assert(~ In (inst n c) (remove (inst n c) s2)).
auto with *.
tauto.
(************************)
induction  c ; 
auto with *.
(***************************************)
simpl.
case(and_applicable_or_not (inst n (AndC c3 c4)) s2); intro.
case(and_applicable_or_not (inst n (AndC c3 c4))  (add (inst x c1) s2)); intro.
right.
auto with *.
left.
  unfold gtA;left ;  simpl ; auto with *.
(***************************)
case(and_applicable_or_not (inst n (AndC c3 c4)) (add (inst x c1) s2)); intros.
assert (  False) .
clear IHc1 IHc2.
apply n1.
inversion_clear a.
inversion_clear H3.
inversion_clear H5.
inversion H4.
subst.
apply (App_and (inst n (AndC c3 c4))  s2 n c3 c4).
split.
auto.
split.
FiD.fsetdec.
FiD.fsetdec.
tauto.
auto.
(****************************************************************)
simpl.
case(or_applicable_or_not (inst n (OrC c3 c4)) s2) ;intro.
case(or_applicable_or_not (inst n (OrC c3 c4)) (add (inst x c1) s2)); intro.
right.
auto with *.
(*****************)
 left.
 unfold gtA ; left ; simpl ; auto with *.
case(or_applicable_or_not (inst n (OrC c3 c4)) (add (inst x c1) s2)); intros.
assert (False).
inversion_clear o.
inversion_clear H3.
inversion_clear H5.
inversion_clear H6.
inversion H4.
rewrite  H8 , H9 , H10 in *; clear H8 H9 H10 H4.
apply n1.
apply (App_or (inst n (OrC c3 c4))  s2 n c3 c4).
split.
trivial.
split.
FiD.fsetdec.
FiD.fsetdec.
tauto.
auto with *.
(*********************************************)
apply (mes_all2  n x  c c1 c2 r s2).  
FiD.fsetdec.
auto with *.
auto with *.
(***************************************************)
simpl.
case(some_applicable_or_not (inst n (SomeC r c)) s2).
intro.
case (some_applicable_or_not (inst n (SomeC r c)) ( (add (inst x c1) s2))).
intros.
right.
auto with *.
intros.
left.
red.
left.
simpl.
auto with *.
intros.
case (some_applicable_or_not (inst n (SomeC r c)) ( (add (inst x c1) s2))).
intros.
assert (False).
apply n1.
inversion_clear s.
inversion_clear H3.
inversion H4.
rewrite H8 , H6 , H7 in *; clear H8 H6 H7 H4.
apply (App_some  (inst x0 (SomeC r0 c0)) s2 x0 r0 c0).
split.
auto.
split ; auto.
FiD.fsetdec.
intro.
inversion_clear H5.
generalize (H4 y); intro.
intro.
inversion_clear H6.
apply H5.
auto with *.
tauto.
intros; right; auto.
simpl.
auto with *.
simpl.
auto with *.
Qed.

(******************************************************************************)
Lemma some_same11_o  : forall x r n  c1 c2 AB1, In (inst n (OrC c1 c2)) AB1-> ~  In (inst n c2) AB1->
  (set_of_some_term x  r AB1) [=]  (set_of_some_term x  r (add (inst n c2) AB1)).
Proof.
intros.
unfold set_of_some_term.
rewrite ( FactP.MP.fold_add  Equivalence_Eq  (Compat_som x r ) (transp_som x r) _ H0).
unfold Constract_set_som .
rewrite  <- ((FP.remove_fold_1 Equivalence_Eq  (Compat_som x r) (transp_som x r)  empty H)).
unfold Constract_set_som.
simpl.
intros. rewrite <-  (FP.union_assoc).
rewrite <-  (FP.union_assoc).
assert(Equal (union (some_term x r c1) (some_term x r c2)) 
(union (union (some_term x r c1) (some_term x r c1)) (some_term x r c2))).
FiD.fsetdec.
rewrite H1.
FiD.fsetdec.
Qed.

Lemma some_same_r_2_o  : forall x r n  c1 c2 AB1, In (inst n (OrC c1 c2)) AB1-> ~  In (inst n c2) AB1->
 (Subset  (set_of_some_term_r  x  r (add (inst n c2) AB1)) (set_of_some_term_r x  r AB1)).
Proof.
intros ;unfold set_of_some_term_r.
generalize (some_same11_o  x r n  c1 c2 AB1 H H0); intro.
assert (fold (Constract_set_som_r (add (inst n c2) AB1)) (set_of_some_term x r (add (inst n c2) AB1)) empty  [=]fold (Constract_set_som_r (add (inst n c2) AB1))
  (set_of_some_term x r AB1) empty).
apply  (FP.fold_equal Equivalence_Eq) ;auto.
auto with *.
rewrite H2.
(******************************************************)
rewrite  (FP.fold_rel (f:= (Constract_set_som_r (add (inst n c2) AB1)))(g:=  (Constract_set_som_r AB1))(j:= empty)).
auto with *.
auto with *.
clear H1  H2.
intros.
unfold Constract_set_som_r.
unfold some_terme_reductble.
(*************************************)
case(some_applicable_or_not_2 x0 (add (inst n c2) AB1)); intro.
case(some_applicable_or_not_2 x0 AB1); intro.
FiD.fsetdec.
(************************************)
apply False_ind.
apply n0; clear n0.
inversion_clear s.
inversion_clear H3.
apply (App_some_2 _ _ x1 r0 c0).
split ; auto. intro.
generalize (H5 y); intro.
intro.
apply H3.
inversion_clear H6.
split.
auto with *.
auto with *.
(******************************************************)
case(some_applicable_or_not_2 x0 AB1); intro.
FiD.fsetdec.
FiD.fsetdec.
Qed.

Lemma some_gte_2_o  : forall x r n  c1 c2 AB1, In (inst n (OrC c1 c2)) AB1-> ~  In (inst n c2) AB1->
 (cardinal (set_of_some_term_r  x  r (add (inst n c2) AB1)) <= cardinal (set_of_some_term_r x  r AB1)).
Proof.
intros.
apply FP.subset_cardinal.
apply ( some_same_r_2_o  x r n  c1 c2 AB1); auto.
Qed.

Lemma mes_all3 : forall x n c c1 c2 r AB1  , 
In ( inst x (AllC r c))  AB1 -> In (inst n (OrC c1 c2)) AB1-> ~  In (inst n c2) AB1->
{gtA (mes_comp   AB1 ( inst x (AllC r c)))   ((mes_comp   (add (inst n c2) AB1) ( inst x (AllC r c))))}
 + {(mes_comp   AB1 ( inst x (AllC r c))) =   (mes_comp  (add (inst n c2) AB1) ( inst x (AllC r c)))}.
Proof.
intros.
simpl.
(*********************************************************)
assert ({set_rel x  c r AB1 > (set_rel x  c r (add (inst n c2) AB1))}
+ 
{ set_rel x  c r AB1 =(set_rel x  c r (add (inst n c2) AB1) ) }).
(***********************************************)
case (eq_dec_concept c c2).
intro.
subst.
case ( FactP.MP.In_dec  (rel x n r ) AB1  ).
intros.
left.
(*************************Le premier cas *********************)
unfold set_rel .
assert (fsetsni.Equal (set_y_in_abox x r AB1) (set_y_in_abox x r (add (inst n c2) AB1)  )).
unfold set_y_in_abox.
rewrite (FP.fold_add Eq_cr (compat_r x r) (transp_r x r) _ H1).
auto with *.
(******cardinal_fold*************************)

 assert (fsetsni.Equal (set_y_c_in_abox c2 (add (inst n c2) AB1)) (fsetsni.add n (set_y_c_in_abox  c2 AB1))).
unfold set_y_c_in_abox.
rewrite (FP.fold_add Eq_cr (compat_c c2) (transp_c c2) _ H1 ).
simpl.
case (eq_dec_concept c2 c2).
auto with set.
tauto.
(*****************************)
rewrite <-   H2. 
rewrite  H3.
assert (fsetsni.In  n (set_y_in_abox x r (add (inst n c2) AB1))).
unfold set_y_in_abox.
assert (In (rel x n r) (add (inst n c2) AB1)).
FiD.fsetdec.
rewrite <-  ( FP.remove_fold_1 Eq_cr (f:=(construct_set_of_y_in_rel x r) ) (compat_r x r)(transp_r  x r) fsetsni.empty H4).
simpl.
assert (eq_ni x x && eq_role r r = true).
unfold eq_ni.
unfold eq_role.
case(NP.Dec.F.eq_dec x x ).
case(eq_dec_role r r  ).
auto with *.
tauto.
intro.
auto with *.
rewrite H5.
auto with *.
assert(fsetsni.cardinal (fsetsni.diff (set_y_in_abox x r AB1) (set_y_c_in_abox c2 AB1)) = S(fsetsni.cardinal
  (fsetsni.diff (set_y_in_abox x r AB1)
     (fsetsni.add n (set_y_c_in_abox c2 AB1))) )).

apply (NP.cardinal_2 ( x:= n)  ).
NiD.fsetdec.
unfold NP.Add .
intros.
(*********************************************************)
split.
intros.
case (NI_as_DT.eq_dec n y).
intro.
inversion e.
left.
auto.
intros.
right.
apply fsetsni.diff_3.
NiD.fsetdec.
NiD.fsetdec.
intro.
inversion_clear H5.
subst.
apply fsetsni.diff_3.
NiD.fsetdec.
(******************************************)
apply (notin_inst_abox_notin_set _ _ _ H1).
NiD.fsetdec.
rewrite H5.
auto.
intros.
(******************************************************)
right.
(******************************)
unfold set_rel .
assert (fsetsni.Equal (set_y_in_abox x r AB1) (set_y_in_abox x r (add (inst n c2) AB1)  )).
unfold set_y_in_abox.
rewrite (FP.fold_add Eq_cr (compat_r x r) (transp_r x r) _ H1).
auto with *.
(*************************************)
rewrite <- H2.
assert (fsetsni.Equal (fsetsni.diff (set_y_in_abox x r AB1) (set_y_c_in_abox c2 AB1)) (fsetsni.diff (set_y_in_abox x r AB1)
     (set_y_c_in_abox c2 (add (inst n c2) AB1)))).
red.
split.
intros.
case (NI_as_DT.eq_dec n a).
intros.
inversion e.
rewrite <-  H4 in *.
generalize(notin_rel_abox_notin_set _ _ _   _ n0).
intros.
apply fsetsni.diff_1 in H3.
auto with *.
intros.
apply fsetsni.diff_3.
NiD.fsetdec.
unfold set_y_c_in_abox.
rewrite FP.fold_add ; auto.
simpl.
case (eq_dec_concept c2 c2 ).
intros.
fold (set_y_c_in_abox c2 AB1).
intro.
apply fsetsni.diff_2 in H3. 
apply H3.
NiD.fsetdec.
intro.
tauto.
intros.
apply fsetsni.diff_3.
NiD.fsetdec.
apply fsetsni.diff_2 in H3. 
intro.
apply H3.
unfold set_y_c_in_abox.
rewrite FP.fold_add ; auto.
simpl.
case (eq_dec_concept c2 c2 ). intros. NiD.fsetdec.
intro.
auto.
auto with *.
(**************************************************)
intros.
right.
unfold set_rel .
assert (fsetsni.Equal (set_y_in_abox x r AB1) (set_y_in_abox x r (add (inst n c2) AB1)  )).
unfold set_y_in_abox.
rewrite (FP.fold_add Eq_cr (compat_r x r) (transp_r x r) _ H1).
auto with *.
(*********************************************)
assert (fsetsni.Equal (set_y_c_in_abox c AB1)  (set_y_c_in_abox c (add (inst n c2) AB1))).
unfold set_y_c_in_abox. 
rewrite FP.fold_add ; auto.
simpl.
case (eq_dec_concept c c2).
intro.
tauto.
intro.
auto with *.
rewrite H2 , H3.
auto with *.
generalize  (some_gte_2_o  x  r n c1 c2 AB1 H0 H1); intro.
inversion_clear H2.
left.
unfold gtA.
right; simpl; intuition.
assert (forall a b,  a<= b -> a =b \/ a <b).
intros.
omega.
generalize (H2 _ _ H3).
intros.
assert ( {cardinal (set_of_some_term_r x r (add (inst n c2) AB1)) =
     cardinal (set_of_some_term_r x r AB1)} + {cardinal (set_of_some_term_r x r (add (inst n c2) AB1)) <>
     cardinal (set_of_some_term_r x r AB1)}).
auto with *.
inversion_clear H6.
right.
auto with *.
left.
unfold gtA.
right; simpl; intuition.
Qed. 

Lemma dec_eq_gt_in_remov3  : forall  c1 c2 x s2 ,  In (inst x  (OrC c1 c2)) s2-> ~ In (inst x  c1) s2 ->~ In (inst x  c2) s2->
                                      forall f,  In f (remove (inst x (OrC c1 c2) ) s2) ->
             ({ gtA  (mes_comp s2 f)  (mes_comp ((add (inst x c2) s2))f )}
          +          {   (mes_comp s2 f)  =  (mes_comp ( (add (inst x c2)s2))f )}).

Proof.
intros.
induction f ; intros . 
case ( Fact_as_DT.eq_dec (inst x (OrC c1 c2)) (inst n  c ) ); intro.
rewrite e in H2.
assert(~ In (inst n c) (remove (inst n c) s2)).
auto with *.
tauto.
(************************)
induction  c ; 
auto with *.
(***************************************)
simpl.
case(and_applicable_or_not (inst n (AndC c3 c4)) s2); intro.
case(and_applicable_or_not (inst n (AndC c3 c4))  (add (inst x c2) s2)); intro.
right.
auto with *.
left.
  unfold gtA;left ;  simpl ; auto with *.
(***************************)
case(and_applicable_or_not (inst n (AndC c3 c4)) (add (inst x c2) s2)); intros.
assert (  False) .
clear IHc1 IHc2.
apply n1.
inversion_clear a.
inversion_clear H3.
inversion_clear H5.
inversion H4.
subst.
apply (App_and (inst n (AndC c3 c4))  s2 n c3 c4).
split.
auto.
split.
FiD.fsetdec.
FiD.fsetdec.
tauto.
auto.
(****************************************************************)
simpl.
case(or_applicable_or_not (inst n (OrC c3 c4)) s2) ;intro.
case(or_applicable_or_not (inst n (OrC c3 c4)) (add (inst x c2) s2)); intro.
right.
auto with *.
(*****************)
 left.
 unfold gtA ; left ; simpl ; auto with *.
case(or_applicable_or_not (inst n (OrC c3 c4)) (add (inst x c2) s2)); intros.
assert (False).
inversion_clear o.
inversion_clear H3.
inversion_clear H5.
inversion_clear H6.
inversion H4.

rewrite  H8 , H9 , H10 in *; clear H8 H9 H10 H4.
apply n1.
apply (App_or (inst n (OrC c3 c4))  s2 n c3 c4).
split.
trivial.
split.
FiD.fsetdec.
FiD.fsetdec.
tauto.
auto with *.
(*********************************************)
apply (mes_all3  n x  c c1 c2 r s2).  
FiD.fsetdec.
auto with *.
auto with *.
(***************************************************)
simpl.
case(some_applicable_or_not (inst n (SomeC r c)) s2).
intro.
case (some_applicable_or_not (inst n (SomeC r c)) ( (add (inst x c2) s2))).
intros.
right.
auto with *.
intros.
left.
red.
left.
simpl.
auto with *.
intros.
case (some_applicable_or_not (inst n (SomeC r c)) ( (add (inst x c2) s2))).
intros.
assert (False).
apply n1.
inversion_clear s.
inversion_clear H3.
inversion H4.
rewrite H8 , H6 , H7 in *; clear H8 H6 H7 H4.
apply (App_some  (inst x0 (SomeC r0 c0)) s2 x0 r0 c0).
split.
auto.
split ; auto.
FiD.fsetdec.
intro.
inversion_clear H5.
generalize (H4 y); intro.
intro.
inversion_clear H6.
apply H5.
auto with *.
tauto.
intros; right; auto.
simpl.
auto with *.
simpl.
auto with *.
Qed.

Lemma orleft_decrease : forall  s1 s2,  Orruleleft s2 s1 ->MultisetLT gtA   (Measure2 s1  s1) (Measure2 s2 s2).
Proof.
intros.
unfold MultisetLT.
unfold transp.
inversion_clear H.
inversion_clear H0.
inversion_clear H2.
generalize H3.
intro htemp.
clear H3.
subst.
(*********************************)
assert (s2 [=] add(inst x (OrC c1 c2)) (remove (inst x (OrC c1 c2))  s2)). 
FiD.fsetdec.
generalize ( Mesure_equal_1 s2 _ _ H1).
assert ((add (inst x c1) s2)  [=] (add (inst x c1) (add (inst x (OrC c1 c2)) (remove (inst x (OrC c1 c2)) s2) ))).
auto with set.
generalize ( Mesure_equal_1 (add (inst x c1) s2) _ _ H2).
clear H1 H2; intros.
symmetry in H1.
  apply (MultisetGT_equal _ _ _ H1).
symmetry in H2.
apply (MultisetGT_equal2 _ _ _ H2).
clear H1 H2.
(******************************************)
assert((Measure2 s2 (add (inst x (OrC c1 c2)) (remove (inst x (OrC c1 c2)) s2)))=mul= 
fold (construct_Multiset s2) (remove (inst x (OrC c1 c2)) s2) (({{mes_comp s2 (inst x (OrC c1 c2))}} + MSetCore.empty))  ).
fold (insert (mes_comp s2 (inst x (OrC c1 c2))) MSetCore.empty) ; fold (construct_Multiset s2 (inst x (OrC c1 c2)) MSetCore.empty) .
unfold Measure2.
rewrite( FP.fold_add); auto with *.
rewrite   (FP.fold_commutes) ; auto .
intuition.
(******************************************)
assert ((Measure2 (add (inst x c1) s2)
     (add (inst x c1)
        (add (inst x (OrC c1 c2)) (remove (inst x (OrC c1 c2)) s2))))
 =mul= 
fold (construct_Multiset (add (inst x c1) s2))  (add (inst x (OrC c1 c2)) (remove (inst x (OrC c1 c2)) s2))
( ({{mes_comp (add (inst x c1) s2) (inst x  c1)}}+ MSetCore.empty))).
fold (insert (mes_comp (add (inst x c1) s2)  (inst x c1)) MSetCore.empty) .  fold (construct_Multiset (add (inst x c1) s2)  (inst x c1) MSetCore.empty) .
unfold Measure2.
rewrite  ( FP.fold_add); auto with *.
rewrite   (FP.fold_commutes) ; auto with * .
FiD.fsetdec.

pose (j :=  ({{mes_comp (add (inst x c1) s2) (inst x c1)}} + MSetCore.empty)).
assert(fold (construct_Multiset (add (inst x c1) s2))
       (add (inst x (OrC c1 c2)) (remove (inst x (OrC c1 c2)) s2)) j=mul=
fold (construct_Multiset (add (inst x c1) s2)) 
 (remove (inst x (OrC c1 c2)) s2) ( {{mes_comp (add (inst x c1) s2) (inst x (OrC c1 c2))}} + j)).
fold (insert (mes_comp (add (inst x c1) s2) (inst x (OrC c1 c2))) j) . fold (construct_Multiset  (add (inst x c1) s2)(inst x (OrC c1 c2)) j) .
 rewrite  ( FP.fold_add); auto with *.
rewrite   (FP.fold_commutes) ; auto with * .
intuition.
symmetry in H1.
apply (MultisetGT_equal2 _ _ _ H1).
symmetry in H2.
apply (MultisetGT_equal _ _ _ H2).
symmetry in H3.
apply (MultisetGT_equal _ _ _ H3).
clear H1 H2 H3.
unfold j; clear j.
(*************************************************)
apply (FP.fold_rel (A:= Multiset)( B:= Multiset) (R:=MultisetLT gtA)) .
apply  (MSetGT  _ (X:= {{mes_comp s2 (inst x (OrC c1 c2))}} )
      (Y:={{mes_comp  (add (inst x c1) s2) (inst x (OrC c1 c2))}} + {{mes_comp (add (inst x c1) s2) (inst x c1)}} )
(Z:=MSetCore.empty)).
auto with *.
auto with *.
auto with *.
intros. exists (mes_comp s2 (inst x (OrC c1 c2))).
auto with *.
(**************************)
apply member_union in H1.
inversion_clear H1.
apply member_singleton in H2.
rewrite H2.
unfold mes_comp.
case( or_applicable_or_not (inst x (OrC c1 c2)) s2); intros.
case (or_applicable_or_not (inst x (OrC c1 c2)) (add (inst x c1) s2)); intros.
apply False_ind.
inversion_clear o0.
inversion_clear H1.
inversion_clear H4.
inversion_clear H5.
inversion H3.
subst.
apply H4.
auto with *.
unfold gtA.
left.
simpl.
auto with *.
apply False_ind.
apply n.
apply (App_or     _     s2 x c1 c2).
auto with *.
apply member_singleton in H2.
inversion_clear H2.
(******)
unfold gtA.
left.
generalize ( fst_comp_lq_sizec  ((add (inst x c1) s2)) x c1).
intros.
apply (lq_lt_lt _ _  _ H1).
simpl.
case( or_applicable_or_not (inst x (OrC c1 c2)) s2); intros.
simpl.
auto with *.
apply False_ind.
apply n.
apply (App_or     _     s2 x c1 c2).
auto with *.
(*****************************************************)
intros.
inversion_clear H2.
case (dec_eq_gt_in_remov2 c1 c2 x s2 H   H0 htemp x0 H1); intros.
unfold construct_Multiset.
red.
unfold transp.
apply (MSetGT _ (X:= X + {{mes_comp s2 x0}})( Y:= Y+{{(mes_comp (add (inst x c1) s2)  x0) }})(Z := Z) ).
solve_meq.
rewrite H4.
solve_meq.
rewrite H5.
solve_meq.
intros.
apply member_union in H2.
inversion_clear H2.
generalize( H6 y H7).
intros.
inversion_clear H2.
exists x1.
auto with *.
auto with *.

apply member_singleton in H7.
rewrite H7.
exists (mes_comp s2 x0) .
auto with *.
auto with *.
red.
unfold transp.
apply (MSetGT _ (X:= X )( Y:= Y) (Z := Z+ {{mes_comp s2 x0}}) ).
auto with *.
unfold construct_Multiset .
rewrite H4.
unfold insert.
solve_meq.
unfold construct_Multiset .
rewrite H5.
rewrite e.
solve_meq.
intros.
generalize (H6 y H2).
auto with *.
Qed.

Lemma orright_decrease : forall  s1 s2,  Orruleright s2 s1 ->MultisetLT gtA   (Measure2 s1  s1) (Measure2 s2 s2).
Proof.
intros.
unfold MultisetLT.
unfold transp.
inversion_clear H.
inversion_clear H0.
inversion_clear H2.
generalize H0.
intro htemp.
clear H0.
subst.
(*********************************)
assert (s2 [=] add(inst x (OrC c1 c2)) (remove (inst x (OrC c1 c2))  s2)). 
FiD.fsetdec.
generalize ( Mesure_equal_1 s2 _ _ H0).
assert ((add (inst x c2) s2)  [=] (add (inst x c2) (add (inst x (OrC c1 c2)) (remove (inst x (OrC c1 c2)) s2) ))).
auto with set.
generalize ( Mesure_equal_1 (add (inst x c2) s2) _ _ H1).
clear H1 H0; intros.
symmetry in H0.
  apply (MultisetGT_equal _ _ _ H0).
symmetry in H1.
apply (MultisetGT_equal2 _ _ _ H1).
clear H1 H0.
(******************************************)
assert((Measure2 s2 (add (inst x (OrC c1 c2)) (remove (inst x (OrC c1 c2)) s2)))=mul= 
fold (construct_Multiset s2) (remove (inst x (OrC c1 c2)) s2) (({{mes_comp s2 (inst x (OrC c1 c2))}} + MSetCore.empty))  ).
fold (insert (mes_comp s2 (inst x (OrC c1 c2))) MSetCore.empty) ; fold (construct_Multiset s2 (inst x (OrC c1 c2)) MSetCore.empty) .
unfold Measure2.
rewrite( FP.fold_add); auto with *.
rewrite   (FP.fold_commutes) ; auto .
intuition.
(******************************************)
assert ((Measure2 (add (inst x c2) s2)
     (add (inst x c2)
        (add (inst x (OrC c1 c2)) (remove (inst x (OrC c1 c2)) s2))))
 =mul= 
fold (construct_Multiset (add (inst x c2) s2))  (add (inst x (OrC c1 c2)) (remove (inst x (OrC c1 c2)) s2))
( ({{mes_comp (add (inst x c2) s2) (inst x  c2)}}+ MSetCore.empty))).

fold (insert (mes_comp (add (inst x c2) s2)  (inst x c2)) MSetCore.empty) .  fold (construct_Multiset (add (inst x c2) s2)  (inst x c2) MSetCore.empty) .
unfold Measure2.
rewrite  ( FP.fold_add); auto with *.
rewrite   (FP.fold_commutes) ; auto with * .
FiD.fsetdec.
pose (j :=  ({{mes_comp (add (inst x c2) s2) (inst x c2)}} + MSetCore.empty)).
assert(fold (construct_Multiset (add (inst x c2) s2))
       (add (inst x (OrC c1 c2)) (remove (inst x (OrC c1 c2)) s2)) j=mul=
fold (construct_Multiset (add (inst x c2) s2)) 
 (remove (inst x (OrC c1 c2)) s2) ( {{mes_comp (add (inst x c2) s2) (inst x (OrC c1 c2))}} + j)).
fold (insert (mes_comp (add (inst x c2) s2) (inst x (OrC c1 c2))) j) . fold (construct_Multiset  (add (inst x c2) s2)(inst x (OrC c1 c2)) j) .
 rewrite  ( FP.fold_add); auto with *.

rewrite   (FP.fold_commutes) ; auto with * .


symmetry in H0.
apply (MultisetGT_equal2 _ _ _ H0).
symmetry in H1.
apply (MultisetGT_equal _ _ _ H1).
symmetry in H2.
apply (MultisetGT_equal _ _ _ H2).
clear H1 H2 H0.
unfold j; clear j.
(*************************************************)
apply (FP.fold_rel (A:= Multiset)( B:= Multiset) (R:=MultisetLT gtA)) .
apply  (MSetGT  _ (X:= {{mes_comp s2 (inst x (OrC c1 c2))}} )
      (Y:={{mes_comp  (add (inst x c2) s2) (inst x (OrC c1 c2))}} + {{mes_comp (add (inst x c2) s2) (inst x c2)}} )
(Z:=MSetCore.empty)).
auto with *.
auto with *.
auto with *.
intros. exists (mes_comp s2 (inst x (OrC c1 c2))).
auto with *.
(**************************)
apply member_union in H0.
inversion_clear H0.
apply member_singleton in H1.
rewrite H1.
unfold mes_comp.
case( or_applicable_or_not (inst x (OrC c1 c2)) s2); intros.
case (or_applicable_or_not (inst x (OrC c1 c2)) (add (inst x c2) s2)); intros.
apply False_ind.
inversion_clear o0.
inversion_clear H0.
inversion_clear H4.
inversion_clear H5.
inversion H2.
subst.
apply H6.
auto with *.
unfold gtA.
left.
simpl.
auto with *.
apply False_ind.
apply n.
apply (App_or     _     s2 x c1 c2).
auto with *.
apply member_singleton in H1.
inversion_clear H1.
(******)
unfold gtA.
left.
generalize ( fst_comp_lq_sizec  ((add (inst x c2) s2)) x c2).
intros.
apply (lq_lt_lt _ _  _ H0).
simpl.
case( or_applicable_or_not (inst x (OrC c1 c2)) s2); intros.
simpl.
auto with *.
apply False_ind.
apply n.
apply (App_or     _     s2 x c1 c2).
auto with *.
(*****************************************************)
intros.
inversion_clear H1.
case (dec_eq_gt_in_remov3 c1 c2 x s2 H    htemp H3 x0 H0); intros.
unfold construct_Multiset.
red.
unfold transp.
apply (MSetGT _ (X:= X + {{mes_comp s2 x0}})( Y:= Y+{{(mes_comp (add (inst x c2) s2)  x0) }})(Z := Z) ).
solve_meq.
rewrite H4.
solve_meq.
rewrite H5.
solve_meq.
intros.
apply member_union in H1.
inversion_clear H1.
generalize( H6 y H7).
intros.
inversion_clear H1.
exists x1.
auto with *.
auto with *.
apply member_singleton in H7.
rewrite H7.
exists (mes_comp s2 x0) .
auto with *.
auto with *.
red.
unfold transp.
apply (MSetGT _ (X:= X )( Y:= Y) (Z := Z+ {{mes_comp s2 x0}}) ).
auto with *.
unfold construct_Multiset .
rewrite H4.
unfold insert.
solve_meq.
unfold construct_Multiset .
rewrite H5.
rewrite e.
solve_meq.
intros.
generalize (H6 y H1).
auto with *.
Qed.