Add Rec LoadPath "~/color82" as CoLoR.	
Require Export Measure_theory.

Lemma mes_all1 : forall x n c c1 r AB1  , 
                 In ( inst x (AllC r c))  AB1 ->In (inst n c1) AB1->
                      (mes_comp   AB1 ( inst x (AllC r c))) =   (mes_comp  (add (inst n c1) AB1) ( inst x (AllC r c))).
Proof.
intros; apply equal_mes_comp .
auto with set.
Qed.

Lemma some_same1 : forall x r n  c1 c2 AB1, In (inst n (AndC c1 c2)) AB1-> ~  In (inst n c1) AB1->
  (set_of_some_term x  r AB1) [=]  (set_of_some_term x  r (add (inst n c1) AB1)).
Proof.
intros; unfold set_of_some_term.
rewrite ( FactP.MP.fold_add  Equivalence_Eq  (Compat_som x r ) (transp_som x r) _ H0).
unfold Constract_set_som .
rewrite  <- ((FP.remove_fold_1 Equivalence_Eq  (Compat_som x r) (transp_som x r)  empty H)).
unfold Constract_set_som; simpl; intros; rewrite <-  (FP.union_assoc); rewrite <-  (FP.union_assoc).
assert(Equal (union (some_term x r c1) (some_term x r c2)) 
(union (union (some_term x r c1) (some_term x r c1)) (some_term x r c2))).
FiD.fsetdec.
rewrite H1.
FiD.fsetdec.
Qed.

Lemma some_same_r  : forall x r n  c1 c2 AB1, In (inst n (AndC c1 c2)) AB1->
               ~  In (inst n c1) AB1->  (Subset  (set_of_some_term_r  x  r (add (inst n c1) AB1)) (set_of_some_term_r x  r AB1)).
Proof.
intros ;unfold set_of_some_term_r.
generalize (some_same1 x r n  c1 c2 AB1 H H0); intro.
assert (fold (Constract_set_som_r (add (inst n c1) AB1)) (set_of_some_term x r (add (inst n c1) AB1)) empty  [=]fold (Constract_set_som_r (add (inst n c1) AB1))
  (set_of_some_term x r AB1) empty).
apply  (FP.fold_equal Equivalence_Eq) ;auto.
auto with set.
rewrite H2.
(******************************************************)
rewrite  (FP.fold_rel (f:= (Constract_set_som_r (add (inst n c1) AB1)))(g:=  (Constract_set_som_r AB1))(j:= empty)); auto with set.
clear H1  H2; intros.
unfold Constract_set_som_r , some_terme_reductble.
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
split; auto with *.
case(some_applicable_or_not_2 x0 AB1); intro; FiD.fsetdec.
Qed.

(******************************************************)
Lemma some_gte  : forall x r n  c1 c2 AB1, In (inst n (AndC c1 c2)) AB1-> ~  In (inst n c1) AB1->
 (cardinal (set_of_some_term_r  x  r (add (inst n c1) AB1)) <= cardinal (set_of_some_term_r x  r AB1)).
Proof.
intros; apply FP.subset_cardinal.
apply ( some_same_r x r n  c1 c2 AB1); auto.
Qed.

(**************************************************************)
Lemma mes_all2 : forall x n c c1 c2 r AB1  , 
In ( inst x (AllC r c))  AB1 -> In (inst n (AndC c1 c2)) AB1-> ~  In (inst n c1) AB1->
{gtA (mes_comp   AB1 ( inst x (AllC r c)))   ((mes_comp   (add (inst n c1) AB1) ( inst x (AllC r c))))}
 + {(mes_comp   AB1 ( inst x (AllC r c))) =   (mes_comp  (add (inst n c1) AB1) ( inst x (AllC r c)))}.

Proof.
intros.
simpl.
(*********************************************************)
assert ( {set_rel x  c r AB1 > (set_rel x  c r (add (inst n c1) AB1))}+ 
{ set_rel x  c r AB1 =(set_rel x  c r (add (inst n c1) AB1) ) }).
case (eq_dec_concept c c1) ; intro.
subst.
case ( FactP.MP.In_dec  (rel x n r ) AB1  ); intro.
(*************************Le premier cas *********************)
left ; unfold set_rel .
(********Assert 1******************************)
assert (fsetsni.Equal (set_y_in_abox x r AB1) (set_y_in_abox x r (add (inst n c1) AB1)  )).
unfold set_y_in_abox.
rewrite (FP.fold_add Eq_cr (compat_r x r) (transp_r x r) _ H1); auto with set.
(********Assert 2*********************)
assert (fsetsni.Equal (set_y_c_in_abox c1 (add (inst n c1) AB1)) (fsetsni.add n (set_y_c_in_abox  c1 AB1))).
unfold set_y_c_in_abox ; rewrite (FP.fold_add Eq_cr (compat_c c1) (transp_c c1) _ H1 ); simpl.
case (eq_dec_concept c1 c1) ;intro.
auto with set.
tauto.
(***************************)
rewrite <-   H2. 
rewrite  H3.
(******* Assert 3**********************)
assert (fsetsni.In  n (set_y_in_abox x r (add (inst n c1) AB1))). unfold set_y_in_abox.
assert (In (rel x n r) (add (inst n c1) AB1)). FiD.fsetdec.
rewrite <-  ( FP.remove_fold_1 Eq_cr (f:=(construct_set_of_y_in_rel x r) ) (compat_r x r)(transp_r  x r) fsetsni.empty H4 );simpl.
assert (eq_ni x x && eq_role r r = true). unfold eq_ni , eq_role.
case(NP.Dec.F.eq_dec x x ); intros; intuition.
case(eq_dec_role r r  ) ;intros ; intuition.
rewrite H5 ;intuition.
(*************Assert 4 ***********************)
assert(fsetsni.cardinal (fsetsni.diff (set_y_in_abox x r AB1) (set_y_c_in_abox c1 AB1)) = S(fsetsni.cardinal
  (fsetsni.diff (set_y_in_abox x r AB1) (fsetsni.add n (set_y_c_in_abox c1 AB1))) )).
apply (NP.cardinal_2 ( x:= n)  ). NiD.fsetdec.
(*************************)
unfold NP.Add ; split;
(**********************)
intros.
case (NI_as_DT.eq_dec n y); intro.
inversion e.
left; auto.
right ; apply fsetsni.diff_3; NiD.fsetdec.
inversion_clear H5. subst.
apply fsetsni.diff_3. NiD.fsetdec.
(******************************************)
apply (notin_inst_abox_notin_set  _ _ _ H1).
NiD.fsetdec.
rewrite H5 ; auto.
(*********le deuxieme cas*******************************************************)
right; unfold set_rel .
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
generalize  (some_gte  x  r n c1 c2 AB1 H0 H1); intro.
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
In ( inst x (AllC r c))  AB1 -> In (inst n (AndC c1 c2)) AB1-> 
{gtA (mes_comp   AB1 ( inst x (AllC r c)))   ((mes_comp   (add (inst n c1) AB1) ( inst x (AllC r c))))}
 + {(mes_comp   AB1 ( inst x (AllC r c))) =   (mes_comp  (add (inst n c1) AB1) ( inst x (AllC r c)))}.
Proof.
intros.
 case (FP.In_dec  (inst n c1) AB1); intro.
right; apply mes_all1;auto.
 apply (mes_all2 x n c c1 c2 r AB1); auto.
Qed.

Lemma some_same11 : forall x r n  c1 c2 AB1, In (inst n (AndC c1 c2)) AB1-> ~  In (inst n c2) AB1->
  (set_of_some_term x  r AB1) [=]  (set_of_some_term x  r (add (inst n c2) AB1)).
Proof.
intros.
unfold set_of_some_term.
rewrite ( FactP.MP.fold_add  Equivalence_Eq  (Compat_som x r ) (transp_som x r) _ H0).
unfold Constract_set_som .
rewrite  <- ((FP.remove_fold_1 Equivalence_Eq  (Compat_som x r) (transp_som x r)  empty H)).
unfold Constract_set_som.
simpl.
rewrite <-  (FP.union_assoc).
rewrite <-  (FP.union_assoc).
assert(Equal (union (some_term x r c1) (some_term x r c2)) 
(union (union (some_term x r c1) (some_term x r c1)) (some_term x r c2))).
FiD.fsetdec.
rewrite H1.
FiD.fsetdec.
Qed.

Lemma some_same_r_2  : forall x r n  c1 c2 AB1, In (inst n (AndC c1 c2)) AB1-> ~  In (inst n c2) AB1->
 (Subset  (set_of_some_term_r  x  r (add (inst n c2) AB1)) (set_of_some_term_r x  r AB1)).
Proof.
intros ;unfold set_of_some_term_r.
generalize (some_same11 x r n  c1 c2 AB1 H H0); intro.
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
split; auto with set.
(******************************************************)
case(some_applicable_or_not_2 x0 AB1); intro.
FiD.fsetdec.
FiD.fsetdec.
Qed.

Lemma some_gte_2  : forall x r n  c1 c2 AB1, In (inst n (AndC c1 c2)) AB1-> ~  In (inst n c2) AB1->
 (cardinal (set_of_some_term_r  x  r (add (inst n c2) AB1)) <= cardinal (set_of_some_term_r x  r AB1)).
Proof.
intros.
apply FP.subset_cardinal.
apply ( some_same_r_2 x r n  c1 c2 AB1); auto.
Qed.


Lemma mes_all3 : forall x n c c1 c2 r AB1  , 
In ( inst x (AllC r c))  AB1 -> In (inst n (AndC c1 c2)) AB1-> ~  In (inst n c2) AB1->
{gtA (mes_comp   AB1 ( inst x (AllC r c)))   ((mes_comp   (add (inst n c2) AB1) ( inst x (AllC r c))))}
 + {(mes_comp   AB1 ( inst x (AllC r c))) =   (mes_comp  (add (inst n c2) AB1) ( inst x (AllC r c)))}.
Proof.
intros.
simpl.
(*********************************************************)
assert ({set_rel x  c r AB1 > (set_rel x  c r (add (inst n c2) AB1))} + 
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
(***************************************************)
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
apply (notin_inst_abox_notin_set  _ _ _ H1).
NiD.fsetdec.
rewrite H5.
auto.
intros.
(**************************************************************)
right.
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
generalize(notin_rel_abox_notin_set  _ _ _   _ n0).
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
generalize  (some_gte_2  x  r n c1 c2 AB1 H0 H1); intro.
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


Lemma mes_all_r : forall x n c c1 c2 r AB1 , 
In ( inst x (AllC r c))  AB1 -> In (inst n (AndC c1 c2)) AB1-> 
{gtA (mes_comp   AB1 ( inst x (AllC r c)))   ((mes_comp   (add (inst n c2) AB1) ( inst x (AllC r c))))}
 + {(mes_comp   AB1 ( inst x (AllC r c))) =   (mes_comp  (add (inst n c2) AB1) ( inst x (AllC r c)))}.
Proof.
intros.
 case (FP.In_dec  (inst n c2) AB1).
intro.
right.
apply mes_all1.
auto.
auto.
intros. 
apply (mes_all3 x n c c1 c2 r AB1);
auto.
Qed.
(***********************************)
Lemma gtA_trans : forall p1 p2 p3, gtA p1 p2 -> gtA p2 p3 -> gtA p1 p3.
intros.
inversion_clear H.
inversion_clear H0.
unfold gtA.
left.
auto with *.
left.
auto with *.
inversion_clear H0.
left.
auto with *.
inversion_clear H1.
right.
inversion_clear H.
auto with *.
Qed.
(***************************************************************************************)
Lemma mes_all_g  : forall x n c c1 c2 r AB1  , 
In ( inst x (AllC r c))  AB1 -> In (inst n (AndC c1 c2)) AB1-> 
{gtA (mes_comp   AB1 ( inst x (AllC r c)))   ((mes_comp  (add (inst n c2) (add (inst n c1) AB1)) ( inst x (AllC r c))))}
 + {(mes_comp   AB1 ( inst x (AllC r c))) =   (mes_comp  (add (inst n c2)(add (inst n c1) AB1)) ( inst x (AllC r c)))}.
Proof.
intros.
case ( mes_all x n c c1 c2 r AB1); auto; intros.
case ( mes_all_r x n c c1 c2 r (add (inst n c1) AB1)).
FiD.fsetdec.
FiD.fsetdec.
intro.
left. apply (gtA_trans _ _ _ g g0).
intros.
left.
rewrite e in g.
auto with *.
case ( mes_all_r x n c c1 c2 r (add (inst n c1) AB1)).
fsetdec.
fsetdec.
intro.
left; rewrite e; auto with set.
intro; right ; rewrite e; auto.
Qed.




(***************************************************************)

Lemma dec_eq_gt_in_the_rest : forall f c1 c2 x s2 ,  In (inst x  (AndC c1 c2)) s2-> f<> (inst x (AndC c1 c2) )-> fsetsfact.In f s2 ->({ gtA  (mes_comp s2 f)  (mes_comp (fsetsfact.add (inst x c2) (fsetsfact.add (inst x c1) s2))f )}
+ {   (mes_comp s2 f)  =  (mes_comp (fsetsfact.add (inst x c2) (fsetsfact.add (inst x c1)s2))f )}).

Proof.
do 5 intro.
intro in_and.
intros.
induction  f.
case ( Fact_as_DT.eq_dec (inst x (AndC c1 c2)) (inst n  c ) ).
intro.
rewrite e in H.
tauto.
(**************************************************************************)
intros.
induction c .  
compute; auto.
compute; auto.
compute; auto.
compute ; auto.
simpl.
case(and_applicable_or_not (inst n (AndC c3 c4)) s2).
intro.
case(and_applicable_or_not (inst n (AndC c3 c4))
        (add (inst x c2) (add (inst x c1) s2))).
intro.
right.
auto with *.
intro ; unfold geA ; left ; unfold gtA;left ;  simpl ; auto with *.
intro.
(***************************)
case(and_applicable_or_not (inst n (AndC c3 c4))  (add (inst x c2) (add (inst x c1) s2))).
intros.
assert (  ~and_applicable (inst n (AndC c3 c4)) (add (inst x c2) (add (inst x c1) s2))) .
intro.
apply n1.
inversion_clear H1.
inversion_clear H2.
inversion_clear H3.
inversion H1.
rewrite H5, H6 , H7 in *.
apply (App_and (inst n (AndC c3 c4))  s2 n c3 c4).
split.
auto.
split.
fsetdec.
fsetdec.
tauto.
intros.
right.
auto.
(****************************************************************)
simpl.
case(or_applicable_or_not (inst n (OrC c3 c4)) s2).
intro.
case(or_applicable_or_not (inst n (OrC c3 c4))
        (add (inst x c2) (add (inst x c1) s2))).
intro.
right.

auto with *.
(*****************)

intro . left ;  simpl  ; unfold gtA ;  left ; simpl ; auto with *.
intro.
case(or_applicable_or_not (inst n (OrC c3 c4))
        (add (inst x c2) (add (inst x c1) s2))).
intros.
assert(~or_applicable (inst n (OrC c3 c4)) (add (inst x c2) (add (inst x c1) s2))).

inversion_clear o.
inversion_clear H1.
inversion_clear H3.
inversion_clear H4.

apply NNPP; intro ; apply n1.
inversion H2.
rewrite H7, H8 , H9 in *; clear H7  H8 H9.
apply (App_or (inst n (OrC c3 c4))  s2 n c3 c4).
split.
auto.
split.
auto.
split.
FiD.fsetdec.
FiD.fsetdec.
tauto.
intro.
unfold geA; right ; 
auto with *.
(**************************************************************)
apply mes_all_g .
auto.
auto.
simpl.
case(some_applicable_or_not (inst n (SomeC r c)) s2).
intro.
case (some_applicable_or_not (inst n (SomeC r c)) (add (inst x c2) (add (inst x c1) s2))).
intros.
unfold geA.
right.
auto with *.
intros.
unfold geA.
left.

red.
left.
simpl.
auto with *.
intros.
case (some_applicable_or_not (inst n (SomeC r c)) (add (inst x c2) (add (inst x c1) s2))).
intros.

assert (some_applicable (inst n (SomeC r c)) s2).
inversion_clear s.
inversion_clear H1.
inversion_clear H3.
inversion H2.
rewrite H5 , H6 , H7 in *; clear H5 H6 H7 H2.

apply (App_some  (inst x0 (SomeC r0 c0)) s2 x0 r0 c0).
split.
auto.
split ; auto.
intro.
generalize (H4 y).
intros.
FiD.fsetdec.
tauto.
intro.
right.
auto with *.
(*******************************)
simpl.
right.
auto with *.
(*************************)
simpl.
right.
auto with *.
Qed.
(*******************************************************************************)

(********************************************************************************)
Lemma dec_eq_gt_in_remov  : forall  c1 c2 x s2 ,  In (inst x  (AndC c1 c2)) s2->
                                      forall f,  In f (remove (inst x (AndC c1 c2) ) s2) ->
             ({ gtA  (mes_comp s2 f)  (mes_comp (add (inst x c2) (add (inst x c1) s2))f )}
          +          {   (mes_comp s2 f)  =  (mes_comp (add (inst x c2) (add (inst x c1)s2))f )}).
Proof.
intros.
 apply dec_eq_gt_in_the_rest.
auto.
fsetdec.
fsetdec. 
Qed.

Lemma dec_eq_gt_in_remov2  : forall  c1 c2 x s2 ,  In (inst x  (AndC c1 c2)) s2-> In (inst x c2)(add (inst x c1) s2) ->
                                      forall f,  In f (remove (inst x (AndC c1 c2) ) s2) ->
             ({ gtA  (mes_comp s2 f)  (mes_comp ((add (inst x c1) s2))f )}
          +          {   (mes_comp s2 f)  =  (mes_comp ( (add (inst x c1)s2))f )}).
Proof.
intros.
assert (add (inst x c2) ((add (inst x c1) s2)) [=] (add (inst x c1) s2)).
FiD.fsetdec.
symmetry in H2. rewrite (equal_mes_comp f _ _ H2).
apply (dec_eq_gt_in_remov c1 c2 x s2 H f H1).
Qed.
(************************************************)
Lemma dec_eq_gt_in_remov3  : forall  c1 c2 x s2 ,  In (inst x  (AndC c1 c2)) s2-> In (inst x c1) s2  ->
                                      forall f,  In f (remove (inst x (AndC c1 c2) ) s2) ->
             ({ gtA  (mes_comp s2 f)  (mes_comp ((add (inst x c2) s2))f )}
          +          {   (mes_comp s2 f)  =  (mes_comp ( (add (inst x c2)s2))f )}).
Proof.
intros.
assert (add (inst x c2) ((add (inst x c1) s2)) [=] (add (inst x c2) s2)).
FiD.fsetdec.
symmetry in H2. rewrite (equal_mes_comp f _ _ H2).
apply (dec_eq_gt_in_remov c1 c2 x s2 H f H1).
Qed.




(*****************************)


Lemma and_decrease : forall  s1 s2, Andrule s2 s1 ->MultisetLT gtA   (Measure2 s1  s1) (Measure2 s2 s2).
Proof.
intros.
inversion_clear H.
inversion_clear H0.
subst.
case (FP.In_dec (inst x c2) (add (inst x c1) s2)).
intros.
red.
unfold transp.
assert ((Measure2 (add (inst x c2) (add (inst x c1) s2))
     (add (inst x c2) (add (inst x c1) s2))) =mul= (Measure2 (add (inst x c2) (add (inst x c1) s2))
     ( (add (inst x c1) s2)))).
rewrite (measure_add_2  (inst x c2)  _ _ i) ; auto with *.
case (FP.In_dec (inst x c1)  s2).
intros.
rewrite F.add_iff in i.
inversion i.
inversion_clear H1.
apply False_ind.
apply H2.
FiD.fsetdec.
apply False_ind.
apply H2.
FiD.fsetdec.
intros.

symmetry in H0.
apply ( MultisetGT_equal  _ _ _ H0) ; clear H0.
assert (s2 [=] add(inst x (AndC c1 c2)) (remove (inst x (AndC c1 c2))  s2)).
FiD.fsetdec.
assert ((Measure2 s2 s2) =mul= Measure2 s2  (add (inst x (AndC c1 c2)) (remove (inst x (AndC c1 c2)) s2))).
apply (Mesure_equal_1 _ _ _ H0).
symmetry in H1.
apply (MultisetGT_equal2 _ _ _ H1).
clear H1.
assert ((add (inst x c1) s2)  [=] (add (inst x c1) (add (inst x (AndC c1 c2)) (remove (inst x (AndC c1 c2)) s2) ))).
auto with *.
clear H0.
assert( (Measure2 (add (inst x c2) (add (inst x c1) s2)) (add (inst x c1) s2)) =mul= 
(Measure2 (add (inst x c2) (add (inst x c1) s2)) (add (inst x c1) (add (inst x (AndC c1 c2)) (remove (inst x (AndC c1 c2)) s2)) )) ).

apply (Mesure_equal_1 _ _ _ H1).
symmetry in H0.
apply (MultisetGT_equal _ _ _ H0).

unfold Measure2.
(**********************************************)

assert((construct_Multiset s2 (inst x (AndC c1 c2))
     (fold (construct_Multiset s2) (remove (inst x (AndC c1 c2)) s2)
        MSetCore.empty)) =mul=(fold (construct_Multiset s2)
     (add (inst x (AndC c1 c2)) (remove (inst x (AndC c1 c2)) s2))
     MSetCore.empty) ).

rewrite( FP.fold_add); auto with *.
clear H1 H0.

apply (MultisetGT_equal2 _ _ _ H3).


assert ((construct_Multiset s2 (inst x (AndC c1 c2))
     (fold (construct_Multiset s2) (remove (inst x (AndC c1 c2)) s2) MSetCore.empty)) =mul= 
(fold (construct_Multiset s2) (remove (inst x (AndC c1 c2)) s2)  (construct_Multiset s2 (inst x (AndC c1 c2))   MSetCore.empty) )).
rewrite (FP.fold_commutes); 
auto with *. symmetry in H0.
apply (MultisetGT_equal2 _ _ _ H0).
(****************************************************************)


assert ( (fold (construct_Multiset (add (inst x c2) (add (inst x c1) s2)))
     (add (inst x c1)
        (add (inst x (AndC c1 c2)) (remove (inst x (AndC c1 c2)) s2)))
     MSetCore.empty)
 =mul=  (construct_Multiset (add (inst x c2) (add (inst x c1) s2)) (inst x c1)
     (fold (construct_Multiset (add (inst x c2) (add (inst x c1) s2)))
        (add (inst x (AndC c1 c2)) (remove (inst x (AndC c1 c2)) s2))
        MSetCore.empty))) .

rewrite( FP.fold_add); auto with *.
FiD.fsetdec.
clear H3 H0.
symmetry in H1.
apply (MultisetGT_equal _ _ _ H1).

assert ((construct_Multiset (add (inst x c2) (add (inst x c1) s2)) (inst x c1)
     (fold (construct_Multiset (add (inst x c2) (add (inst x c1) s2)))
        (add (inst x (AndC c1 c2)) (remove (inst x (AndC c1 c2)) s2))
        MSetCore.empty)) =mul= (fold (construct_Multiset (add (inst x c2) (add (inst x c1) s2)))
        (add (inst x (AndC c1 c2)) (remove (inst x (AndC c1 c2)) s2)) ( (construct_Multiset (add (inst x c2) (add (inst x c1) s2)) (inst x c1)MSetCore.empty ) ))).
rewrite (FP.fold_commutes); auto with *.
symmetry in H0.
apply (MultisetGT_equal _ _ _ H0).
assert( (fold (construct_Multiset (add (inst x c2) (add (inst x c1) s2)))
     (add (inst x (AndC c1 c2)) (remove (inst x (AndC c1 c2)) s2))
     (construct_Multiset (add (inst x c2) (add (inst x c1) s2)) (inst x c1)
        MSetCore.empty)) =mul= (construct_Multiset (add (inst x c2) (add (inst x c1) s2))
     (inst x (AndC c1 c2))
     (fold (construct_Multiset (add (inst x c2) (add (inst x c1) s2)))
        (remove (inst x (AndC c1 c2)) s2)
        (construct_Multiset (add (inst x c2) (add (inst x c1) s2))
           (inst x c1) MSetCore.empty))) ).
rewrite( FP.fold_add); auto with *.
clear H1 H0.
symmetry in H3.
apply (MultisetGT_equal _ _ _ H3).

pose(j :=  (construct_Multiset (add (inst x c2) (add (inst x c1) s2))
         (inst x c1) MSetCore.empty)).

fold j.
assert ( (construct_Multiset (add (inst x c2) (add (inst x c1) s2))
     (inst x (AndC c1 c2))
     (fold (construct_Multiset (add (inst x c2) (add (inst x c1) s2)))
        (remove (inst x (AndC c1 c2)) s2) j))
=mul= fold (construct_Multiset (add (inst x c2) (add (inst x c1) s2)))
           (remove (inst x (AndC c1 c2)) s2)
(construct_Multiset (add (inst x c2) (add (inst x c1) s2)) (inst x (AndC c1 c2)) j)) .  
rewrite (FP.fold_commutes); auto with *.

unfold j in *.
symmetry in H0.
apply (MultisetGT_equal _ _ _ H0).

(***********************************)
apply (FP.fold_rel (A:= Multiset)( B:= Multiset) (R:=MultisetLT gtA)) .
clear H3 H0.
unfold construct_Multiset.
unfold insert.
unfold MultisetLT.
unfold transp.

clear j.
apply  (MSetGT  _ (X:= {{mes_comp s2 (inst x (AndC c1 c2))}} )
      (Y:={{mes_comp (add (inst x c2) (add (inst x c1) s2)) (inst x (AndC c1 c2))}} + {{mes_comp (add (inst x c2) (add (inst x c1) s2)) (inst x c1)}} )
(Z:=MSetCore.empty)).
auto with *.
auto with *.
auto with *.
intros. exists (mes_comp s2 (inst x (AndC c1 c2))).
auto with *.
apply member_union in H0.
inversion_clear H0.
apply member_singleton in H1.
rewrite H1.
unfold mes_comp.
case( and_applicable_or_not (inst x (AndC c1 c2)) s2).
intros.
case (and_applicable_or_not (inst x (AndC c1 c2))
        (add (inst x c2) (add (inst x c1) s2))).
intros.
apply False_ind.
inversion_clear a0.
inversion_clear H0.
inversion_clear H4.
inversion H3.
rewrite H6 , H7,  H8 in * ; clear H6 H7 H8.
apply H5.
auto with *.
intros.
unfold gtA.
left.
simpl.
auto with *.
intros.
apply False_ind.
apply n0.

apply (App_and     _     s2 x c1 c2).
auto with *.
apply member_singleton in H1.
inversion_clear H1.
(***********************)
unfold gtA.
left.
generalize ( fst_comp_lq_sizec (add (inst x c2) (add (inst x c1) s2)) x c1).
intros.
apply (lq_lt_lt  _ _  _ H0).
simpl.
case( and_applicable_or_not (inst x (AndC c1 c2)) s2).
intros.
simpl.
auto with *.
intros.
apply False_ind.
apply n0.
apply (App_and     _     s2 x c1 c2).
auto with *.
(***************************************************)
(******************************************************)
clear H3 j H0.
intros.
inversion_clear H1.
case (dec_eq_gt_in_remov2 c1 c2 x s2 H i x0  H0).
intros.
(*****************************)
unfold construct_Multiset.
red.
unfold transp.

apply (MSetGT _ (X:= X + {{mes_comp s2 x0}})( Y:= Y+{{(mes_comp (add (inst x c2) (add (inst x c1) s2)) x0) }})(Z := Z) ).
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
exists (mes_comp s2 x0) .
auto with *.
apply member_singleton in H7.
rewrite H7.
assert( (add (inst x c1) s2) [=] (add (inst x c2) (add (inst x c1) s2))).
FiD.fsetdec.

rewrite <- (equal_mes_comp x0 _ _ H1).
auto.
(**************************************)
intros.
apply (MSetGT _ (X:= X )( Y:= Y) (Z := Z+ {{mes_comp s2 x0}}) ).
solve_meq.
unfold construct_Multiset .
rewrite H4.
solve_meq.
unfold construct_Multiset .
rewrite H5.
assert( (add (inst x c1) s2) [=] (add (inst x c2) (add (inst x c1) s2))).
FiD.fsetdec.
rewrite <- (equal_mes_comp x0 _ _ H1).
rewrite e.
solve_meq.
intros.
generalize (H6 y H1).
auto with *.
(*****************************)
(**********************************************************)
(***********************)

intros.
case (FP.In_dec (inst x c1)  s2) ; intros.
assert((add (inst x c2) (add (inst x c1) s2)) [=](add (inst x c2) s2) ).
FiD.fsetdec.
unfold MultisetLT , transp .
generalize   (Mesure_equal_1 (add (inst x c2) (add (inst x c1) s2)) (add (inst x c2) (add (inst x c1) s2))  (add (inst x c2) s2) H0).
intros. 
symmetry in H1.
apply   (MultisetGT_equal (Measure2 s2 s2)  _ _ H1) ; clear H1.
assert (s2 [=] add(inst x (AndC c1 c2)) (remove (inst x (AndC c1 c2))  s2)).

clear H0.
FiD.fsetdec.

assert ((Measure2 s2 s2) =mul= Measure2 s2  (add (inst x (AndC c1 c2)) (remove (inst x (AndC c1 c2)) s2))).
apply (Mesure_equal_1 _ _ _ H1).
symmetry in H3.
apply (MultisetGT_equal2 _ _ _ H3).
clear H3.
assert ((add (inst x c2) s2)  [=] (add (inst x c2) (add (inst x (AndC c1 c2)) (remove (inst x (AndC c1 c2)) s2) ))).
auto with *.
clear H0 H1.
assert( (Measure2 (add (inst x c2) (add (inst x c1) s2)) (add (inst x c2) s2)) =mul= 
(Measure2 (add (inst x c2) (add (inst x c1) s2)) (add (inst x c2) (add (inst x (AndC c1 c2)) (remove (inst x (AndC c1 c2)) s2)) )) ).

apply (Mesure_equal_1 _ _ _ H3).
symmetry in H0.
apply (MultisetGT_equal _ _ _ H0).

unfold Measure2.
(**********************************************)

assert((construct_Multiset s2 (inst x (AndC c1 c2))
     (fold (construct_Multiset s2) (remove (inst x (AndC c1 c2)) s2)
        MSetCore.empty)) =mul=(fold (construct_Multiset s2)
     (add (inst x (AndC c1 c2)) (remove (inst x (AndC c1 c2)) s2))
     MSetCore.empty) ).

rewrite( FP.fold_add); auto with *.


apply (MultisetGT_equal2 _ _ _ H1).
clear H3 H0.

assert ((construct_Multiset s2 (inst x (AndC c1 c2))
     (fold (construct_Multiset s2) (remove (inst x (AndC c1 c2)) s2) MSetCore.empty)) =mul= 
(fold (construct_Multiset s2) (remove (inst x (AndC c1 c2)) s2)  (construct_Multiset s2 (inst x (AndC c1 c2))   MSetCore.empty) )).
rewrite (FP.fold_commutes); 
auto with *. symmetry in H0.
apply (MultisetGT_equal2 _ _ _ H0).
(****************************************************************)


assert ( (fold (construct_Multiset (add (inst x c2) (add (inst x c1) s2)))
     (add (inst x c2)
        (add (inst x (AndC c1 c2)) (remove (inst x (AndC c1 c2)) s2)))
     MSetCore.empty)
 =mul=  (construct_Multiset (add (inst x c2) (add (inst x c1) s2)) (inst x c2)
     (fold (construct_Multiset (add (inst x c2) (add (inst x c1) s2)))
        (add (inst x (AndC c1 c2)) (remove (inst x (AndC c1 c2)) s2))
        MSetCore.empty))) .

rewrite( FP.fold_add); auto with *.
FiD.fsetdec.

clear H1 H0.
symmetry in H3.
apply (MultisetGT_equal _ _ _ H3).

assert ((construct_Multiset (add (inst x c2) (add (inst x c1) s2)) (inst x c2)
     (fold (construct_Multiset (add (inst x c2) (add (inst x c1) s2)))
        (add (inst x (AndC c1 c2)) (remove (inst x (AndC c1 c2)) s2))
        MSetCore.empty)) =mul= (fold (construct_Multiset (add (inst x c2) (add (inst x c1) s2)))
        (add (inst x (AndC c1 c2)) (remove (inst x (AndC c1 c2)) s2)) ( (construct_Multiset (add (inst x c2) (add (inst x c1) s2)) (inst x c2)MSetCore.empty ) ))).
rewrite (FP.fold_commutes); auto with *.
symmetry in H0.
apply (MultisetGT_equal _ _ _ H0).
assert( (fold (construct_Multiset (add (inst x c2) (add (inst x c1) s2)))
     (add (inst x (AndC c1 c2)) (remove (inst x (AndC c1 c2)) s2))
     (construct_Multiset (add (inst x c2) (add (inst x c1) s2)) (inst x c2)
        MSetCore.empty)) =mul= (construct_Multiset (add (inst x c2) (add (inst x c1) s2))
     (inst x (AndC c1 c2))
     (fold (construct_Multiset (add (inst x c2) (add (inst x c1) s2)))
        (remove (inst x (AndC c1 c2)) s2)
        (construct_Multiset (add (inst x c2) (add (inst x c1) s2))
           (inst x c2) MSetCore.empty))) ).
rewrite( FP.fold_add); auto with *.
clear H3 H0.
symmetry in H1.
apply (MultisetGT_equal _ _ _ H1).

pose(j :=  (construct_Multiset (add (inst x c2) (add (inst x c1) s2))
         (inst x c2) MSetCore.empty)).

fold j.
assert ( (construct_Multiset (add (inst x c2) (add (inst x c1) s2))
     (inst x (AndC c1 c2))
     (fold (construct_Multiset (add (inst x c2) (add (inst x c1) s2)))
        (remove (inst x (AndC c1 c2)) s2) j))
=mul= fold (construct_Multiset (add (inst x c2) (add (inst x c1) s2)))
           (remove (inst x (AndC c1 c2)) s2)
(construct_Multiset (add (inst x c2) (add (inst x c1) s2)) (inst x (AndC c1 c2)) j)) .  
rewrite (FP.fold_commutes); auto with *.

unfold j in *.
symmetry in H0.
apply (MultisetGT_equal _ _ _ H0).

(***********************************)
apply (FP.fold_rel (A:= Multiset)( B:= Multiset) (R:=MultisetLT gtA)) .
clear H1 H0.
unfold construct_Multiset.
unfold insert.
unfold MultisetLT.
unfold transp.

clear j.
apply  (MSetGT  _ (X:= {{mes_comp s2 (inst x (AndC c1 c2))}} )
      (Y:={{mes_comp (add (inst x c2) (add (inst x c1) s2)) (inst x (AndC c1 c2))}} + {{mes_comp (add (inst x c2) (add (inst x c1) s2)) (inst x c2)}} )
(Z:=MSetCore.empty)).
auto with *.
auto with *.
auto with *.
intros. exists (mes_comp s2 (inst x (AndC c1 c2))).
auto with *.
apply member_union in H0.
inversion_clear H0.
apply member_singleton in H1.
rewrite H1.
unfold mes_comp.
case( and_applicable_or_not (inst x (AndC c1 c2)) s2);
intros.
case (and_applicable_or_not (inst x (AndC c1 c2))
        (add (inst x c2) (add (inst x c1) s2))).
intros.
apply False_ind.
inversion_clear a0.
inversion_clear H0.
inversion_clear H4.
inversion H3.
rewrite H6 , H7,  H8 in * ; clear H6 H7 H8.
apply H5.
auto with *.
intros.
unfold gtA.
left.
simpl.
auto with *.
intros.
apply False_ind.
apply n0.

apply (App_and     _     s2 x c1 c2).
auto with *.
apply member_singleton in H1.
inversion_clear H1.
(***********************)
unfold gtA.
left.
generalize ( fst_comp_lq_sizec  (add (inst x c2) (add (inst x c1) s2)) x c2).
intros.
apply (lq_lt_lt  _ _  _ H0).
simpl.
case( and_applicable_or_not (inst x (AndC c1 c2)) s2).
intros.
simpl.
auto with *.
intros.
apply False_ind.
apply n0.
apply (App_and     _     s2 x c1 c2).
auto with *.
(***************************************************)
(******************************************************)
clear H1 j H0.
intros.
inversion_clear H1.
case (dec_eq_gt_in_remov3 c1 c2 x s2 H i x0  H0).
intros.
(*****************************)
unfold construct_Multiset.
red.
unfold transp.

apply (MSetGT _ (X:= X + {{mes_comp s2 x0}})( Y:= Y+{{(mes_comp (add (inst x c2) (add (inst x c1) s2)) x0) }})(Z := Z) ).
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
exists (mes_comp s2 x0) .
auto with *.
apply member_singleton in H7.
rewrite H7.
assert( (add (inst x c2) s2) [=] (add (inst x c2) (add (inst x c1) s2))).
FiD.fsetdec.

rewrite <- (equal_mes_comp x0 _ _ H1).
auto.
(**************************************)
intros.
apply (MSetGT _ (X:= X )( Y:= Y) (Z := Z+ {{mes_comp s2 x0}}) ).
solve_meq.
unfold construct_Multiset .
rewrite H4.
solve_meq.
unfold construct_Multiset .
rewrite H5.
assert( (add (inst x c2) s2) [=] (add (inst x c2) (add (inst x c1) s2))).
FiD.fsetdec.
rewrite <- (equal_mes_comp x0 _ _ H1).
rewrite e.
solve_meq.
intros.
generalize (H6 y H1).
auto with *.
(*************************************************************)
assert (s2 [=] add(inst x (AndC c1 c2)) (remove (inst x (AndC c1 c2))  s2)).
FiD.fsetdec.

assert ((Measure2 s2 s2) =mul= Measure2 s2  (add (inst x (AndC c1 c2)) (remove (inst x (AndC c1 c2)) s2))).
apply (Mesure_equal_1 _ _ _ H0).
symmetry in H1.
apply (MultisetGT_equal2 _ _ _ H1).
clear H1.
assert ((add (inst x c2) (add (inst x c1) s2))  [=] (add (inst x c2)(add (inst x c1)  (add (inst x (AndC c1 c2)) (remove (inst x (AndC c1 c2)) s2)) ))).
clear H0.
FiD.fsetdec.

clear H0 .
assert( (Measure2 (add (inst x c2) (add (inst x c1) s2)) (add (inst x c2)  (add (inst x c1) s2))) =mul= 
(Measure2 (add (inst x c2) (add (inst x c1) s2)) (add (inst x c2)  ((add (inst x c1) (add (inst x (AndC c1 c2)) (remove (inst x (AndC c1 c2)) s2))) )) )).

apply (Mesure_equal_1 _ _ _ H1).
symmetry in H0.
apply (MultisetGT_equal _ _ _ H0).

unfold Measure2.
(**********************************************)

assert((construct_Multiset s2 (inst x (AndC c1 c2))
     (fold (construct_Multiset s2) (remove (inst x (AndC c1 c2)) s2)
        MSetCore.empty)) =mul=(fold (construct_Multiset s2)
     (add (inst x (AndC c1 c2)) (remove (inst x (AndC c1 c2)) s2))
     MSetCore.empty) ).

rewrite( FP.fold_add); auto with *.


apply (MultisetGT_equal2 _ _ _ H3).


assert ((construct_Multiset s2 (inst x (AndC c1 c2))
     (fold (construct_Multiset s2) (remove (inst x (AndC c1 c2)) s2) MSetCore.empty)) =mul= 
(fold (construct_Multiset s2) (remove (inst x (AndC c1 c2)) s2)  (construct_Multiset s2 (inst x (AndC c1 c2))   MSetCore.empty) )).
rewrite (FP.fold_commutes); 
auto with *. symmetry in H4.
apply (MultisetGT_equal2 _ _ _ H4).
(****************************************************************)


assert ( (fold (construct_Multiset (add (inst x c2) (add (inst x c1) s2)))
     (add (inst x c2) (add (inst x c1)
        (add (inst x (AndC c1 c2)) (remove (inst x (AndC c1 c2)) s2))))
     MSetCore.empty)
 =mul=  (construct_Multiset (add (inst x c2) (add (inst x c1) s2)) (inst x c2)
     (fold (construct_Multiset (add (inst x c2) (add (inst x c1) s2)))
        ( (add (inst x c1) (add (inst x (AndC c1 c2)) (remove (inst x (AndC c1 c2)) s2))))
        MSetCore.empty))) .

rewrite( FP.fold_add); auto with *.
clear H0 H1 H3 H4.
FiD.fsetdec.
clear H0 H1 H3 H4.

symmetry in H5.
apply (MultisetGT_equal _ _ _ H5).

assert ((construct_Multiset (add (inst x c2) (add (inst x c1) s2)) (inst x c2)
     (fold (construct_Multiset (add (inst x c2) (add (inst x c1) s2)))
       (add (inst x c1) (add (inst x (AndC c1 c2)) (remove (inst x (AndC c1 c2)) s2)))
        MSetCore.empty)) =mul= (fold (construct_Multiset (add (inst x c2) (add (inst x c1) s2)))
        (add (inst x c1) (add (inst x (AndC c1 c2)) (remove (inst x (AndC c1 c2)) s2))) ( (construct_Multiset (add (inst x c2) (add (inst x c1) s2)) (inst x c2)MSetCore.empty ) ))).
rewrite (FP.fold_commutes); auto with *.
symmetry in H0.
apply (MultisetGT_equal _ _ _ H0).


(***************************************************)
clear H5 H0.
pose ( j :=  (construct_Multiset (add (inst x c2) (add (inst x c1) s2)) (inst x c2)
        MSetCore.empty)).
fold j.
pose (s1 := (add (inst x c2) (add (inst x c1) s2))). fold s1.
assert( (fold (construct_Multiset s1)
     (add (inst x c1)
        (add (inst x (AndC c1 c2)) (remove (inst x (AndC c1 c2)) s2))) j) =mul= 
(construct_Multiset s1 (inst x c1)  )
     (fold (construct_Multiset  s1)
         (add (inst x (AndC c1 c2)) (remove (inst x (AndC c1 c2)) s2)) j)).

rewrite( FP.fold_add); auto with *.
FiD.fsetdec.

symmetry in H0.
apply (MultisetGT_equal _ _ _ H0).


assert ( (construct_Multiset s1 (inst x c1)
     (fold (construct_Multiset s1)
        (add (inst x (AndC c1 c2)) (remove (inst x (AndC c1 c2)) s2)) j))
=mul= fold (construct_Multiset s1)
            (add (inst x (AndC c1 c2)) (remove (inst x (AndC c1 c2)) s2))
(construct_Multiset (add (inst x c2) (add (inst x c1) s2))  (inst x c1)  j)) .  
fold s1.
rewrite (FP.fold_commutes); auto with *.


symmetry in H1.
apply (MultisetGT_equal _ _ _ H1).
(********************************************************)
clear H0 H1.
pose (k := (construct_Multiset (add (inst x c2) (add (inst x c1) s2)) (inst x c1) j)).
fold k.
assert (  (fold (construct_Multiset s1)
     (add (inst x (AndC c1 c2)) (remove (inst x (AndC c1 c2)) s2)) k) =mul=

(construct_Multiset s1 (inst x (AndC c1 c2))  )
     (fold (construct_Multiset  s1)
         ( (remove (inst x (AndC c1 c2)) s2)) k )).
rewrite( FP.fold_add); auto with *.


symmetry in H0.
apply (MultisetGT_equal _ _ _ H0).


assert ( (construct_Multiset s1 (inst x (AndC c1 c2))
     (fold (construct_Multiset s1) (remove (inst x (AndC c1 c2)) s2) k))
=mul= fold (construct_Multiset s1)
            ( (remove (inst x (AndC c1 c2)) s2))
(construct_Multiset s1  (inst x (AndC c1 c2)) k)) .  

rewrite (FP.fold_commutes); auto with *.
symmetry in H1.
apply (MultisetGT_equal _ _ _ H1).
clear H0 H1.
(***********************************)
apply (FP.fold_rel (A:= Multiset)( B:= Multiset) (R:=MultisetLT gtA)) .

unfold construct_Multiset.
unfold insert.
unfold k  .
unfold j.
unfold MultisetLT.
unfold transp.
apply  (MSetGT  _ (X:= {{mes_comp s2 (inst x (AndC c1 c2))}} )
      (Y:={{mes_comp s1 (inst x (AndC c1 c2))}} + {{mes_comp s1 (inst x c1)}}+ {{mes_comp s1 (inst x c2)}} )
(Z:=MSetCore.empty)).
auto with *.
auto with *.
auto with *.
intros. exists (mes_comp s2 (inst x (AndC c1 c2))).
auto with *.
apply member_union in H0.
inversion_clear H0.
apply member_union in H1.
inversion_clear H1.

apply member_singleton in H0.
rewrite H0.
unfold mes_comp.
case( and_applicable_or_not (inst x (AndC c1 c2)) s2);
intros.
case (and_applicable_or_not (inst x (AndC c1 c2)) s1).
unfold s1.
intros.
apply False_ind.
inversion_clear a0.
inversion_clear H1.
inversion_clear H4.
inversion H3.
rewrite H6 , H7,  H8 in * ; clear H6 H7 H8.
apply H5.
auto with *.
intros.
unfold gtA.
left.
simpl.
auto with *.
intros.
apply False_ind.
apply n1.

apply (App_and     _     s2 x c1 c2).
auto with *.
(***********************)
apply member_singleton in H0.
rewrite H0.
unfold gtA.
left.
generalize ( fst_comp_lq_sizec  (add (inst x c2) (add (inst x c1) s2)) x c1).
intros.
apply (lq_lt_lt _ _  _ H1).
simpl.
case( and_applicable_or_not (inst x (AndC c1 c2)) s2).
intros.
simpl.
auto with *.
intros.
apply False_ind.
apply n1.
apply (App_and     _     s2 x c1 c2).
auto with *.
(***************************************************)
apply member_singleton in H1.
rewrite H1.
unfold gtA.
left.
generalize ( fst_comp_lq_sizec  (add (inst x c2) (add (inst x c1) s2)) x c2).
intros.
apply (lq_lt_lt  _ _  _ H0).
simpl.
case( and_applicable_or_not (inst x (AndC c1 c2)) s2).
intros.
simpl.
auto with *.
intros.
apply False_ind.
apply n1.
apply (App_and     _     s2 x c1 c2).
auto with *.
(******************************************************)
clear  j k.
intros.
inversion_clear H1.
case (dec_eq_gt_in_remov c1 c2 x s2 H   x0 H0); intros.
(*****************************)
unfold construct_Multiset.
red.
unfold transp.
apply (MSetGT _ (X:= X + {{mes_comp s2 x0}})( Y:= Y+{{(mes_comp (add (inst x c2) (add (inst x c1) s2)) x0) }})(Z := Z) ).
solve_meq.
rewrite H4.
solve_meq.
rewrite H5.
unfold s1.
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
exists (mes_comp s2 x0) .
auto with *.
apply member_singleton in H7.
rewrite H7.
auto with *.
apply (MSetGT _ (X:= X )( Y:= Y) (Z := Z+ {{mes_comp s2 x0}}) ).
solve_meq.
unfold construct_Multiset .
rewrite H4.
solve_meq.
unfold construct_Multiset .
rewrite H5.
unfold s1.
rewrite e.
solve_meq.
intros.
generalize (H6 y H1).
auto with *.
Qed.







