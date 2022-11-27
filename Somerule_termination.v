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

Lemma set_of_some_term_g_eq  : forall n r c s1 s2 ,  Somerule s2 s1 -> In (inst n (AllC r c)) s2  -> set_of_some_term n r s1[=]set_of_some_term n r s2.
Proof.
intros.
unfold set_of_some_term.
inversion_clear H.
inversion_clear H1.
inversion_clear H3.
subst.
rewrite FactP.MP.fold_add ;auto.
unfold Constract_set_som.
simpl.
rewrite union_empty.
fold (Constract_set_som  n r ).
assert ( In (inst x (SomeC r0 c1)) (add (inst z c1) s2)).
FiD.fsetdec. rewrite FactP.MP.fold_add ;auto. unfold  Constract_set_som.
rewrite <-  ( FactP.MP.remove_fold_1  Equivalence_Eq  (Compat_som n r ) (transp_som n r) _ H ).
simpl. unfold  Constract_set_som.
simpl.
case(eq_role r r0). FiD.fsetdec. FiD.fsetdec.
intro ; rewrite F.add_iff in H2 ;inversion_clear H2.
discriminate H3.
generalize   (Quatre s2 z r0 x  H3) ;intro ; tauto.
Qed.

(******** les termes reductible dans le successeur sans subensemble de l'orgine***)
Lemma set_of_some_term_subs : forall n r c s1 s2 ,  Somerule s2 s1 -> In (inst n (AllC r c)) s2 -> set_of_some_term_r n r s1[<=]set_of_some_term_r n r s2.
Proof.
intros.
unfold set_of_some_term_r.
rewrite  (FP.fold_equal _ (compat_css s1)  (transp_css s1) empty (set_of_some_term_g_eq n r c s1 s2 H H0)) ; auto.
rewrite (FP.fold_rel (g:= (Constract_set_som_r s2))(f:=(Constract_set_som_r s1) ) (j:= empty)).
auto with *.
auto with *.
intros.
unfold Constract_set_som_r .
unfold some_terme_reductble.
case(some_applicable_or_not_2 x s1);intro.
case(some_applicable_or_not_2 x s2); intro.
FiD.fsetdec. 
inversion_clear s.
inversion_clear H3.
apply  False_ind.
apply n0; clear n0.
apply (App_some_2 _ _ x0 r0 c1).
split ; auto.
intro ; intro.
apply (H5 y) ; clear H5.
inversion_clear H.
inversion_clear H5.
inversion_clear H7.
subst ;split.
inversion_clear H3.
FiD.fsetdec.
FiD.fsetdec.
FiD.fsetdec.
Qed.

(**********************************************************************)
Lemma set_of_some_term_cardinal  : forall n r c s1 s2 ,  Somerule s2 s1 -> In (inst n (AllC r c)) s2 -> cardinal (set_of_some_term_r n r s1) <= cardinal (set_of_some_term_r n r s2).
Proof.
intros.
apply (FP.subset_cardinal).
apply (set_of_some_term_subs n r c s1 s2) ;auto.
Qed.

Lemma transitif : forall a b c, b >= c -> geA (a,b) (a,c).
Proof.
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

Lemma set_of_xc_term_subs : forall n r c s1 s2 ,  Somerule s2 s1 -> In (inst n (AllC r c)) s2 -> fsetsni.Subset (set_y_c_in_abox c s2) (set_y_c_in_abox c s1).
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
rewrite FactP.MP.fold_add ;auto ;simpl. 
case (eq_dec_concept c c1) ; intro ; auto with *.
intro. rewrite F.add_iff in H3 ;inversion_clear H3.
discriminate H5.
generalize   (Quatre s2 z r0 x  H5) ;intro ; tauto.
Qed.

Lemma ido : forall a b z , ~ fsetsni.In z a ->  fsetsni.Equal (fsetsni.diff a b)(fsetsni.diff (fsetsni.add z a)  (fsetsni.add z b)).
Proof.
intros.
NiD.fsetdec.
Qed.

Lemma  jido: forall a b c,   c< b ->   a + b >= S a + c.
intros.
omega.
Qed.

Lemma pipo : forall a b z ,~ fsetsni.In z b  -> fsetsni.Equal (fsetsni.diff (fsetsni.add z a) b  ) (fsetsni.add z (fsetsni.diff a b )).
Proof.
intros.
NiD.fsetdec.
Qed.

Lemma mipo : forall z a b , ~ fsetsni.In z a -> ~ fsetsni.In z (fsetsni.diff a b).
Proof.
NiD.fsetdec.
Qed.
(******* this the important lemma *****************)
Lemma measure_off_all : forall n r c s1 s2 ,  Somerule s2 s1 -> In (inst n (AllC r c)) s2 -> geA (mes_comp s2 (inst n (AllC r c))) (mes_comp s1 (inst n (AllC r c))).
Proof.
intros.
unfold mes_comp.
inversion_clear H.
inversion_clear H1.
inversion_clear H3.
(******************************)
case (NI_as_DT.eq_dec n x); intro.
inversion e.
rewrite H3 in * ; clear H3 e.
(******  x = n ****)
    case (eq_dec_role  r r0); intro.
    rewrite <- e in *; clear e.
assert(fsetsni.Equal (set_y_in_abox x r  s1) (fsetsni.add z (set_y_in_abox x r s2))).
unfold set_y_in_abox.
subst.
rewrite FactP.MP.fold_add ;auto; simpl.
assert (eq_ni x x && eq_role r r = true).
unfold eq_ni , eq_role .
case (NP.Dec.F.eq_dec x x ); intro.
case(eq_dec_role r r); intro.
auto.
tauto.
auto with *.
rewrite H2; clear H2.
rewrite FactP.MP.fold_add ;auto; simpl.
auto with *.
 rewrite F.add_iff ;intro Hi; inversion_clear Hi. discriminate H2.
generalize (Quatre  s2 z r x  H2) ;intro ; tauto.
(********************************************)
case (eq_dec_concept c c1); intros.
rewrite <- e in *; clear e.
assert (fsetsni.Equal  (set_y_c_in_abox c s1) (fsetsni.add z (set_y_c_in_abox c s2))).
unfold set_y_c_in_abox.
subst.
rewrite FactP.MP.fold_add ;auto; simpl.
rewrite FactP.MP.fold_add ;auto; simpl.
case (eq_dec_concept c c); intro.
auto with *.
tauto.
rewrite F.add_iff ;intro Hi; inversion_clear Hi. discriminate H2.
generalize ( Quatre  s2 z r x  H2) ;intro ; tauto.
assert ( set_rel x c r s2 = set_rel x c r s1) .  unfold set_rel .
apply NP.Equal_cardinal.
rewrite H3.
rewrite H5.
apply ido.
unfold set_y_in_abox.
apply FP.fold_rel.
auto with *.
intros. induction x0 ; intros; simpl.
auto.
case (eq_ni n0 x && eq_role r r1).
case (NI_as_DT.eq_dec n1 z); intro.
inversion e.
rewrite H8 in *.
generalize ( quatre2  s2 z r1 n0 H4); intro.
tauto.
NiD.fsetdec.
auto.
auto.
clear H3 H5.
assert( cardinal (set_of_some_term_r x r s2) >=cardinal (set_of_some_term_r x r s1)).
apply  (set_of_some_term_cardinal  _ _ c ) ; auto . apply (mk_Somerule s2 s1 x z r c) ;  auto.
rewrite H6. apply transitif.
omega.
(********* x = n et r = r0 but c<> c2*******)
assert (fsetsni.Equal (set_y_c_in_abox c s2)(set_y_c_in_abox c s1)).
unfold set_y_c_in_abox .
subst.
rewrite FactP.MP.fold_add ;auto. simpl.
rewrite FactP.MP.fold_add ;auto. simpl.
case (eq_dec_concept c c1) ; intro.
tauto.
auto with *.
rewrite F.add_iff ;intro Hi; inversion_clear Hi. discriminate H2.
generalize ( Quatre  s2 z r x  H2) ;intro ; tauto.
apply transitif.
assert (fsetsni.Equal (fsetsni.diff (set_y_in_abox x r s1) (set_y_c_in_abox c s1)) (fsetsni.add z (fsetsni.diff (set_y_in_abox x r s2) (set_y_c_in_abox c s2)))).
rewrite H3,  H5.
apply  pipo.
unfold set_y_c_in_abox.
subst.
rewrite FactP.MP.fold_add ;auto. simpl.
rewrite FactP.MP.fold_add ;auto. simpl.
case (eq_dec_concept c c1) ; intro.
tauto.
auto with *. apply FP.fold_rel.
auto with *.
intros. induction x0 ; intros; simpl. 
case (eq_dec_concept c c0); intro.
rewrite <- e in *.
case (NI_as_DT.eq_dec n2 z); intro.
inversion e0.
rewrite H7 in *.
generalize ( trois  s2 z c  H2) ;intro ; tauto.
NiD.fsetdec.
auto.
auto.
auto.
rewrite F.add_iff ;intro Hi; inversion_clear Hi. discriminate H2.
generalize ( Quatre  s2 z r x  H2) ;intro ; tauto.
assert (set_rel x c r s1 = S (set_rel x c r s2 )%nat).
unfold set_rel.
rewrite H6.
assert (~ fsetsni.In z (fsetsni.diff (set_y_in_abox x r s2) (set_y_c_in_abox c s2))).

apply mipo.
unfold set_y_in_abox.
apply FP.fold_rel.
auto with *.
intros. induction x0 ; intros; simpl.
auto.
 case (eq_ni n1 x && eq_role r r1).
case (NI_as_DT.eq_dec n2 z); intro.
inversion e.
rewrite H9 in *.
generalize ( quatre2  s2 z r1 n1 H4); intro.
tauto.
NiD.fsetdec.
auto.
auto.
apply  (NP.cardinal_2 H7).
auto with *.
rewrite H7.
apply jido.
clear H3 H5 H6 H7.
assert (Somerule s2 s1).
apply (mk_Somerule s2 s1 x z r c1); auto.
apply  (FP.subset_cardinal_lt (set_of_some_term_subs x r c s1 s2 H3 H0) (x:= (inst x (SomeC r c1)) )).  
(****************************************)
unfold set_of_some_term_r.
assert (In (inst x (SomeC r c1)) (set_of_some_term x r s2)).
unfold set_of_some_term.
rewrite <- (FP.remove_fold_1 _ ( Compat_som x r) (transp_som x r) empty H) ; auto.
unfold Constract_set_som .
simpl.
case (eq_dec_NI x x); intro.
unfold eq_role.
case(eq_dec_role r r ) ; intro.
auto with *.
tauto.
tauto.
rewrite <- (FP.remove_fold_1 _ (compat_css s2)  (transp_css s2)  empty H5).
unfold Constract_set_som_r.
unfold some_terme_reductble.
case(some_applicable_or_not_2 (inst x (SomeC r c1)) s2); intro.
auto with *.
apply False_ind.
apply n1.
apply  (App_some_2 _ _ x r c1); auto.
(*********************************************)
unfold set_of_some_term_r.
subst.
apply FP.fold_rel.
auto with *.
intros.
case(Fact_as_DT.eq_dec x0 (inst x (SomeC r c1)) ); intro.
inversion e.
unfold Constract_set_som_r .
unfold some_terme_reductble.
case(some_applicable_or_not_2 (inst x (SomeC r c1))
           (add (rel x z r) (add (inst z c1) s2))); intro.
inversion_clear s.
inversion_clear H7.
inversion H8.
rewrite H10 , H11,  H12 in *. clear H10  H11  H12.
apply False_ind.
(******)
apply (H9 z).
auto with *.
auto with *.
unfold Constract_set_som_r .
unfold some_terme_reductble.
case (some_applicable_or_not_2 x0 (add (rel x z r) (add (inst z c1) s2))); intro.
rewrite F.union_iff.
intro.
inversion_clear H6.
rewrite F.singleton_iff in H7.
tauto.
tauto.
auto with *.
assert (fsetsni.Equal (set_y_in_abox x r s2) (set_y_in_abox x r s1)).
unfold set_y_in_abox.
subst.
rewrite FactP.MP.fold_add ;auto. simpl.
unfold eq_role.
case(  eq_dec_role r r0) ; intro .
tauto.
case (eq_ni x x) ;
simpl ;
rewrite FactP.MP.fold_add ;auto ; simpl;
auto with *.
 rewrite F.add_iff ;intro Hi; inversion_clear Hi. discriminate H2.
generalize (Quatre  s2 z r0 x  H2) ;intro ; tauto.
apply transitif.
assert ( set_rel x c r s2 >= set_rel x c r s1).
unfold set_rel.
apply NP.subset_cardinal ; rewrite H3 ; apply lah .
apply (set_of_xc_term_subs x r)  ; auto. 
  apply (mk_Somerule s2 s1 x z r0 c1) ;  auto.

assert( cardinal (set_of_some_term_r x r s2) >=cardinal (set_of_some_term_r x r s1)).
apply  (set_of_some_term_cardinal  _ _ c ) ; auto . apply (mk_Somerule s2 s1 x z r0 c1) ;  auto.
omega.
(* n <> x ok its proved ***)
assert (fsetsni.Equal (set_y_in_abox n r s2) (set_y_in_abox n r s1)).
unfold set_y_in_abox.
subst.
rewrite FactP.MP.fold_add ;auto. simpl.
unfold eq_ni.
case(NP.Dec.F.eq_dec x n ) ; intro .
inversion e. symmetry in H2; tauto.
simpl.
rewrite FactP.MP.fold_add ;auto. simpl.
auto with *.
 rewrite F.add_iff ;intro Hi; inversion_clear Hi. discriminate H2.
generalize (Quatre  s2 z r0 x  H2) ;intro ; tauto.
apply transitif.
assert ( set_rel n c r s2 >= set_rel n c r s1).
unfold set_rel.
apply NP.subset_cardinal ; rewrite H3 ; apply lah .
apply (set_of_xc_term_subs n r)  ; auto. 
  apply (mk_Somerule s2 s1 x z r0 c1) ;  auto.
assert( cardinal (set_of_some_term_r n r s2) >=cardinal (set_of_some_term_r n r s1)).
apply  (set_of_some_term_cardinal  _ _ c ) ; auto . apply (mk_Somerule s2 s1 x z r0 c1) ;  auto.
omega.
Qed.


(*******************************************************************)
Lemma first :  forall f s1 s2 ,Somerule s2 s1  -> In f s2 ->  geA  (mes_comp s2 f)  (mes_comp s1 f ).
Proof.
intros.
induction f.
induction c.
red  ; auto with *.
red  ; auto with *.
red  ; auto with *.
red  ; auto with *.

(***** cas  du And *********************)
unfold geA. clear IHc1 IHc2.
right ;  simpl.
(***subcase 1 ****)
case (and_applicable_or_not (inst n (AndC c1 c2)) s2) ; intros.
case (and_applicable_or_not (inst n (AndC c1 c2)) s1); intros.
auto with *.
apply False_ind.
apply n0; clear n0.
inversion_clear a.
inversion_clear H1.
inversion_clear H3.
inversion H2.
subst ; clear H2.
inversion_clear H.
inversion_clear H2.
inversion_clear H5.
subst.
apply (App_and _ _  n c1 c2 ); split ; auto with *.
split ; auto with *.
intro ;apply H4; split.
inversion_clear H3.
apply F.add_iff in H5 ; inversion_clear H5.
discriminate H3.
apply F.add_iff in H3 ; inversion_clear H3.
inversion H5.
rewrite H8 in *.
 generalize (trois  s2 n  (AndC c1 c2) H0 ) ; intro; tauto.
auto.
inversion_clear H3.
apply F.add_iff in H7 ; inversion_clear H7.
discriminate H3.
apply F.add_iff in H3 ; inversion_clear H3.
inversion H7.
rewrite H8 in *.
 generalize (trois  s2 n  (AndC c1 c2) H0 ) ; intro; tauto.
auto.
(**** subcase 4 ********)
case (and_applicable_or_not (inst n (AndC c1 c2)) s1); intros.

apply False_ind.
apply n0; clear n0.
inversion_clear a.
inversion_clear H1.
inversion_clear H3.
inversion H2.
subst ; clear H2.
inversion_clear H.
inversion_clear H2.
inversion_clear H5.
subst.
apply (App_and _ _  n c1 c2 ); split ; auto with *.
split ; auto with *.
intro ;apply H4; split.
inversion_clear H3.
auto with *.
inversion_clear H3.
auto with *.
auto with *.
(******** cas du or ****************************)
unfold geA. clear IHc1 IHc2.
right ;  simpl.
(***subcase 1 ****)
case (or_applicable_or_not (inst n (OrC c1 c2)) s2) ; intros.
case (or_applicable_or_not (inst n (OrC c1 c2)) s1); intros.
auto with *.
apply False_ind.
apply n0; clear n0.
inversion_clear o.
inversion_clear H1.
inversion_clear H3.
inversion H2.
subst ; clear H2.
inversion_clear H.
inversion_clear H2.
inversion_clear H5.
subst.
apply (App_or  _ _  n c1 c2 ); split ; auto with *.
split ; auto with *.
split.
inversion_clear H4.
intro ;apply H3.
apply F.add_iff in H4 ; inversion_clear H4.
discriminate H7.
apply F.add_iff in H7 ; inversion_clear H7.
inversion H4.
rewrite H8 in *.
 generalize (trois  s2 n  (OrC c1 c2) H0 ) ; intro; tauto.
auto.
inversion_clear H4.
intro ;apply H5.
apply F.add_iff in H4 ; inversion_clear H4.
discriminate H7.
apply F.add_iff in H7 ; inversion_clear H7.
inversion H4.
rewrite H8 in *.
 generalize (trois  s2 n  (OrC c1 c2) H0 ) ; intro; tauto.
auto.
(**** subcase 4 ********)
case (or_applicable_or_not (inst n (OrC c1 c2)) s1); intros.
apply False_ind.
apply n0; clear n0.
inversion_clear o.
inversion_clear H1.
inversion_clear H3.
inversion H2.
subst ; clear H2.
inversion_clear H.
inversion_clear H2.
inversion_clear H5.
subst.
apply (App_or _ _  n c1 c2 ); split ; auto with *.
split ; auto with *.
inversion_clear H4.
split.
intro ;apply H3.
auto with *.
intro ; apply H5 ; auto with *.
auto with *.
(************ cas du some ***********************************)
Focus 2.
inversion_clear H.
inversion_clear H1.
inversion_clear H3.
clear IHc.
case(Fact_as_DT.eq_dec (inst n (SomeC r c))(inst x (SomeC r0 c1))); intro.
left.
inversion e.
rewrite H5, H6, H7 in *; clear e H5 H6 H7.
simpl.
assert (some_applicable (inst x (SomeC r0 c1)) s2).
apply ( App_some _ _ x r0 c1) ; split; auto.
assert (~ some_applicable (inst x (SomeC r0 c1)) s1).
intro.
inversion_clear H5.
inversion_clear H6.
inversion_clear H7.
inversion H5.
rewrite H9 , H10 ,  H11 in * ; clear H9 H10 H11.
apply (H8 z) ; subst ; split ; auto with *.
case ( some_applicable_or_not (inst x (SomeC r0 c1))s2); intro.
case (some_applicable_or_not (inst x (SomeC r0 c1)) s1); intro.
tauto.
red ; left; simpl; auto with *.
case (some_applicable_or_not (inst x (SomeC r0 c1)) s1); intro ; tauto.
(****************************************)
right ;  simpl.
case ( some_applicable_or_not (inst n (SomeC r c))s2); intro.
case (some_applicable_or_not (inst n (SomeC r c)) s1); intro.
auto with *.
apply False_ind.
apply n1; clear n1.
inversion_clear s.
inversion_clear H3.
inversion_clear H6.
inversion  H5.
rewrite <- H8, H9, H10 in *; clear H8 H9 H10 H5.
apply (App_some _ _ n r1 c0).
split; auto.
split; subst ; auto with *.
intro; intro.
inversion_clear H2.
apply (H7 y) ; clear H7.
apply F.add_iff in H6 ; inversion_clear H6.
discriminate H2.
apply F.add_iff in H2 ; inversion_clear H2.
inversion H6.
apply F.add_iff in H5 ; inversion_clear H5.
inversion H2.
apply False_ind; apply n0.
subst.
auto with *.
apply F.add_iff in H2 ; inversion_clear H2.
discriminate H5.
rewrite <- H7 in *.
generalize (Quatre  s2  z r1 n H5 ) ; intro.
tauto.
apply F.add_iff in H5 ; inversion_clear H5.
inversion H2.
rewrite <- H8 in *.
generalize (trois  s2 z  (c0) H6 ); intro; tauto.
apply F.add_iff in H2 ; inversion_clear H2.
discriminate H5.
auto.
(*********************************)
case(some_applicable_or_not (inst n (SomeC r c)) s1); intro.
apply False_ind; apply n1; clear n1.
inversion_clear s.
inversion_clear H3.
inversion_clear H6.
inversion H5.
rewrite <- H8, H9, H10 in *; clear H8 H9 H10 H5.
apply (App_some _ _ n r1 c0).
split; auto.
split; auto.
intro ;intro.
apply (H7 y); clear H7.
inversion_clear H5.
subst; split; auto with *.
auto with *.
(****************************************)
(*********** le cas  du rel ***************)
Focus 2.
right ; simpl; auto with *.
(**************Le cas du diff*****)
Focus 2.
right ; simpl; auto with *.
(*********** the last case and the hard one **********)
(******   its about all **********************************)
clear IHc.
apply measure_off_all ; auto.
Qed.


Lemma dec_gt_eq_measure : forall f s1 s2 ,Somerule s2 s1  -> In f s2 ->  {gtA  (mes_comp s2 f)  (mes_comp s1 f )} + {(mes_comp s2 f)  =(mes_comp s1 f ) }.
Proof.
intros; apply dec_eq_gtA.
 apply first ; auto.
Qed.


(**********************************************************************)
(************************************************************************)
(**********************************************************************)
(************************************************************************)
(**********************************************************************)
(************************************************************************)
(**********************************************************************)
(************************************************************************)

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

Lemma some_decrease : forall  s1 s2,  Somerule s2 s1 ->MultisetLT gtA   (Measure2 s1  s1) (Measure2 s2 s2).
Proof.
intros.
unfold MultisetLT.
unfold transp.
inversion H.
inversion_clear H0.
inversion_clear H3.
(*************************************)
assert (s2 [=] add  (inst x (SomeC r c1)) (remove (inst x (SomeC r c1))  s2)). 
FiD.fsetdec.
assert ( Measure2 s2 s2 =mul=  (fold (construct_Multiset s2) (remove (inst x (SomeC r c1)) s2)
    {{ (mes_comp s2 (inst x (SomeC r c1))) }})).
generalize ( Mesure_equal_1 s2 _ _ H3) ;intro.
rewrite H5.
unfold Measure2.
rewrite( FP.fold_add); auto with *. 
rewrite  <-    (FP.fold_commutes) ; auto with * .
symmetry in H5.
apply (MultisetGT_equal2 _ _ _ H5).
clear H5.
(*****************************************)
assert ( Measure2 s1 s1 =mul=  fold (construct_Multiset s1) (remove (inst x (SomeC r c1)) s2)
       ({{mes_comp s1 (inst x (SomeC r c1))}} +
   ({{mes_comp s1 (inst z c1)}} +
    ({{mes_comp s1 (rel x z r)}} + MSetCore.empty)))).
assert ( s1  [=] add (rel x z r) (add (inst z c1) (add (inst x (SomeC r c1)) (remove (inst x (SomeC r c1))s2)))).
rewrite <- H3 ; rewrite H1; intuition.
generalize ( Mesure_equal_1 s1 _ _ H5) ;intro Hi ;
rewrite Hi; clear Hi H5 H3.
unfold Measure2.
rewrite( FP.fold_add); auto with *. 
rewrite  <-    (FP.fold_commutes) ; auto with * .
rewrite( FP.fold_add); auto with *. 
rewrite  <-    (FP.fold_commutes) ; auto with * .
rewrite( FP.fold_add); auto with *. 
rewrite  <-    (FP.fold_commutes) ; auto with * .
rewrite (FP.add_remove).
auto.
auto.
rewrite (FP.add_remove).
intro.
apply F.add_iff in H3 ; inversion_clear H3.
discriminate H5.
generalize (Quatre  s2  z r x H5 ) ; intro;tauto.
auto.
symmetry in H5.
apply (MultisetGT_equal _ _ _ H5).
clear H5 H3.
(*******************************************)
apply (FP.fold_rel (A:= Multiset)( B:= Multiset) (R:=MultisetLT gtA)) .
apply  (MSetGT  _ (X:= {{mes_comp s2 (inst x (SomeC r c1))}} )
      (Y:=({{mes_comp s1 (inst x (SomeC r c1))}} +
   ({{mes_comp s1 (inst z c1)}} +
    ({{mes_comp s1 (rel x z r)}} + MSetCore.empty))) )
(Z:=MSetCore.empty)).
auto with *.
auto with *.
auto with *.
intros.
exists (mes_comp s2 (inst x (SomeC r c1))).
auto with *.
apply member_union in H3.
inversion_clear H3.
apply member_singleton in H5.
rewrite H5.
unfold mes_comp.
case(some_applicable_or_not (inst x (SomeC r c1)) s2);intro.
case(some_applicable_or_not (inst x (SomeC r c1)) s1);intro.
apply False_ind.
inversion_clear s0.
inversion_clear H3.
inversion_clear H7.
inversion H6.
rewrite H9 , H10,  H11 in *.
apply (H8 z).
subst.
auto with *.
simpl.
unfold gtA.
left.
simpl.
auto with *.
(*******************************)
apply False_ind.
apply n.
apply (App_some _ _ x r c1).
auto with *.
(*********************************************)
apply member_union in H5.
inversion_clear H5.
apply member_singleton in H3.
rewrite H3. 
unfold gtA.
left. generalize (fst_comp_lq_sizec  s1 z  c1) ;intro.
apply (lq_lt_lt _ _  _ H5); clear H5.
unfold mes_comp.
case(some_applicable_or_not (inst x (SomeC r c1)) s2);intro.
simpl.
auto with *.
apply False_ind.
apply n.
apply (App_some _ _ x r c1).
auto with *.
apply member_union in H3.
inversion_clear H3.
apply member_singleton in H5.
rewrite H5.
simpl.
case(some_applicable_or_not (inst x (SomeC r c1)) s2);intro.
left.
simpl.
auto with *.
apply False_ind.
apply n.
apply (App_some _ _ x r c1).
auto with *.
inversion_clear H5.
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
generalize  (H10 y H11); intro.
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
intro;  apply ( H10 y).
Qed.