Add Rec LoadPath "color82" as CoLoR.	
Require Export myimp.
Require Export Inverse_Image.
Require Export Mesure.

(*****************************************************)


(******************First Definition of Measure************************************)
Definition  Measure  AB :=  (List_M AB AB). 
Definition succ    AB1 AB2 :=  sucessor AB1 AB2. 
Definition Lt_abox (s1 s2 : Abox) := MultisetLT gtA   (Measure  s1) (Measure s2).

(*************** scnd definition ****************************)

Definition construct_Multiset  (A: Abox) (f:fact) M1 : Multiset :=  insert (mes_comp   A  f)  M1.
Definition  Measure2 A B : Multiset  := ( fold  (construct_Multiset  A )   B MSetCore.empty ).
Definition Measure_Abox AB := Measure2 AB AB.

(**************************************)


Lemma measure_add_1 : forall f s2 AB , ~ In f s2-> (Measure2 AB (add f s2)) =mul= ( Measure2 AB  (add f empty ) ) +(Measure2 AB  s2 ).
Proof.
intros.
assert (compat_op Fact_as_DT.eq meq (construct_Multiset AB)).
unfold compat_op , construct_Multiset ; intros.
inversion H0 ;   subst .
  solve_meq.
auto.
assert(transpose meq (construct_Multiset AB)).
unfold transpose ,  construct_Multiset ; intros ; solve_meq.
unfold Measure2.
Locate fold_add.
rewrite (FP.fold_add) ; auto.
rewrite (FP.fold_add); auto ; try FiD.fsetdec.
rewrite ( FP.fold_empty);  simpl; solve_meq.
Qed.

(**********************************************************)
Lemma measure_add_2 : forall f s2 AB ,  In f s2-> (Measure2 AB (add f s2)) =mul= (Measure2 AB  s2 ).
Proof.
intros ; unfold Measure2.
rewrite (FP.add_fold) ; auto with * .
unfold compat_op , construct_Multiset ; intros;  subst .
  solve_meq.
unfold transpose ,  construct_Multiset ; intros ; solve_meq.
Qed.


(************************************************************)
Lemma measure_union  : forall s2  AB s1, Empty (inter s1 s2)-> ( Measure2 AB (union s1 s2)) =mul= (Measure2 AB  s1 ) +( Measure2 AB  s2 ).
Proof.
intros; unfold Measure2.
rewrite (FP.fold_union) ; auto.
fold  (Measure2  AB s2).
fold  (Measure2  AB s1).

unfold Empty in H.
generalize (FP.fold_rec_weak (A:= Multiset) (P:= fun s M =>(Measure2 AB s + Measure2 AB s2)=mul= M )
(f:= construct_Multiset AB)(i:=Measure2 AB s2 )).
intros.
assert ( (forall (s s' : Abox) (a : Multiset),
      s [=] s' ->
      Measure2 AB s + Measure2 AB s2 =mul= a ->
      Measure2 AB s' + Measure2 AB s2 =mul= a)).
intros.

assert ( forall s5 s6, s5 [=] s6-> Measure2 AB s5 =mul=  Measure2 AB s6).
unfold Measure2.

apply (FP.fold_equal ).
auto with *.
unfold compat_op.
intros.
subst.
unfold construct_Multiset.
solve_meq.
unfold transpose.
intros. unfold construct_Multiset.
solve_meq.
symmetry in H1.
rewrite ( H3 s' s H1).
auto.
generalize (H0 H1).
intros.
assert ( Measure2 AB empty + Measure2 AB s2 =mul= Measure2 AB s2).
simpl.
unfold Measure2.
rewrite (FP.fold_empty).
solve_meq.
generalize ( H2 H3).
intros.
assert((forall (x : elt) (a : Multiset) (s : Abox),
      ~ In x s ->
      Measure2 AB s + Measure2 AB s2 =mul= a ->
      Measure2 AB (add x s) + Measure2 AB s2 =mul= construct_Multiset AB x a) ).
intros.

rewrite   (measure_add_1 x  s AB H5 ).
simpl.
unfold construct_Multiset.
assert ( Measure2  AB (add x empty) =mul= {{mes_comp AB x}}).
unfold Measure2.
rewrite (FP.fold_add).
rewrite ( FP.fold_empty).
solve_meq.
auto.
unfold compat_op.
intros.
subst.
unfold construct_Multiset.
solve_meq.
unfold transpose.
intros. unfold construct_Multiset.
solve_meq.
auto with *.
rewrite H7.
rewrite <- H6.
solve_meq.
generalize (H4 H5).
intros.
generalize (H6 s1).
intros.
symmetry.
apply H7.
auto.
unfold compat_op.
intros.
subst.
unfold construct_Multiset.
solve_meq.
unfold transpose.
intros. unfold construct_Multiset.
solve_meq.
unfold Empty in H.
intros.
generalize (H x).
intros.
FiD.fsetdec.
Qed.


(*************************************************************************)
(************************************************************************)

(******************* For set_some *************************************)
Lemma  Compat_som : forall x , compat_op (Fact_as_DT.eq ) Equal (Constract_set_som x).
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
Lemma  transp_som : forall x , transpose Equal (Constract_set_som x).
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
auto .
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

(******************************************************************Eq_cr***************************)
Hint Resolve compat_cm Eq_meq transp_r transp_cm compat_r  transp_c compat_c  Compat_som  Eq_cr  transp_som Equivalence_Eq .
(**********************************************************************************************)
(*********************************************************************************************)
(***********************************************************************************************)
(*************************************************************************************************)
(************************************************************************************************)

Lemma Mesure_equal_1  : forall s1 s2 s3 , s2 [=]s3 -> Measure2 s1 s2 =mul= Measure2 s1 s3.
Proof.
intros; unfold Measure2.
apply   (FP.fold_equal Eq_meq  (compat_cm s1) (transp_cm s1)  _ H  ). 
Qed.

(***********************************************************)
Lemma Measure_equal_2 : forall s1 s2 s3 , s1 [=]s2 -> Measure2 s1 s3 =mul= Measure2 s2  s3.
Proof.
intros; unfold Measure2.
apply  (FactP.fold_compat   _  _ Eq_meq (construct_Multiset s1) (construct_Multiset s2) (compat_cm s1) (transp_cm s1) (compat_cm s2) (transp_cm s2)).

(*************************************)

intros.
unfold construct_Multiset .
simpl.

case  x ; intros .
induction c ; intros ; try solve_meq ; simpl.
(******************************************************************)
case  (and_applicable_or_not (inst n (AndC c1 c2)) s1); intros.
case  (and_applicable_or_not (inst n (AndC c1 c2)) s2); intros.
solve_meq.
apply False_ind.
apply n0 ; clear n0.
inversion_clear a.
inversion_clear H1.
inversion_clear H3.
inversion H2.
rewrite <-  H5 ,H6, H7 , H in *; clear   H5 H6 H7 H2.

apply (App_and  _ _ x0 c1 c2).
auto with *.
case  (and_applicable_or_not (inst n (AndC c1 c2)) s2); intros.
apply False_ind.
apply n0 ; clear n0.
inversion_clear a.
inversion_clear H1.
inversion_clear H3.
inversion H2.
rewrite  H5 ,H6, H7 in *; clear   H5 H6 H7 H2.
rewrite <- H in *.
Print and_applicable.
apply (App_and  _ _ n c1 c2).
auto with *.
auto with *.
(************************************************************)
case  (or_applicable_or_not (inst n (OrC c1 c2)) s1); intros.
case  (or_applicable_or_not (inst n (OrC c1 c2)) s2); intros.
solve_meq.
apply False_ind.
apply n0 ; clear n0.
inversion_clear 0.
inversion_clear H1.
inversion_clear H3.
inversion H2.
rewrite <-  H5 ,H6, H7 , H in *; clear   H5 H6 H7 H2.

apply (App_or  _ _ x0 c1 c2).
auto with *.
case  (or_applicable_or_not (inst n (OrC c1 c2)) s2); intros.
apply False_ind.
apply n0 ; clear n0.
inversion_clear o.
inversion_clear H1.
inversion_clear H3.
inversion H2.
rewrite  H5 ,H6, H7 in *; clear   H5 H6 H7 H2.
rewrite <- H in *.

apply (App_or _ _ n c1 c2).
auto with *.
auto with *.
(**************************************************)
assert ((set_rel n c r s1) = (set_rel n c r s2)).
unfold set_rel.
assert (fsetsni.Equal (set_y_in_abox n r s1)  (set_y_in_abox n r s2) ).
unfold set_y_in_abox.
apply     ( FP.fold_equal Eq_cr ) ; auto.


rewrite H1.
assert (fsetsni.Equal (set_y_c_in_abox c s1)  (set_y_c_in_abox c s2) ).
unfold set_y_c_in_abox.

apply     ( FP.fold_equal Eq_cr ) ; auto.
rewrite H2.
auto.
rewrite H1.
assert (set_of_some_term n s1 [=] (set_of_some_term n s2)).
unfold set_of_some_term.
apply   ( FP.fold_equal Equivalence_Eq); auto. 
rewrite H2.
auto with *.
(***********************************************)
case(some_applicable_or_not (inst n (SomeC r c)) s1) ; intros.
case(some_applicable_or_not (inst n (SomeC r c)) s2) ; intros.

solve_meq.
apply False_ind.
apply n0 ; clear n0.
inversion_clear s.
inversion_clear H1.
inversion_clear H3.
inversion H2.
rewrite <-  H5 ,H6, H7 , H in *; clear   H5 H6 H7 H2.

apply (App_some   _ _ n  r0 c1 ).
intuition.
generalize (H4 y0).
intro.
apply H2.
rewrite H.
auto with *.

case(some_applicable_or_not (inst n (SomeC r c)) s2) ; intros.

apply False_ind.
apply n0 ; clear n0.
inversion_clear s.
inversion_clear H1.
inversion_clear H3.
inversion H2.
rewrite  H5 ,H6, H7 in *; clear   H5 H6 H7 H2.
apply (App_some   _ _ x0  r0 c1 ).
rewrite  H in *.
intuition.
generalize (H4 y0).
intro.
apply H2.
rewrite <-  H.
auto with *.

auto with *.
auto with *.
auto with *.
(****************************************)
Qed.


Lemma mes_all1 : forall x n c c1 r AB1  , 
In ( inst x (AllC r c))  AB1 ->In (inst n c1) AB1->
 (mes_comp   AB1 ( inst x (AllC r c))) =   (mes_comp  (add (inst n c1) AB1) ( inst x (AllC r c))).

Proof.
simpl.
intros.
(*****************************************)
assert ( cardinal (set_of_some_term x AB1) = cardinal (set_of_some_term x  (add (inst n c1) AB1))).
unfold set_of_some_term.
Locate add_fold .
rewrite ( FP.add_fold  Equivalence_Eq  (Compat_som x ) (transp_som x)).
auto.
auto.
(*********************************************)
assert (set_rel x  c r AB1 = (set_rel x  c r (add (inst n c1) AB1) )).
   unfold set_rel.
unfold set_y_in_abox.
 rewrite (FP.add_fold Eq_cr (compat_r x r) (transp_r x r) _ H0).
unfold set_y_c_in_abox. 
rewrite (FP.add_fold  Eq_cr (compat_c c) (transp_c c) _  H0).
auto with *.
auto with *.
Qed.




(************************************************************************************************)
(************************************************************************************************)

Lemma mes_all2 : forall x n c c1 c2 r AB1  , 
In ( inst x (AllC r c))  AB1 -> In (inst n (AndC c1 c2)) AB1-> ~  In (inst n c1) AB1->
{gtA (mes_comp   AB1 ( inst x (AllC r c)))   ((mes_comp   (add (inst n c1) AB1) ( inst x (AllC r c))))}
 + {(mes_comp   AB1 ( inst x (AllC r c))) =   (mes_comp  (add (inst n c1) AB1) ( inst x (AllC r c)))}.

Proof.
(***********************************************)
intros.
simpl.
(*****************************************)
assert ( cardinal (set_of_some_term x AB1) = cardinal (set_of_some_term x  (add (inst n c1) AB1))).
unfold set_of_some_term.
rewrite ( FactP.MP.fold_add  Equivalence_Eq  (Compat_som x ) (transp_som x) _ H1).
unfold Constract_set_som .
rewrite  <- ((FP.remove_fold_1 Equivalence_Eq  (Compat_som x ) (transp_som x)  empty H0)).

unfold Constract_set_som.
simpl.
case ( eq_dec_NI x n).
intros. rewrite <-  (FP.union_assoc).
rewrite <-  (FP.union_assoc).

assert(Equal (union (some_term x c1) (some_term x c2)) 
(union (union (some_term x c1) (some_term x c1)) (some_term x c2))).
FiD.fsetdec.
rewrite H2.
FiD.fsetdec.
intro.
auto with *.
rewrite <- H2.
(*********************************************************)
assert (
{set_rel x  c r AB1 > (set_rel x  c r (add (inst n c1) AB1))}
+ 
{ set_rel x  c r AB1 =(set_rel x  c r (add (inst n c1) AB1) ) }
).

(***********************************************)
case (eq_dec_concept c c1).
intro.
subst.
case ( FactP.MP.In_dec  (rel x n r ) AB1  ).
intros.
left.

(*************************Le premier cas *********************)
unfold set_rel .
assert (fsetsni.Equal (set_y_in_abox x r AB1) (set_y_in_abox x r (add (inst n c1) AB1)  )).
unfold set_y_in_abox.

rewrite (FP.fold_add Eq_cr (compat_r x r) (transp_r x r) _ H1).).
auto with *.

(******cardinal_fold*************************)

 assert (fsetsni.Equal (set_y_c_in_abox c1 (add (inst n c1) AB1)) (fsetsni.add n (set_y_c_in_abox  c1 AB1))).
unfold set_y_c_in_abox.
rewrite (FP.fold_add Eq_cr (compat_c c1) (transp_c c1) _ H1 ).
simpl.
case (eq_dec_concept c1 c1).

auto with set.
tauto.
(*****************************)
rewrite <-   H3. 
rewrite  H4.


assert (fsetsni.In  n (set_y_in_abox x r (add (inst n c1) AB1))).
unfold set_y_in_abox.


assert (In (rel x n r) (add (inst n c1) AB1)).


FiD.fsetdec.



rewrite <-  ( FP.remove_fold_1 Eq_cr (f:=(construct_set_of_y_in_rel x r) ) (compat_r x r)(transp_r  x r) fsetsni.empty H5).
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
rewrite H6.
auto with *.


(***************************************************)
(*
rewrite <- H3 in H5.

SearchAbout cardinal.*)
assert(fsetsni.cardinal (fsetsni.diff (set_y_in_abox x r AB1) (set_y_c_in_abox c1 AB1)) = S(fsetsni.cardinal
  (fsetsni.diff (set_y_in_abox x r AB1)
     (fsetsni.add n (set_y_c_in_abox c1 AB1))) )).
SearchAbout cardinal.
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
inversion_clear H6.

subst.
apply fsetsni.diff_3.
NiD.fsetdec.
(******************************************)

Lemma tis: forall AB1 c1 y,  ~ In (inst y c1) AB1-> ~ fsetsni.In y (set_y_c_in_abox c1 AB1).
Proof.
intros.
unfold set_y_c_in_abox.
Locate fold_rec_nodep .
apply FP.fold_rec_nodep.
NiD.fsetdec.
intros.
induction x.
simpl.
case(eq_dec_concept c1 c).
intros.
rewrite e in *.
Locate add_iff.

rewrite(NiD.F.add_iff).

intro.
inversion_clear H2.
rewrite H3 in *.
auto with *.
auto with *.
intros.
auto with *.
simpl.
auto with *.
simpl.
auto with *.
Qed.
apply (tis _ _ _ H1).

NiD.fsetdec.
rewrite H6.
auto.
intros.
(**************************************************************)
right.

(********************************************)
(*********************************************)

(*unfold set_rel .***************** later *************)

unfold set_rel .

assert (fsetsni.Equal (set_y_in_abox x r AB1) (set_y_in_abox x r (add (inst n c1) AB1)  )).
unfold set_y_in_abox.

rewrite (FP.fold_add Eq_cr (compat_r x r) (transp_r x r) _ H1).).
auto with *.
(*************************************)
rewrite <- H3.
assert (fsetsni.Equal (fsetsni.diff (set_y_in_abox x r AB1) (set_y_c_in_abox c1 AB1)) (fsetsni.diff (set_y_in_abox x r AB1)
     (set_y_c_in_abox c1 (add (inst n c1) AB1)))).
red.
split.
intros.
case (NI_as_DT.eq_dec n a).
intros.
inversion e.
rewrite <-  H5 in *.

Lemma tis2: forall n x r AB1, ~ In (rel x n r) AB1-> ~  fsetsni.In n (set_y_in_abox x r AB1).
Proof.
intros; unfold set_y_in_abox .
apply FP.fold_rec_nodep.
auto with set.

intros.
induction x0; simpl ; auto with set .


unfold eq_ni , eq_role.
case (NP.Dec.F.eq_dec n0 x) ;intro ;simpl ; auto with set .

case (eq_dec_role ); intro ; simpl ;auto with set .

rewrite e0 , e in *.
rewrite(NiD.F.add_iff) ; intro.
inversion_clear H2 ;auto with *.
rewrite H3 in *; auto with *.
Qed.


generalize(tis2 _ _ _   _ n0).
intros.
apply fsetsni.diff_1 in H4.
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
apply fsetsni.diff_2 in H4. 
apply H4.
NiD.fsetdec.
intro.
tauto.
intros.
apply fsetsni.diff_3.
NiD.fsetdec.
apply fsetsni.diff_2 in H4. 
intro.
apply H4.
unfold set_y_c_in_abox.


rewrite FP.fold_add ; auto.
simpl.
case (eq_dec_concept c1 c1 ). intros. NiD.fsetdec.
intro.
auto.
auto with *.
(**************************************************)
intros.
right.

unfold set_rel .

assert (fsetsni.Equal (set_y_in_abox x r AB1) (set_y_in_abox x r (add (inst n c1) AB1)  )).
unfold set_y_in_abox.

rewrite (FP.fold_add Eq_cr (compat_r x r) (transp_r x r) _ H1).).
auto with *.
(*********************************************)
assert (fsetsni.Equal (set_y_c_in_abox c AB1)  (set_y_c_in_abox c (add (inst n c1) AB1))).

unfold set_y_c_in_abox. 

rewrite FP.fold_add ; auto.
simpl.
case (eq_dec_concept c c1).
intro.
tauto.
intro.
auto with *.
rewrite H3 , H4.
auto with *.
inversion_clear H3.
left.
unfold gtA.
right.
simpl.
auto with *.
right.
auto with *.
Qed.




Lemma mes_all : forall x n c c1 c2 r AB1 , 
In ( inst x (AllC r c))  AB1 -> In (inst n (AndC c1 c2)) AB1-> 
{gtA (mes_comp   AB1 ( inst x (AllC r c)))   ((mes_comp   (add (inst n c1) AB1) ( inst x (AllC r c))))}
 + {(mes_comp   AB1 ( inst x (AllC r c))) =   (mes_comp  (add (inst n c1) AB1) ( inst x (AllC r c)))}.
Proof.
intros.
Locate In_dec.
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

Lemma mes_all3 : forall x n c c1 c2 r AB1  , 
In ( inst x (AllC r c))  AB1 -> In (inst n (AndC c1 c2)) AB1-> ~  In (inst n c2) AB1->
{gtA (mes_comp   AB1 ( inst x (AllC r c)))   ((mes_comp   (add (inst n c2) AB1) ( inst x (AllC r c))))}
 + {(mes_comp   AB1 ( inst x (AllC r c))) =   (mes_comp  (add (inst n c2) AB1) ( inst x (AllC r c)))}.
Proof.

(***********************************************)
intros.
simpl.
(*****************************************)
assert ( cardinal (set_of_some_term x AB1) = cardinal (set_of_some_term x  (add (inst n c2) AB1))).
unfold set_of_some_term.
rewrite ( FactP.MP.fold_add  Equivalence_Eq  (Compat_som x ) (transp_som x) _ H1).
unfold Constract_set_som .
rewrite  <- ((FP.remove_fold_1 Equivalence_Eq  (Compat_som x ) (transp_som x)  empty H0)).

unfold Constract_set_som.
simpl.
case ( eq_dec_NI x n).
intros. rewrite <-  (FP.union_assoc).
rewrite <-  (FP.union_assoc).

assert(Equal (union (some_term x c1) (some_term x c2)) 
(union (union (some_term x c2) (some_term x c1)) (some_term x c2))).
FiD.fsetdec.
rewrite H2.
FiD.fsetdec.
intro.
auto with *.
rewrite <- H2.
(*********************************************************)
assert (
{set_rel x  c r AB1 > (set_rel x  c r (add (inst n c2) AB1))}
+ 
{ set_rel x  c r AB1 =(set_rel x  c r (add (inst n c2) AB1) ) }
).

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

rewrite (FP.fold_add Eq_cr (compat_r x r) (transp_r x r) _ H1).).
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
rewrite <-   H3. 
rewrite  H4.


assert (fsetsni.In  n (set_y_in_abox x r (add (inst n c2) AB1))).
unfold set_y_in_abox.


assert (In (rel x n r) (add (inst n c2) AB1)).


FiD.fsetdec.



rewrite <-  ( FP.remove_fold_1 Eq_cr (f:=(construct_set_of_y_in_rel x r) ) (compat_r x r)(transp_r  x r) fsetsni.empty H5).
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
rewrite H6.
auto with *.


(***************************************************)
(*
rewrite <- H3 in H5.

SearchAbout cardinal.*)
assert(fsetsni.cardinal (fsetsni.diff (set_y_in_abox x r AB1) (set_y_c_in_abox c2 AB1)) = S(fsetsni.cardinal
  (fsetsni.diff (set_y_in_abox x r AB1)
     (fsetsni.add n (set_y_c_in_abox c2 AB1))) )).
SearchAbout cardinal.
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
inversion_clear H6.

subst.
apply fsetsni.diff_3.
NiD.fsetdec.
(******************************************)


apply (tis _ _ _ H1).

NiD.fsetdec.
rewrite H6.
auto.
intros.
(**************************************************************)
right.

(********************************************)
(*********************************************)

(*unfold set_rel .***************** later *************)

unfold set_rel .

assert (fsetsni.Equal (set_y_in_abox x r AB1) (set_y_in_abox x r (add (inst n c2) AB1)  )).
unfold set_y_in_abox.

rewrite (FP.fold_add Eq_cr (compat_r x r) (transp_r x r) _ H1).).
auto with *.
(*************************************)
rewrite <- H3.
assert (fsetsni.Equal (fsetsni.diff (set_y_in_abox x r AB1) (set_y_c_in_abox c2 AB1)) (fsetsni.diff (set_y_in_abox x r AB1)
     (set_y_c_in_abox c2 (add (inst n c2) AB1)))).
red.
split.
intros.
case (NI_as_DT.eq_dec n a).
intros.
inversion e.
rewrite <-  H5 in *.



generalize(tis2 _ _ _   _ n0).
intros.
apply fsetsni.diff_1 in H4.
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
apply fsetsni.diff_2 in H4. 
apply H4.
NiD.fsetdec.
intro.
tauto.
intros.
apply fsetsni.diff_3.
NiD.fsetdec.
apply fsetsni.diff_2 in H4. 
intro.
apply H4.
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

rewrite (FP.fold_add Eq_cr (compat_r x r) (transp_r x r) _ H1).).
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
rewrite H3 , H4.
auto with *.
inversion_clear H3.
left.
unfold gtA.
right.
simpl.
auto with *.
right.
auto with *.
Qed.






Lemma mes_all_r : forall x n c c1 c2 r AB1 , 
In ( inst x (AllC r c))  AB1 -> In (inst n (AndC c1 c2)) AB1-> 
{gtA (mes_comp   AB1 ( inst x (AllC r c)))   ((mes_comp   (add (inst n c2) AB1) ( inst x (AllC r c))))}
 + {(mes_comp   AB1 ( inst x (AllC r c))) =   (mes_comp  (add (inst n c2) AB1) ( inst x (AllC r c)))}.
Proof.
intros.
Locate In_dec.
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


(****************************************until now ok *********************************************)
(***************************************************************************************)
Lemma mes_all_g  : forall x n c c1 c2 r AB1  , 
In ( inst x (AllC r c))  AB1 -> In (inst n (AndC c1 c2)) AB1-> 
{gtA (mes_comp   AB1 ( inst x (AllC r c)))   ((mes_comp  (add (inst n c2) (add (inst n c1) AB1)) ( inst x (AllC r c))))}
 + {(mes_comp   AB1 ( inst x (AllC r c))) =   (mes_comp  (add (inst n c2)(add (inst n c1) AB1)) ( inst x (AllC r c)))}.

Proof.
intros.

case ( mes_all x n c c1 c2 r AB1).


auto.
auto.
intros.
case ( mes_all_r x n c c1 c2 r (add (inst n c1) AB1)).
FiD.fsetdec.
FiD.fsetdec.
intro.
left.
Focus 2.
intros.
left.
rewrite e in g.
auto with *.
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
apply (gtA_trans _ _ _ g g0).
intros.

case ( mes_all_r x n c c1 c2 r (add (inst n c1) AB1)).
FiD.fsetdec.
FiD.fsetdec.
intro.
left.
rewrite e.
auto with *.
intros.
right.
rewrite e.
auto.
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
compute.
auto.

compute.
auto.
compute.
auto.
compute .
auto.

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
case(and_applicable_or_not (inst n (AndC c3 c4))
        (add (inst x c2) (add (inst x c1) s2))).
intros.

assert (  ~and_applicable (inst n (AndC c3 c4))
      (add (inst x c2) (add (inst x c1) s2))) .
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
FiD.fsetdec.
FiD.fsetdec.
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
Print some_applicable.
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
Lemma equal_mes_comp : forall f s1 s2 , s1 [=] s2 ->  (mes_comp s1 f ) = (mes_comp s2 f ).
Proof.
intros.
simpl.
unfold mes_comp .
case f ; intros. case c ;  intros ;  simpl ; auto with *.
case (and_applicable_or_not (inst n (AndC c0 c1)) s1).
case (and_applicable_or_not (inst n (AndC c0 c1)) s2).
intros; auto with *.
intros.
apply False_ind; apply n0 ; clear n0.
inversion_clear a.
inversion_clear H0.
inversion H1.
rewrite H3, H4, H5 in *; clear H1 H3 H4 H5.
inversion_clear H2.
apply (App_and _ _ n c0 c1) ; rewrite <- H.
auto with *.
(*********case (and_applicable_or_not (inst n (AndC c0 c1)) s2).********************************)

case (and_applicable_or_not (inst n (AndC c0 c1)) s2).
intros.
apply False_ind; apply n0 ; clear n0.
inversion_clear a.
inversion_clear H0.
inversion H1.
rewrite H3, H4, H5 in *; clear H1 H3 H4 H5.
inversion_clear H2.
apply (App_and _ _ n c0 c1) ; rewrite  H.
auto with *.
auto with *.
(******************************************************)
case (or_applicable_or_not (inst n (OrC c0 c1)) s1).
case (or_applicable_or_not (inst n (OrC c0 c1)) s2).
intros; auto with *.
intros.
apply False_ind; apply n0 ; clear n0.
inversion_clear o.
inversion_clear H0.
inversion H1.
rewrite H3, H4, H5 in *; clear H1 H3 H4 H5.
inversion_clear H2.
apply (App_or _ _ n c0 c1) ; rewrite <- H.
auto with *.
(****************************************)

case (or_applicable_or_not (inst n (OrC c0 c1)) s2).
intros.
apply False_ind; apply n0 ; clear n0.
inversion_clear o.
inversion_clear H0.
inversion H1.
rewrite H3, H4, H5 in *; clear H1 H3 H4 H5.
inversion_clear H2.
apply (App_or _ _ n c0 c1) ; rewrite  H.
auto with *.
auto with *.
(***************************************)


assert ((set_rel n c0 r s1) = (set_rel n c0 r s2)).
unfold set_rel.
assert (fsetsni.Equal (set_y_in_abox n r s1)  (set_y_in_abox n r s2) ).
unfold set_y_in_abox.
apply     ( FP.fold_equal Eq_cr ) ; auto.


rewrite H0.
assert (fsetsni.Equal (set_y_c_in_abox c0 s1)  (set_y_c_in_abox c0 s2) ).
unfold set_y_c_in_abox.

apply     ( FP.fold_equal Eq_cr ) ; auto.
rewrite H1.
auto.
rewrite H0.
assert (set_of_some_term n s1 [=] (set_of_some_term n s2)).
unfold set_of_some_term.
apply   ( FP.fold_equal Equivalence_Eq); auto. 
rewrite H1.
auto with *.
(************************************************************)
case(some_applicable_or_not (inst n (SomeC r c0)) s1) ; intros.
case(some_applicable_or_not (inst n (SomeC r c0)) s2) ; intros.

solve_meq.
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
auto with *.

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
auto with *.

auto with *.
auto with *.
auto with *.
Qed.

(********************************************************************************)
Lemma dec_eq_gt_in_remov  : forall  c1 c2 x s2 ,  In (inst x  (AndC c1 c2)) s2->
                                      forall f,  In f (remove (inst x (AndC c1 c2) ) s2) ->
             ({ gtA  (mes_comp s2 f)  (mes_comp (add (inst x c2) (add (inst x c1) s2))f )}
          +          {   (mes_comp s2 f)  =  (mes_comp (add (inst x c2) (add (inst x c1)s2))f )}).
Proof.
intros.
 apply dec_eq_gt_in_the_rest.
auto.
FiD.fsetdec.
FiD.fsetdec. 
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
Lemma MultisetGT_equal  : forall M1 M2 M3, M2 =mul= M3 -> MultisetGT gtA M1 M2 -> MultisetGT gtA M1 M3.
Proof.
intros.
inversion H0.
Print MultisetGT.
assert (  M3 =mul= Z + Y).
rewrite <-  H.
auto.
apply (MSetGT gtA H1  H2 H5  H4). 
Qed.
Lemma MultisetGT_equal2  : forall M1 M2 M3, M2 =mul= M3 -> MultisetGT gtA M2 M1 -> MultisetGT gtA M3 M1.
Proof.
intros.
inversion H0.
Print MultisetGT.
assert (  M3 =mul= Z + X).
rewrite <-  H.
auto.
apply (MSetGT gtA H1  H5 H3  H4). 
Qed.
(**********************************)
Lemma importante :  ( forall s x c , fst  (mes_comp s (inst x c))  <=  sizeC c).
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
(* generalize ( importante  (add (inst x c2) (add (inst x c1) s2)) x c1).
intros.*)
Lemma mah :forall a b c,  a <= b ->   b< c -> a < c.
intros.
omega.
Qed.

(*******************************************)
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
Check FP.fold_commutes.
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
Print MultisetGT .
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
Print and_applicable.
apply (App_and     _     s2 x c1 c2).
auto with *.
apply member_singleton in H1.
inversion_clear H1.
(***********************)
unfold gtA.
left.
generalize ( importante  (add (inst x c2) (add (inst x c1) s2)) x c1).
intros.
apply (mah _ _  _ H0).
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
Print MultisetGT.
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
(****** goooooooooooooooood*******************)

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
Print MultisetGT .
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
Print and_applicable.
apply (App_and     _     s2 x c1 c2).
auto with *.
apply member_singleton in H1.
inversion_clear H1.
(***********************)
unfold gtA.
left.
generalize ( importante  (add (inst x c2) (add (inst x c1) s2)) x c2).
intros.
apply (mah _ _  _ H0).
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
Print MultisetGT.
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
Print MultisetGT .

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
Print and_applicable.
apply (App_and     _     s2 x c1 c2).
auto with *.
(*****************************************************)

(***********************)
apply member_singleton in H0.
rewrite H0.
unfold gtA.
left.
generalize ( importante  (add (inst x c2) (add (inst x c1) s2)) x c1).
intros.
apply (mah _ _  _ H1).
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
generalize ( importante  (add (inst x c2) (add (inst x c1) s2)) x c2).
intros.
apply (mah _ _  _ H0).
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
Print MultisetGT.
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




end...............
(*********************************************)
(*                                                      *)

(*************************************************)



Lemma  succ_decrease : forall  s1 s2, succ  s1 s2 ->MultisetLT gtA   (Measure  s1) (Measure s2).
Proof.
intros.
inversion_clear H.
inversion_clear H1.
inversion_clear H.
inversion_clear H1.
rewrite H2; clear H2.
(*************************************)
assert (mes_comp     s2  ( (inst x (AndC c1 c2))) = (sizef  (inst x (AndC c1 c2)), 0)).
assert (and_applicable   ( (inst x (AndC c1 c2))) s2).
apply (App_and (inst x (AndC c1 c2)) s2 x c1 c2).
tauto.
hnf.
simpl.
case (and_applicable_or_not (inst x (AndC c1 c2)) s2).
intro. auto.
intro. 
contradiction.
(*****************************)
 assert ((mes_comp  (fsetsfact.add (inst x c2) (fsetsfact.add (inst x c1) s2))   (inst x (AndC c1 c2) )) = (0,0)).
simpl.
case (  and_applicable_or_not (inst x (AndC c1 c2))).
intros.
inversion_clear a.
inversion_clear H2.
inversion_clear H5.
inversion  H4.
rewrite H7 , H8 , H9 in *.

apply NNPP.
intro.
apply H6.
split.
auto with *.
auto with *.
intro.
auto.
(************************************)
 assert ( forall f , f<> (inst x (AndC c1 c2) )-> fsetsfact.In f s2 -> geA  (mes_comp s2 f)  (mes_comp (fsetsfact.add (inst x c2) (fsetsfact.add (inst x c1) s2)) f)).
intros.
simpl.
induction  f.
intros.


case ( Fact_as_DT.eq_dec (inst x (AndC c1 c2)) (inst n  c ) ).
intro.
rewrite e in *.
rewrite H1 , H2.
unfold geA.
unfold gtA.
left.
left.
unfold sizef.
intuition.  intros. 


induction c .  




compute.
auto.
compute.
auto.
compute.
auto.
compute .
auto.
(*******************)
unfold geA. simpl.

case (and_applicable_or_not (inst n (AndC c3 c4))
        (fsetsfact.add (inst x c2) (fsetsfact.add (inst x c1) s2))).
intros.

case (and_applicable_or_not (inst n (AndC c3 c4))  s2).
intros.

right.
simpl.
red.
auto.
intro.
apply NNPP ;intro B ;  clear B.
inversion_clear a.
inversion_clear H6.
inversion_clear H8.
inversion H7.
rewrite H10 ,H11 , H12 in *. clear H10 H11 H12  H7.
apply n1.
apply (App_and (inst n (AndC c3 c4))  s2 n c3 c4).
intuition.
intro.
case (and_applicable_or_not (inst n (AndC c3 c4))  s2).
intros.
left.
unfold gtA.
left.
simpl.
auto with *.
intro.
right.
red.
auto.

clear IHc1 IHc2.
unfold geA.

(*********************)
simpl.

case (or_applicable_or_not (inst n (OrC c3 c4))
        (fsetsfact.add (inst x c2) (fsetsfact.add (inst x c1) s2))).
intros.
case (or_applicable_or_not (inst n (OrC c3 c4)) s2).
intros.
right.
red.
auto.
(*****)
intro.
inversion_clear o.
inversion_clear H6.
inversion_clear H8.
inversion_clear H9.
apply NNPP ;intro B ;  clear B.
inversion H7.
 
rewrite H13 ,H11 , H12 in *. clear H13 H11 H12  H7.
apply n1.
apply (App_or  (inst n (OrC c3 c4))  s2 n c3 c4).
intuition.
(**********************)
intro.
case (or_applicable_or_not (inst n (OrC c3 c4)) s2).
intros.
left.
unfold gtA.
left.
simpl.
auto with *.
intros.
right.
red.
auto.
(*************************************)
Focus 2.
simpl.
case (some_applicable_or_not (inst n ( (SomeC r c)))
        (fsetsfact.add (inst x c2) (fsetsfact.add (inst x c1) s2))).
intro.
case (some_applicable_or_not (inst n  (SomeC r c)) s2).
intro.
unfold geA.
right.
red.
auto.
intro.
apply NNPP; intro B ; clear B.
inversion_clear s.
inversion_clear H6.
inversion_clear H8.
inversion H7.
rewrite H10 , H11, H12 in * ; clear H10 H11 H12 H7.
apply n1.
 
apply (App_some  (inst x0 (SomeC r0 c0))  s2 x0 r0 c0).

intuition.
generalize (H9 y). intros.
auto with *.
(*********************)
intro.
case (some_applicable_or_not (inst n  (SomeC r c)) s2) ; intros.
unfold geA.
left.
red.
left.
simpl.
auto with *.
right.
red. auto.
(********************************)
Focus 2.
right.
red.
simpl.
auto.

Focus 2.
right.
red.
simpl.
auto.
Lemma intermed1 : forall s2 n x r c c1 c2 , geA (mes_comp s2 (inst n (AllC r c)))
  (mes_comp (fsetsfact.add (inst x c2) (fsetsfact.add (inst x c1) s2))
     (inst n (AllC r c))).
Proof.
Admitted.
apply intermed1.

(************************)
unfold Measure.
induction mes_list.
induction (Measure s2).
Check map.
unfold geA in H4.

apply MSetGT.
induction  ( fsetsfact.elements s2).
compute.
kkk

(***********************************)

(**********************************)
simpl.
assert(fsetsfact.Subset ( (fsetsfact.filter (rel_without_inst n r c s2) s2))  (
    (fsetsfact.filter
       (rel_without_inst n r c
          (fsetsfact.add (inst x c2) (fsetsfact.add (inst x c1) s2)))
       (fsetsfact.add (inst x c2) (fsetsfact.add (inst x c1) s2))) )) .
Locate filter_subset.
unfold fsetsfact.Subset .
intros.
Locate filter_iff.

rewrite   factFact.filter_iff.
split.




generalize  (fsetsfact.filter_1).
intros.
generalize (H7 (fsetsfact.add (inst x c2) (fsetsfact.add (inst x c1) s2)) a ).
unfold rel_without_inst in H6.
intro.rel_without_inst
simpl.
red.

compute.
unfold geA.
unfold rel_without_inst.
right.
********************)
red.
simpl.
(*********************************************)
(************************************************)
assert (
fsetsfact.cardinal (fsetsfact.filter (rel_without_inst n r c s2) s2)  = fsetsfact.cardinal
  (fsetsfact.filter
     (rel_without_inst n r c
        (fsetsfact.add (inst x c2) (fsetsfact.add (inst x c1) s2)))
     (fsetsfact.add (inst x c2) (fsetsfact.add (inst x c1) s2))))
.
f_equal.

f_equal.
Print rel_without_inst.
generalize 





















  (*Lt_abox  s1 s2.  this must proved*)

Lemma wf_multiLT :  well_founded (MultisetLT gt ).
Proof.
apply   mOrd_wf.
intuition.
inversion H.
inversion H0.
omega.
compute.
auto with *.
Qed.

Lemma wf_lt_abox : well_founded Lt_abox .
Proof.
red.
apply  (wf_inverse_image Abox Multiset ( MultisetLT gt ) Measure ).
apply wf_multiLT.
Qed.

Lemma wf_succ : well_founded succ.
Proof.

apply (wf_incl Abox succ Lt_abox ).
red.
apply succ_decrease.
exact wf_lt_abox .
Qed.
(********************************************
the laset proof   **)
