Require Export Tableau.

(****************************************************************************)

Definition set_ni_left_atom A  (AB:Abox) : Ensemble NI := fun x => In   (inst x (AtomC A)) AB.

Definition rel_ni_atom_role  (R : NR) (AB :Abox) : Relation NI := fun x y =>In  (rel x y (AtomR R)) AB.

Set Implicit Arguments.Definition  can_in (AB : Abox) :Interp := Build_Interp _  (fun c => set_ni_left_atom c  AB) (fun R => rel_ni_atom_role R AB)(fun x => x ).

(****************************************************************************)
Set Implicit Arguments.
Hint Resolve can_in .
(****************************************************************************)
(****************************************************************************)

Lemma content_clash_not_satisfiable : forall AB, contains_clash AB ->~ abox_satisfiable AB.
Proof.
intros.
inversion_clear H.
inversion_clear H0.
inversion_clear H.
inversion_clear H0.
intro.
inversion_clear H0.
unfold is_model_Abox in H2.
generalize (H2 (inst x x0) ).
intros.
generalize (H0 H ).
intros.
generalize (H2 (inst x (NotC x0)) ).
intros.
generalize (H4 H1 ).
intros.
unfold inter_satisfies_fact in H3 .
unfold inter_satisfies_fact in H5 .
contradiction.
intro.
inversion_clear H.
unfold is_model_Abox in H1.
 generalize (H1 (inst x Bottom) ). 
intros. generalize (H H0 ).
intros.
inversion_clear H2.
Qed.


(***************************************************************************)
(***************************************************************************)

Lemma can_in_int : forall x c AB,   In  (inst x  c ) AB -> interp_inst (can_in AB) x =x .
Proof.
intros.
trivial.
Qed.
(***************************************************************************)
Lemma can_in_relation : forall x y r AB , In  (rel x  y r ) AB ->  inter_satisfies_fact  (can_in AB) (rel x  y r ).
Proof.
intros.
simpl.
induction  r.
simpl.
trivial.
Qed.
(***************************************************************************)
Lemma can_in_satis_atom : forall x  c AB,  In  (inst x  (AtomC c) ) AB ->  inter_satisfies_fact  (can_in AB) (inst x  (AtomC c) ).
Proof.
intros.
eauto with *.
Qed.
(***************************************************************************)
Lemma completl_cn_and :forall AB c1 c2 x ,  complete AB ->  ~ contains_clash AB->  In  (inst x  (AndC c1 c2) ) AB -> ( In  (inst x  c1 ) AB /\  In  (inst x  c2 ) AB).
 
Proof.
intros.
unfold complete , rule in H.
generalize (H ( add (inst x c2) (  add   (inst x c1) AB))). 
intro.
apply NNPP.
intro.
apply H2.
left.
clear H2.
clear H.

apply (mk_andrule AB ( add (inst x c2) (  add   (inst x c1) AB)) x c1 c2).
auto with *.
trivial.


Qed.
(***************************************************************************)
Lemma completl_cn_or :forall AB c1 c2 x ,  complete  AB ->  ~ contains_clash AB-> In  (inst x  (OrC c1 c2) ) AB -> 
( In (inst x  c1 ) AB \/  In (inst x  c2 ) AB ).
Proof.
intros.
unfold complete , rule in H.
generalize (H ( add  (inst x c1) AB) ). 
intro.
apply NNPP.
intro.
apply H2.
right.
left.
clear H2.
clear H.
apply (mk_orruleleft  AB  (add  (inst x c1) AB)  x c1 c2).
tauto .
auto.
Qed.
(***************************************************************************)
Lemma completl_cn_all: forall AB c r x ,  complete  AB ->  ~ contains_clash AB-> In  (inst x  (AllC r c) ) AB ->(forall y,   In (rel x  y r ) AB ->  In (inst y c) AB).
Proof.
unfold complete , rule .
intros.
generalize (H ( add  (inst y c) AB)).
intro.
apply NNPP.
intro.
apply H3.
compute.
right. right. right.  left.
clear H3.
clear H.
apply (mk_Alrule AB ( add  (inst y c) AB) x y r c). tauto .
auto.
Qed.

(*************************************************************************)
Lemma completl_cn_some: forall AB c r x ,  complete  AB ->  ~ contains_clash AB-> In  (inst x  (SomeC r c) ) AB -> (exists y , In  (rel x  y r ) AB /\  In (inst y c) AB).
Proof.
unfold complete , ALC_rule.
intros.
generalize (Var_fresh (set_ni_in_abox  AB)).
intros.
inversion_clear H2.

generalize ( H (  add (rel x x0 r) (  add (inst x0 c) AB))); clear H.
intro.
apply NNPP.
intro.
apply H; clear H.
compute.
right.
right.
right.
right.
left.
apply (mk_Somerule  AB ( add (rel x x0 r) ( add (inst x0 c) AB)) x x0  r c ).
intuition.
apply H2.
exists y.
tauto.
auto.
Qed.


(****************)
Lemma canonical_satisfa_inst : forall AB  c x, is_Normal_Abox AB ->   
complete  AB ->  ~ contains_clash AB->  In  (inst x  c)  AB -> inter_satisfies_fact  (can_in AB) (inst x  c ).

Proof.
intro.
induction c ;intros.
auto with *.
(*******)
compute.
apply Full_intro.
(*****************)
unfold contains_clash  in H1.
elim H1.
exists x.
exists Bottom.
right.
trivial.
(**********************)


generalize (H (inst x (NotC c)) H2).
intros.
inversion_clear H3.
unfold can_in , set_ni_left_atom, rel_ni_atom_role, Ensembles.In  in *|-*.

rewrite H4 in *|-*.
compute.
intro.
apply H1.
red.
exists x.
exists c.
left.
rewrite H4.
tauto.
(***************************)
generalize(IHc1 x); clear IHc1; intro IHc1.
generalize (IHc2 x);clear IHc2; intro IHc2.
generalize ( completl_cn_and   H0 H1 H2).
intro.
inversion_clear H3.
simpl.
intuition.
(******************************)
generalize(IHc1 x); clear IHc1; intro IHc1.
generalize (IHc2 x);clear IHc2; intro IHc2.
generalize ( completl_cn_or  H0 H1 H2).
intro.
simpl.
intuition.
(**********************)
generalize ( completl_cn_all  H0 H1 H2).
intros.
induction r.
simpl.
intro.
intros.
red in H4.
generalize (H3 y H4).
intro.
generalize( IHc y H H0 H1 H5);clear IHc; simpl; intro IHc.
auto.
(***********************************************************)
simpl.
generalize ( completl_cn_some   H0 H1 H2).
intros. induction r.
simpl.
red.

intuition.
inversion H3.
exists x0.
split.
tauto.
simpl.
inversion_clear H4.
generalize( IHc x0 H H0 H1 H6);clear IHc; simpl; intro IHc.
auto.
Qed.


Require Export FSetDecide. 

Module Import FiD := WDecide_fun  Fact_as_DT fsetsfact.

(***************************)

Lemma  not_diff_in_succ : forall AB AB0 x y , ~  In (dif x y) AB0 ->  ALC_rule  AB0 AB->  ~  In (dif x y) AB .
Proof.
intros; inversion_clear H0; inversion_clear H1.
subst.
clear H0 ; rewrite F.add_iff ; rewrite F.add_iff ; intro.
inversion_clear H0.
discriminate H1.
inversion_clear H1.
discriminate H0.
auto.

inversion_clear H0.
subst.
clear H1 ; rewrite F.add_iff ;  intro.
inversion_clear H0.
discriminate H1.
auto.

inversion_clear H0; inversion_clear H1.
subst.
clear H0 ; rewrite F.add_iff ;  intro.
inversion_clear H0.
discriminate H1.
auto.

inversion_clear H0.
subst.
clear H1 ; rewrite F.add_iff . 
intro.
inversion_clear H0.
discriminate H1.
auto.


inversion_clear H0.
inversion_clear H1.
subst.
clear H0 ; rewrite F.add_iff ;  rewrite F.add_iff ;intro.
inversion_clear H0.
discriminate H1.
inversion_clear H1.
discriminate H0.
auto.
auto.

Qed.

(************************************)
Lemma  not_diff_in_exponsion : forall AB AB0 x y , ~  In (dif x y) AB0 ->rstar_rule  ALC_rule  AB0 AB->  ~  In (dif x y) AB .
Proof.
intros.
induction H0.
auto.

apply IHRstar.
apply (not_diff_in_succ   H H0).
Qed.

Lemma  not_diff_in_exponsion_initial : forall AB  x y ,  (rstar_rule  ALC_rule Abox_initial  AB)->  ~  In (dif x y) AB .
Proof.
intros.
 apply (not_diff_in_exponsion  (AB:=AB)  (AB0 := Abox_initial)).
unfold Abox_initial.
rewrite F.singleton_iff.
intro.
discriminate H0.
auto.
Qed.



(**********************)
Lemma canonical_satisfa_abox_complet : forall AB  , (rstar_rule  ALC_rule Abox_initial  AB) ->is_Normal_Abox AB ->   
complete  AB ->  ~ contains_clash AB-> abox_satisfiable AB.
Proof.
intros.
red.
exists  (can_in AB).
red. 
intros.
induction Aa. 
apply canonical_satisfa_inst; trivial.
apply can_in_relation ; trivial.
generalize (not_diff_in_exponsion_initial (x:= n) (y:=n0) H) ; intros.
tauto.
Qed.
(*****)

