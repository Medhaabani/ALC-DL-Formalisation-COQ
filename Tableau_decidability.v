Require Export Tableau .

Require Export FSetEqProperties.
Module Import FactP := WEqProperties_fun  Fact_as_DT fsetsfact.
Module  NiP := WEqProperties_fun  NI_as_DT fsetsni.

Require Export FSetDecide. 
Module  NiD := WDecide_fun  NI_as_DT fsetsni.
Module Export FiD := WDecide_fun  Fact_as_DT fsetsfact.

Require Export FSetProperties.
Module Import FP := WProperties_fun  Fact_as_DT fsetsfact.
Module  NP := WProperties_fun  NI_as_DT fsetsni.

Definition is_dec (p:Prop) := {p}+{~p}.

Definition eq_dec (T :Set) := forall x y:T, is_dec (x=y).

Lemma eq_dec_concept : eq_dec concept  . 
Proof.
unfold  eq_dec ,is_dec .
repeat decide equality.
Qed.

Lemma eq_dec_role : eq_dec role  . 
unfold  eq_dec ,is_dec .
decide equality.
Qed.

Lemma eq_dec_NI : eq_dec NI  . 
unfold  eq_dec ,is_dec .
trivial.
Qed.

Lemma dec_not: forall p, is_dec p -> is_dec (~p).
Proof.
unfold is_dec; intros.
inversion_clear H.
right ; auto.
left ; auto.
Qed.

Lemma dec_not2: forall p, is_dec (~ p) -> is_dec p.
Proof.
unfold is_dec; intros.
inversion_clear H.
right ; auto.
left ; apply NNPP . auto.
Qed.

Lemma dec_and: forall p1 p2, is_dec p1 -> is_dec p2 -> is_dec (p1 /\  p2).
Proof.
unfold is_dec; intros.
inversion_clear H.
inversion_clear H0.
left ; auto.
right ; tauto.
right ; tauto.
Qed.

Definition is_inv (T U:Set) (f:T->U) p (y:U) := 
      ({x: T | f x = y /\ p x} + (forall x, f x <> y \/ ~(p x)))%type.

Lemma dec_inall: forall p (f:NI->fact),
(forall y, is_inv NI fact f p y) -> 
forall l, 
    {x: NI |  InA  Fact_as_DT.eq (f x) l /\ (p x)} + 
    (forall x, ~(InA  Fact_as_DT.eq  (f x)  l /\ (p x))).

Proof.
   induction l; intros.
   right; intros.
   unfold not; intro.
   inversion_clear H0.
   inversion_clear H1.

   case (H a); intros.
   inversion_clear s.
   inversion_clear H0.
   left; exists x; split; auto.
  

   inversion_clear IHl.
   inversion_clear H0.
   inversion_clear H1.
   left; exists x; split; auto.
   right; auto.

   intros.
   unfold not; intro.
   inversion_clear H1.
   elim (o x); intros; auto.
   inversion_clear H2.
   apply H1; rewrite H4; auto.
   apply (H0 x); split; auto.
Qed.

Lemma dec_exists_list :  forall  l c  r n  ,
(  { y|   ( InA  Fact_as_DT.eq(rel n  y  r) l /\  ~ InA  Fact_as_DT.eq (inst  y  c) l )}+
   (forall y ,~ ( InA  Fact_as_DT.eq (rel n  y  r) l/\  ~ InA  Fact_as_DT.eq (inst  y  c) l) )  ).
Proof.
   intros.
   apply dec_inall; intros.
   unfold is_inv.
   case y; clear y; intros.
   right; intros.
   left; unfold not; intro.
   discriminate H.

   case (eq_dec_NI n n0 ); intros.
   rewrite e; clear e n.
   case (eq_dec_role r r0); intros.
   rewrite e; clear e r.
   case ( InA_dec  Fact_as_DT.eq_dec (inst n1 c) l); intros.
   right; intros.
   case (eq_dec_NI x n1); intros.
   rewrite e; right; unfold not; intros.
   apply H; auto.
   left; unfold not; intro.

   injection H; clear H; intro.
   apply n; auto.
   left; exists n1; split; auto.

   right; intros; left.
   unfold not; intro.
   injection H; clear H; intros.
   apply n; auto.

   right; intros; left.
   unfold not; intro.
   injection H; clear H; intros.
   apply n2; auto.

   right; intros; left.
   discriminate.
Qed.

Lemma dec_exists_list2 :  forall  l c  r n  ,
(  { y|   ( InA  Fact_as_DT.eq(rel n  y  r) l /\   InA  Fact_as_DT.eq (inst  y  c) l )}+
   (forall y ,~ ( InA  Fact_as_DT.eq (rel n  y  r) l/\   InA  Fact_as_DT.eq (inst  y  c) l) )  ).
Proof.
   intros.
   apply dec_inall; intros.
   unfold is_inv.
   case y; clear y; intros.
   right; intros.
   left; unfold not; intro.
   discriminate H.
   case (eq_dec_NI n n0 ); intros.
   rewrite e; clear e n.
   case (eq_dec_role r r0); intros.
   rewrite e; clear e r.
   case ( InA_dec  Fact_as_DT.eq_dec (inst n1 c) l); intros.
   left; exists n1; auto.
   right.
intuition.
apply not_and_or.
intro.
inversion H.
inversion H0.
rewrite H3 in *; clear H3.
tauto.
right ; intro; left . intro.
inversion H ; auto.
right ; intro; left . intro.
inversion H ; auto.
right ; intro; left ; discriminate .
Qed.


Lemma dec_exists :  forall  AB c  r n  ,
(  { y|   (  In (rel n  y  r) AB /\  ~   In (inst  y  c) AB )}+
   (forall y ,~ (   In (rel n  y  r) AB /\  ~  In  (inst  y  c) AB) )  ).
Proof.
intros.
induction    (dec_exists_list (  elements AB ) c r n).
left;inversion_clear a; exists x.
repeat rewrite (factFact.elements_iff AB); auto.
right ; intro; repeat rewrite (factFact.elements_iff AB); auto.
Qed.

Lemma dec_exists_some :  forall  AB c  r n  ,
(  { y|   (  In (rel n  y  r) AB /\    In (inst  y  c) AB )}+
   (forall y ,~ (   In (rel n  y  r) AB /\    In  (inst  y  c) AB) )  ).
Proof.
intros.
induction    (dec_exists_list2 (  elements AB ) c r n).
left;inversion_clear a; exists x.
repeat rewrite (factFact.elements_iff AB); auto.
right ; intro; repeat rewrite (factFact.elements_iff AB); auto.
Qed.

Definition is_simp_inv (T U:Set) (f:T->U)  (y:U) := ({x: T | f x = y } + {forall x, f x <> y })%type.

Lemma is_simpl_inv_rel :forall n r y, is_simp_inv NI fact (fun x => rel n x r)  y.
Proof.
intros.
unfold is_simp_inv.
induction y.
right; intro ;intro ; inversion_clear H.
induction (eq_dec_NI n n0).
induction (eq_dec_role r r0).
left ; exists n1; rewrite a , a0; clear a a0 ; auto.
right ; intro ; intro; inversion H ; auto.
right ; intro ; intro; inversion H ; auto.
right ; intro ; intro; inversion H ; auto.
Qed.

Lemma is_simpl_inv_inst :forall  c  y, is_simp_inv NI fact (fun x => inst x c)  y.
Proof.
intros.
unfold is_simp_inv.
induction y.
induction (eq_dec_concept  c c0).
left; exists n ; rewrite a ; clear a ; auto.
right; intro ;intro ; inversion H; auto.
right ; intro ; intro; inversion H ; auto.
right ; intro ; intro; inversion H ; auto.
Qed.
Lemma dec_in_all: forall f,
   (forall y, is_simp_inv NI fact f  y)
     -> forall l, {x: NI | InA  Fact_as_DT.eq  (f x) l } + {forall x, ~(InA  Fact_as_DT.eq  (f x)  l )}.
Proof.
   induction l; intros.
   right; intros.
   unfold not; intro.
   inversion_clear H0.
   case (H a); intros.
   inversion_clear s.
   left; exists x; auto.
   inversion_clear IHl.
   inversion_clear H0.
     left; exists x.
   auto with *.
      right.
 intros.
   unfold not; intro.
   inversion_clear H1.
   elim (n x). auto.
   apply (H0 x) .
eauto with *.
Qed.



Lemma exist_or_not_inst_list : forall  c  l,  {    x|   InA  Fact_as_DT.eq  (inst  x c  ) l}+  {  forall x , ~ InA  Fact_as_DT.eq (inst  x  c) l }  .
Proof.
 intro.
apply     (dec_in_all _  (is_simpl_inv_inst  c)).  
Qed.

Lemma exist_or_not_role_list : forall  n r  l,  {    x|   InA  Fact_as_DT.eq  (rel  n x r  ) l}+  {  forall x , ~ InA  Fact_as_DT.eq (rel n  x  r) l }  .
Proof.
 intro ; intro.
apply     (dec_in_all _  (is_simpl_inv_rel n r)).  
Qed.

Lemma dec_exist_inst : forall  c  AB,  {    x|    In  (inst  x c  ) AB}+  {  forall x , ~   In (inst  x  c) AB }  .
Proof.
intros.
induction    (exist_or_not_inst_list  c (  elements AB ) ).
left;inversion_clear a; exists x.
repeat rewrite (factFact.elements_iff AB); auto.
right ; intro; repeat rewrite (factFact.elements_iff AB); auto.
Qed.

Lemma dec_exist_role  : forall  n r  AB,  {    x|    In  (rel n  x  r) AB}+  {  forall x , ~  In (rel n  x  r) AB }  .
Proof.
intros.
induction    (exist_or_not_role_list  n r (  elements AB ) ).
left;inversion_clear a; exists x.
repeat rewrite (factFact.elements_iff AB); auto.
right ; intro; repeat rewrite (factFact.elements_iff AB); auto.
Qed.

(******************************************)
Inductive and_applicable  (f:fact ) (AB : Abox)  :Prop :=
App_and :forall x c1 c2 ,
 (inst x  (AndC c1 c2) = f)  /\    In  f  AB /\ ~ (  In  (inst x c1) AB  /\    In (inst x c2 ) AB ) ->
and_applicable  f AB.


Lemma and_applicable_or_not : forall f AB, {and_applicable  f AB} + {~ and_applicable  f AB}.
Proof.
induction f.
induction c; intros.
right ;intuition; inversion_clear H ; inversion_clear H0; inversion H.
right ;intuition; inversion_clear H ; inversion_clear H0; inversion H.
right ;intuition; inversion_clear H ; inversion_clear H0; inversion H.
right ;intuition; inversion_clear H ; inversion_clear H0; inversion H.
clear IHc1 IHc2.
Export fsetsfact.
case (In_dec (inst n (AndC c1 c2)) AB); intros.
case (In_dec (inst n  c1 ) AB); intros.
case (In_dec (inst n  c2 ) AB); intros.
right ;intro; inversion_clear H ; inversion_clear H0; inversion_clear  H1.
apply H2; inversion_clear H; auto.
left ; apply  (App_and _ _ n c1 c2); tauto.
left; apply  (App_and _ _ n c1 c2); tauto.
right; intro; inversion_clear H ; inversion_clear H0; inversion_clear H1; tauto.
right ;intuition; inversion_clear H ; inversion_clear H0; inversion H.
right ;intuition; inversion_clear H ; inversion_clear H0; inversion H.
right ;intuition; inversion_clear H ; inversion_clear H0; inversion H.
right ;intuition; inversion_clear H ; inversion_clear H0; inversion H.
right ;intuition; inversion_clear H ; inversion_clear H0; inversion H.
Qed.

(********************************************)
Inductive or_applicable   (f:fact )(AB : Abox)  :Prop :=
App_or :forall x c1 c2 ,
 (inst x  (OrC c1 c2) = f)  /\  In  f  AB /\ ~   In  (inst x c1) AB  /\ ~   In (inst x c2 ) AB ->
or_applicable  f AB.

Lemma or_applicable_or_not : forall f AB, {or_applicable  f AB} + {~ or_applicable  f AB}.
induction f.
induction c; intros.
right;intro; inversion_clear H; inversion_clear H0; inversion_clear H.
right ; intro; inversion_clear H; inversion_clear H0; inversion_clear H.
right;intro; inversion_clear H; inversion_clear H0; inversion_clear H.
right ; intro; inversion_clear H; inversion_clear H0; inversion_clear H.
right;intro; inversion_clear H; inversion_clear H0; inversion_clear H.
clear IHc1;clear IHc2.
case (In_dec (inst n (OrC c1 c2)) AB); intros.
case (In_dec (inst n  c1 ) AB); intros.
right; intro; inversion_clear H.
inversion_clear H0.
inversion_clear H1.
inversion_clear H2.
inversion  H.
rewrite H4 , H5 in *.
auto.
case (In_dec (inst n  c2 ) AB); intros.
right; intro; inversion_clear H ; inversion_clear H0 ; inversion_clear H1; inversion_clear H2.
inversion H.
rewrite H4 , H6 in *.
auto.
left; apply (App_or ( inst n (OrC c1 c2)) AB n c1 c2 ) ; tauto.
right; intro; inversion_clear H; inversion_clear H0; inversion_clear H1; auto.
right ; intro; inversion_clear H; inversion_clear H0; inversion_clear H.
right;intro; inversion_clear H; inversion_clear H0; inversion_clear H.
right ; intro; inversion_clear H; inversion_clear H0; inversion_clear H.
right ; intro; inversion_clear H; inversion_clear H0; inversion_clear H.
Qed.

(**************************************)
Inductive some_applicable  f  (AB : Abox)  :Prop :=
App_some :forall x  r c1  ,   f= (inst x  (SomeC  r c1 )) /\    In  f AB  /\   
(forall y, ~ (  In  (rel x y r)  AB /\    In  (inst y c1 ) AB )) ->
some_applicable  f  AB.

Lemma some_applicable_or_not : forall  f AB , {some_applicable  f AB} + {~ some_applicable  f AB}.
Proof.
intros.
induction f.
destruct  c.
right;intro; inversion_clear H; inversion_clear H0; inversion_clear H.
right ; intro; inversion_clear H; inversion_clear H0; inversion_clear H.
right;intro; inversion_clear H; inversion_clear H0; inversion_clear H.
right ; intro; inversion_clear H; inversion_clear H0; inversion_clear H.
right;intro; inversion_clear H; inversion_clear H0; inversion_clear H.
right ; intro; inversion_clear H; inversion_clear H0; inversion_clear H.
right;intro; inversion_clear H; inversion_clear H0; inversion_clear H.

case (In_dec (inst n (SomeC r c)) AB); intros.
case (dec_exists_some  AB c  r n); intros.
inversion  s.
right.
intro.
inversion_clear H0.
inversion_clear H1.
inversion_clear H2.
generalize( H3 x); intros.
inversion  H0.

rewrite  H5, H6 , H7 in *.
auto.
left.

apply ( App_some (inst n (SomeC r c)) AB n r c  ).
tauto.
right; intro; inversion_clear H ; inversion_clear H0 ;
inversion_clear H1; auto.

right ; intro; inversion_clear H; inversion_clear H0; inversion_clear H.
right;intro; inversion_clear H; inversion_clear H0; inversion_clear H.
Qed.

(**************************************)
Inductive some_applicable_2  f  (AB : Abox)  :Prop :=
App_some_2 :forall x  r c1  ,   f= (inst x  (SomeC  r c1 )) /\      
(forall y, ~ (  In  (rel x y r)  AB /\    In  (inst y c1 ) AB )) ->
some_applicable_2  f  AB.

Lemma some_applicable_or_not_2 : forall  f AB , {some_applicable_2  f AB} + {~ some_applicable_2  f AB}.
Proof.
intros.
induction f.
destruct  c.
right;intro; inversion_clear H; inversion_clear H0; inversion_clear H.
right ; intro; inversion_clear H; inversion_clear H0; inversion_clear H.
right;intro; inversion_clear H; inversion_clear H0; inversion_clear H.
right ; intro; inversion_clear H; inversion_clear H0; inversion_clear H.
right;intro; inversion_clear H; inversion_clear H0; inversion_clear H.
right ; intro; inversion_clear H; inversion_clear H0; inversion_clear H.
right;intro; inversion_clear H; inversion_clear H0; inversion_clear H.
(*case (In_dec (inst n (SomeC r c)) AB); intros.*)
case (dec_exists_some  AB c  r n); intros.
inversion  s.
right.
intro.
inversion_clear H0.
inversion_clear H1.
(*inversion_clear H2.*)
generalize( H2 x); intros.
inversion  H0.
rewrite  H5, H6 , H4 in *.
auto.
left.
apply ( App_some_2 (inst n (SomeC r c)) AB n r c  ).
tauto.
right ; intro; inversion_clear H; inversion_clear H0; inversion_clear H.
right;intro; inversion_clear H; inversion_clear H0; inversion_clear H.
Qed.



(***********************************************************)


Inductive all_applicable    (f:fact ) (AB : Abox)  :Prop :=
App_all  :forall x  r c1 y,  f=  (inst x  (AllC  r c1 )) /\     In   f  AB /\   In (rel x y r) AB  /\ ~   In  (inst y c1 ) AB ->
all_applicable  f  AB.

Lemma all_applicable_or_not : forall f AB, {all_applicable  f AB} + {~ all_applicable  f AB}.
Proof.

induction f.
induction   c ; intros.
right;intro; inversion_clear H; inversion_clear H0; inversion_clear H.
right ; intro; inversion_clear H; inversion_clear H0; inversion_clear H.
right;intro; inversion_clear H; inversion_clear H0; inversion_clear H.
right ; intro; inversion_clear H; inversion_clear H0; inversion_clear H.
right ; intro; inversion_clear H; inversion_clear H0; inversion_clear H.
right;intro; inversion_clear H; inversion_clear H0; inversion_clear H.
clear  IHc.
case (In_dec (inst n (AllC r c)) AB); intros.
case (dec_exists  AB c  r n); intros.
inversion_clear s.
left.
apply (App_all (inst n (AllC r c)) AB n r c x).
tauto.
right.
intro.
inversion_clear H.
inversion_clear H0.
inversion_clear H1.
inversion H.
rewrite H3  , H4 ,   H5 in * ; clear H3 H4 H5.
generalize (n0 y).
tauto.
right.
intro.
inversion_clear H.
inversion_clear H0.
inversion_clear H1.
inversion_clear H.
tauto.
right;intro; inversion_clear H; inversion_clear H0; inversion_clear H.
right ; intro; inversion_clear H; inversion_clear H0; inversion_clear H.
right;intro; inversion_clear H; inversion_clear H0; inversion_clear H.
Qed.


 Definition rule_applicable  f AB := and_applicable  f AB \/ or_applicable  f AB \/ 
                      all_applicable  f AB \/ some_applicable  f AB.

Hint  Resolve   all_applicable_or_not or_applicable_or_not and_applicable_or_not
 some_applicable_or_not.

Lemma rule_applicable_or_not : forall f AB, {rule_applicable  f AB}+{~rule_applicable  f AB}.
Proof.
unfold rule_applicable.
intros.
case (and_applicable_or_not  f AB); intros.

left ; tauto.

case (or_applicable_or_not f AB); intros .

left; auto.
case (all_applicable_or_not f AB); intros.

left; tauto.
case  (some_applicable_or_not  f AB ); intros.
auto.

right.
tauto.
Qed.

(***********************************************************)
(*********************************************************)
Lemma andrule_andapplicable : forall b1 b2  , Andrule b1 b2 -> exists f, and_applicable f b1.
Proof.
intros.
inversion_clear H.
inversion_clear H0.
exists (inst x (AndC c1 c2)).
apply   (App_and  (inst x (AndC c1 c2)) b1 x c1 c2).
tauto.
Qed.

(***************************)
Lemma somerule_someapplicable : forall  b1 b2   , Somerule b1 b2 -> exists f, some_applicable f b1.
intros.
inversion_clear H.
inversion_clear H0.
exists (inst x (SomeC r c1)).
apply   (App_some (inst x (SomeC r c1)) b1 x  r c1).
intuition.
Qed.
