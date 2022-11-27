Require Export Normal_neg.

Inductive fact : Set :=
      inst : NI -> concept -> fact
     |  rel : NI -> NI -> role -> fact
     |  dif :NI-> NI-> fact.

Axiom  eq_dec_nc : forall c1 c2: NC, {c1 = c2} + {c1 <> c2}.
Axiom  eq_dec_nr : forall r1 r2: NR, {r1 = r2} + {r1 <> r2}.
Axiom  eq_dec_ni : forall x y: NI, {x = y} + {x <> y}.

Hint  Resolve eq_dec_nc eq_dec_ni eq_dec_nr .

(***********************************************************************************************)
(* Require Export FSets.*)
Require Export FSetInterface.


(*****************Fact as Decidable type  (equal is decidable)*****************************)
Module Fact_as_DT <: DecidableType.
  Definition t := fact.
  Definition eq := @eq t.
  Definition eq_refl := @refl_equal t.
  Definition eq_sym := @sym_eq t.
  Definition eq_trans := @trans_eq t.
  Lemma  eq_dec : forall x y : t,{ eq x y} + {~eq x y}.
  Proof.
  unfold eq.
  repeat decide equality .
  Qed.
End Fact_as_DT.

(*******************NI is too Decidable type (mybe need to be order type for generating new variable)**********************************)

Module NI_as_DT <: DecidableType.
  Definition t := NI.
  Definition eq := @eq t.
  Definition eq_refl := @refl_equal t.
  Definition eq_sym := @sym_eq t.
  Definition eq_trans := @trans_eq t.
  Lemma  eq_dec : forall x y : t,{ eq x y} + {~eq x y}.
  Proof.
  unfold eq.
  trivial.
 Qed.
End NI_as_DT.
(***********************************************************)
Declare Module Import  fsetsfact : WSfun Fact_as_DT.
Notation Abox := fsetsfact.t.

Declare Module fsetsni : WSfun NI_as_DT . 
Notation Setni := fsetsni.t.
(***************************************************************)
Definition construct_set_in_fact f  A   :=  match f with 
 | inst  ni c  =>  fsetsni.add   ni  A
 | rel  ni1 ni2 r =>fsetsni.add ni1( fsetsni.add  ni2 A)
 | dif  ni1 ni2  => fsetsni.add ni1 ( fsetsni.add  ni2  A)  end.

Definition set_ni_in_abox (AB : Abox) : Setni := ( fold construct_set_in_fact  AB fsetsni.empty ).
(****************************************************************)

Definition occur_ni_fact  y  Aa :Prop := match Aa with
          | inst ni1 c => y= ni1
          | rel  ni1 ni2 r => y = ni1 \/ y = ni2
          | dif  ni1 ni2  => y = ni1 \/ y = ni2
    end.


(*****************************************************************)
Definition fact_normal  f  := match f with
      |  inst x c => inst x (NNF c)
      |  _ => f
      end. 

Definition is_fact_normal  f   := match f with
      |  inst x c  => isNF c
      |  _ => True
      end. 


Definition  is_Normal_Abox ab : Prop   := forall f , In  f ab      ->  is_fact_normal f .

(************************************************************************)


Definition inter_satisfies_fact  i  Aa  := match Aa with 
	|inst ni c => Ensembles.In  (D i) (interpC i  c ) (interp_inst i ni)
	|rel  ni1 ni2 r  => (interpR (interp_r i) r (interp_inst i ni1) (interp_inst i ni2))
	|dif ni1 ni2  => interp_inst i ni1 <>interp_inst i ni2
end.


Definition  is_model_Abox  i  AB  : Prop :=
	forall  Aa :fact  , fsetsfact.In  Aa AB ->  inter_satisfies_fact  i Aa.

Definition abox_satisfiable  AB : Prop :=  exists i , 
                                is_model_Abox i AB.


(*************************not used************************************************************)
(******         Parameter Var_generate : Setni -> NI.*****************************************)
(***********Parameter Var_generate_spec : forall E,  fsetsni.In (Var_generate E) E.*********)

(**********used********************************************************************)
Parameter Var_fresh : forall ( L : Setni) ,{x : NI|~  fsetsni.In x L}.
(******************************************************************************)

Parameter x0 : NI.
Parameter C : concept.
Definition Abox_initial := singleton  (inst x0 C).


Hint Resolve eq_dec Fact_as_DT.eq_dec.







