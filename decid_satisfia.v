Require Export  Semantic.

Axiom  eq_dec_nc : forall c1 c2: NC, {c1 = c2} + {c1 <> c2}.
Axiom  eq_dec_nr : forall r1 r2: NR, {r1 = r2} + {r1 <> r2}.
Axiom  eq_dec_ni : forall x y: NI, {x = y} + {x <> y}.

Lemma eq_dec_nat:   forall n m: nat , {n = m} + {n <> m}.
Proof.
decide equality.
Qed.

Hint  Resolve eq_dec_nc eq_dec_ni eq_dec_nr eq_dec_nat.

(****************************************)
Lemma eq_dec_role:   forall r1 r2: role, {r1 = r2} + {r1 <> r2}.
Proof.
decide equality.
Qed.

Hint  Resolve eq_dec_role.

(***********************************************)
Lemma eq_dec_concept :  forall c1 c2: concept, {c1 = c2} + {c1 <> c2}.
Proof.
decide equality.
Qed.
(*************************** Correct proof but not needed for now *****************
Lemma or_false : forall p: Prop , p -> (p \/ False).
Proof.
tauto.
Qed.

Lemma or_false2 : forall p: Prop ,( p \/ False) <-> p.
Proof.
intuition.
Qed.
Hint  Resolve or_false.

Lemma first: forall p  : Prop, {p } +{~ p} -> {p \/ False  } +{~  (p \/ False) } .
Proof.
intuition.
Qed.
Lemma first1 : forall p  q: Prop, {p } +{~ p} -> {q } +{~ q}-> {p \/ q  } +{~  (p \/ q) } .
Proof.
intuition.
Qed.

Hint  Resolve first.

Ltac mimo := match goal with| |- ( { ?X1  \/ False} + {~ ( ?X1 \/ False)} ) => (apply  (first  X1 ) ) 
                                                  |  |-  ( { ?X1  \/ ?X2} + {~ ( ?X1 \/ ?X2 )} ) => (apply  (first1  X1 X2 ) )  
                                                  |  |-  ( { ?X1  } + {~ ( ?X1 )} ) =>  decide equality end.


Lemma occure_or_not :  forall c1 c2: concept, {occure_in c1 c2} + {~occure_in c1 c2 }.
Proof.
double induction c1 c2 ; intros ; simpl;  repeat  mimo;  auto.  
Qed.

***)







