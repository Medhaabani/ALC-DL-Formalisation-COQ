Require Export Normal_neg.
(*Require Export  Ensembles.*)


(*********************** TBox syntaxe ****************************)
Inductive termin_form :Set := 
inclu : concept -> concept -> termin_form   (*  [_ symbole *)
|eq : concept-> concept -> termin_form.      (* =*)

Definition is_formu_simp  F : Prop := match  F with
| inclu c1 c2 => exists x,  c1 = (AtomC x) 
|eq c1 c2 =>  exists x,c1 = ( AtomC x) 
end.


Definition Tbox := Ensemble termin_form.

Definition all_left_are_atomic (T : Tbox)   := forall Ax  , In termin_form T  Ax -> is_formu_simp Ax.



Definition termi_formu_satisfiabl i  Ax   : Prop := 
match Ax with
|inclu c1 c2  =>  Included (D i) (interpC i  c1) (interpC i  c2)
|eq c1 c2 => (interpC  i  c1) = (interpC i c2) 
end.

Definition is_model_Tbox  i T  : Prop :=
forall Ax , In termin_form  T  Ax ->  termi_formu_satisfiabl i Ax.

Definition tbox_consistent T  := 
                     exists i , 
                                is_model_Tbox i T.

Definition satisfiable_tbox (c: concept) (T: Tbox) : Prop :=    
                          exists  i, 
                                is_model_Tbox  i T
     ->   interpC i c <> Empty_set (D i).

Definition unsatisfiable_tbox c T := ~ satisfiable_tbox c T.












