Require Export  Relations.
Require Export Tableau_decidability.

(***************************************)
Definition clos_trans_succ   := clos_trans Abox succ  .  
Definition is_expansion A B  := clos_trans_succ  B A.  
(***************************************)

(* Lensemble des rxy dans l'abox telque y: c n'est pas dans l'abox *)
(* autrement dit le nombre des applicabilité visible de la règle all sur x: allc r c*)

(******************************la 1  specification **************************************)
Definition eq_role  r1 r2 := if eq_dec_role r1 r2 then true else false.
Definition  eq_ni  x y := if  NI_as_DT.eq_dec    x y   then  true else  false .

(*************************************************************************************)
(* l'enemble des y telque rx y dans l'abox abox -> setni *)

Definition construct_set_of_y_in_rel  x r  (f:fact) (A :Setni) : Setni :=  match f with 
 | rel x1 y  r1  => if ( eq_ni  x1   x  ) && (eq_role  r r1) then  fsetsni.add   y  A  else A 
 |  _ => A end.


Definition set_y_in_abox  x  r  (AB : Abox) : Setni := ( fold  (construct_set_of_y_in_rel  x r)   AB fsetsni.empty ).
(*************************************************)
(* set of y tel que y:c in abox *)
(*************************************************)
Definition construct_set_of_y_in_concept   c   (f:fact) (A :Setni) : Setni :=  match f with 
 | inst y c1 => if  (eq_dec_concept c c1) then fsetsni.add   y  A  else  A
 |  _ => A end.

Definition set_y_c_in_abox  c (AB : Abox) : Setni :=( fold  (construct_set_of_y_in_concept   c ) AB fsetsni.empty ).

Definition set_rel  x c r AB := fsetsni.cardinal (fsetsni.diff (set_y_in_abox  x  r  AB) (set_y_c_in_abox  c AB )).

(********************************************************************************************)
(*********************************************************)
(*    Nember of exist term in Abox *)
(*******************************************************)
Fixpoint  some_term  (x : NI) r c  :  Abox := 
match c with
 AtomC  _  => empty
|Top   =>   empty
|Bottom  => empty
|NotC  c1 =>  some_term  x r  c1 
|AndC  c1 c2 =>union( some_term  x r c1)  ( some_term  x r c2)
|OrC  c1 c2 => union (some_term x r c1) ( some_term  x  r c2)
 |AllC  _ c1 => some_term  x r  c1 
| SomeC  r1 c1 =>  if eq_role r r1 then add (inst x (SomeC  r1 c1) ) (some_term  x r  c1)   else some_term  x r  c1  end.

Definition set_some_in_fact  x  r  f  :=  match   f  with 
|  inst  y c => some_term  x  r c   
|_ =>  empty end .

Definition Constract_set_som    x r f   A  := union  (set_some_in_fact  x r  f )  A.
Definition set_of_some_term  x r  AB := fold  ( Constract_set_som x r ) AB empty.

(**************************************************************)
(* we need now to  defined the set of some terme in abox that not reduced yet it meanse that reductible in the abox *)

Definition some_terme_reductble  AB f  := match some_applicable_or_not_2  f AB with 
                                                                          | left _   => singleton f
                                                                          | right _ => empty   end.

Definition Constract_set_som_r  AB   f   A  := union  (  some_terme_reductble  AB  f )  A.
Definition set_of_some_term_r   x r  AB  :=  fold ( Constract_set_som_r  AB) (set_of_some_term  x r  AB) empty. 

(*******************************************)

Fixpoint sizeC  (c :concept) :  nat := match c with 
 AtomC  _  => 1
|Top   =>  1
|Bottom  => 1
|NotC  c1 =>  1+  (sizeC c1) 
|AndC  c1 c2 => 1 +  (sizeC c1) + sizeC c2
|OrC  c1 c2 => 1+  sizeC c1 + sizeC c2
|AllC r c1 => 1+  sizeC c1
|SomeC  r c1 => 1+ sizeC c1 end.

Definition sizef  f:= match f with 
|inst n c => sizeC c
|_ => 0 end .
(*************************************Definition de la Mesure *********************************)

Definition mes_comp   AB f   := match f with 
|inst x c => match c with 
                 | AndC c1 c2 => match and_applicable_or_not  f AB with 
                                        | left _   => (sizef  f, 0)
                                        | right _  => (0,0)
                                   end
                  |OrC c1 c2 => match or_applicable_or_not  f AB with 
                                        | left _   => (sizef  f, 0)
                                        | right _  => (0,0)
                                   end
                    |SomeC r c1 => match some_applicable_or_not  f AB with 
                                        | left _   => (sizef  f, 0)
                                        | right _  => (0,0)
                                   end
                     |AllC r c1 => (sizef  f, set_rel x c1 r AB +   cardinal (set_of_some_term_r   x  r AB ) ) 

                      | _ =>(0,0) 
                                        end
|_ => (0,0) end.

(******************************************************************)