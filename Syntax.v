Parameter  NC  NR : Set.  					(*NC  pour les noms des  concepts *)
		                                                     (*NR  pour les noms des  roles*)
(*********************************************************************)

Inductive  role : Set := 
AtomR : NR -> role.

(********************************************************************)

Inductive  concept : Set :=
AtomC : NC  -> concept
|Top   : concept
|Bottom : concept
|NotC : concept ->  concept
|AndC : concept -> concept  -> concept
|OrC : concept -> concept  -> concept
|AllC :role  -> concept  -> concept
|SomeC : role  ->  concept -> concept.


(********************************************)

Definition ImplyC  c1 c2 := OrC ( NotC c1) c2. 

Definition EquvC c1 c2 := AndC (ImplyC c1 c2) (ImplyC c2 c1).

 (***************************************************)

 Fixpoint occure_in (a b :concept) {struct b} : Prop:= 
 a=b \/ 
 match b with  |NotC c1 => occure_in a c1
 |AndC c1 c2 => (occure_in a c1) \/ (occure_in a c2)
 |OrC c1 c2 =>   (occure_in a c1) \/ (occure_in a c2)
 |AllC  r c => occure_in a c
 |SomeC r c => occure_in a c |_ => False
 end.
 
 Fixpoint occure_atom_in_concept   A ( b :concept) {struct b} : Prop := 
 match b with  | AtomC b => A  = b
 |Top => False
 |Bottom => False  
 |NotC c1 => occure_atom_in_concept  A c1
 |AndC c1 c2 => (occure_atom_in_concept A c1) \/ (occure_atom_in_concept A c2)
 |OrC c1 c2 =>   (occure_atom_in_concept A c1) \/ (occure_atom_in_concept A c2)
 |AllC  r c => occure_atom_in_concept A  c
 |SomeC r c => occure_atom_in_concept A  c end.
 