(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

set "baseuri" "cic:/matita/valued_lattice/".

include "ordered_groups.ma".

record vlattice (R : ogroup) : Type ≝ {
  vl_carr:> Type;
  value: vl_carr → R;
  join: vl_carr → vl_carr → vl_carr;
  meet: vl_carr → vl_carr → vl_carr;
  meet_refl: ∀x. value (meet x x) ≈ value x;
  join_refl: ∀x. value (join x x) ≈ value x;
  meet_comm: ∀x,y. value (meet x y) ≈ value (meet y x);
  join_comm: ∀x,y. value (join x y) ≈ value (join y x);
  join_assoc: ∀x,y,z. value (join x (join y z)) ≈ value (join (join x y) z);
  meet_assoc: ∀x,y,z. value (meet x (meet y z)) ≈ value (meet (meet x y) z);   
  meet_wins1: ∀x,y. value (join x (meet x y)) ≈ value x;
  meet_wins2: ∀x,y. value (meet x (join x y)) ≈ value x;
  meet_join_plus: ∀x,y. value (join x y) + value (meet x y) ≈ value x + value y;
  join_meet_le: ∀x,y,z. value (join x (meet y z)) ≤ value (join x y);
  meet_join_le: ∀x,y,z. value (meet x (join y z)) ≤ value (meet x y)  
}. 

interpretation "valued lattice meet" 'and a b =
 (cic:/matita/valued_lattice/meet.con _ _ a b).

interpretation "valued lattice join" 'or a b =
 (cic:/matita/valued_lattice/join.con _ _ a b).
 
notation < "\nbsp \mu a" non associative with precedence 80 for @{ 'value2 $a}.
interpretation "lattice value" 'value2 a = (cic:/matita/valued_lattice/value.con _ _ a).

notation "\mu" non associative with precedence 80 for @{ 'value }.
interpretation "lattice value" 'value = (cic:/matita/valued_lattice/value.con _ _).

lemma foo: ∀R.∀L:vlattice R.∀x,y,z:L.
  μ(x ∧ (y ∨ z)) ≈ (μ x) + (μ y) + μ z + -μ (y ∧ z) + -μ (z ∨ (x ∨ y)).
intros (R L x y z);
lapply (meet_join_plus ? ? x (y ∨ z)) as H;
lapply (meet_join_plus ? ? y z) as H1;
 (*CSC: A questo punto ti servono dei lemmi sui gruppi che non sono ancora
   stati dimostrati. E una valanga di passi di riscrittura :-)
 *)


lemma meet_join_le1: ∀R.∀L:vlattice R.∀x,y,z:L.μ (x ∧ z) ≤ μ (x ∧ (y ∨ z)). 
intros (R L x y z);
apply (le_rewr ??? (μ x + μ y + μ z + -μ (y ∧ z) + -μ(z ∨ (x ∨ y))) (foo ?????));
apply (le_rewr ??? (μ x + μ y + μ z + -μ (y ∧ z) + -μ((z ∨ x) ∨ y))); 
  [ apply feq_plusl; apply eq_opp_sym; apply join_assoc;]
lapply (meet_join_le ?? z x y);
cut (- μ (z ∨ x ∨ y) ≈ - μ (z ∨ x) - μ y + μ (y ∧ (z ∨ x)));
 [2: 
 
 
lemma join_meet_le1: ∀R.∀L:vlattice R.∀x,y,z:L.μ (x ∨ (y ∧ z)) ≤ μ (x ∨ z).   
(* hint per duplicati? *)
intros (R L x y z);
apply (le_rewr ??? (0 + μ (x ∨ z)) (zero_neutral ??));
apply (le_rewr ??? (μ (x ∨ z) + 0) (plus_comm ???));
apply (le_rewr ??? (μ (x ∨ z) + (-μ(y ∨ z) + μ(y ∨ z))) (opp_inverse ? ?));



