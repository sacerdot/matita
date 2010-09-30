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



include "metric_space.ma".

record premetric_lattice_ (R : todgroup) : Type ≝ {
  pml_carr:> metric_space R;
  meet: pml_carr → pml_carr → pml_carr;
  join: pml_carr → pml_carr → pml_carr
}.

interpretation "valued lattice meet" 'and a b = (meet ? ? a b).

interpretation "valued lattice join" 'or a b = (join ? ? a b).
 
record premetric_lattice_props (R : todgroup) (ml : premetric_lattice_ R) : Prop ≝ {
  prop1a: ∀a : ml.δ (a ∧ a) a ≈ 0;
  prop1b: ∀a : ml.δ (a ∨ a) a ≈ 0;
  prop2a: ∀a,b: ml. δ (a ∨ b) (b ∨ a) ≈ 0;
  prop2b: ∀a,b: ml. δ (a ∧ b) (b ∧ a) ≈ 0;
  prop3a: ∀a,b,c: ml. δ (a ∨ (b ∨ c)) ((a ∨ b) ∨ c) ≈ 0;
  prop3b: ∀a,b,c: ml. δ (a ∧ (b ∧ c)) ((a ∧ b) ∧ c) ≈ 0;
  prop4a: ∀a,b: ml. δ (a ∨ (a ∧ b)) a ≈ 0;
  prop4b: ∀a,b: ml. δ (a ∧ (a ∨ b)) a ≈ 0;
  prop5: ∀a,b,c: ml. δ (a ∨ b) (a ∨ c) + δ (a ∧ b) (a ∧ c) ≤ δ b c
}.

record pmlattice (R : todgroup) : Type ≝ {
  carr :> premetric_lattice_ R;
  ispremetriclattice:> premetric_lattice_props R carr
}.
  
include "lattice.ma".

lemma lattice_of_pmlattice: ∀R: todgroup. pmlattice R → lattice.
intros (R pml); not ported to duality 
apply (mk_lattice (apart_of_metric_space ? pml));
[apply (join ? pml)|apply (meet ? pml)
|3,4,5,6,7,8,9,10: intros (x y z); whd; intro H; whd in H; cases H (LE AP);]
[apply (prop1b ? pml pml x);    |apply (prop1a ? pml pml x);
|apply (prop2a ? pml pml x y);  |apply (prop2b ? pml pml x y); 
|apply (prop3a ? pml pml x y z);|apply (prop3b ? pml pml x y z);
|apply (prop4a ? pml pml x y);  |apply (prop4b ? pml pml x y);]
try (apply ap_symmetric; assumption); intros 4 (x y z H); change with (0 < (δ y z));
[ change in H with (0 < δ (x ∨ y) (x ∨ z));
  apply (lt_le_transitive ???? H);  
  apply (le0plus_le ???? (mpositive ? pml ??) (prop5 ? pml pml x y z));
| change in H with (0 < δ (x ∧ y) (x ∧ z));
  apply (lt_le_transitive ???? H);  
  apply (le0plus_le ???? (mpositive ? pml (x∨y) (x∨z)));
  apply (le_rewl ??? ? (plus_comm ???));
  apply (prop5 ? pml pml);] 
qed.

coercion cic:/matita/premetric_lattice/lattice_of_pmlattice.con.
