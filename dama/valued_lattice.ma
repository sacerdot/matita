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
  modular_mjp: ∀x,y. value (join x y) + value (meet x y) ≈ value x + value y;
  join_meet_le: ∀x,y,z.  value (join x y) ≤ value (join x (meet y z));
  meet_join_le: ∀x,y,z.  value (meet x y) ≤ value (meet x (join y z)) 
}. 

interpretation "valued lattice meet" 'and a b =
 (cic:/matita/valued_lattice/meet.con _ _ a b).

interpretation "valued lattice join" 'or a b =
 (cic:/matita/valued_lattice/join.con _ _ a b).
 
notation < "\nbsp \mu a" non associative with precedence 80 for @{ 'value2 $a}.
interpretation "lattice value" 'value2 a = (cic:/matita/valued_lattice/value.con _ _ a).

notation "\mu" non associative with precedence 80 for @{ 'value }.
interpretation "lattice value" 'value = (cic:/matita/valued_lattice/value.con _ _).

lemma feq_joinr: ∀R.∀L:vlattice R.∀x,y,z:L. 
  μ x ≈ μ y → μ (z ∧ x) ≈ μ (z ∧ y) → μ (z ∨ x) ≈ μ (z ∨ y).
intros (R L x y z H H1);
apply (plus_cancr ??? (μ(z∧x)));
apply (eq_trans ?? (μz + μx) ? (modular_mjp ????));
apply (eq_trans ?? (μz + μy) ? H); clear H;
apply (eq_trans ?? (μ(z∨y) + μ(z∧y))); [1: apply eq_sym; apply modular_mjp]
apply (plus_cancl ??? (- μ (z ∨ y)));
apply (eq_trans ?? ? ? (plus_assoc ????));
apply (eq_trans ?? (0+ μ(z∧y)) ? (opp_inverse ??));
apply (eq_trans ?? ? ? (zero_neutral ??));
apply (eq_trans ?? (- μ(z∨y)+ μ(z∨y)+ μ(z∧x)) ?? (plus_assoc ????));
apply (eq_trans ?? (0+ μ(z∧x)) ?? (opp_inverse ??)); 
apply (eq_trans ?? (μ (z ∧ x)) ?H1 (zero_neutral ??));
qed.

lemma modularj: ∀R.∀L:vlattice R.∀y,z:L. μ(y∨z) ≈ μy + μz + -μ (y ∧ z).
intros (R L y z);
lapply (modular_mjp ?? y z) as H1;
apply (plus_cancr ??? (μ(y ∧ z)));
apply (eq_trans ?? ? ? H1); clear H1;
apply (eq_trans ?? ? ?? (plus_assoc ????));   
apply (eq_trans ?? (μy+ μz + 0)); [2: apply feq_plusl; apply eq_sym; apply opp_inverse]   
apply (eq_trans ?? ? ?? (plus_comm ???));
apply (eq_trans ?? (μy + μz) ?? (eq_sym ??? (zero_neutral ??)));
apply eq_reflexive.
qed.

lemma modularm: ∀R.∀L:vlattice R.∀y,z:L. μ(y∧z) ≈ μy + μz + -μ (y ∨ z).
intros (R L y z);
lapply (modular_mjp ?? y z) as H1;
apply (plus_cancl ??? (μ(y ∨ z)));
apply (eq_trans ?? ? ? H1); clear H1;
apply (eq_trans ????? (plus_comm ???));
apply (eq_trans ?? ? ?? (plus_assoc ????));   
apply (eq_trans ?? (μy+ μz + 0)); [2: apply feq_plusl; apply eq_sym; apply opp_inverse]   
apply (eq_trans ?? ? ?? (plus_comm ???));
apply (eq_trans ?? (μy + μz) ?? (eq_sym ??? (zero_neutral ??)));
apply eq_reflexive.
qed.

lemma modularmj: ∀R.∀L:vlattice R.∀x,y,z:L.μ(x∧(y∨z))≈(μx + μ(y ∨ z) + - μ(x∨(y∨z))).
intros (R L x y z);
lapply (modular_mjp ?? x (y ∨ z)) as H1;
apply (eq_trans ?? (μ(x∨(y∨z))+ μ(x∧(y∨z)) +-μ(x∨(y∨z))) ?? H1); clear H1;
apply (eq_trans ?? ? ?? (plus_comm ???));
(* apply (eq_trans ?? (0+μ(x∧(y∧z))) ?? (opp_inverse ??)); ASSERT FALSE *)
apply (eq_trans ?? (- μ(x∨(y∨z))+ μ(x∨(y∨z))+ μ(x∧(y∨z)))); [2: apply eq_sym; apply plus_assoc;]
apply (eq_trans ?? (0+μ(x∧(y∨z)))); [2: apply feq_plusr; apply eq_sym; apply opp_inverse;]
(* apply (eq_trans ?? ? ? (eq_refl ??) (zero_neutral ??)); ASSERT FALSE *)
apply (eq_trans ?? (μ(x∧(y∨z)))); [apply eq_reflexive]
apply eq_sym; apply zero_neutral.
qed.

lemma step1_3_57: ∀R.∀L:vlattice R.∀x,y,z:L.
  μ(x ∧ (y ∨ z)) ≈ (μ x) + (μ y) + μ z + -μ (y ∧ z) + -μ (z ∨ (x ∨ y)).
intros (R L x y z);
apply (eq_trans ?? ? ? (modularmj ?? x y z));
apply (eq_trans ?? ( μx+ (μy+ μz+- μ(y∧z)) +- μ(x∨(y∨z))) ?); [
  apply feq_plusr; apply feq_plusl; apply (modularj ?? y z);]
apply (eq_trans ?? (μx+ μy+ μz+- μ(y∧z)+- μ(x∨(y∨z)))); [2:
  apply feq_plusl; apply feq_opp;
  apply (eq_trans ?? ? ? (join_assoc ?????));
  apply (eq_trans ?? ? ? (join_comm ????));
  apply eq_reflexive;]
apply feq_plusr; apply (eq_trans ?? ? ? (plus_assoc ????));
apply feq_plusr; apply plus_assoc;
qed.

lemma meet_join_le1: ∀R.∀L:vlattice R.∀x,y,z:L.μ (x ∧ z) ≤ μ (x ∧ (y ∨ z)). 
intros (R L x y z);
apply (le_rewr ??? ? (eq_sym ??? (step1_3_57 ?????)));
apply (le_rewr ??? (μx+ μy+ μz+- μ(y∧z)+ -μ(z∨x∨y))); [
  apply feq_plusl; apply feq_opp; apply (eq_trans ?? ? ?? (eq_sym ??? (join_assoc ?????))); apply eq_reflexive;]
apply (le_rewr ??? (μx+ μy+ μz+- μ(y∧z)+ (- ( μ(z∨x)+ μy+- μ((z∨x)∧y))))); [
  apply feq_plusl; apply feq_opp; apply eq_sym; apply modularj]
apply (le_rewr ??? (μx+ μy+ μz+- μ(y∧z)+ (- μ(z∨x)+ -μy+-- μ((z∨x)∧y)))); [
  apply feq_plusl; apply (eq_trans ?? (- (μ(z∨x)+ μy) + -- μ((z∨x)∧y))); [
    apply feq_plusr; apply eq_sym; apply eq_opp_plus_plus_opp_opp;]
  apply eq_sym; apply eq_opp_plus_plus_opp_opp;]
apply (le_rewr ??? (μx+ μy+ μz+- μ(y∧z)+(- μ(z∨x)+- μy+ μ(y∧(z∨x))))); [
  repeat apply feq_plusl; apply eq_sym; apply (eq_trans ?? (μ((z∨x)∧y)) ? (eq_opp_opp_x_x ??));
  apply meet_comm;]
apply (le_rewr ??? (μx+ μy+ μz+- μ(y∧z)+(- μ(z∨x)+- μy)+ μ(y∧(z∨x)))); [
  apply eq_sym; apply plus_assoc;]
apply (le_rewr ??? (μx+ μy+ μz+- μ(y∧z)+(- μy + - μ(z∨x))+ μ(y∧(z∨x)))); [
  repeat apply feq_plusr; repeat apply feq_plusl; apply plus_comm;]
apply (le_rewr ??? (μx+ μy+ μz+- μ(y∧z)+- μy + - μ(z∨x)+ μ(y∧(z∨x)))); [
  repeat apply feq_plusr; apply eq_sym; apply plus_assoc;]
apply (le_rewr ??? (μx+ μy+ μz+- μy + - μ(y∧z)+- μ(z∨x)+ μ(y∧(z∨x)))); [
  repeat apply feq_plusr; apply (eq_trans ?? ? ?? (plus_assoc ????));
  apply (eq_trans ?? ( μx+ μy+ μz+(- μy+- μ(y∧z))) ? (eq_sym ??? (plus_assoc ????)));
  apply feq_plusl; apply plus_comm;]
apply (le_rewr ??? (μx+ μy+ -μy+ μz + - μ(y∧z)+- μ(z∨x)+ μ(y∧(z∨x)))); [
  repeat apply feq_plusr; apply (eq_trans ?? ? ?? (plus_assoc ????));
  apply (eq_trans ?? (μx+ μy+( -μy+ μz)) ? (eq_sym ??? (plus_assoc ????)));
  apply feq_plusl; apply plus_comm;]
apply (le_rewr ??? (μx+ 0 + μz + - μ(y∧z)+- μ(z∨x)+ μ(y∧(z∨x)))); [
  repeat apply feq_plusr; apply (eq_trans ?? ? ?? (plus_assoc ????));
  apply feq_plusl; apply eq_sym; apply (eq_trans ?? ? ? (plus_comm ???));
  apply opp_inverse; apply eq_reflexive;] 
apply (le_rewr ??? (μx+ μz + - μ(y∧z)+- μ(z∨x)+ μ(y∧(z∨x)))); [
  repeat apply feq_plusr; apply (eq_trans ?? ? ?? (plus_comm ???));
  apply eq_sym; apply zero_neutral;]
apply (le_rewr ??? (μz+ μx + - μ(y∧z)+- μ(z∨x)+ μ(y∧(z∨x)))); [
  repeat apply feq_plusr; apply plus_comm;]
apply (le_rewr ??? (μz+ μx +- μ(z∨x)+ - μ(y∧z)+ μ(y∧(z∨x)))); [
  repeat apply feq_plusr; apply (eq_trans ?? ? ?? (plus_assoc ????));
  apply (eq_trans ?? ? ? (eq_sym ??? (plus_assoc ????))); apply feq_plusl;
  apply plus_comm;]
apply (le_rewr ??? (μ(z∧x)+ - μ(y∧z)+ μ(y∧(z∨x)))); [
  repeat apply feq_plusr; apply modularm;]
apply (le_rewr ??? (μ(z∧x)+ (- μ(y∧z)+ μ(y∧(z∨x)))) (plus_assoc ????));
apply (le_rewl ??? (μ(x∧z) + 0)); [apply (eq_trans ?? ? ? (plus_comm ???)); apply zero_neutral]
apply (le_rewl ??? (μ(x∧z) + (-μ(y∧z) + μ(y∧z)))); [ apply feq_plusl; apply opp_inverse]
apply (le_rewl ??? (μ(z∧x) + (-μ(y∧z) + μ(y∧z)))); [ apply feq_plusr; apply meet_comm;]
repeat apply fle_plusl; apply meet_join_le;
qed.
