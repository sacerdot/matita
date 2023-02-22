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



include "ordered_group.ma".

record vlattice (R : togroup) : Type ≝ {
  wl_carr:> Type;
  value: wl_carr → R;
  join: wl_carr → wl_carr → wl_carr;
  meet: wl_carr → wl_carr → wl_carr;
  meet_refl: ∀x. value (meet x x) ≈ value x;
  join_refl: ∀x. value (join x x) ≈ value x;
  meet_comm: ∀x,y. value (meet x y) ≈ value (meet y x);
  join_comm: ∀x,y. value (join x y) ≈ value (join y x);
  join_assoc: ∀x,y,z. value (join x (join y z)) ≈ value (join (join x y) z);
  meet_assoc: ∀x,y,z. value (meet x (meet y z)) ≈ value (meet (meet x y) z);   
  meet_wins1: ∀x,y. value (join x (meet x y)) ≈ value x;
  meet_wins2: ∀x,y. value (meet x (join x y)) ≈ value x;
  modular_mjp: ∀x,y. value (join x y) + value (meet x y) ≈ value x + value y;
  join_meet_le: ∀x,y,z.  value (join x (meet y z)) ≤ value (join x y);
  meet_join_le: ∀x,y,z.  value (meet x y) ≤ value (meet x (join y z)) 
}. 

interpretation "valued lattice meet" 'and a b = (meet ? ? a b).

interpretation "valued lattice join" 'or a b = (join ? ? a b).
 
notation < "\nbsp \mu a" non associative with precedence 80 for @{ 'value2 $a}.
interpretation "lattice value" 'value2 a = (value ? ? a).

notation "\mu" non associative with precedence 80 for @{ 'value }.
interpretation "lattice value" 'value = (value ? ?).

lemma feq_joinr: ∀R.∀L:vlattice R.∀x,y,z:L. 
  μ x ≈ μ y → μ (z ∧ x) ≈ μ (z ∧ y) → μ (z ∨ x) ≈ μ (z ∨ y).
intros (R L x y z H H1);
apply (plus_cancr ??? (μ(z∧x)));
apply (Eq≈ (μz + μx) (modular_mjp ????));
apply (Eq≈ (μz + μy) H); clear H;
apply (Eq≈ (μ(z∨y) + μ(z∧y)) (modular_mjp ??z y));
apply (plus_cancl ??? (- μ (z ∨ y)));
apply (Eq≈ ? (plus_assoc ????));
apply (Eq≈ (0+ μ(z∧y)) (opp_inverse ??));
apply (Eq≈ ? (zero_neutral ??));
apply (Eq≈ (- μ(z∨y)+ μ(z∨y)+ μ(z∧x)) ? (plus_assoc ????));
apply (Eq≈ (0+ μ(z∧x)) ? (opp_inverse ??)); 
apply (Eq≈ (μ (z ∧ x)) H1 (zero_neutral ??));
qed.

lemma modularj: ∀R.∀L:vlattice R.∀y,z:L. μ(y∨z) ≈ μy + μz + -μ (y ∧ z).
intros (R L y z);
lapply (modular_mjp ?? y z) as H1;
apply (plus_cancr ??? (μ(y ∧ z)));
apply (Eq≈ ? H1); clear H1;
apply (Eq≈ ?? (plus_assoc ????));   
apply (Eq≈ (μy+ μz + 0) ? (opp_inverse ??));   
apply (Eq≈ ?? (plus_comm ???));
apply (Eq≈ (μy + μz) ? (eq_sym ??? (zero_neutral ??)));
apply eq_reflexive.
qed.

lemma modularm: ∀R.∀L:vlattice R.∀y,z:L. μ(y∧z) ≈ μy + μz + -μ (y ∨ z).
(* CSC: questa è la causa per cui la hint per cercare i duplicati ci sta 1 mese *)
(* exact modularj; *)
intros (R L y z);
lapply (modular_mjp ?? y z) as H1;
apply (plus_cancl ??? (μ(y ∨ z)));
apply (Eq≈ ? H1); clear H1;
apply (Eq≈ ?? (plus_comm ???));
apply (Eq≈ ?? (plus_assoc ????));    
apply (Eq≈ (μy+ μz + 0) ? (opp_inverse ??));   
apply (Eq≈ ?? (plus_comm ???));
apply (Eq≈ (μy + μz) ? (eq_sym ??? (zero_neutral ??)));
apply eq_reflexive.
qed.

lemma modularmj: ∀R.∀L:vlattice R.∀x,y,z:L.μ(x∧(y∨z))≈(μx + μ(y ∨ z) + - μ(x∨(y∨z))).
intros (R L x y z);
lapply (modular_mjp ?? x (y ∨ z)) as H1;
apply (Eq≈ (μ(x∨(y∨z))+ μ(x∧(y∨z)) +-μ(x∨(y∨z))) ? (feq_plusr ???? H1)); clear H1;
apply (Eq≈ ? ? (plus_comm ???));
apply (Eq≈ (- μ(x∨(y∨z))+ μ(x∨(y∨z))+ μ(x∧(y∨z))) ? (plus_assoc ????));
apply (Eq≈ (0+μ(x∧(y∨z))) ? (opp_inverse ??));
apply (Eq≈ (μ(x∧(y∨z))) ? (zero_neutral ??));
apply eq_reflexive.
qed.

lemma modularjm: ∀R.∀L:vlattice R.∀x,y,z:L.μ(x∨(y∧z))≈(μx + μ(y ∧ z) + - μ(x∧(y∧z))).
intros (R L x y z);
lapply (modular_mjp ?? x (y ∧ z)) as H1;
apply (Eq≈ (μ(x∧(y∧z))+ μ(x∨(y∧z)) +-μ(x∧(y∧z)))); [2: apply feq_plusr; apply (eq_trans ???? (plus_comm ???)); apply H1] clear H1;
apply (Eq≈ ? ? (plus_comm ???));
apply (Eq≈ (- μ(x∧(y∧z))+ μ(x∧(y∧z))+ μ(x∨y∧z)) ? (plus_assoc ????));
apply (Eq≈ (0+ μ(x∨y∧z)) ? (opp_inverse ??));
apply eq_sym; apply zero_neutral;
qed.

lemma step1_3_57': ∀R.∀L:vlattice R.∀x,y,z:L.
  μ(x ∨ (y ∧ z)) ≈ (μ x) + (μ y) + μ z + -μ (y ∨ z) + -μ (z ∧ (x ∧ y)).
intros (R L x y z);
apply (Eq≈ ? (modularjm ?? x y z));
apply (Eq≈ ( μx+ (μy+ μz+- μ(y∨z)) +- μ(x∧(y∧z)))); [
  apply feq_plusr; apply feq_plusl; apply (modularm ?? y z);]
apply (Eq≈ (μx+ μy+ μz+- μ(y∨z)+- μ(x∧(y∧z)))); [2:
  apply feq_plusl; apply feq_opp;
  apply (Eq≈ ? (meet_assoc ?????));
  apply (Eq≈ ? (meet_comm ????));
  apply eq_reflexive;]
apply feq_plusr; apply (Eq≈ ? (plus_assoc ????));
apply feq_plusr; apply plus_assoc;
qed.

lemma step1_3_57: ∀R.∀L:vlattice R.∀x,y,z:L.
  μ(x ∧ (y ∨ z)) ≈ (μ x) + (μ y) + μ z + -μ (y ∧ z) + -μ (z ∨ (x ∨ y)).
intros (R L x y z);
apply (Eq≈ ? (modularmj ?? x y z));
apply (Eq≈ ( μx+ (μy+ μz+- μ(y∧z)) +- μ(x∨(y∨z)))); [
  apply feq_plusr; apply feq_plusl; apply (modularj ?? y z);]
apply (Eq≈ (μx+ μy+ μz+- μ(y∧z)+- μ(x∨(y∨z)))); [2:
  apply feq_plusl; apply feq_opp;
  apply (Eq≈ ? (join_assoc ?????));
  apply (Eq≈ ? (join_comm ????));
  apply eq_reflexive;]
apply feq_plusr; apply (Eq≈ ? (plus_assoc ????));
apply feq_plusr; apply plus_assoc;
qed.

(* LEMMA 3.57 *) 

lemma join_meet_le_join: ∀R.∀L:vlattice R.∀x,y,z:L.μ (x ∨ (y ∧ z)) ≤ μ (x ∨ z). 
intros (R L x y z);
apply (le_rewl ??? ? (eq_sym ??? (step1_3_57' ?????)));
apply (le_rewl ??? (μx+ μy+ μz+- μ(y∨z)+ -μ(z∧x∧y))); [
  apply feq_plusl; apply feq_opp; apply (eq_trans ?? ? ?? (eq_sym ??? (meet_assoc ?????))); apply eq_reflexive;]
apply (le_rewl ??? (μx+ μy+ μz+- μ(y∨z)+ (- ( μ(z∧x)+ μy+- μ((z∧x)∨y))))); [
  apply feq_plusl; apply feq_opp; apply eq_sym; apply modularm]
apply (le_rewl ??? (μx+ μy+ μz+- μ(y∨z)+ (- μ(z∧x)+ -μy+-- μ((z∧x)∨y)))); [
  apply feq_plusl; apply (Eq≈ (- (μ(z∧x)+ μy) + -- μ((z∧x)∨y))); [
    apply feq_plusr; apply eq_sym; apply eq_opp_plus_plus_opp_opp;]
  apply eq_sym; apply eq_opp_plus_plus_opp_opp;]
apply (le_rewl ??? (μx+ μy+ μz+- μ(y∨z)+(- μ(z∧x)+- μy+ μ(y∨(z∧x))))); [
  repeat apply feq_plusl; apply eq_sym; apply (Eq≈ (μ((z∧x)∨y)) (eq_opp_opp_x_x ??));
  apply join_comm;]
apply (le_rewl ??? (μx+ μy+ μz+- μ(y∨z)+(- μ(z∧x)+- μy)+ μ(y∨(z∧x)))); [
  apply eq_sym; apply plus_assoc;]
apply (le_rewl ??? (μx+ μy+ μz+- μ(y∨z)+(- μy + - μ(z∧x))+ μ(y∨(z∧x)))); [
  repeat apply feq_plusr; repeat apply feq_plusl; apply plus_comm;]
apply (le_rewl ??? (μx+ μy+ μz+- μ(y∨z)+- μy + - μ(z∧x)+ μ(y∨(z∧x)))); [
  repeat apply feq_plusr; apply eq_sym; apply plus_assoc;]
apply (le_rewl ??? (μx+ μy+ μz+- μy + - μ(y∨z)+- μ(z∧x)+ μ(y∨(z∧x)))); [
  repeat apply feq_plusr; apply (eq_trans ?? ? ?? (plus_assoc ????));
  apply (Eq≈ ( μx+ μy+ μz+(- μy+- μ(y∨z))) (eq_sym ??? (plus_assoc ????)));
  apply feq_plusl; apply plus_comm;]
apply (le_rewl ??? (μx+ μy+ -μy+ μz + - μ(y∨z)+- μ(z∧x)+ μ(y∨(z∧x)))); [
  repeat apply feq_plusr; apply (eq_trans ?? ? ?? (plus_assoc ????));
  apply (Eq≈ (μx+ μy+( -μy+ μz)) (eq_sym ??? (plus_assoc ????)));
  apply feq_plusl; apply plus_comm;]
apply (le_rewl ??? (μx+ 0 + μz + - μ(y∨z)+- μ(z∧x)+ μ(y∨(z∧x)))); [
  repeat apply feq_plusr; apply (eq_trans ?? ? ?? (plus_assoc ????));
  apply feq_plusl; apply eq_sym; apply (eq_trans ?? ? ? (plus_comm ???));
  apply opp_inverse; apply eq_reflexive;] 
apply (le_rewl ??? (μx+ μz + - μ(y∨z)+- μ(z∧x)+ μ(y∨(z∧x)))); [
  repeat apply feq_plusr; apply (eq_trans ?? ? ?? (plus_comm ???));
  apply eq_sym; apply zero_neutral;]
apply (le_rewl ??? (μz+ μx + - μ(y∨z)+- μ(z∧x)+ μ(y∨(z∧x)))); [
  repeat apply feq_plusr; apply plus_comm;]
apply (le_rewl ??? (μz+ μx +- μ(z∧x)+ - μ(y∨z)+ μ(y∨(z∧x)))); [
  repeat apply feq_plusr; apply (eq_trans ?? ? ?? (plus_assoc ????));
  apply (eq_trans ?? ? ? (eq_sym ??? (plus_assoc ????))); apply feq_plusl;
  apply plus_comm;]
apply (le_rewl ??? (μ(z∨x)+ - μ(y∨z)+ μ(y∨(z∧x)))); [
  repeat apply feq_plusr; apply modularj;]
apply (le_rewl ??? (μ(z∨x)+ (- μ(y∨z)+ μ(y∨(z∧x)))) (plus_assoc ????));
apply (le_rewr ??? (μ(x∨z) + 0)); [apply (eq_trans ?? ? ? (plus_comm ???)); apply zero_neutral]
apply (le_rewr ??? (μ(x∨z) + (-μ(y∨z) + μ(y∨z)))); [ apply feq_plusl; apply opp_inverse]
apply (le_rewr ??? (μ(z∨x) + (-μ(y∨z) + μ(y∨z)))); [ apply feq_plusr; apply join_comm;]
repeat apply fle_plusl; apply join_meet_le;
qed.

lemma meet_le_meet_join: ∀R.∀L:vlattice R.∀x,y,z:L.μ (x ∧ z) ≤ μ (x ∧ (y ∨ z)). 
intros (R L x y z);
apply (le_rewr ??? ? (eq_sym ??? (step1_3_57 ?????)));
apply (le_rewr ??? (μx+ μy+ μz+- μ(y∧z)+ -μ(z∨x∨y))); [
  apply feq_plusl; apply feq_opp; apply (eq_trans ?? ? ?? (eq_sym ??? (join_assoc ?????))); apply eq_reflexive;]
apply (le_rewr ??? (μx+ μy+ μz+- μ(y∧z)+ (- ( μ(z∨x)+ μy+- μ((z∨x)∧y))))); [
  apply feq_plusl; apply feq_opp; apply eq_sym; apply modularj]
apply (le_rewr ??? (μx+ μy+ μz+- μ(y∧z)+ (- μ(z∨x)+ -μy+-- μ((z∨x)∧y)))); [
  apply feq_plusl; apply (Eq≈ (- (μ(z∨x)+ μy) + -- μ((z∨x)∧y))); [
    apply feq_plusr; apply eq_sym; apply eq_opp_plus_plus_opp_opp;]
  apply eq_sym; apply eq_opp_plus_plus_opp_opp;]
apply (le_rewr ??? (μx+ μy+ μz+- μ(y∧z)+(- μ(z∨x)+- μy+ μ(y∧(z∨x))))); [
  repeat apply feq_plusl; apply eq_sym; apply (Eq≈ (μ((z∨x)∧y)) (eq_opp_opp_x_x ??));
  apply meet_comm;]
apply (le_rewr ??? (μx+ μy+ μz+- μ(y∧z)+(- μ(z∨x)+- μy)+ μ(y∧(z∨x)))); [
  apply eq_sym; apply plus_assoc;]
apply (le_rewr ??? (μx+ μy+ μz+- μ(y∧z)+(- μy + - μ(z∨x))+ μ(y∧(z∨x)))); [
  repeat apply feq_plusr; repeat apply feq_plusl; apply plus_comm;]
apply (le_rewr ??? (μx+ μy+ μz+- μ(y∧z)+- μy + - μ(z∨x)+ μ(y∧(z∨x)))); [
  repeat apply feq_plusr; apply eq_sym; apply plus_assoc;]
apply (le_rewr ??? (μx+ μy+ μz+- μy + - μ(y∧z)+- μ(z∨x)+ μ(y∧(z∨x)))); [
  repeat apply feq_plusr; apply (eq_trans ?? ? ?? (plus_assoc ????));
  apply (Eq≈ ( μx+ μy+ μz+(- μy+- μ(y∧z)))  (eq_sym ??? (plus_assoc ????)));
  apply feq_plusl; apply plus_comm;]
apply (le_rewr ??? (μx+ μy+ -μy+ μz + - μ(y∧z)+- μ(z∨x)+ μ(y∧(z∨x)))); [
  repeat apply feq_plusr; apply (Eq≈ ?? (plus_assoc ????));
  apply (Eq≈ (μx+ μy+( -μy+ μz)) (eq_sym ??? (plus_assoc ????)));
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
