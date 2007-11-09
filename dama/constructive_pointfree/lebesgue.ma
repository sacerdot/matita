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

set "baseuri" "cic:/matita/lebesgue/".

include "reals.ma".
include "lattices.ma".

axiom ltT : ∀R:real.∀a,b:R.Type.  
  
   
alias symbol "or" = "constructive or".
definition rapart ≝ λR:real.λa,b:R.a < b ∨ b < a. 

notation "a # b" non associative with precedence 50 for
 @{ 'apart $a $b}.
notation "a \approx b" non associative with precedence 50 for
 @{ 'napart $a $b}.    
interpretation "real apartness" 'apart a b =
 (cic:/matita/lebesgue/rapart.con _ a b). 
interpretation "real non apartness" 'napart a b =
 (cic:/matita/constructive_connectives/Not.con
   (cic:/matita/lebesgue/rapart.con _ a b)). 

record is_semi_metric (R : real) (T : Type) (d : T → T → R): Prop ≝ {
 sm_positive: ∀a,b:T. d a b ≤ 0; 
 sm_reflexive: ∀a. d a a ≈ 0;
 sm_symmetric: ∀a,b. d a b ≈ d b a;
 sm_tri_ineq: ∀a,b,c:T. d a b ≤ d a c + d c b
}.

record semimetric_set (R : real) : Type ≝ {
  ms_carr :> Type;
  ms_semimetric: ms_carr → ms_carr → R;
  ms_properties:> is_semi_metric R ms_carr ms_semimetric
}.

notation < "\nbsp \delta a \nbsp b" non associative with precedence 80 for @{ 'delta2 $a $b}.
interpretation "semimetric" 'delta2 a b = (cic:/matita/lebesgue/ms_semimetric.con _ _ a b).
notation "\delta" non associative with precedence 80 for @{ 'delta }.
interpretation "semimetric" 'delta = (cic:/matita/lebesgue/ms_semimetric.con _ _).

record pre_semimetric_lattice (R : real) : Type ≝ {
  ml_lattice :> lattice;
  ml_semimetric_set_ : semimetric_set R;
  with_ml_lattice_eq_ml_semimetric_set_: ms_carr ? ml_semimetric_set_ = ml_lattice
}.

lemma ml_semimetric_set : ∀R.∀ms:pre_semimetric_lattice R. semimetric_set R.
intros (R ml); constructor 1; [apply (ml : Type);]
cases ml (l ms with_); clear ml; simplify;
[1: rewrite < with_; apply (ms_semimetric ? ms);  
|2: cases with_; simplify; apply (ms_properties ? ms);]
qed.

coercion cic:/matita/lebesgue/ml_semimetric_set.con.

record is_semimetric_lattice (R : real) (ml : pre_semimetric_lattice R) : Prop ≝ {
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
  
record semimetric_lattice (R : real) : Type ≝ {
  ml_pre_semimetric_lattice:> pre_semimetric_lattice R;
  ml_semimetric_lattice_properties: is_semimetric_lattice R ml_pre_semimetric_lattice
}.

definition apart:= 
 λR: real. λml: semimetric_lattice R. λa,b: ml. 
 (* 0 < δ a b *) ltT ? 0 (δ a b).
 (* < scazzato, ma CSC dice che poi si cambia dopo  *)    

interpretation "semimetric lattice apartness" 'apart a b =
 (cic:/matita/lebesgue/apart.con _ _ a b). 
interpretation "semimetric lattice non apartness" 'napart a b =
 (cic:/matita/constructive_connectives/Not.con
   (cic:/matita/lebesgue/apart.con _ _ a b)).
  

lemma triangular_inequality : ∀R: real. ∀ms: semimetric_set R.∀a,b,c:ms.
 δ a b ≤ δ a c + δ c b.
intros (R ms a b c); exact (sm_tri_ineq R ms (ms_semimetric R ms) ms a b c);
qed. 

lemma foo : ∀R: real. ∀ml: semimetric_lattice R.∀a,b,a1,b1: ml. 
  a ≈ a1 → b ≈ b1 → (δ a b ≈ δ a1 b1).  
intros;
lapply (triangular_inequality ? ? a b a1) as H1;
lapply (triangular_inequality ? ? a1 b b1) as H2;
lapply (og_ordered_abelian_group_properties R ? ? (δ a a1) H2) as H3;
