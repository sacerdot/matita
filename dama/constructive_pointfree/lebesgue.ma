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

record measured_set (R : real) : Type ≝ {
  ms_carr :> Type;
  ms_measure: ms_carr → ms_carr → R
}.

notation "\delta" non associative with precedence 90 for @{ 'delta }.
interpretation "measure" 'delta = (cic:/matita/lebesgue/ms_measure.con _ _).

record pre_measured_lattice (R : real) : Type ≝ {
  ml_lattice :> lattice;
  ml_measured_set_ : measured_set R;
  with_ml_lattice_eq_ml_measured_set_: ms_carr ? ml_measured_set_ = ml_lattice
}.

lemma ml_measured_set : ∀R.∀ms:pre_measured_lattice R. measured_set R.
intros (R ml); constructor 1; [1:apply (ml : Type);] cases ml; 
rewrite < H; clear H; cases ml_measured_set_; simplify; exact f;
qed.  

coercion cic:/matita/lebesgue/ml_measured_set.con.

record is_measured_lattice (R : real) (ml : pre_measured_lattice R) : Prop ≝ {
  prop1a: ∀a : ml.δ (a ∧ a) a = 0;
  prop1b: ∀a : ml.δ (a ∨ a) a = 0;
  prop2a: ∀a,b: ml. δ (a ∨ b) (b ∨ a) = 0;
  prop2b: ∀a,b: ml. δ (a ∧ b) (b ∧ a) = 0;
  prop3a: ∀a,b,c: ml. δ (a ∨ (b ∨ c)) ((a ∨ b) ∨ c) = 0;
  prop3b: ∀a,b,c: ml. δ (a ∧ (b ∧ c)) ((a ∧ b) ∧ c) = 0;
  prop4a: ∀a,b: ml. δ (a ∨ (a ∧ b)) a = 0;
  prop4b: ∀a,b: ml. δ (a ∧ (a ∨ b)) a = 0;
  prop5: ∀a,b,c: ml. δ (a ∨ b) (a ∨ c) + δ (a ∧ b) (a ∧ c) ≤ δ b c
}. 
  
record measured_lattice (R : real) : Type ≝ {
  ml_pre_measured_lattice:> pre_measured_lattice R;
  ml_measured_lattice_properties: is_measured_lattice R ml_pre_measured_lattice
}.
  
definition apart:= 
 λR: real. λml: measured_lattice R. λa,b: ml. 0 < δ a b.
 (* < scazzato, ma CSC dice che poi si cambia dopo  *)    

notation "a # b" non associative with precedence 50 for
 @{ 'apart $a $b}.
interpretation "measured lattice apartness" 'apart a b =
 (cic:/matita/lebesgue/apart.con _ _ a b). 
notation "a \approx b" non associative with precedence 50 for
 @{ 'napart $a $b}.
interpretation "measured lattice non apartness" 'napart a b =
 (cic:/matita/logic/connectives/Not.con
   (cic:/matita/lebesgue/apart.con _ _ a b)). 

lemma foo : ∀R: real. ∀ml: measured_lattice R.∀a,b,a1,b1: ml. 
  a ≈ a1 → b ≈ b1 → δ a b = δ a1 b1. 
     (* =R scazzato *)  
intros;
