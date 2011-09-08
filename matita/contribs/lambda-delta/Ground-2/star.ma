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

include "basics/star.ma".
include "Ground-2/xoa_props.ma".

(* PROPERTIES of RELATIONS **************************************************)

definition confluent: ∀A. ∀R: relation A. Prop ≝ λA,R.
                      ∀a0,a1. R a0 a1 → ∀a2. R a0 a2 →
                      ∃∃a. R a1 a & R a2 a.

lemma TC_strip: ∀A,R. confluent A R →
                ∀a0,a1. TC … R a0 a1 → ∀a2. R a0 a2 →
                ∃∃a. R a1 a & TC … R a2 a.
#A #R #HR #a0 #a1 #H elim H -H a1
[ #a1 #Ha01 #a2 #Ha02
  elim (HR … Ha01 … Ha02) -HR a0 /3/
| #a #a1 #_ #Ha1 #IHa0 #a2 #Ha02
  elim (IHa0 … Ha02) -IHa0 Ha02 a0 #a0 #Ha0 #Ha20
  elim (HR … Ha1 … Ha0) -HR a /4/
]
qed.

lemma TC_confluent: ∀A,R. confluent A R → confluent A (TC … R).
#A #R #HR #a0 #a1 #H elim H -H a1
[ #a1 #Ha01 #a2 #Ha02
  elim (TC_strip … HR … Ha02 … Ha01) -HR a0 /3/
| #a #a1 #_ #Ha1 #IHa0 #a2 #Ha02
  elim (IHa0 … Ha02) -IHa0 Ha02 a0 #a0 #Ha0 #Ha20
  elim (TC_strip … HR … Ha0 … Ha1) -HR a /4/
]
qed.

lemma TC_reflexive: ∀A,R. reflexive A R → reflexive A (TC … R).
/2/ qed.

