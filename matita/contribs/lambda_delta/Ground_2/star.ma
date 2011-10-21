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
include "Ground_2/xoa_props.ma".

(* PROPERTIES of RELATIONS **************************************************)

definition confluent: ∀A. ∀R1,R2: relation A. Prop ≝ λA,R1,R2.
                      ∀a0,a1. R1 a0 a1 → ∀a2. R2 a0 a2 →
                      ∃∃a. R2 a1 a & R1 a2 a.

definition transitive: ∀A. ∀R1,R2: relation A. Prop ≝ λA,R1,R2.
                       ∀a1,a0. R1 a1 a0 → ∀a2. R2 a0 a2 →
                       ∃∃a. R2 a1 a & R1 a a2.

lemma TC_strip1: ∀A,R1,R2. confluent A R1 R2 →
                 ∀a0,a1. TC … R1 a0 a1 → ∀a2. R2 a0 a2 →
                 ∃∃a. R2 a1 a & TC … R1 a2 a.
#A #R1 #R2 #HR12 #a0 #a1 #H elim H -H a1
[ #a1 #Ha01 #a2 #Ha02
  elim (HR12 … Ha01 … Ha02) -HR12 a0 /3/
| #a #a1 #_ #Ha1 #IHa0 #a2 #Ha02
  elim (IHa0 … Ha02) -IHa0 Ha02 a0 #a0 #Ha0 #Ha20
  elim (HR12 … Ha1 … Ha0) -HR12 a /4/
]
qed.

lemma TC_strip2: ∀A,R1,R2. confluent A R1 R2 →
                 ∀a0,a2. TC … R2 a0 a2 → ∀a1. R1 a0 a1 →
                 ∃∃a. TC … R2 a1 a & R1 a2 a.
#A #R1 #R2 #HR12 #a0 #a2 #H elim H -H a2
[ #a2 #Ha02 #a1 #Ha01
  elim (HR12 … Ha01 … Ha02) -HR12 a0 /3/
| #a #a2 #_ #Ha2 #IHa0 #a1 #Ha01
  elim (IHa0 … Ha01) -IHa0 Ha01 a0 #a0 #Ha10 #Ha0
  elim (HR12 … Ha0 … Ha2) -HR12 a /4/
]
qed.

lemma TC_confluent: ∀A,R1,R2.
                    confluent A R1 R2 → confluent A (TC … R1) (TC … R2).
#A #R1 #R2 #HR12 #a0 #a1 #H elim H -H a1
[ #a1 #Ha01 #a2 #Ha02
  elim (TC_strip2 … HR12 … Ha02 … Ha01) -HR12 a0 /3/
| #a #a1 #_ #Ha1 #IHa0 #a2 #Ha02
  elim (IHa0 … Ha02) -IHa0 Ha02 a0 #a0 #Ha0 #Ha20
  elim (TC_strip2 … HR12 … Ha0 … Ha1) -HR12 a /4/
]
qed.

lemma TC_strap: ∀A. ∀R:relation A. ∀a1,a,a2.
                R a1 a → TC … R a a2 → TC … R a1 a2.
/3/ qed.

lemma TC_strap1: ∀A,R1,R2. transitive A R1 R2 →
                 ∀a1,a0. TC … R1 a1 a0 → ∀a2. R2 a0 a2 →
                 ∃∃a. R2 a1 a & TC … R1 a a2.
#A #R1 #R2 #HR12 #a1 #a0 #H elim H -H a0
[ #a0 #Ha10 #a2 #Ha02
  elim (HR12 … Ha10 … Ha02) -HR12 a0 /3/
| #a #a0 #_ #Ha0 #IHa #a2 #Ha02
  elim (HR12 … Ha0 … Ha02) -HR12 a0 #a0 #Ha0 #Ha02
  elim (IHa … Ha0) -a /4/
]
qed.

lemma TC_strap2: ∀A,R1,R2. transitive A R1 R2 →
                 ∀a0,a2. TC … R2 a0 a2 → ∀a1. R1 a1 a0 →
                 ∃∃a. TC … R2 a1 a & R1 a a2.
#A #R1 #R2 #HR12 #a0 #a2 #H elim H -H a2
[ #a2 #Ha02 #a1 #Ha10
  elim (HR12 … Ha10 … Ha02) -HR12 a0 /3/
| #a #a2 #_ #Ha02 #IHa #a1 #Ha10
  elim (IHa … Ha10) -a0 #a0 #Ha10 #Ha0
  elim (HR12 … Ha0 … Ha02) -HR12 a /4/
]
qed.

lemma TC_transitive: ∀A,R1,R2.
                     transitive A R1 R2 → transitive A (TC … R1) (TC … R2).
#A #R1 #R2 #HR12 #a1 #a0 #H elim H -a0
[ #a0 #Ha10 #a2 #Ha02
  elim (TC_strap2 … HR12 … Ha02 … Ha10) -HR12 a0 /3/
| #a #a0 #_ #Ha0 #IHa #a2 #Ha02
  elim (TC_strap2 … HR12 … Ha02 … Ha0) -HR12 a0 #a0 #Ha0 #Ha02
  elim (IHa … Ha0) -a /4/
]
qed.

lemma TC_reflexive: ∀A,R. reflexive A R → reflexive A (TC … R).
/2/ qed.

lemma TC_star_ind: ∀A,R. reflexive A R → ∀a1. ∀P:A→Prop.
                   P a1 → (∀a,a2. TC … R a1 a → R a a2 → P a → P a2) →
                   ∀a2. TC … R a1 a2 → P a2.
#A #R #H #a1 #P #Ha1 #IHa1 #a2 #Ha12 elim Ha12 -Ha12 a2 /3/
qed.