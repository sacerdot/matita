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

include "basic_2/notation/relations/lrsubeqc_2.ma".
include "basic_2/syntax/lenv.ma".

(* RESTRICTED REFINEMENT FOR LOCAL ENVIRONMENTS *****************************)

inductive lsubr: relation lenv ≝
| lsubr_atom: ∀L. lsubr L (⋆)
| lsubr_pair: ∀I,L1,L2,V. lsubr L1 L2 → lsubr (L1.ⓑ{I}V) (L2.ⓑ{I}V)
| lsubr_beta: ∀L1,L2,V,W. lsubr L1 L2 → lsubr (L1.ⓓⓝW.V) (L2.ⓛW)
.

interpretation
  "restricted refinement (local environment)"
  'LRSubEqC L1 L2 = (lsubr L1 L2).

(* Basic properties *********************************************************)

lemma lsubr_refl: ∀L. L ⫃ L.
#L elim L -L /2 width=1 by lsubr_atom, lsubr_pair/
qed.

(* Basic inversion lemmas ***************************************************)

fact lsubr_inv_atom1_aux: ∀L1,L2. L1 ⫃ L2 → L1 = ⋆ → L2 = ⋆.
#L1 #L2 * -L1 -L2 //
[ #I #L1 #L2 #V #_ #H destruct
| #L1 #L2 #V #W #_ #H destruct
]
qed-.

lemma lsubr_inv_atom1: ∀L2. ⋆ ⫃ L2 → L2 = ⋆.
/2 width=3 by lsubr_inv_atom1_aux/ qed-.

fact lsubr_inv_abst1_aux: ∀L1,L2. L1 ⫃ L2 → ∀K1,W. L1 = K1.ⓛW →
                          L2 = ⋆ ∨ ∃∃K2. K1 ⫃ K2 & L2 = K2.ⓛW.
#L1 #L2 * -L1 -L2
[ #L #K1 #W #H destruct /2 width=1 by or_introl/
| #I #L1 #L2 #V #HL12 #K1 #W #H destruct /3 width=3 by ex2_intro, or_intror/
| #L1 #L2 #V1 #V2 #_ #K1 #W #H destruct
]
qed-.

lemma lsubr_inv_abst1: ∀K1,L2,W. K1.ⓛW ⫃ L2 →
                       L2 = ⋆ ∨ ∃∃K2. K1 ⫃ K2 & L2 = K2.ⓛW.
/2 width=3 by lsubr_inv_abst1_aux/ qed-.

fact lsubr_inv_pair2_aux: ∀L1,L2. L1 ⫃ L2 → ∀I,K2,W. L2 = K2.ⓑ{I}W →
                          (∃∃K1. K1 ⫃ K2 & L1 = K1.ⓑ{I}W) ∨
                          ∃∃K1,V. K1 ⫃ K2 & L1 = K1.ⓓⓝW.V & I = Abst.
#L1 #L2 * -L1 -L2
[ #L #J #K2 #W #H destruct
| #I #L1 #L2 #V #HL12 #J #K2 #W #H destruct /3 width=3 by ex2_intro, or_introl/
| #L1 #L2 #V1 #V2 #HL12 #J #K2 #W #H destruct /3 width=4 by ex3_2_intro, or_intror/
]
qed-.

lemma lsubr_inv_pair2: ∀I,L1,K2,W. L1 ⫃ K2.ⓑ{I}W →
                       (∃∃K1. K1 ⫃ K2 & L1 = K1.ⓑ{I}W) ∨
                       ∃∃K1,V1. K1 ⫃ K2 & L1 = K1.ⓓⓝW.V1 & I = Abst.
/2 width=3 by lsubr_inv_pair2_aux/ qed-.

(* Advanced inversion lemmas ************************************************)

lemma lsubr_inv_abbr2: ∀L1,K2,V. L1 ⫃ K2.ⓓV →
                       ∃∃K1. K1 ⫃ K2 & L1 = K1.ⓓV.
#L1 #K2 #V #H elim (lsubr_inv_pair2 … H) -H *
[ #K1 #HK12 #H destruct /2 width=3 by ex2_intro/
| #K1 #V1 #_ #_ #H destruct
]
qed-.

lemma lsubr_inv_abst2: ∀L1,K2,W. L1 ⫃ K2.ⓛW →
                       (∃∃K1. K1 ⫃ K2 & L1 = K1.ⓛW) ∨
                       ∃∃K1,V. K1 ⫃ K2 & L1 = K1.ⓓⓝW.V.
#L1 #K2 #W #H elim (lsubr_inv_pair2 … H) -H *
[ #K1 #HK12 #H destruct /3 width=3 by ex2_intro, or_introl/
| #K1 #V1 #HK12 #H #_ destruct /3 width=4 by ex2_2_intro, or_intror/
]
qed-.

(* Basic forward lemmas *****************************************************)

lemma lsubr_fwd_pair2: ∀I2,L1,K2,V2. L1 ⫃ K2.ⓑ{I2}V2 →
                       ∃∃I1,K1,V1. K1 ⫃ K2 & L1 = K1.ⓑ{I1}V1.
#I2 #L1 #K2 #V2 #H elim (lsubr_inv_pair2 … H) -H *
[ #K1 #HK12 #H destruct /3 width=5 by ex2_3_intro/
| #K1 #V1 #HK12 #H1 #H2 destruct /3 width=5 by ex2_3_intro/
]
qed-.
