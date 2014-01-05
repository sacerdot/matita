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

include "basic_2/substitution/cpys_lift.ma".
include "basic_2/substitution/lleq.ma".

(* LAZY EQUIVALENCE FOR LOCAL ENVIRONMENTS **********************************)

(* Advanced properties ******************************************************)

lemma lleq_skip: ∀L1,L2,d,i. i < d → |L1| = |L2| → L1 ⋕[#i, d] L2.
#L1 #L2 #d #i #Hid #HL12 @conj // -HL12
#U @conj #H elim (cpys_inv_lref1 … H) -H // *
#I #Z #Y #X #H elim (ylt_yle_false … H) -H
/2 width=1 by ylt_inj/
qed.

lemma lleq_lref: ∀I1,I2,L1,L2,K1,K2,V,d,i. d ≤ i →
                 ⇩[0, i] L1 ≡ K1.ⓑ{I1}V → ⇩[0, i] L2 ≡ K2.ⓑ{I2}V →
                 K1 ⋕[V, 0] K2 → L1 ⋕[#i, d] L2.
#I1 #I2 #L1 #L2 #K1 #K2 #V #d #i #Hdi #HLK1 #HLK2 * #HK12 #IH @conj [ -IH | -HK12 ]
[ lapply (ldrop_fwd_length … HLK1) -HLK1 #H1
  lapply (ldrop_fwd_length … HLK2) -HLK2 #H2
  >H1 >H2 -H1 -H2 normalize //
| #U @conj #H elim (cpys_inv_lref1 … H) -H // *
  #I #K #X #W #_ #_ #H #HVW #HWU
  [ lapply (ldrop_mono … H … HLK1) | lapply (ldrop_mono … H … HLK2) ] -H
  #H destruct elim (IH W) /3 width=7 by cpys_subst, yle_inj/
]
qed.

lemma lleq_free: ∀L1,L2,d,i. |L1| ≤ i → |L2| ≤ i → |L1| = |L2| → L1 ⋕[#i, d] L2.
#L1 #L2 #d #i #HL1 #HL2 #HL12 @conj // -HL12
#U @conj #H elim (cpys_inv_lref1 … H) -H // *
#I #Z #Y #X #_ #_ #H lapply (ldrop_fwd_length_lt2 … H) -H
#H elim (lt_refl_false i) /2 width=3 by lt_to_le_to_lt/
qed.
