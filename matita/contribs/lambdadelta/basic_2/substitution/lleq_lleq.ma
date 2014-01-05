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

include "basic_2/substitution/cpys_cpys.ma".
include "basic_2/substitution/lleq.ma".

(* Advanced forward lemmas **************************************************)

lemma lleq_fwd_lref: ∀L1,L2,d,i. L1 ⋕[#i, d] L2 →
                     ∨∨ |L1| ≤ i ∧ |L2| ≤ i
                      | i < d
                      | ∃∃I1,I2,K1,K2,V. ⇩[0, i] L1 ≡ K1.ⓑ{I1}V &
                                         ⇩[0, i] L2 ≡ K2.ⓑ{I2}V &
                                         K1 ⋕[V, 0] K2 & d ≤ i.
#L1 #L2 #d #i * #HL12 #IH elim (lt_or_ge i (|L1|)) /3 width=3 by or3_intro0, conj/
elim (lt_or_ge i d) /2 width=1 by or3_intro1/ #Hdi #Hi
elim (ldrop_O1_lt … Hi) #I1 #K1 #V1 #HLK1
elim (ldrop_O1_lt L2 i) // -Hi #I2 #K2 #V2 #HLK2
lapply (ldrop_fwd_length_minus2 … HLK2) #H
lapply (ldrop_fwd_length_minus2 … HLK1) >HL12 <H -HL12 -H
#H lapply (injective_plus_l … H) -H #HK12
elim (lift_total V1 0 (i+1)) #W1 #HVW1
elim (lift_total V2 0 (i+1)) #W2 #HVW2
elim (IH W1) elim (IH W2) #_ #H2 #H1 #_
elim (cpys_inv_lref1_ldrop … (H1 ?) … HLK2 … HVW1) -H1
[ elim (cpys_inv_lref1_ldrop … (H2 ?) … HLK1 … HVW2) -H2 ]
/3 width=7 by cpys_subst, yle_inj/ -W1 -W2 #H12 #_ #_ #H21 #_ #_
lapply (cpys_antisym_eq … H12 … H21) -H12 -H21 #H destruct
@or3_intro2 @(ex4_5_intro … HLK1 HLK2) // @conj // -HK12
#V elim (lift_total V 0 (i+1))
#W #HVW elim (IH W) -IH #H12 #H21 @conj #H
[ elim (cpys_inv_lref1_ldrop … (H12 ?) … HLK2 … HVW) -H12 -H21
| elim (cpys_inv_lref1_ldrop … (H21 ?) … HLK1 … HVW) -H21 -H12
] /3 width=7 by cpys_subst, yle_inj/
qed-.
