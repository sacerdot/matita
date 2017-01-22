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

include "basic_2/substitution/cpye_lift.ma".
include "basic_2/substitution/lleq_alt.ma".

(* LAZY EQUIVALENCE FOR LOCAL ENVIRONMENTS **********************************)

(* Forward lemmas on evaluation for extended substitution *******************)

lemma lleq_fwd_cpye: ∀L1,L2,T,d. L1 ⋕[T, d] L2 → ∀G,T1. ⦃G, L1⦄ ⊢ T ▶*[d, ∞] 𝐍⦃T1⦄ →
                     ∀T2. ⦃G, L2⦄ ⊢ T ▶*[d, ∞] 𝐍⦃T2⦄ → T1 = T2.
#L1 #L2 #T #d #H @(lleq_ind_alt … H) -L1 -L2 -T -d
[ #L1 #L2 #d #k #_ #G #T1 #H1 #T2 #H2
  >(cpye_inv_sort1 … H1) -H1 >(cpye_inv_sort1 … H2) -H2 //
| #L1 #L2 #d #i #_ #Hid #G #T1 #H1 #T2 #H2
  >(cpye_inv_lref1_free … H1) -H1 [ >(cpye_inv_lref1_free … H2) -H2 ]
  /2 width=1 by or3_intro2/
| #I1 #I2 #L1 #L2 #K1 #K2 #V #d #i #Hdi #HLK1 #HLK2 #_ #IHV #G #T1 #H1 #T2 #H2
  elim (cpye_inv_lref1_subst_ex … H1 … HLK1) -H1 -HLK1 //
  elim (cpye_inv_lref1_subst_ex … H2 … HLK2) -H2 -HLK2 //
  >yminus_Y_inj #V2 #HV2 #HVT2 #V1 #HV1 #HVT1
  lapply (IHV … HV1 … HV2) -IHV -HV1 -HV2 #H destruct /2 width=5 by lift_mono/
| #L1 #L2 #d #i #_ #HL1 #HL2 #G #T1 #H1 #T2 #H2
  >(cpye_inv_lref1_free … H1) -H1 [ >(cpye_inv_lref1_free … H2) -H2 ]
  /2 width=1 by or3_intro0/
| #L1 #L2 #d #p #_ #G #T1 #H1 #T2 #H2
  >(cpye_inv_gref1 … H1) -H1 >(cpye_inv_gref1 … H2) -H2 //
| #a #I #L1 #L2 #V #T #d #_ #_ #IHV #IHT #G #X1 #H1 #X2 #H2
  elim (cpye_inv_bind1 … H1) -H1 #V1 #T1 #HV1 #HT1 #H destruct
  elim (cpye_inv_bind1 … H2) -H2 #V2 #T2 #HV2 #HT2 #H destruct
  /3 width=3 by eq_f2/
| #I #L1 #L2 #V #T #d #_ #_ #IHV #IHT #G #X1 #H1 #X2 #H2
  elim (cpye_inv_flat1 … H1) -H1 #V1 #T1 #HV1 #HT1 #H destruct
  elim (cpye_inv_flat1 … H2) -H2 #V2 #T2 #HV2 #HT2 #H destruct
  /3 width=3 by eq_f2/
]
qed-.
