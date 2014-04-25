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

include "basic_2/relocation/cpy_lift.ma".
include "basic_2/substitution/cpys.ma".
include "basic_2/reduction/lpx_ldrop.ma".

(* SN EXTENDED PARALLEL REDUCTION FOR LOCAL ENVIRONMENTS ********************)

(* Properties on context-sensitive extended substitution for terms **********)

lemma cpx_cpy_trans_lpx: ∀h,g,G,L1,T1,T. ⦃G, L1⦄ ⊢ T1 ➡[h, g] T →
                         ∀L2. ⦃G, L1⦄ ⊢ ➡[h, g] L2 →
                         ∀T2,d,e. ⦃G, L2⦄ ⊢ T ▶[d, e] T2 → ⦃G, L1⦄ ⊢ T1 ➡[h, g] T2.
#h #g #G #L1 #T1 #T #H elim H -G -L1 -T1 -T
[ #J #G #L1 #L2 #HL12 #T2 #d #e #H elim (cpy_inv_atom1 … H) -H //
  * #I #K2 #V2 #i #_ #_ #HLK2 #HVT2 #H destruct
  elim (lpx_ldrop_trans_O1 … HL12 … HLK2) -L2 #X #HLK1 #H
  elim (lpx_inv_pair2 … H) -H #K1 #V1 #_ #HV12 #H destruct
  /2 width=7 by cpx_delta/
| #G #L1 #k #l #Hkl #L2 #_ #X #d #e #H >(cpy_inv_sort1 … H) -X /2 width=2 by cpx_sort/
| #I #G #L1 #K1 #V1 #V #T #i #HLK1 #_ #HVT #IHV1 #L2 #HL12 #T2 #d #e #HT2
  elim (lpx_ldrop_conf … HLK1 … HL12) -HL12 #X #H #HLK2
  elim (lpx_inv_pair1 … H) -H #K2 #V0 #HK12 #_ #H destruct
  lapply (ldrop_fwd_drop2 … HLK2) -V0 #HLK2
  lapply (cpy_weak … HT2 0 (∞) ? ?) -HT2 // #HT2
  elim (cpy_inv_lift1_be … HT2 … HLK2 … HVT) -HT2 -HLK2 -HVT
  /3 width=7 by cpx_delta/
| #a #I #G #L1 #V1 #V #T1 #T #HV1 #_ #IHV1 #IHT1 #L2 #HL12 #X #d #e #H elim (cpy_inv_bind1 … H) -H
  #V2 #T2 #HV2 #HT2 #H destruct /4 width=5 by lpx_pair, cpx_bind/
| #I #G #L1 #V1 #V #T1 #T #_ #_ #IHV1 #IHT1 #L2 #HL12 #X #d #e #H elim (cpy_inv_flat1 … H) -H
  #V2 #T2 #HV2 #HT2 #H destruct /3 width=5 by cpx_flat/
| #G #L1 #V1 #U1 #U #T #_ #HTU #IHU1 #L2 #HL12 #T2 #d #e #HT2
  lapply (cpy_weak … HT2 0 (∞) ? ?) -HT2 // #HT2
  elim (lift_total T2 0 1) #U2 #HTU2
  lapply (cpy_lift_be … HT2 (L2.ⓓV1) … (Ⓕ) … HTU … HTU2 ? ?) -T
  /4 width=5 by cpx_zeta, lpx_pair, ldrop_drop/
| /3 width=5 by cpx_tau/
| /3 width=5 by cpx_ti/
| #a #G #L1 #V1 #V #W1 #W #T1 #T #HV1 #HW1 #_ #IHV1 #IHW1 #IHT1 #L2 #HL12 #X #d #e #HX
  elim (cpy_inv_bind1 … HX) -HX #Y #T2 #HY #HT2 #H destruct
  elim (cpy_inv_flat1 … HY) -HY #W2 #V2 #HW2 #HV2 #H destruct
  /5 width=11 by lpx_pair, cpx_beta, lsuby_cpy_trans, lsuby_succ/
| #a #G #L1 #V1 #V #U #W1 #W #T1 #T #_ #HVU #HW1 #_ #IHV1 #IHW1 #IHT1 #L2 #HL12 #X #d #e #HX
  elim (cpy_inv_bind1 … HX) -HX #W2 #Y #HW2 #HY #H destruct
  elim (cpy_inv_flat1 … HY) -HY #U2 #T2 #HU2 #HT2 #H destruct
  lapply (cpy_weak … HU2 0 (∞) ? ?) -HU2 // #HU2
  elim (cpy_inv_lift1_be … HU2 L2 … HVU) -U
  /4 width=7 by lpx_pair, cpx_theta, ldrop_drop/
]
qed-.

lemma cpx_cpys_trans_lpx: ∀h,g,G,L1,T1,T. ⦃G, L1⦄ ⊢ T1 ➡[h, g] T →
                          ∀L2. ⦃G, L1⦄ ⊢ ➡[h, g] L2 →
                          ∀T2,d,e. ⦃G, L2⦄ ⊢ T ▶*[d, e] T2 → ⦃G, L1⦄ ⊢ T1 ➡[h, g] T2.
#h #g #G #L1 #T1 #T #HT1 #L2 #HL12 #T2 #d #e #H @(cpys_ind … H) -T2
/2 width=7 by cpx_cpy_trans_lpx/
qed-.
