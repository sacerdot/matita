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

include "basic_2/dynamic/lsubsv_ldrop.ma".
(*
include "basic_2/dynamic/lsubsv_ssta.ma".
include "basic_2/dynamic/lsubsv_cpcs.ma".
*)
(* LOCAL ENVIRONMENT REFINEMENT FOR STRATIFIED NATIVE VALIDITY **************)

(* Properties concerning stratified native validity *************************)
(*
axiom lsubsv_xprs_trans: ∀h,g,L1,L2. h ⊢ L1 ⊩:⊑[g] L2 →
                         ∀T1,T2. ⦃h, L2⦄ ⊢ T1 •➡*[g] T2 → ⦃h, L1⦄ ⊢ T1 •➡*[g] T2.

/3 width=3 by lsubsv_fwd_lsubss, lsubss_xprs_trans/ qed-.
*)
axiom lsubsv_snv_trans: ∀h,g,L2,T. ⦃h, L2⦄ ⊩ T :[g] →
                        ∀L1. h ⊢ L1 ⊩:⊑[g] L2 → ⦃h, L1⦄ ⊩ T :[g].
(*
#h #g #L2 #T #H elim H -L2 -T //
[ #I2 #L2 #K2 #V2 #i #HLK2 #_ #IHV2 #L1 #HL12
  elim (lsubsv_ldrop_O1_trans … HL12 … HLK2) -L2 #X #H #HLK1
  elim (lsubsv_inv_pair2 … H) -H * #K1 [ | -IHV2 ]
  [ #HK12 #H destruct /3 width=5/
  | #V1 #l #HV1 #_ #_ #_ #H destruct /2 width=5/
  ]
| #a #I #L2 #V #T #_ #_ #IHV #IHT #L1 #HL12 /4 width=1/
| #a #L2 #V #W #W0 #T #U #l #_ #_ #HVW #HW0 #HTU #IHV #IHT #L1 #HL12
  lapply (IHV … HL12) -IHV #HV
  lapply (IHT … HL12) -IHT #HT
  lapply (lsubsv_ssta_trans … HVW … HL12) -HVW #HVW
  lapply (lsubsv_cprs_trans … HL12 … HW0) -HW0 #HW0
  lapply (lsubsv_xprs_trans … HL12 … HTU) -HL12 -HTU /2 width=8/
| #L2 #W #T #U #l #_ #_ #HTU #HWU #IHW #IHT #L1 #HL12
  lapply (IHW … HL12) -IHW #HW
  lapply (IHT … HL12) -IHT #HT
  lapply (lsubsv_ssta_trans … HTU … HL12) -HTU #HTU
  lapply (lsubsv_cpcs_trans … HL12 … HWU) -HL12 -HWU /2 width=4/
]
qed-.
*)
