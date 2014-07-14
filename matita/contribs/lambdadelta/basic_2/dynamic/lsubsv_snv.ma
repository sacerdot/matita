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

include "basic_2/computation/cpds_cpds.ma".
include "basic_2/dynamic/snv_aaa.ma".
include "basic_2/dynamic/lsubsv_cpds.ma".
include "basic_2/dynamic/lsubsv_cpcs.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR STRATIFIED NATIVE VALIDITY **************)

(* Properties concerning stratified native validity *************************)

lemma lsubsv_snv_trans: ∀h,g,G,L2,T. ⦃G, L2⦄ ⊢ T ¡[h, g] →
                        ∀L1. G ⊢ L1 ⫃¡[h, g] L2 → ⦃G, L1⦄ ⊢ T ¡[h, g].
#h #g #G #L2 #T #H elim H -G -L2 -T //
[ #I #G #L2 #K2 #V #i #HLK2 #_ #IHV #L1 #HL12
  elim (lsubsv_drop_O1_trans … HL12 … HLK2) -L2 #X #H #HLK1
  elim (lsubsv_inv_pair2 … H) -H * #K1
  [ #HK12 #H destruct /3 width=5 by snv_lref/
  | #W #l #H1V #H1W #HWV #_ #HWl #_ #_ #H1 #H2 destruct -IHV
    /3 width=10 by snv_scast, snv_lref/
  ]
| #a #I #G #L2 #V #T #_ #_ #IHV #IHT #L1 #HL12 destruct
  /4 width=1 by snv_bind, lsubsv_pair/
| #a #G #L2 #V #W #W0 #T #U #l #_ #_ #HVl #HVW #HW0 #HTU #IHV #IHT #L1 #HL12
  lapply (lsubsv_cprs_trans … HL12 … HW0) -HW0 #HW0
  elim (lsubsv_sta_trans … HVW … HVl … HL12) -HVW #W1 #HVW1 #HW1
  lapply (cpcs_cprs_strap1 … HW1 … HW0) -W #HW10
  lapply (lsubd_da_trans … HVl L1 ?) -HVl /2 width=1 by lsubsv_fwd_lsubd/ #HVl
  elim (lsubsv_cpds_trans … HTU … HL12) -HTU #X #HTU #H
  elim (cprs_inv_abst1 … H) -H #W #U2 #HW0 #_ #H destruct
  lapply (cpcs_cprs_strap1 … HW10 … HW0) -W0 #H
  elim (cpcs_inv_cprs … H) -H #W0 #HW10 #HW0
  /4 width=11 by snv_appl, cpds_cprs_trans, cprs_bind/
| #G #L2 #W #T #U #l #_ #_ #HTl #HTU #HUW #IHW #IHT #L1 #HL12
  lapply (lsubsv_cpcs_trans … HL12 … HUW) -HUW #HUW
  elim (lsubsv_sta_trans … HTU … HTl … HL12) -HTU #U0 #HTU0 #HU0
  lapply (lsubd_da_trans … HTl L1 ?) -HTl
  /4 width=5 by lsubsv_fwd_lsubd, snv_cast, cpcs_trans/
]
qed-.
