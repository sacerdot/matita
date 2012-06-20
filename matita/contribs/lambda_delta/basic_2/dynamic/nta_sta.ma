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

include "basic_2/static/sta.ma".
include "basic_2/equivalence/cpcs_cpcs.ma".
include "basic_2/dynamic/nta.ma".

(* NATIVE TYPE ASSIGNMENT ON TERMS ******************************************)

(* Properties on static type assignment *************************************)

lemma nta_fwd_sta: ∀h,L,T,U. ⦃h, L⦄ ⊢ T : U →
                   ∃∃U0. ⦃h, L⦄ ⊢ T • U0 & L ⊢ U0 ⬌* U.
#h #L #T #U #H elim H -L -T -U
[ /2 width=3/
| #L #K #V #W1 #V1 #i #HLK #_ #HWV1 * #W0 #HVW0 #HW01
  elim (lift_total W0 0 (i+1)) #V0 #HWV0
  lapply (ldrop_fwd_ldrop2 … HLK) #HLK0
  lapply (cpcs_lift … HLK0 … HWV0 … HWV1 HW01) -HLK0 -HWV1 -HW01 /3 width=6/
| #L #K #W #V1 #W1 #i #HLK #HWV1 #HW1 * /3 width=6/
| #I #L #V #W #T #U #_ #_ * #W0 #_ #_ * /3 width=3/
| #L #V #W #T #U #_ #_ * #W0 #_ #HW0 * #X #H #HX
  elim (sta_inv_bind1 … H) -H #U0 #HTU0 #H destruct
  @(ex2_1_intro … (ⓐV.ⓛW.U0)) /2 width=1/ /3 width=1/
| #L #V #W #T #U #_ #_ * #U0 #HTU0 #HU0 #_ -W
  @(ex2_1_intro … (ⓐV.U0)) /2 width=1/
| #L #T #U #HTU * #U0 #HTU0 #HU0 /3 width=3/
| #L #T #U1 #U2 #V2 #_ #HU12 #_ * #U0 #HTU0 #HU01 #_
  lapply (cpcs_trans … HU01 … HU12) -U1 /2 width=3/
]
qed-.
