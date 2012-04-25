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
include "basic_2/dynamic/nta_lift.ma".

(* NATIVE TYPE ASSIGNMENT ON TERMS ******************************************)

axiom pippo: ∀h,L,X,Y1,U. ⦃h, L⦄ ⊢ ⓐX.Y1 : U → ∀Y2. L ⊢ Y1 ⬌* Y2 →
             ∀U2. ⦃h, L⦄ ⊢ Y2 : U2 → ⦃h, L⦄ ⊢ ⓐX.Y2 : U.

(* Properties on static type assignment *************************************)

lemma nta_fwd_sta: ∀h,L,T,U. ⦃h, L⦄ ⊢ T : U →
                   ∃∃U0. ⦃h, L⦄ ⊢ T • U0 & L ⊢ U0 ⬌* U & ⦃h, L⦄ ⊢ T : U0.
#h #L #T #U #H elim H -L -T -U
[ /2 width=4/
| #L #K #V #W1 #V1 #i #HLK #_ #HWV1 * #W0 #H1VW0 #HW01 #H2VW0
  elim (lift_total W0 0 (i+1)) #V0 #HWV0
  lapply (ldrop_fwd_ldrop2 … HLK) #HLK0
  lapply (cpcs_lift … HLK0 … HWV0 … HWV1 HW01) -HLK0 -HWV1 -HW01 /3 width=9/
| #L #K #W #V1 #W1 #i #HLK #HWV1 #HW1 * /3 width=9/
| #I #L #V #W #T #U #_ #_ * #W0 #_ #_ #H2VW0 * /3 width=4/
| #L #V #W #T #U #_ #_ * #W0 #_ #HW0 #H2VW0 * #X #H1 #HX #H2
  elim (sta_inv_bind1 … H1) -H1 #U0 #HTU0 #H destruct
  elim (nta_inv_bind1 … H2) /4 width=4/
| #L #V #W #T #U #_ #_ * #U0 #H1TU0 #HU0 #H2TU0 * #W0 #_ #_ #H2UW0 -W
  elim (nta_fwd_correct … H2TU0) #T0 #HUT0
  @(ex3_1_intro … (ⓐV.U0)) /2 width=1/ -H1TU0
  @(nta_pure … W0 … H2TU0) -T /3 width=3/
| #L #T #U #HTU * #U0 #H1TU0 #HU0 #H2TU0
  elim (nta_fwd_correct … H2TU0) -H2TU0 /4 width=8/
| #L #T #U1 #U2 #V2 #_ #HU12 #_ * #U0 #H1TU0 #HU01 #H2TU0 #_
  lapply (cpcs_trans … HU01 … HU12) -U1 /2 width=4/
]
qed-.
