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

include "basic_2/dynamic/nta_lift.ma".

(* NATIVE TYPE ASSIGNMENT ON TERMS ******************************************)

(* Main properties **********************************************************)

(* Basic_1: was: ty3_unique *)
theorem nta_mono: ∀h,L,T,U1. ⦃h, L⦄ ⊢ T : U1 → ∀U2. ⦃h, L⦄ ⊢ T : U2 →
                  L ⊢ U1 ⬌* U2.
#h #L #T #U1 #H elim H -L -T -U1
[ #L #k #X #H
  lapply (nta_inv_sort1 … H) -H //
| #L #K #V #W11 #W12 #i #HLK #_ #HW112 #IHVW11 #X #H
  elim (nta_inv_lref1 … H) -H * #K0 #V0 #W21 #W22 #HLK0 #HVW21 #HW212 #HX
  lapply (ldrop_mono … HLK0 … HLK) -HLK0 #H destruct
  lapply (ldrop_fwd_ldrop2 … HLK) -HLK #HLK
  @(cpcs_trans … HX) -X /3 width=9 by cpcs_lift/ (**) (* to slow without trace *)
| #L #K #W #V1 #V #i #HLK #_ #HWV #_ #X #H
  elim (nta_inv_lref1 … H) -H * #K0 #W0 #V2 #V0 #HLK0 #_ #HWV0 #HX
  lapply (ldrop_mono … HLK0 … HLK) -HLK0 -HLK #H destruct
  lapply (lift_mono … HWV0 … HWV) -HWV0 -HWV #H destruct //
| #I #L #V #W1 #T #U1 #_ #_ #_ #IHTU1 #X #H
  elim (nta_inv_bind1 … H) -H #W2 #U2 #_ #HTU2 #H
  @(cpcs_trans … H) -X /3 width=1/
| #L #V #W1 #T #U1 #_ #_ #_ #IHTU1 #X #H
  elim (nta_fwd_pure1 … H) -H #U2 #W2 #_ #HTU2 #H
  @(cpcs_trans … H) -X /3 width=1/
| #L #V #W1 #T #U1 #_ #_ #IHTU1 #_ #X #H
  elim (nta_fwd_pure1 … H) -H #U2 #W2 #_ #HTU2 #H
  @(cpcs_trans … H) -X /3 width=1/
| #L #T #U1 #_ #_ #X #H
  elim (nta_inv_cast1 … H) -H //
| #L #T #U11 #U12 #V12 #_ #HU112 #_ #IHTU11 #_ #U2 #HTU2
  @(cpcs_canc_sn … HU112) -U12 /2 width=1/
]
qed-.

(* Advanced properties ******************************************************)

lemma nta_cast_alt: ∀h,L,T,W,U. ⦃h, L⦄ ⊢ T : W → ⦃h, L⦄ ⊢ T : U →
             ⦃h, L⦄ ⊢ ⓝW.T : U.
#h #L #T #W #U #HTW #HTU
lapply (nta_mono … HTW … HTU) #HWU
elim (nta_fwd_correct … HTU) -HTU /3 width=3/
qed.
