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

include "basic_2/computation/csn_aaa.ma".
include "basic_2/equivalence/lcpcs_aaa.ma".
include "basic_2/dynamic/nta.ma".

(* NATIVE TYPE ASSIGNMENT ON TERMS ******************************************)

(* Forward lemmas on atomic arity assignment for terms **********************)

lemma nta_fwd_aaa: ∀h,L,T,U. ⦃h, L⦄ ⊢ T : U → ∃∃A. L ⊢ T ⁝ A & L ⊢ U ⁝ A.
#h #L #T #U #H elim H -L -T -U
[ /2 width=3/
| #L #K #V #W #U #i #HLK #_ #HWU * #B #HV #HW
  lapply (ldrop_fwd_ldrop2 … HLK) /3 width=9/
| #L #K #W #V #U #i #HLK #_ #HWU * #B #HW #_ -V
  lapply (ldrop_fwd_ldrop2 … HLK) /3 width=9/
| * #L #V #W #T #U #_ #_ * #B #HV #HW * #A #HT #HU
  [ /3 width=3/ | /3 width=5/ ]
| #L #V #W #T #U #_ #_ * #B #HV #HW * #X #H1 #H2
  elim (aaa_inv_abst … H1) -H1 #B1 #A1 #HW1 #HT #H destruct
  elim (aaa_inv_abst … H2) -H2 #B2 #A #_ #HU #H destruct
  lapply (aaa_mono … HW1 … HW) -HW1 #H destruct /4 width=5/
| #L #V #W #T #U #_ #_ * #X #HT #HUX * #A #H #_ -W
  elim (aaa_inv_appl … H) -H #B #HV #HUA
  lapply (aaa_mono … HUA … HUX) -HUX #H destruct /3 width=5/
| #L #T #U #_ * #A #HT #HU /3 width=3/
| #L #T #U1 #U2 #V2 #_ #HU12 #_ * #X #HT #HU1 * #A #HU2 #_
  lapply (aaa_cpcs_mono … HU12 … HU1 … HU2) -U1 #H destruct /2 width=3/
]
qed-.

(* Note: this is the stong normalization property *)
(* Basic_1: was only: ty3_sn3 *)
theorem nta_fwd_csn: ∀h,L,T,U. ⦃h, L⦄ ⊢ T : U → L ⊢ ⬇* T ∧ L ⊢ ⬇* U.
#h #L #T #U #H elim (nta_fwd_aaa … H) -H /3 width=2/
qed-. 
