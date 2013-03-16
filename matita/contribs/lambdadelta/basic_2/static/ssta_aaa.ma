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

include "basic_2/static/aaa_lift.ma".
include "basic_2/static/ssta.ma".

(* STRATIFIED STATIC TYPE ASSIGNMENT ON TERMS *******************************)

(* Properties on atomic arity assignment for terms **************************)

lemma ssta_aaa: ∀h,g,L,T,A. L ⊢ T ⁝ A → ∀U,l. ⦃h, L⦄ ⊢ T •[g] ⦃l, U⦄ → L ⊢ U ⁝ A.
#h #g #L #T #A #H elim H -L -T -A
[ #L #k #U #l #H
  elim (ssta_inv_sort1 … H) -H #_ #H destruct //
| #I #L #K #V #B #i #HLK #HV #IHV #U #l #H
  elim (ssta_inv_lref1 … H) -H * #K0 #V0 #W0 [2: #l0 ] #HLK0 #HVW0 #HU [ #H ]
  lapply (ldrop_mono … HLK0 … HLK) -HLK0 #H0 destruct
  lapply (ldrop_fwd_ldrop2 … HLK) -HLK #HLK
  @(aaa_lift … HLK … HU) -HU -L // -HV /2 width=2/
| #a #L #V #T #B #A #HV #_ #_ #IHT #X #l #H
  elim (ssta_inv_bind1 … H) -H #U #HTU #H destruct /3 width=2/
| #a #L #V #T #B #A #HV #_ #_ #IHT #X #l #H
  elim (ssta_inv_bind1 … H) -H #U #HTU #H destruct /3 width=2/
| #L #V #T #B #A #HV #_ #_ #IHT #X #l #H
  elim (ssta_inv_appl1 … H) -H #U #HTU #H destruct /3 width=3/
| #L #V #T #A #_ #_ #IHV #IHT #X #l #H
  lapply (ssta_inv_cast1 … H) -H /2 width=2/
]
qed.
