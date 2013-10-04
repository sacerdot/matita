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

include "basic_2/static/ssta.ma".
include "basic_2/static/aaa_lift.ma".
include "basic_2/static/aaa_da.ma".

(* ATONIC ARITY ASSIGNMENT FOR TERMS ****************************************)

(* Properties on stratified static type assignment for terms ****************)

lemma aaa_ssta_conf: ∀h,g,G,L. Conf3 … (aaa G L) (ssta h g G L).
#h #g #G #L #T #A #H elim H -G -L -T -A
[ #G #L #k #U #H
  lapply (ssta_inv_sort1 … H) -H #H destruct //
| #I #G #L #K #V #B #i #HLK #HV #IHV #U #H
  elim (ssta_inv_lref1 … H) -H * #K0 #V0 #W0 #HLK0 #HVW0 #HU
  lapply (ldrop_mono … HLK0 … HLK) -HLK0 #H0 destruct
  lapply (ldrop_fwd_ldrop2 … HLK) -HLK #HLK
  @(aaa_lift … HLK … HU) -HU -L // -HV /2 width=2/
| #a #G #L #V #T #B #A #HV #_ #_ #IHT #X #H
  elim (ssta_inv_bind1 … H) -H #U #HTU #H destruct /3 width=2/
| #a #G #L #V #T #B #A #HV #_ #_ #IHT #X #H
  elim (ssta_inv_bind1 … H) -H #U #HTU #H destruct /3 width=2/
| #G #L #V #T #B #A #HV #_ #_ #IHT #X #H
  elim (ssta_inv_appl1 … H) -H #U #HTU #H destruct /3 width=3/
| #G #L #V #T #A #_ #_ #IHV #IHT #X #H
  lapply (ssta_inv_cast1 … H) -H /2 width=2/
]
qed-.

(* Forward lemmas on stratified static type assignment for terms ************)

lemma aaa_fwd_ssta: ∀h,g,G,L,T,A. ⦃G, L⦄ ⊢ T ⁝ A → ∃U. ⦃G, L⦄ ⊢ T •[h, g] U.
#h #g #G #L #T #A #H elim (aaa_fwd_da … H) -H /2 width=3 by da_ssta/
qed-.
