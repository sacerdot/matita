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
include "basic_2/static/aaa_lift.ma".

(* STATIC TYPE ASSIGNMENT FOR TERMS *****************************************)

(* Properties on atomic arity assignment for terms **************************)

lemma aaa_sta: ∀h,G,L,T,A. ⦃G, L⦄ ⊢ T ⁝ A → ∃U. ⦃G, L⦄ ⊢ T •[h] U.
#h #G #L #T #A #H elim H -G -L -T -A
[ /2 width=2 by sta_sort, ex_intro/
| * #G #L #K [ #V | #W ] #B #i #HLK #_ * [ #W | #V ] #HVW
  elim (lift_total W 0 (i+1)) /3 width=7 by sta_ldef, sta_ldec, ex_intro/
| #a #G #L #V #T #B #A #_ #_ #_ * /3 width=2 by sta_bind, ex_intro/
| #a #G #L #V #T #B #A #_ #_ #_ * /3 width=2 by sta_bind, ex_intro/
| #G #L #V #T #B #A #_ #_ #_ * /3 width=2 by sta_appl, ex_intro/
| #G #L #W #T #A #_ #_ #_ * /3 width=2 by sta_cast, ex_intro/
]
qed-.

lemma sta_aaa_conf: ∀h,G,L. Conf3 … (aaa G L) (sta h G L).
#h #G #L #T #A #H elim H -G -L -T -A
[ #G #L #k #U #H
  lapply (sta_inv_sort1 … H) -H #H destruct //
| #I #G #L #K #V #B #i #HLK #HV #IHV #U #H
  elim (sta_inv_lref1 … H) -H * #K0 #V0 #W0 #HLK0 #HVW0 #HU
  lapply (drop_mono … HLK0 … HLK) -HLK0 #H0 destruct
  lapply (drop_fwd_drop2 … HLK) -HLK #HLK
  @(aaa_lift … HLK … HU) -HU -L /2 width=2 by/
| #a #G #L #V #T #B #A #HV #_ #_ #IHT #X #H
  elim (sta_inv_bind1 … H) -H #U #HTU #H destruct /3 width=2 by aaa_abbr/
| #a #G #L #V #T #B #A #HV #_ #_ #IHT #X #H
  elim (sta_inv_bind1 … H) -H #U #HTU #H destruct /3 width=2 by aaa_abst/
| #G #L #V #T #B #A #HV #_ #_ #IHT #X #H
  elim (sta_inv_appl1 … H) -H #U #HTU #H destruct /3 width=3 by aaa_appl/
| #G #L #V #T #A #_ #_ #IHV #IHT #X #H
  lapply (sta_inv_cast1 … H) -H /2 width=2 by/
]
qed-.
