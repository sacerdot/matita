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

include "basic_2/static/da_aaa.ma".
include "basic_2/computation/scpds_aaa.ma".
include "basic_2/dynamic/snv.ma".

(* STRATIFIED NATIVE VALIDITY FOR TERMS *************************************)

(* Forward lemmas on atomic arity assignment for terms **********************)

lemma snv_fwd_aaa: ∀h,o,G,L,T. ⦃G, L⦄ ⊢ T ¡[h, o] → ∃A. ⦃G, L⦄ ⊢ T ⁝ A.
#h #o #G #L #T #H elim H -G -L -T
[ /2 width=2 by aaa_sort, ex_intro/
| #I #G #L #K #V #i #HLK #_ * /3 width=6 by aaa_lref, ex_intro/
| #a * #G #L #V #T #_ #_ * #B #HV * #A #HA /3 width=2 by aaa_abbr, aaa_abst, ex_intro/
| #a #G #L #V #W0 #T #U0 #d #_ #_ #HVW0 #HTU0 * #B #HV * #X #HT
  lapply (scpds_aaa_conf … HV … HVW0) -HVW0 #HW0
  lapply (scpds_aaa_conf … HT … HTU0) -HTU0 #H
  elim (aaa_inv_abst … H) -H #B0 #A #H1 #HU #H2 destruct
  lapply (aaa_mono … H1 … HW0) -W0 #H destruct /3 width=4 by aaa_appl, ex_intro/
| #G #L #U #T #U0 #_ #_ #HU0 #HTU0 * #B #HU * #A #HT
  lapply (scpds_aaa_conf … HU … HU0) -HU0 #HU0
  lapply (scpds_aaa_conf … HT … HTU0) -HTU0 #H
  lapply (aaa_mono … H … HU0) -U0 #H destruct /3 width=3 by aaa_cast, ex_intro/
]
qed-.

(* Advanced forward lemmas **************************************************)

lemma snv_fwd_da: ∀h,o,G,L,T. ⦃G, L⦄ ⊢ T ¡[h, o] → ∃d. ⦃G, L⦄ ⊢ T ▪[h, o] d.
#h #o #G #L #T #H elim (snv_fwd_aaa … H) -H /2 width=2 by aaa_da/
qed-.

lemma snv_fwd_lstas: ∀h,o,G,L,T. ⦃G, L⦄ ⊢ T ¡[h, o] →
                     ∀d. ∃U. ⦃G, L⦄ ⊢ T •*[h, d] U.
#h #o #G #L #T #H #d elim (snv_fwd_aaa … H) -H
#A #HT elim (aaa_lstas h … HT d) -HT /2 width=2 by ex_intro/
qed-.
