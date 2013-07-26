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
include "basic_2/computation/cpds_aaa.ma".
include "basic_2/equivalence/cpcs_aaa.ma".
include "basic_2/dynamic/snv.ma".

(* STRATIFIED NATIVE VALIDITY FOR TERMS *************************************)

(* Forward lemmas on atomic arity assignment for terms **********************)

lemma snv_fwd_aaa: ∀h,g,L,T. ⦃h, L⦄ ⊢ T ¡[g] → ∃A. L ⊢ T ⁝ A.
#h #g #L #T #H elim H -L -T
[ /2 width=2/
| #I #L #K #V #i #HLK #_ * /3 width=6/
| #a * #L #V #T #_ #_ * #B #HV * #A #HA /3 width=2/
| #a #L #V #W #W0 #T #U #l #_ #_ #HVW #HW0 #HTU * #B #HV * #X #HT
  lapply (cpds_aaa h g … HV W0 ?) [ -HTU /3 width=4/ ] -W #HW0 (**) (* auto fail without -HTU *)
  lapply (cpds_aaa … HT … HTU) -HTU #H
  elim (aaa_inv_abst … H) -H #B0 #A #H1 #HU #H2 destruct
  lapply (aaa_mono … H1 … HW0) -W0 #H destruct /3 width=4/
| #L #W #T #U #l #_ #_ #HTU #HUW * #B #HW * #A #HT
  lapply (aaa_cpcs_mono … HUW A … HW) -HUW /2 width=7/ -HTU #H destruct /3 width=3/
]
qed-.

lemma snv_fwd_csn: ∀h,g,L,T. ⦃h, L⦄ ⊢ T ¡[g] → ⦃h, L⦄ ⊢ ⬊*[g] T.
#h #g #L #T #H elim (snv_fwd_aaa … H) -H /2 width=2/
qed-.
