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
include "basic_2/unfold/lstas_lift.ma".
include "basic_2/computation/csx_aaa.ma".
include "basic_2/computation/cpds_aaa.ma".
include "basic_2/equivalence/cpcs_aaa.ma".
include "basic_2/dynamic/snv.ma".

(* STRATIFIED NATIVE VALIDITY FOR TERMS *************************************)

(* Forward lemmas on atomic arity assignment for terms **********************)

lemma snv_fwd_aaa: ∀h,g,G,L,T. ⦃G, L⦄ ⊢ T ¡[h, g] → ∃A. ⦃G, L⦄ ⊢ T ⁝ A.
#h #g #G #L #T #H elim H -G -L -T
[ /2 width=2 by aaa_sort, ex_intro/
| #I #G #L #K #V #i #HLK #_ * /3 width=6 by aaa_lref, ex_intro/
| #a * #G #L #V #T #_ #_ * #B #HV * #A #HA /3 width=2 by aaa_abbr, aaa_abst, ex_intro/
| #a #G #L #V #W #W0 #T #U #l #_ #_ #Hl #HVW #HW0 #HTU * #B #HV * #X #HT
  lapply (cpds_aaa_conf h g … HV W0 ?) [ -HTU /3 width=4 by cpds_strap1, sta_cprs_cpds/ ] -W #HW0 (**) (* auto fail without -HTU *)
  lapply (cpds_aaa_conf … HT … HTU) -HTU #H
  elim (aaa_inv_abst … H) -H #B0 #A #H1 #HU #H2 destruct
  lapply (aaa_mono … H1 … HW0) -W0 #H destruct /3 width=4 by aaa_appl, ex_intro/
| #G #L #W #T #U #l #_ #_ #_ #HTU #HUW * #B #HW * #A #HT
  lapply (sta_aaa_conf … HT … HTU) -HTU #H
  lapply (cpcs_aaa_mono … HUW … H … HW) -HUW -H #H destruct /3 width=3 by aaa_cast, ex_intro/
]
qed-.

lemma snv_fwd_csx: ∀h,g,G,L,T. ⦃G, L⦄ ⊢ T ¡[h, g] → ⦃G, L⦄ ⊢ ⬊*[h, g] T.
#h #g #G #L #T #H elim (snv_fwd_aaa … H) -H /2 width=2 by aaa_csx/
qed-.

(* Advanced forward lemmas **************************************************)

lemma snv_fwd_da: ∀h,g,G,L,T. ⦃G, L⦄ ⊢ T ¡[h, g] → ∃l. ⦃G, L⦄ ⊢ T ▪[h, g] l.
#h #g #G #L #T #H elim (snv_fwd_aaa … H) -H /2 width=2 by aaa_da/
qed-.

lemma snv_fwd_sta: ∀h,g,G,L,T. ⦃G, L⦄ ⊢ T ¡[h, g] → ∃U. ⦃G, L⦄ ⊢ T •[h] U.
#h #g #G #L #T #H elim (snv_fwd_aaa … H) -H /2 width=2 by aaa_sta/
qed-.

lemma snv_lstas_fwd_correct: ∀h,g,G,L,T1,T2,l. ⦃G, L⦄ ⊢ T1 ¡[h, g] → ⦃G, L⦄ ⊢ T1 •* [h, l] T2 →
                             ∃U2. ⦃G, L⦄ ⊢ T2 •[h] U2.
#h #g #G #L #T1 #T2 #l #HT1 #HT12
elim (snv_fwd_sta … HT1) -HT1 /2 width=5 by lstas_fwd_correct/
qed-.

(* Advanced properties ******************************************************)

lemma snv_scast: ∀h,g,G,L,V,W,l. ⦃G, L⦄ ⊢ V ¡[h, g] → ⦃G, L⦄ ⊢ W ¡[h, g] →
                 scast h g l G L V W → ⦃G, L⦄ ⊢V ▪[h, g] l+1 → ⦃G, L⦄ ⊢ ⓝW.V ¡[h, g].
#h #g #G #L #V #W #l #HV #HW #H #Hl
elim (snv_fwd_sta … HV) /4 width=6 by snv_cast, sta_lstas/
qed-.
