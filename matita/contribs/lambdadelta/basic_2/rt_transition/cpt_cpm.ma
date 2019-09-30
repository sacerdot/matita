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

include "basic_2/rt_transition/cpm_drops.ma".
include "basic_2/rt_transition/cpt_drops.ma".

(* T-BOUND CONTEXT-SENSITIVE PARALLEL T-TRANSITION FOR TERMS ****************)

(* Properties with t-bound rt-transition for terms **************************)

lemma cpm_cpt_cpr (h) (n) (G) (L):
      ∀T1,T2. ⦃G,L⦄ ⊢ T1 ➡[n,h] T2 →
      ∃∃T0. ⦃G,L⦄ ⊢ T1 ⬆[h,n] T0 & ⦃G,L⦄ ⊢ T0 ➡[h] T2.
#h #n #G #L #T1 #T2 #H
@(cpm_ind … H) -n -G -L -T1 -T2
[ #I #G #L /2 width=3 by ex2_intro/
| #G #L #s /3 width=3 by cpm_sort, ex2_intro/
| #n #G #K #V1 #V2 #W2 #_ * #V0 #HV10 #HV02 #HVW2
  elim (lifts_total V0 (𝐔❴1❵)) #W0 #HVW0
  lapply (cpm_lifts_bi … HV02 (Ⓣ) … (K.ⓓV1) … HVW0 … HVW2) -HVW2
  [ /3 width=1 by drops_refl, drops_drop/ ] -HV02 #HW02
  /3 width=3 by cpt_delta, ex2_intro/
| #n #G #K #V1 #V2 #W2 #_ * #V0 #HV10 #HV02 #HVW2
  elim (lifts_total V0 (𝐔❴1❵)) #W0 #HVW0
  lapply (cpm_lifts_bi … HV02 (Ⓣ) … (K.ⓛV1) … HVW0 … HVW2) -HVW2
  [ /3 width=1 by drops_refl, drops_drop/ ] -HV02 #HW02
  /3 width=3 by cpt_ell, ex2_intro/
| #n #I #G #K #T2 #U2 #i #_ * #T0 #HT0 #HT02 #HTU2
  elim (lifts_total T0 (𝐔❴1❵)) #U0 #HTU0
  lapply (cpm_lifts_bi … HT02 (Ⓣ) … (K.ⓘ{I}) … HTU0 … HTU2) -HTU2
  [ /3 width=1 by drops_refl, drops_drop/ ] -HT02 #HU02
  /3 width=3 by cpt_lref, ex2_intro/
| #n #p #I #G #L #V1 #V2 #T1 #T2 #HV12 #_ #_ * #T0 #HT10 #HT02
  /3 width=5 by cpt_bind, cpm_bind, ex2_intro/
| #n #G #L #V1 #V2 #T1 #T2 #HV12 #_ #_ * #T0 #HT10 #HT02
  /3 width=5 by cpt_appl, cpm_appl, ex2_intro/
| #n #G #L #V1 #V2 #T1 #T2 #_ #_ * #V0 #HV10 #HV02 * #T0 #HT10 #HT02
  /3 width=5 by cpt_cast, cpm_cast, ex2_intro/
| #n #G #L #V #U1 #T1 #T2 #HTU1 #_ * #T0 #HT10 #HT02
  elim (cpt_lifts_sn … HT10 (Ⓣ) … (L.ⓓV) … HTU1) -T1
  [| /3 width=1 by drops_refl, drops_drop/ ] #U0 #HTU0 #HU10
  /3 width=6 by cpt_bind, cpm_zeta, ex2_intro/
| #n #G #L #U #T1 #T2 #_ * #T0 #HT10 #HT02
| #n #G #L #U1 #U2 #T #_ * #U0 #HU10 #HU02
  /3 width=3 by cpt_ee, ex2_intro/
| #n #p #G #L #V1 #V2 #W1 #W2 #T1 #T2 #HV12 #HW12 #_ #_ #_ * #T0 #HT10 #HT02
  /4 width=7 by cpt_appl, cpt_bind, cpm_beta, ex2_intro/
| #n #p #G #L #V1 #V2 #V0 #W1 #W2 #T1 #T2 #HV12 #HW12 #_ #_ #_ * #T0 #HT10 #HT02 #HV20
  /4 width=9 by cpt_appl, cpt_bind, cpm_theta, ex2_intro/
]

(* Forward lemmas with t-bound rt-transition for terms **********************)

lemma cpt_fwd_cpm (h) (n) (G) (L):
      ∀T1,T2. ⦃G,L⦄ ⊢ T1 ⬆[h,n] T2 → ⦃G,L⦄ ⊢ T1 ➡[n,h] T2.