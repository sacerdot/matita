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

include "basic_2/rt_transition/cpr_tdeq.ma".
include "basic_2/rt_transition/cwhx_drops.ma".
include "basic_2/rt_transition/cwhx_rdeq.ma".
include "basic_2/rt_computation/fsb_aaa.ma".
include "basic_2/rt_computation/cpms_cpms.ma".
include "basic_2/rt_computation/cpms_fpbg.ma".

(* T-BOUND CONTEXT-SENSITIVE PARALLEL RT-COMPUTATION FOR TERMS **************)

(* Properties with whd normality for unbound rt-transition ******************)

lemma aaa_cpms_cwhx (h) (G) (L):
                    ∀T1,A. ⦃G,L⦄ ⊢ T1 ⁝ A →
                    ∃∃n,T2. ⦃G,L⦄ ⊢ T1 ➡*[n,h] T2 & ⦃G,L⦄ ⊢ ⬈[h] 𝐖𝐇⦃T2⦄.
#h #G #L #T1 #A #H
letin o ≝ (sd_O h)
@(aaa_ind_fpbg … o … H) -G -L -T1 -A
#G #L #T1 #A * -G -L -T1 -A
[ #G #L #s #_ /2 width=4 by cwhx_sort, ex2_2_intro/
| * #G #K #V1 #A #_ #IH -A
  elim (IH … G K V1) [2,4: /3 width=1 by fpb_fpbg, fpb_fqu, fqu_lref_O/ ] -IH #n #V2 #HV12 #HV2
  elim (lifts_total … V2 (𝐔❴1❵)) #T2 #HVT2
  /5 width=10 by cpms_ell, cpms_delta, cwhx_lifts, drops_refl, drops_drop, ex2_2_intro/
| #I #G #K #A #i #_ #IH -A
  elim (IH … G K (#i)) [| /3 width=1 by fpb_fpbg, fpb_fqu/ ] -IH #n #V2 #HV12 #HV2
  elim (lifts_total … V2 (𝐔❴1❵)) #T2 #HVT2
  /5 width=10 by cpms_lref, cwhx_lifts, drops_refl, drops_drop, ex2_2_intro/
| * #G #L #V #T1 #B #A #_ #_ #IH -B -A
  [ elim (cpr_abbr_pos h o G L V T1) #T0 #HT10 #HnT10
    elim (IH G L T0) -IH [| /4 width=2 by fpb_fpbg, cpm_fpb/ ] -HnT10 #n #T2 #HT02 #HT2
    /3 width=5 by cpms_step_sn, ex2_2_intro/
  | elim (IH … G (L.ⓓV) T1) -IH [| /3 width=1 by fpb_fpbg, fpb_fqu, fqu_bind_dx/ ] #n #T2 #HT12 #HT2
    /3 width=5 by cwhx_ldef, cpms_bind_dx, ex2_2_intro/
  ]
| #p #G #L #W #T1 #B #A #_ #_ #_ -B -A
  /2 width=5 by cwhx_abst, ex2_2_intro/
| #G #L #V #T1 #B #A #_ #HT1 #IH
  elim (IH … G L T1) [| /3 width=1 by fpb_fpbg, fpb_fqu, fqu_flat_dx/ ] #n1 #T2 #HT12 #HT2
  elim (tdeq_dec h o T1 T2) [ -n1 #HT12 | -HT2 #HnT12 ]
  [ lapply (tdeq_cwhx_trans … HT2 … HT12) -T2
    @(insert_eq_0 … L) #Y @(insert_eq_0 … T1) #X * -Y -X
    [ #L0 #s0 #H1 #H2 destruct -IH
      lapply (aaa_inv_sort … HT1) -HT1 #H destruct
    | #p #L0 #W0 #T0 #H1 #H2 destruct -HT1
      elim (IH G L0 (ⓓ{p}ⓝW0.V.T0)) -IH [ /4 width=5 by cpms_step_sn, cpm_beta, ex2_2_intro/ ]
      @fpb_fpbg @fpb_cpx [ /2 width=1 by cpx_beta/ ] #H
      elim (tdeq_inv_pair … H) -H #H #_ #_ destruct
    | #L0 #V0 #T0 #_ #H1 #H2 destruct -HT1
      elim (lifts_total V (𝐔❴1❵)) #W #HVW
      elim (IH G L0 (-ⓓV0.ⓐW.T0)) -IH [ /4 width=5 by cpms_step_sn, cpm_theta, ex2_2_intro/ ]
      @fpb_fpbg @fpb_cpx [ /2 width=3 by cpx_theta/ ] #H
      elim (tdeq_inv_pair … H) -H #H #_ #_ destruct
    ]
  | elim (IH G L (ⓐV.T2)) -IH [ /4 width=5 by cpms_trans, cpms_appl_dx, ex2_2_intro/ ]
    @(cpms_tdneq_fwd_fpbg … n1) [ /2 width=3 by cpms_appl_dx/ ] #H
    elim (tdeq_inv_pair … H) -H #_ #_ #H /2 width=1 by/
  ]
| #G #L #U #T1 #A #_ #_ #IH -A
  elim (IH … G L T1) [| /3 width=1 by fpb_fpbg, fpb_fqu, fqu_flat_dx/ ] #n #T2 #HT12 #HT2
  /3 width=4 by cpms_eps, ex2_2_intro/
]
qed-.
