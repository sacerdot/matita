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

include "basic_2/rt_computation/cpue_csx.ma".
include "basic_2/rt_conversion/cpce_drops.ma".
include "basic_2/dynamic/cnv_cpue.ma".

(* CONTEXT-SENSITIVE NATIVE VALIDITY FOR TERMS ******************************)

(* Properties with context-sensitive parallel eta-conversion for terms ******)

lemma cpce_total_cnv (a) (h) (G) (L):
      ∀T1. ⦃G,L⦄ ⊢ T1 ![a,h] → ∃T2. ⦃G,L⦄ ⊢ T1 ⬌η[h] T2.
#a #h #G #L #T1 #HT1
lapply (cnv_fwd_csx … HT1) #H
generalize in match HT1; -HT1
@(csx_ind_fpbg … H) -G -L -T1
#G #L * *
[ #s #_ #_ /2 width=2 by cpce_sort, ex_intro/
| #i #H1i #IH #H2i
  elim (drops_ldec_dec L i) [ * #K #W #HLK | -H1i -IH #HnX ]
  [ lapply (cnv_inv_lref_pair … H2i … HLK) -H2i #H2W
    lapply (csx_inv_lref_pair … HLK H1i) -H1i #H1W
    elim (cpue_total_csx … H1W) -H1W #X
    elim (abst_dec X) [ * | -IH ]
    [ #p #V1 #U #H destruct * #n #HWU #_
      elim (IH G K V1) -IH
      [ #V2 #HV12
        elim (lifts_total V2 (𝐔❴↑i❵)) #W2 #HVW2
        /3 width=12 by cpce_eta_drops, ex_intro/
      | /3 width=6 by  cnv_cpms_trans, cnv_fwd_pair_sn/
      | /4 width=6 by fqup_cpms_fwd_fpbg, fpbg_fqu_trans, fqup_lref/
      ]
    | #HnX #HWX
      @(ex_intro … (#i))
      @cpce_zero_drops #n0 #p #K0 #W0 #V0 #U0 #HLK0 #HWU0
      lapply (drops_mono … HLK0 … HLK) -i -L #H destruct
      elim (cnv_cpue_cpms_conf … H2W … HWU0 … HWX) -n0 -W #X0 * #n0 #HUX0 #_ #HX0
      elim (cpms_inv_abst_sn … HUX0) -HUX0 #V1 #U1 #_ #_ #H destruct -n0 -K -V0 -U0
      elim (tueq_inv_bind2 … HX0) -HX0 #U0 #_ #H destruct -U1
      /2 width=4 by/
    ]
  | /5 width=3 by cpce_zero_drops, ex1_2_intro, ex_intro/
  ]
| #l #_ #_ /2 width=2 by cpce_gref, ex_intro/
| #p #I #V1 #T1 #_ #IH #H
  elim (cnv_inv_bind … H) -H #HV1 #HT1
  elim (IH … HV1) [| /3 width=1 by fpb_fpbg, fpb_fqu, fqu_pair_sn/ ] #V2 #HV12
  elim (IH … HT1) [| /4 width=1 by fpb_fpbg, fpb_fqu, fqu_bind_dx/ ] #T2 #HT12
  /3 width=2 by cpce_bind, ex_intro/
| #I #V1 #T1 #_ #IH #H
  elim (cnv_fwd_flat … H) -H #HV1 #HT1
  elim (IH … HV1) [| /3 width=1 by fpb_fpbg, fpb_fqu, fqu_pair_sn/ ] #V2 #HV12
  elim (IH … HT1) [| /3 width=1 by fpb_fpbg, fpb_fqu, fqu_flat_dx/ ] #T2 #HT12
  /3 width=2 by cpce_flat, ex_intro/
]
qed-.
