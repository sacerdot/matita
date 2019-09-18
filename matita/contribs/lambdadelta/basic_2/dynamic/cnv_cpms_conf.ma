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

include "basic_2/dynamic/cnv_cpm_conf.ma".
include "basic_2/dynamic/cnv_cpms_tdeq_conf.ma".

(* CONTEXT-SENSITIVE NATIVE VALIDITY FOR TERMS ******************************)

(* Sub confluence propery with t-bound rt-computation for terms *************)

fact cnv_cpms_conf_lpr_tdeq_tdeq_aux (h) (a) (G0) (L0) (T0):
     (∀G,L,T. ⦃G0,L0,T0⦄ >[h] ⦃G,L,T⦄ → IH_cnv_cpm_trans_lpr h a G L T) →
     (∀G,L,T. ⦃G0,L0,T0⦄ >[h] ⦃G,L,T⦄ → IH_cnv_cpms_conf_lpr h a G L T) →
     ⦃G0,L0⦄ ⊢ T0 ![h,a] →
     ∀n1,T1. ⦃G0,L0⦄ ⊢ T0 ➡*[n1,h] T1 → T0 ≛ T1 →
     ∀n2,T2. ⦃G0,L0⦄ ⊢ T0 ➡*[n2,h] T2 → T0 ≛ T2 →
     ∀L1. ⦃G0,L0⦄ ⊢ ➡[h] L1 → ∀L2. ⦃G0,L0⦄ ⊢ ➡[h] L2 →
     ∃∃T. ⦃G0,L1⦄ ⊢ T1 ➡*[n2-n1,h] T & ⦃G0,L2⦄ ⊢ T2 ➡*[n1-n2,h] T.
#h #a #G #L0 #T0 #IH2 #IH1 #HT0
#n1 #T1 #H1T01 #H2T01 #n2 #T2 #H1T02 #H2T02
#L1 #HL01 #L2 #HL02
elim (cnv_cpms_tdeq_conf_lpr_aux … IH2 IH1 … H1T01 … H1T02 … HL01 … HL02) -IH2 -IH1 -H1T01 -H1T02 -HL01 -HL02
/2 width=3 by ex2_intro/
qed-.

fact cnv_cpms_conf_lpr_refl_tdneq_sub (h) (a) (G0) (L0) (T0) (m21) (m22):
     (∀G,L,T. ⦃G0,L0,T0⦄ >[h] ⦃G,L,T⦄ → IH_cnv_cpm_trans_lpr h a G L T) →
     (∀G,L,T. ⦃G0,L0,T0⦄ >[h] ⦃G,L,T⦄ → IH_cnv_cpms_conf_lpr h a G L T) →
     ⦃G0,L0⦄ ⊢ T0 ![h,a] →
     ∀X2. ⦃G0,L0⦄ ⊢ T0 ➡[m21,h] X2 → (T0 ≛ X2 → ⊥) → ∀T2. ⦃G0,L0⦄ ⊢ X2 ➡*[m22,h] T2 →
     ∀L1. ⦃G0,L0⦄ ⊢ ➡[h] L1 → ∀L2. ⦃G0,L0⦄ ⊢ ➡[h] L2 →
     ∃∃T. ⦃G0,L1⦄ ⊢ T0 ➡*[m21+m22,h] T& ⦃G0,L2⦄ ⊢ T2 ➡*[h] T.
#h #a #G0 #L0 #T0 #m21 #m22 #IH2 #IH1 #H0
#X2 #HX02 #HnX02 #T2 #HXT2
#L1 #HL01 #L2 #HL02
lapply (cnv_cpm_trans_lpr_aux … IH1 IH2 … HX02 … L0 ?) // #HX2
elim (cnv_cpm_conf_lpr_aux … IH2 IH1 … HX02 … 0 T0 … L0 … HL01) //
<minus_n_O <minus_O_n #Y1 #HXY1 #HTY1
elim (cnv_cpms_strip_lpr_sub … IH1 … HXT2 0 X2 … HL02 L0) [|*: /4 width=2 by fpb_fpbg, cpm_fpb/ ]
<minus_n_O <minus_O_n #Y2 #HTY2 #HXY2 -HXT2
elim (IH1 … HXY1 … HXY2 … HL01 … HL02) [|*: /4 width=2 by fpb_fpbg, cpm_fpb/ ]
-a -L0 -X2 <minus_n_O <minus_O_n #Y #HY1 #HY2
lapply (cpms_trans … HTY1 … HY1) -Y1 #HT0Y
lapply (cpms_trans … HTY2 … HY2) -Y2 #HT2Y
/2 width=3 by ex2_intro/
qed-.

fact cnv_cpms_conf_lpr_step_tdneq_sub (h) (a) (G0) (L0) (T0) (m11) (m12) (m21) (m22):
     (∀G,L,T. ⦃G0,L0,T0⦄ >[h] ⦃G,L,T⦄ → IH_cnv_cpm_trans_lpr h a G L T) →
     (∀G,L,T. ⦃G0,L0,T0⦄ >[h] ⦃G,L,T⦄ → IH_cnv_cpms_conf_lpr h a G L T) →
     ⦃G0,L0⦄ ⊢ T0 ![h,a] →
     ∀X1. ⦃G0,L0⦄ ⊢ T0 ➡[m11,h] X1 → T0 ≛ X1 → ∀T1. ⦃G0,L0⦄ ⊢ X1 ➡*[m12,h] T1 → X1 ≛ T1 →
     ∀X2. ⦃G0,L0⦄ ⊢ T0 ➡[m21,h] X2 → (T0 ≛ X2 → ⊥) → ∀T2. ⦃G0,L0⦄ ⊢ X2 ➡*[m22,h] T2 →
     ∀L1. ⦃G0,L0⦄ ⊢ ➡[h] L1 → ∀L2. ⦃G0,L0⦄ ⊢ ➡[h] L2 →
     ((∀G,L,T. ⦃G0,L0,X1⦄ >[h] ⦃G,L,T⦄ → IH_cnv_cpm_trans_lpr h a G L T) →
       (∀G,L,T. ⦃G0,L0,X1⦄ >[h] ⦃G,L,T⦄ → IH_cnv_cpms_conf_lpr h a G L T) →
       ∀m21,m22.
       ∀X2. ⦃G0,L0⦄ ⊢ X1 ➡[m21,h] X2 → (X1 ≛ X2 → ⊥) →
       ∀T2. ⦃G0,L0⦄ ⊢ X2 ➡*[m22,h] T2 →
       ∀L1. ⦃G0,L0⦄ ⊢ ➡[h] L1 → ∀L2. ⦃G0,L0⦄ ⊢ ➡[h] L2 →
       ∃∃T. ⦃G0,L1⦄ ⊢ T1 ➡*[m21+m22-m12,h] T & ⦃G0,L2⦄ ⊢ T2 ➡*[m12-(m21+m22),h]T
     ) →
     ∃∃T. ⦃G0,L1⦄ ⊢ T1 ➡*[m21+m22-(m11+m12),h] T & ⦃G0,L2⦄ ⊢ T2 ➡*[m11+m12-(m21+m22),h] T.
#h #a #G0 #L0 #T0 #m11 #m12 #m21 #m22 #IH2 #IH1 #HT0
#X1 #H1X01 #H2X01 #T1 #H1XT1 #H2XT1 #X2 #H1X02 #H2X02 #T2 #HXT2
#L1 #HL01 #L2 #HL02 #IH
lapply (cnv_cpm_trans_lpr_aux … IH1 IH2 … H1X01 … L0 ?) // #HX1
lapply (cnv_cpm_trans_lpr_aux … IH1 IH2 … H1X02 … L0 ?) // #HX2
elim (cnv_cpm_conf_lpr_aux … IH2 IH1 … H1X01 … H1X02 … L0 … L0) // #Z0 #HXZ10 #HXZ20
cut (⦃G0, L0, T0⦄ >[h] ⦃G0, L0, X2⦄) [ /4 width=5 by cpms_fwd_fpbs, cpm_fpb, ex2_3_intro/ ] #H1fpbg (**) (* cut *)
lapply (fpbg_fpbs_trans ?? G0 ? L0 ? Z0 ? … H1fpbg) [ /2 width=2 by cpms_fwd_fpbs/ ] #H2fpbg
lapply (cnv_cpms_trans_lpr_sub … IH2 … HXZ20 … L0 ?) // #HZ0
elim (IH1 … HXT2 … HXZ20 … L2 … L0) [|*: /4 width=2 by fpb_fpbg, cpm_fpb/ ] -HXT2 -HXZ20 #Z2 #HTZ2 #HZ02
elim (tdeq_dec X1 Z0) #H2XZ
[ -IH
  elim (cnv_cpms_conf_lpr_tdeq_tdeq_aux … HX1 … H1XT1 H2XT1 … HXZ10 H2XZ … L1 … L0) [2,3: // |4,5: /4 width=5 by cpm_fpbq, fpbq_fpbg_trans/ ]
| -H1XT1 -H2XT1
  elim (cpms_tdneq_fwd_step_sn_aux … HXZ10 HX1 H2XZ) [|*: /4 width=5 by cpm_fpbq, fpbq_fpbg_trans/ ]
  -HXZ10 -H2XZ #n1 #n2 #X0 #H1X10 #H2X10 #HXZ0 #Hn
  elim (IH … H1X10 H2X10 … HXZ0 … L1 … L0) [2,3: // |4,5: /4 width=5 by cpm_fpbq, fpbq_fpbg_trans/ ]
  >Hn -n1 -n2 -X0 -IH
]
#Z1 #HTZ1 #HZ01
elim (IH1 … HZ01 … HZ02  L1 … L2) // -L0 -T0 -X1 -X2 -Z0 #Z #HZ01 #HZ02
lapply (cpms_trans … HTZ1 … HZ01) -Z1 <arith_l4 #HT1Z
lapply (cpms_trans … HTZ2 … HZ02) -Z2 <arith_l4 #HT2Z
/2 width=3 by ex2_intro/
qed-.

fact cnv_cpms_conf_lpr_tdeq_tdneq_aux (h) (a) (G0) (L0) (T0) (n1) (m21) (m22):
     (∀G,L,T. ⦃G0,L0,T0⦄ >[h] ⦃G,L,T⦄ → IH_cnv_cpm_trans_lpr h a G L T) →
     (∀G,L,T. ⦃G0,L0,T0⦄ >[h] ⦃G,L,T⦄ → IH_cnv_cpms_conf_lpr h a G L T) →
     ⦃G0,L0⦄ ⊢ T0 ![h,a] →
     ∀T1. ⦃G0,L0⦄ ⊢ T0 ➡*[n1,h] T1 → T0 ≛ T1 →
     ∀X2. ⦃G0,L0⦄ ⊢ T0 ➡[m21,h] X2 → (T0 ≛ X2 → ⊥) → ∀T2. ⦃G0,L0⦄ ⊢ X2 ➡*[m22,h] T2 →
     ∀L1. ⦃G0,L0⦄ ⊢ ➡[h] L1 → ∀L2. ⦃G0,L0⦄ ⊢ ➡[h] L2 →
     ∃∃T. ⦃G0,L1⦄ ⊢ T1 ➡*[m21+m22-n1,h] T & ⦃G0,L2⦄ ⊢ T2 ➡*[n1-(m21+m22),h] T.
#h #a #G0 #L0 #T0 #n1 #m21 #m22 #IH2 #IH1 #HT0
#T1 #H1T01 #H2T01
generalize in match m22; generalize in match m21; -m21 -m22
generalize in match IH1; generalize in match IH2;
@(cpms_tdeq_ind_sn … H1T01 HT0 H2T01 IH1 IH2) -n1 -T0
[ #HT1 #IH2 #IH1 #m21 #m22
  #X2 #HX02 #HnX02 #T2 #HXT2 #L1 #HL01 #L2 #HL02
  <minus_O_n <minus_n_O
  @(cnv_cpms_conf_lpr_refl_tdneq_sub … IH2 IH1) -IH2 -IH1 /2 width=4 by/
| #m11 #m12 #T0 #X1 #H1X01 #HT0 #H2X01 #H1XT1 #_ #H2XT1 #IH #IH2 #IH1 #m21 #m22
  #X2 #HX02 #HnX02 #T2 #HXT2 #L1 #HL01 #L2 #HL02
  @(cnv_cpms_conf_lpr_step_tdneq_sub … IH2 IH1 … IH) -IH2 -IH1 -IH /2 width=4 by/
]
qed-.

fact cnv_cpms_conf_lpr_tdneq_tdneq_aux (h) (a) (G0) (L0) (T0) (m11) (m12) (m21) (m22):
     (∀G,L,T. ⦃G0,L0,T0⦄ >[h] ⦃G,L,T⦄ → IH_cnv_cpm_trans_lpr h a G L T) →
     (∀G,L,T. ⦃G0,L0,T0⦄ >[h] ⦃G,L,T⦄ → IH_cnv_cpms_conf_lpr h a G L T) →
     ⦃G0,L0⦄ ⊢ T0 ![h,a] →
     ∀X1. ⦃G0,L0⦄ ⊢ T0 ➡[m11,h] X1 → (T0 ≛ X1 → ⊥) → ∀T1. ⦃G0,L0⦄ ⊢ X1 ➡*[m12,h] T1 →
     ∀X2. ⦃G0,L0⦄ ⊢ T0 ➡[m21,h] X2 → (T0 ≛ X2 → ⊥) → ∀T2. ⦃G0,L0⦄ ⊢ X2 ➡*[m22,h] T2 →
     ∀L1. ⦃G0,L0⦄ ⊢ ➡[h] L1 → ∀L2. ⦃G0,L0⦄ ⊢ ➡[h] L2 →
     ∃∃T. ⦃G0,L1⦄ ⊢ T1 ➡*[m21+m22-(m11+m12),h] T & ⦃G0,L2⦄ ⊢ T2 ➡*[m11+m12-(m21+m22),h] T.
#h #a #G0 #L0 #T0 #m11 #m12 #m21 #m22 #IH2 #IH1 #H0
#X1 #HX01 #HnX01 #T1 #HXT1 #X2 #HX02 #HnX02 #T2 #HXT2
#L1 #HL01 #L2 #HL02
lapply (cnv_cpm_trans_lpr_aux … IH1 IH2 … HX01 … L0 ?) // #HX1
lapply (cnv_cpm_trans_lpr_aux … IH1 IH2 … HX02 … L0 ?) // #HX2
elim (cnv_cpm_conf_lpr_aux … IH2 IH1 … HX01 … HX02 … L0 … L0) // #Z0 #HXZ10 #HXZ20
cut (⦃G0, L0, T0⦄ >[h] ⦃G0, L0, X1⦄) [ /4 width=5 by cpms_fwd_fpbs, cpm_fpb, ex2_3_intro/ ] #H1fpbg (**) (* cut *)
lapply (fpbg_fpbs_trans ?? G0 ? L0 ? Z0 ? … H1fpbg) [ /2 width=2 by cpms_fwd_fpbs/ ] #H2fpbg
lapply (cnv_cpms_trans_lpr_sub … IH2 … HXZ10 … L0 ?) // #HZ0
elim (IH1 … HXT1 … HXZ10 … L1 … L0) [|*: /4 width=2 by fpb_fpbg, cpm_fpb/ ] -HXT1 -HXZ10 #Z1 #HTZ1 #HZ01
elim (IH1 … HXT2 … HXZ20 … L2 … L0) [|*: /4 width=2 by fpb_fpbg, cpm_fpb/ ] -HXT2 -HXZ20 #Z2 #HTZ2 #HZ02
elim (IH1 … HZ01 … HZ02  L1 … L2) // -L0 -T0 -X1 -X2 -Z0 #Z #HZ01 #HZ02
lapply (cpms_trans … HTZ1 … HZ01) -Z1 <arith_l4 #HT1Z
lapply (cpms_trans … HTZ2 … HZ02) -Z2 <arith_l4 #HT2Z
/2 width=3 by ex2_intro/
qed-.

fact cnv_cpms_conf_lpr_aux (h) (a) (G0) (L0) (T0):
     (∀G,L,T. ⦃G0,L0,T0⦄ >[h] ⦃G,L,T⦄ → IH_cnv_cpm_trans_lpr h a G L T) →
     (∀G,L,T. ⦃G0,L0,T0⦄ >[h] ⦃G,L,T⦄ → IH_cnv_cpms_conf_lpr h a G L T) →
     ∀G,L,T. G0 = G → L0 = L → T0 = T → IH_cnv_cpms_conf_lpr h a G L T.
#h #a #G #L #T #IH2 #IH1 #G0 #L0 #T0 #HG #HL #HT
#HT0 #n1 #T1 #HT01 #n2 #T2 #HT02 #L1 #HL01 #L2 #HL02 destruct
elim (tdeq_dec T0 T1) #H2T01
elim (tdeq_dec T0 T2) #H2T02
[ @(cnv_cpms_conf_lpr_tdeq_tdeq_aux … IH2 IH1) -IH2 -IH1 /2 width=1 by/
| elim (cpms_tdneq_fwd_step_sn_aux … HT02 HT0 H2T02 IH1 IH2) -HT02 -H2T02
  #m21 #m22 #X2 #HX02 #HnX02 #HXT2 #H2 destruct
  @(cnv_cpms_conf_lpr_tdeq_tdneq_aux … IH2 IH1) -IH2 -IH1 /2 width=4 by/
| elim (cpms_tdneq_fwd_step_sn_aux … HT01 HT0 H2T01 IH1 IH2) -HT01 -H2T01
  #m11 #m12 #X1 #HX01 #HnX01 #HXT1 #H1 destruct
  @ex2_commute @(cnv_cpms_conf_lpr_tdeq_tdneq_aux … IH2 IH1) -IH2 -IH1 /2 width=4 by/
| elim (cpms_tdneq_fwd_step_sn_aux … HT01 HT0 H2T01 IH1 IH2) -HT01 -H2T01
  elim (cpms_tdneq_fwd_step_sn_aux … HT02 HT0 H2T02 IH1 IH2) -HT02 -H2T02
  #m21 #m22 #X2 #HX02 #HnX02 #HXT2 #H2 #m11 #m12 #X1 #HX01 #HnX01 #HXT1 #H1 destruct
  @(cnv_cpms_conf_lpr_tdneq_tdneq_aux … IH2 IH1) -IH2 -IH1 /2 width=4 by/
]
qed-.
