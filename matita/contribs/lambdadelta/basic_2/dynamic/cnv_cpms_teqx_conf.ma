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

include "basic_2/dynamic/cnv_cpm_teqx_conf.ma".
include "basic_2/dynamic/cnv_cpms_teqx.ma".

(* CONTEXT-SENSITIVE NATIVE VALIDITY FOR TERMS ******************************)

(* Sub confluence propery with restricted rt-transition for terms ***********)

fact cnv_cpms_teqx_strip_lpr_aux (h) (a) (G0) (L0) (T0):
     (∀G,L,T. ❪G0,L0,T0❫ > ❪G,L,T❫ → IH_cnv_cpm_trans_lpr h a G L T) →
     (∀G,L,T. ❪G0,L0,T0❫ > ❪G,L,T❫ → IH_cnv_cpms_conf_lpr h a G L T) →
     ∀n1,T1. ❪G0,L0❫ ⊢ T0 ➡*[h,n1] T1 → ❪G0,L0❫ ⊢ T0 ![h,a] → T0 ≅ T1 →
     ∀n2,T2. ❪G0,L0❫ ⊢ T0 ➡[h,n2] T2 → T0 ≅ T2 →
     ∀L1. ❪G0,L0❫ ⊢ ➡[h,0] L1 → ∀L2. ❪G0,L0❫ ⊢ ➡[h,0] L2 →
     ∃∃T. ❪G0,L1❫ ⊢ T1 ➡[h,n2-n1] T & T1 ≅ T & ❪G0,L2❫ ⊢ T2 ➡*[h,n1-n2] T & T2 ≅ T.
#h #a #G #L0 #T0 #IH2 #IH1 #n1 #T1 #H1T01 #H0T0 #H2T01
@(cpms_teqx_ind_sn … H1T01 H0T0 H2T01 IH1 IH2) -n1 -T0
[ #H0T1 #n2 #T2 #H1T12 #H2T12 #L1 #HL01 #L2 #HL02
  <minus_O_n <minus_n_O
  elim (cnv_cpm_teqx_conf_lpr … H0T1 0 T1 … H1T12 H2T12 … HL01 … HL02) // -L0 -H2T12
  <minus_O_n <minus_n_O #T #H1T1 #H2T1 #H1T2 #H2T2
  /3 width=5 by cpm_cpms, ex4_intro/
| #m1 #m2 #T0 #T3 #H1T03 #H0T0 #H2T03 #_ #_ #_ #IH
  #n2 #T2 #H1T02 #H2T02 #L1 #HL01 #L2 #HL02
  elim (cnv_cpm_teqx_conf_lpr … H0T0 … H1T03 H2T03 … H1T02 H2T02 … L0 … HL02) -T0 //
  #T0 #H1T30 #H2T30 #H1T20 #H2T20
  elim (IH … H1T30 H2T30 … HL01 … HL02) -L0 -T3
  #T3 #H1T13 #H2T13 #H1T03 #H2T03
  <minus_plus >arith_l3
  /3 width=7 by cpms_step_sn, teqx_trans, ex4_intro/
]
qed-.

fact cnv_cpms_teqx_conf_lpr_aux (h) (a) (G0) (L0) (T0):
     (∀G,L,T. ❪G0,L0,T0❫ > ❪G,L,T❫ → IH_cnv_cpm_trans_lpr h a G L T) →
     (∀G,L,T. ❪G0,L0,T0❫ > ❪G,L,T❫ → IH_cnv_cpms_conf_lpr h a G L T) →
     ∀n1,T1. ❪G0,L0❫ ⊢ T0 ➡*[h,n1] T1 → ❪G0,L0❫ ⊢ T0 ![h,a] → T0 ≅ T1 →
     ∀n2,T2. ❪G0,L0❫ ⊢ T0 ➡*[h,n2] T2 → T0 ≅ T2 →
     ∀L1. ❪G0,L0❫ ⊢ ➡[h,0] L1 → ∀L2. ❪G0,L0❫ ⊢ ➡[h,0] L2 →
     ∃∃T. ❪G0,L1❫ ⊢ T1 ➡*[h,n2-n1] T & T1 ≅ T & ❪G0,L2❫ ⊢ T2 ➡*[h,n1-n2] T & T2 ≅ T.
#h #a #G #L0 #T0 #IH2 #IH1 #n1 #T1 #H1T01 #H0T0 #H2T01
generalize in match IH1; generalize in match IH2;
@(cpms_teqx_ind_sn … H1T01 H0T0 H2T01 IH1 IH2) -n1 -T0
[ #H0T1 #IH2 #IH1 #n2 #T2 #H1T12 #H2T12 #L1 #HL01 #L2 #HL02
  <minus_O_n <minus_n_O
  elim (cnv_cpms_teqx_strip_lpr_aux … IH2 IH1 … H1T12 H0T1 H2T12 0 T1 … HL02 … HL01) // -L0 -H2T12
  <minus_O_n <minus_n_O #T #H1T2 #H2T2 #H1T1 #H2T1
  /3 width=5 by cpm_cpms, ex4_intro/
| #m1 #m2 #T0 #T3 #H1T03 #H0T0 #H2T03 #_ #_ #_ #IH #IH2 #IH1
  #n2 #T2 #H1T02 #H2T02 #L1 #HL01 #L2 #HL02
  elim (cnv_cpms_teqx_strip_lpr_aux … IH2 IH1 … H1T02 H0T0 H2T02 … H1T03 H2T03 … HL02 L0) -H0T0 -H2T03 //
  #T4 #H1T24 #H2T24 #H1T34 #H2T34
  elim (IH … H1T34 H2T34 … HL01 … HL02) [|*: /4 width=5 by cpm_fpbq, fpbq_fpbg_trans/ ] -L0 -T0 -T3 (**)
  #T3 #H1T13 #H2T13 #H1T43 #H2T43
  <minus_plus >arith_l3
  /3 width=7 by cpms_step_sn, teqx_trans, ex4_intro/
]
qed-.
