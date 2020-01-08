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

include "ground_2/xoa/ex_5_3.ma".
include "basic_2/rt_equivalence/cpcs_cpcs.ma".
include "basic_2/dynamic/cnv_preserve_cpcs.ma".
include "basic_2/dynamic/nta.ma".

(* NATIVE TYPE ASSIGNMENT FOR TERMS *****************************************)

(* Properties based on preservation *****************************************)

lemma cnv_cpms_nta (h) (a) (G) (L):
      ∀T. ❪G,L❫ ⊢ T ![h,a] → ∀U.❪G,L❫ ⊢ T ➡*[1,h] U → ❪G,L❫ ⊢ T :[h,a] U.
/3 width=4 by cnv_cast, cnv_cpms_trans/ qed.

lemma cnv_nta_sn (h) (a) (G) (L):
      ∀T. ❪G,L❫ ⊢ T ![h,a] → ∃U. ❪G,L❫ ⊢ T :[h,a] U.
#h #a #G #L #T #HT
elim (cnv_fwd_cpm_SO … HT) #U #HTU
/4 width=2 by cnv_cpms_nta, cpm_cpms, ex_intro/
qed-.

(* Basic_1: was: ty3_typecheck *)
lemma nta_typecheck (h) (a) (G) (L):
      ∀T,U. ❪G,L❫ ⊢ T :[h,a] U → ∃T0. ❪G,L❫ ⊢ ⓝU.T :[h,a] T0.
/3 width=1 by cnv_cast, cnv_nta_sn/ qed-.

(* Basic_1: was: ty3_correct *)
(* Basic_2A1: was: ntaa_fwd_correct *)
lemma nta_fwd_correct (h) (a) (G) (L):
      ∀T,U. ❪G,L❫ ⊢ T :[h,a] U → ∃T0. ❪G,L❫ ⊢ U :[h,a] T0.
/3 width=2 by nta_fwd_cnv_dx, cnv_nta_sn/ qed-.

lemma nta_pure_cnv (h) (G) (L):
      ∀T,U. ❪G,L❫ ⊢ T :[h,𝛚] U →
      ∀V. ❪G,L❫ ⊢ ⓐV.U ![h,𝛚] → ❪G,L❫ ⊢ ⓐV.T :[h,𝛚] ⓐV.U.
#h #G #L #T #U #H1 #V #H2
elim (cnv_inv_cast … H1) -H1 #X0 #HU #HT #HUX0 #HTX0
elim (cnv_inv_appl … H2) #n #p #X1 #X2 #_ #HV #_ #HVX1 #HUX2
elim (cnv_cpms_conf … HU … HUX0 … HUX2) -HU -HUX2
<minus_O_n <minus_n_O #X #HX0 #H
elim (cpms_inv_abst_sn … H) -H #X3 #X4 #HX13 #HX24 #H destruct
@(cnv_cast … (ⓐV.X0)) [2:|*: /2 width=1 by cpms_appl_dx/ ] (**) (* full auto a bit slow *)
/3 width=10 by cnv_appl, cpms_trans, cpms_cprs_trans/
qed.

(* Basic_1: uses: ty3_sred_wcpr0_pr0 *)
lemma nta_cpr_conf_lpr (h) (a) (G):
      ∀L1,T1,U. ❪G,L1❫ ⊢ T1 :[h,a] U → ∀T2. ❪G,L1❫ ⊢ T1 ➡[h] T2 →
      ∀L2. ❪G,L1❫ ⊢ ➡[h] L2 → ❪G,L2❫ ⊢ T2 :[h,a] U.
#h #a #G #L1 #T1 #U #H #T2 #HT12 #L2 #HL12
/3 width=6 by cnv_cpm_trans_lpr, cpm_cast/
qed-.

(* Basic_1: uses: ty3_sred_pr2 ty3_sred_pr0 *)
lemma nta_cpr_conf (h) (a) (G) (L):
      ∀T1,U. ❪G,L❫ ⊢ T1 :[h,a] U →
      ∀T2. ❪G,L❫ ⊢ T1 ➡[h] T2 → ❪G,L❫ ⊢ T2 :[h,a] U.
#h #a #G #L #T1 #U #H #T2 #HT12
/3 width=6 by cnv_cpm_trans, cpm_cast/
qed-.

(* Note: this is the preservation property *)
(* Basic_1: uses: ty3_sred_pr3 ty3_sred_pr1 *)
lemma nta_cprs_conf (h) (a) (G) (L):
      ∀T1,U. ❪G,L❫ ⊢ T1 :[h,a] U →
      ∀T2. ❪G,L❫ ⊢ T1 ➡*[h] T2 → ❪G,L❫ ⊢ T2 :[h,a] U.
#h #a #G #L #T1 #U #H #T2 #HT12
/3 width=6 by cnv_cpms_trans, cpms_cast/
qed-.

(* Basic_1: uses: ty3_cred_pr2 *)
lemma nta_lpr_conf (h) (a) (G):
      ∀L1,T,U. ❪G,L1❫ ⊢ T :[h,a] U →
      ∀L2. ❪G,L1❫ ⊢ ➡[h] L2 → ❪G,L2❫ ⊢ T :[h,a] U.
#h #a #G #L1 #T #U #HTU #L2 #HL12
/2 width=3 by cnv_lpr_trans/
qed-.

(* Basic_1: uses: ty3_cred_pr3 *)
lemma nta_lprs_conf (h) (a) (G):
      ∀L1,T,U. ❪G,L1❫ ⊢ T :[h,a] U →
      ∀L2. ❪G,L1❫ ⊢ ➡*[h] L2 → ❪G,L2❫ ⊢ T :[h,a] U.
#h #a #G #L1 #T #U #HTU #L2 #HL12
/2 width=3 by cnv_lprs_trans/
qed-.

(* Inversion lemmas based on preservation ***********************************)

lemma nta_inv_ldef_sn (h) (a) (G) (K) (V):
      ∀X2. ❪G,K.ⓓV❫ ⊢ #0 :[h,a] X2 →
      ∃∃W,U. ❪G,K❫ ⊢ V :[h,a] W & ⇧*[1] W ≘ U & ❪G,K.ⓓV❫ ⊢ U ⬌*[h] X2 & ❪G,K.ⓓV❫ ⊢ X2 ![h,a].
#h #a #G #Y #X #X2 #H
elim (cnv_inv_cast … H) -H #X1 #HX2 #H1 #HX21 #H2
elim (cnv_inv_zero … H1) -H1 #Z #K #V #HV #H destruct
elim (cpms_inv_delta_sn … H2) -H2 *
[ #_ #H destruct
| #W #HVW #HWX1
  /3 width=5 by cnv_cpms_nta, cpcs_cprs_sn, ex4_2_intro/
]
qed-.

lemma nta_inv_lref_sn (h) (a) (G) (L):
      ∀X2,i. ❪G,L❫ ⊢ #↑i :[h,a] X2 →
      ∃∃I,K,T2,U2. ❪G,K❫ ⊢ #i :[h,a] T2 & ⇧*[1] T2 ≘ U2 & ❪G,K.ⓘ[I]❫ ⊢ U2 ⬌*[h] X2 & ❪G,K.ⓘ[I]❫ ⊢ X2 ![h,a] & L = K.ⓘ[I].
#h #a #G #L #X2 #i #H
elim (cnv_inv_cast … H) -H #X1 #HX2 #H1 #HX21 #H2
elim (cnv_inv_lref … H1) -H1 #I #K #Hi #H destruct
elim (cpms_inv_lref_sn … H2) -H2 *
[ #_ #H destruct
| #X #HX #HX1
  /3 width=9 by cnv_cpms_nta, cpcs_cprs_sn, ex5_4_intro/
]
qed-.

lemma nta_inv_lref_sn_drops_cnv (h) (a) (G) (L):
      ∀X2,i. ❪G,L❫ ⊢ #i :[h,a] X2 →
      ∨∨ ∃∃K,V,W,U. ⇩*[i] L ≘ K.ⓓV & ❪G,K❫ ⊢ V :[h,a] W & ⇧*[↑i] W ≘ U & ❪G,L❫ ⊢ U ⬌*[h] X2 & ❪G,L❫ ⊢ X2 ![h,a]
       | ∃∃K,W,U. ⇩*[i] L ≘ K. ⓛW & ❪G,K❫ ⊢ W ![h,a] & ⇧*[↑i] W ≘ U & ❪G,L❫ ⊢ U ⬌*[h] X2 & ❪G,L❫ ⊢ X2 ![h,a].
#h #a #G #L #X2 #i #H
elim (cnv_inv_cast … H) -H #X1 #HX2 #H1 #HX21 #H2
elim (cnv_inv_lref_drops … H1) -H1 #I #K #V #HLK #HV
elim (cpms_inv_lref1_drops … H2) -H2 *
[ #_ #H destruct
| #Y #X #W #H #HVW #HUX1
  lapply (drops_mono … H … HLK) -H #H destruct
  /4 width=8 by cnv_cpms_nta, cpcs_cprs_sn, ex5_4_intro, or_introl/
| #n #Y #X #U #H #HVU #HUX1 #H0 destruct
  lapply (drops_mono … H … HLK) -H #H destruct
  elim (lifts_total V (𝐔❨↑i❩)) #W #HVW
  lapply (cpms_lifts_bi … HVU (Ⓣ) … L … HVW … HUX1) -U
  [ /2 width=2 by drops_isuni_fwd_drop2/ ] #HWX1
  /4 width=9 by cprs_div, ex5_3_intro, or_intror/
]
qed-.

lemma nta_inv_bind_sn_cnv (h) (a) (p) (I) (G) (K) (X2):
      ∀V,T. ❪G,K❫ ⊢ ⓑ[p,I]V.T :[h,a] X2 →
      ∃∃U. ❪G,K❫ ⊢ V ![h,a] & ❪G,K.ⓑ[I]V❫ ⊢ T :[h,a] U & ❪G,K❫ ⊢ ⓑ[p,I]V.U ⬌*[h] X2 & ❪G,K❫ ⊢ X2 ![h,a].
#h #a #p * #G #K #X2 #V #T #H
elim (cnv_inv_cast … H) -H #X1 #HX2 #H1 #HX21 #H2
elim (cnv_inv_bind … H1) -H1 #HV #HT
[ elim (cpms_inv_abbr_sn_dx … H2) -H2 *
  [ #V0 #U #HV0 #HTU #H destruct
    /4 width=5 by cnv_cpms_nta, cprs_div, cpms_bind, ex4_intro/
  | #U #HTU #HX1U #H destruct
    /4 width=5 by cnv_cpms_nta, cprs_div, cpms_zeta, ex4_intro/
  ]
| elim (cpms_inv_abst_sn … H2) -H2 #V0 #U #HV0 #HTU #H destruct
  /4 width=5 by cnv_cpms_nta, cprs_div, cpms_bind, ex4_intro/
]
qed-.

(* Basic_1: uses: ty3_gen_appl *)
lemma nta_inv_appl_sn (h) (G) (L) (X2):
      ∀V,T. ❪G,L❫ ⊢ ⓐV.T :[h,𝟐] X2 →
      ∃∃p,W,U. ❪G,L❫ ⊢ V :[h,𝟐] W & ❪G,L❫ ⊢ T :[h,𝟐] ⓛ[p]W.U & ❪G,L❫ ⊢ ⓐV.ⓛ[p]W.U ⬌*[h] X2 & ❪G,L❫ ⊢ X2 ![h,𝟐].
#h #G #L #X2 #V #T #H
elim (cnv_inv_cast … H) -H #X #HX2 #H1 #HX2 #H2
elim (cnv_inv_appl … H1) #n #p #W #U #H <H -n #HV #HT #HVW #HTU
/5 width=11 by cnv_cpms_nta, cnv_cpms_conf_eq, cpcs_cprs_div, cpms_appl_dx, ex4_3_intro/
qed-.

(* Basic_2A1: uses: nta_fwd_pure1 *)
lemma nta_inv_pure_sn_cnv (h) (G) (L) (X2):
      ∀V,T. ❪G,L❫ ⊢ ⓐV.T :[h,𝛚] X2 →
      ∨∨ ∃∃p,W,U. ❪G,L❫ ⊢ V :[h,𝛚] W & ❪G,L❫ ⊢ T :[h,𝛚] ⓛ[p]W.U & ❪G,L❫ ⊢ ⓐV.ⓛ[p]W.U ⬌*[h] X2 & ❪G,L❫ ⊢ X2 ![h,𝛚]
       | ∃∃U. ❪G,L❫ ⊢ T :[h,𝛚] U & ❪G,L❫ ⊢ ⓐV.U ![h,𝛚] & ❪G,L❫ ⊢ ⓐV.U ⬌*[h] X2 & ❪G,L❫ ⊢ X2 ![h,𝛚].
#h #G #L #X2 #V #T #H
elim (cnv_inv_cast … H) -H #X1 #HX2 #H1 #HX21 #H
elim (cnv_inv_appl … H1) * [| #n ] #p #W0 #T0 #Hn #HV #HT #HW0 #HT0
[ lapply (cnv_cpms_trans … HT … HT0) #H0
  elim (cnv_inv_bind … H0) -H0 #_ #HU
  elim (cnv_fwd_cpm_SO … HU) #U0 #HU0 -HU
  lapply (cpms_step_dx … HT0 1 (ⓛ[p]W0.U0) ?) -HT0 [ /2 width=1 by cpm_bind/ ] #HT0
  lapply (cpms_appl_dx … V V … HT0) [ // ] #HTU0
  lapply (cnv_cpms_conf_eq … H1 … HTU0 … H) -H1 -H -HTU0 #HU0X1
  /4 width=8 by cnv_cpms_nta, cpcs_cprs_div, ex4_3_intro, or_introl/
| elim (cnv_cpms_fwd_appl_sn_decompose …  H1 … H) -H1 -H #X0 #_ #H #HX01
  elim (cpms_inv_plus … 1 n … HT0) #U #HTU #HUT0
  lapply (cnv_cpms_trans … HT … HTU) #HU
  lapply (cnv_cpms_conf_eq … HT … HTU … H) -H #HUX0
  @or_intror @(ex4_intro … U … HX2) -HX2
  [ /2 width=1 by cnv_cpms_nta/
  | /4 width=7 by cnv_appl, lt_to_le/
  | /4 width=3 by cpcs_trans, cpcs_cprs_div, cpcs_flat/
  ]
]
qed-.

(* Basic_2A1: uses: nta_inv_cast1 *)
lemma nta_inv_cast_sn (h) (a) (G) (L) (X2):
      ∀U,T. ❪G,L❫ ⊢ ⓝU.T :[h,a] X2 →
      ∧∧ ❪G,L❫ ⊢ T :[h,a] U & ❪G,L❫ ⊢ U ⬌*[h] X2 & ❪G,L❫ ⊢ X2 ![h,a].
#h #a #G #L #X2 #U #T #H
elim (cnv_inv_cast … H) -H #X0 #HX2 #H1 #HX20 #H2
elim (cnv_inv_cast … H1) #X #HU #HT #HUX #HTX
elim (cpms_inv_cast1 … H2) -H2 [ * || * ]
[ #U0 #T0 #HU0 #HT0 #H destruct -HU -HU0
  lapply (cnv_cpms_conf_eq … HT … HTX … HT0) -HT -HT0 -HTX #HXT0
  lapply (cprs_step_dx … HX20 T0 ?) -HX20 [ /2 width=1 by cpm_eps/ ] #HX20
| #HTX0 -HU
  lapply (cnv_cpms_conf_eq … HT … HTX … HTX0) -HT -HTX -HTX0 #HX0
| #m #HUX0 #H destruct -HT -HTX
  lapply (cnv_cpms_conf_eq … HU … HUX … HUX0) -HU -HUX0 #HX0
]
/4 width=3 by cpcs_cprs_div, cpcs_cprs_step_sn, and3_intro/
qed-.

(* Basic_1: uses: ty3_gen_cast *)
lemma nta_inv_cast_sn_old (h) (a) (G) (L) (X2):
      ∀T0,T1. ❪G,L❫ ⊢ ⓝT1.T0 :[h,a] X2 →
      ∃∃T2. ❪G,L❫ ⊢ T0 :[h,a] T1 & ❪G,L❫ ⊢ T1 :[h,a] T2 & ❪G,L❫ ⊢ ⓝT2.T1 ⬌*[h] X2 & ❪G,L❫ ⊢ X2 ![h,a].
#h #a #G #L #X2 #T0 #T1 #H
elim (cnv_inv_cast … H) -H #X0 #HX2 #H1 #HX20 #H2
elim (cnv_inv_cast … H1) #X #HT1 #HT0 #HT1X #HT0X
elim (cpms_inv_cast1 … H2) -H2 [ * || * ]
[ #U1 #U0 #HTU1 #HTU0 #H destruct
  lapply (cnv_cpms_conf_eq … HT0 … HT0X … HTU0) -HT0 -HT0X -HTU0 #HXU0
  /5 width=5 by cnv_cpms_nta, cpcs_cprs_div, cpcs_cprs_step_sn, cpcs_flat, ex4_intro/
| #HTX0
  elim (cnv_nta_sn … HT1) -HT1 #U1 #HTU1
  lapply (cnv_cpms_conf_eq … HT0 … HT0X … HTX0) -HT0 -HT0X -HTX0 #HX0
  lapply (cprs_step_sn … (ⓝU1.T1) … HT1X) -HT1X [ /2 width=1 by cpm_eps/ ] #HT1X
  /4 width=5 by cpcs_cprs_div, cpcs_cprs_step_sn, ex4_intro/
| #n #HT1X0 #H destruct -X -HT0
  elim (cnv_nta_sn … HT1) -HT1 #U1 #HTU1
  /4 width=5 by cprs_div, cpms_eps, ex4_intro/
]
qed-.

(* Basic_1: uses: ty3_gen_lift *)
(* Note: "❪G, L❫ ⊢ U2 ⬌*[h] X2" can be "❪G, L❫ ⊢ X2 ➡*[h] U2" *)
lemma nta_inv_lifts_sn (h) (a) (G):
      ∀L,T2,X2. ❪G,L❫ ⊢ T2 :[h,a] X2 →
      ∀b,f,K. ⇩*[b,f] L ≘ K → ∀T1. ⇧*[f] T1 ≘ T2 →
      ∃∃U1,U2. ❪G,K❫ ⊢ T1 :[h,a] U1 & ⇧*[f] U1 ≘ U2 & ❪G,L❫ ⊢ U2 ⬌*[h] X2 & ❪G,L❫ ⊢ X2 ![h,a].
#h #a #G #L #T2 #X2 #H #b #f #K #HLK #T1 #HT12
elim (cnv_inv_cast … H) -H #U2 #HX2 #HT2 #HXU2 #HTU2
lapply (cnv_inv_lifts … HT2 … HLK … HT12) -HT2 #HT1
elim (cpms_inv_lifts_sn … HTU2 … HLK … HT12) -T2 -HLK #U1 #HU12 #HTU1
/3 width=5 by cnv_cpms_nta, cpcs_cprs_sn, ex4_2_intro/
qed-.

(* Forward lemmas based on preservation *************************************)

(* Basic_1: was: ty3_unique *)
theorem nta_mono (h) (a) (G) (L) (T):
        ∀U1. ❪G,L❫ ⊢ T :[h,a] U1 → ∀U2. ❪G,L❫ ⊢ T :[h,a] U2 → ❪G,L❫  ⊢ U1 ⬌*[h] U2.
#h #a #G #L #T #U1 #H1 #U2 #H2
elim (cnv_inv_cast … H1) -H1 #X1 #_ #_ #HUX1 #HTX1
elim (cnv_inv_cast … H2) -H2 #X2 #_ #HT #HUX2 #HTX2
lapply (cnv_cpms_conf_eq … HT … HTX1 … HTX2) -T #HX12
/3 width=3 by cpcs_cprs_div, cpcs_cprs_step_sn/
qed-.

(* Advanced properties ******************************************************)

(* Basic_1: uses: ty3_sconv_pc3 *)
lemma nta_cpcs_bi (h) (a) (G) (L):
      ∀T1,U1. ❪G,L❫ ⊢ T1 :[h,a] U1 → ∀T2,U2. ❪G,L❫ ⊢ T2 :[h,a] U2 →
      ❪G,L❫ ⊢ T1 ⬌*[h] T2 → ❪G,L❫ ⊢ U1 ⬌*[h] U2.
#h #a #G #L #T1 #U1 #HTU1 #T2 #U2 #HTU2 #HT12
elim (cpcs_inv_cprs … HT12) -HT12 #T0 #HT10 #HT02
/3 width=6 by nta_mono, nta_cprs_conf/
qed-.
