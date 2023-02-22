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

include "ground/lib/arith_2b.ma".
include "basic_2/rt_transition/lpr_lpr.ma".
include "basic_2/rt_computation/cpms_lsubr.ma".
include "basic_2/rt_computation/cpms_cpms.ma".
include "basic_2/dynamic/cnv_drops.ma".
include "basic_2/dynamic/cnv_preserve_sub.ma".

(* CONTEXT-SENSITIVE NATIVE VALIDITY FOR TERMS ******************************)

(* Sub diamond propery with t-bound rt-transition for terms *****************)

fact cnv_cpm_conf_lpr_atom_atom_aux (h) (G) (L1) (L2) (I):
     ∃∃T. ❨G,L1❩ ⊢ ⓪[I] ➡*[h,0] T & ❨G,L2❩ ⊢ ⓪[I] ➡*[h,0] T.
/2 width=3 by ex2_intro/ qed-.

fact cnv_cpm_conf_lpr_atom_ess_aux (h) (G) (L1) (L2) (s):
     ∃∃T. ❨G,L1❩ ⊢ ⋆s ➡*[h,1] T & ❨G,L2❩ ⊢ ⋆(⫯[h]s) ➡*[h,0] T.
/3 width=3 by cpm_cpms, ex2_intro/ qed-.

fact cnv_cpm_conf_lpr_atom_delta_aux (h) (a) (G) (L) (i):
     (∀G0,L0,T0. ❨G,L,#i❩ > ❨G0,L0,T0❩ → IH_cnv_cpms_conf_lpr h a G0 L0 T0) →
     ❨G,L❩⊢#i![h,a] →
     ∀K,V. ⇩[i]L ≘ K.ⓓV →
     ∀n,XV. ❨G,K❩ ⊢ V ➡[h,n] XV →
     ∀X. ⇧[↑i]XV ≘ X →
     ∀L1. ❨G,L❩ ⊢ ➡[h,0] L1 → ∀L2. ❨G,L❩ ⊢ ➡[h,0] L2 →
     ∃∃T. ❨G,L1❩ ⊢ #i ➡*[h,n] T & ❨G,L2❩ ⊢ X ➡*[h,0] T.
#h #a #G #L #i #IH #HT #K #V #HLK #n #XV #HVX #X #HXV #L1 #HL1 #L2 #HL2
lapply (cnv_inv_lref_pair … HT … HLK) -HT #HV
elim (lpr_drops_conf … HLK … HL1) -HL1 // #Y1 #H1 #HLK1
elim (lpr_inv_pair_sn … H1) -H1 #K1 #V1 #HK1 #HV1 #H destruct
elim (lpr_drops_conf … HLK … HL2) -HL2 // #Y2 #H2 #HLK2
elim (lpr_inv_pair_sn … H2) -H2 #K2 #V2 #HK2 #_ #H destruct
lapply (drops_isuni_fwd_drop2 … HLK2) -V2 // #HLK2
lapply (fqup_lref (Ⓣ) … G … HLK) -HLK #HLK
elim (cnv_cpm_conf_lpr_sub … IH … HV1 … HVX … HK1 … HK2) [|*: /2 width=1 by fqup_fpbg/ ] -L -K -V
<minus_O_n <minus_n_O #V #HV1 #HVX
elim (cpms_lifts_sn … HVX … HLK2 … HXV) -XV -HLK2 #XV #HVX #HXV
/3 width=6 by cpms_delta_drops, ex2_intro/
qed-.

fact cnv_cpm_conf_lpr_atom_ell_aux (h) (a) (G) (L) (i):
     (∀G0,L0,T0. ❨G,L,#i❩ > ❨G0,L0,T0❩ → IH_cnv_cpms_conf_lpr h a G0 L0 T0) →
     ❨G,L❩⊢#i![h,a] →
     ∀K,W. ⇩[i]L ≘ K.ⓛW →
     ∀n,XW. ❨G,K❩ ⊢ W ➡[h,n] XW →
     ∀X. ⇧[↑i]XW ≘ X →
     ∀L1. ❨G,L❩ ⊢ ➡[h,0] L1 → ∀L2. ❨G,L❩ ⊢ ➡[h,0] L2 →
     ∃∃T. ❨G,L1❩ ⊢ #i ➡*[h,↑n] T & ❨G,L2❩ ⊢ X ➡*[h,0] T.
#h #a #G #L #i #IH #HT #K #W #HLK #n #XW #HWX #X #HXW #L1 #HL1 #L2 #HL2
lapply (cnv_inv_lref_pair … HT … HLK) -HT #HW
elim (lpr_drops_conf … HLK … HL1) -HL1 // #Y1 #H1 #HLK1
elim (lpr_inv_pair_sn … H1) -H1 #K1 #W1 #HK1 #HW1 #H destruct
elim (lpr_drops_conf … HLK … HL2) -HL2 // #Y2 #H2 #HLK2
elim (lpr_inv_pair_sn … H2) -H2 #K2 #W2 #HK2 #_ #H destruct
lapply (drops_isuni_fwd_drop2 … HLK2) -W2 // #HLK2
lapply (fqup_lref (Ⓣ) … G … HLK) -HLK #HLK
elim (cnv_cpm_conf_lpr_sub … IH … HW1 … HWX … HK1 … HK2) [|*: /2 width=1 by fqup_fpbg/ ] -L -K -W
<minus_O_n <minus_n_O #W #HW1 #HWX
elim (cpms_lifts_sn … HWX … HLK2 … HXW) -XW -HLK2 #XW #HWX #HXW
/3 width=6 by cpms_ell_drops, ex2_intro/
qed-.

fact cnv_cpm_conf_lpr_delta_delta_aux (h) (a) (I) (G) (L) (i):
     (∀G0,L0,T0. ❨G,L,#i❩ > ❨G0,L0,T0❩ → IH_cnv_cpms_conf_lpr h a G0 L0 T0) →
     ❨G,L❩⊢#i![h,a] →
     ∀K1,V1. ⇩[i]L ≘ K1.ⓑ[I]V1 → ∀K2,V2. ⇩[i]L ≘ K2.ⓑ[I]V2 →
     ∀n1,XV1. ❨G,K1❩ ⊢ V1 ➡[h,n1] XV1 → ∀n2,XV2. ❨G,K2❩ ⊢ V2 ➡[h,n2] XV2 →
     ∀X1. ⇧[↑i]XV1 ≘ X1 → ∀X2. ⇧[↑i]XV2 ≘ X2 →
     ∀L1. ❨G,L❩ ⊢ ➡[h,0] L1 → ∀L2. ❨G,L❩ ⊢ ➡[h,0] L2 →
     ∃∃T. ❨G,L1❩ ⊢ X1 ➡*[h,n2-n1] T & ❨G,L2❩ ⊢ X2 ➡*[h,n1-n2] T.
#h #a #I #G #L #i #IH #HT
#K #V #HLK #Y #X #HLY #n1 #XV1 #HVX1 #n2 #XV2 #HVX2 #X1 #HXV1 #X2 #HXV2
#L1 #HL1 #L2 #HL2
lapply (drops_mono … HLY … HLK) -HLY #H destruct
lapply (cnv_inv_lref_pair … HT … HLK) -HT #HV
elim (lpr_drops_conf … HLK … HL1) -HL1 // #Y1 #H1 #HLK1
elim (lpr_inv_pair_sn … H1) -H1 #K1 #V1 #HK1 #_ #H destruct
lapply (drops_isuni_fwd_drop2 … HLK1) -V1 // #HLK1
elim (lpr_drops_conf … HLK … HL2) -HL2 // #Y2 #H2 #HLK2
elim (lpr_inv_pair_sn … H2) -H2 #K2 #V2 #HK2 #_ #H destruct
lapply (drops_isuni_fwd_drop2 … HLK2) -V2 // #HLK2
lapply (fqup_lref (Ⓣ) … G … HLK) -HLK #HLK
elim (cnv_cpm_conf_lpr_sub … IH … HVX1 … HVX2 … HK1 … HK2) [|*: /2 width=1 by fqup_fpbg/ ] -L -K -V
#V #HVX1 #HVX2
elim (cpms_lifts_sn … HVX1 … HLK1 … HXV1) -XV1 -HLK1 #W1 #HVW1 #HXW1
/3 width=11 by cpms_lifts_bi, ex2_intro/
qed-.

fact cnv_cpm_conf_lpr_delta_ell_aux (L) (K1) (K2) (V) (W) (i):
     ⇩[i]L ≘ K1.ⓓV → ⇩[i]L ≘ K2.ⓛW → ⊥.
#L #K1 #K2 #V #W #i #HLK1 #HLK2
lapply (drops_mono … HLK2 … HLK1) -L -i #H destruct
qed-.

fact cnv_cpm_conf_lpr_bind_bind_aux (h) (a) (p) (I) (G) (L) (V) (T):
     (∀G0,L0,T0. ❨G,L,ⓑ[p,I]V.T❩ > ❨G0,L0,T0❩ → IH_cnv_cpms_conf_lpr h a G0 L0 T0) →
     ❨G,L❩ ⊢ ⓑ[p,I]V.T ![h,a] →
     ∀V1. ❨G,L❩ ⊢ V ➡[h,0] V1 → ∀V2. ❨G,L❩ ⊢ V ➡[h,0] V2 →
     ∀n1,T1. ❨G,L.ⓑ[I]V❩ ⊢ T ➡[h,n1] T1 → ∀n2,T2. ❨G,L.ⓑ[I]V❩ ⊢ T ➡[h,n2] T2 →
     ∀L1. ❨G,L❩ ⊢ ➡[h,0] L1 → ∀L2. ❨G,L❩ ⊢ ➡[h,0] L2 →
     ∃∃T. ❨G,L1❩ ⊢ ⓑ[p,I]V1.T1 ➡*[h,n2-n1] T & ❨G,L2❩ ⊢ ⓑ[p,I]V2.T2 ➡*[h,n1-n2] T.
#h #a #p #I #G0 #L0 #V0 #T0 #IH #H0
#V1 #HV01 #V2 #HV02 #n1 #T1 #HT01 #n2 #T2 #HT02
#L1 #HL01 #L2 #HL02
elim (cnv_inv_bind … H0) -H0 #HV0 #HT0
elim (cpr_conf_lpr … HV01 … HV02 … HL01 … HL02) #V #HV1 #HV2
elim (cnv_cpm_conf_lpr_sub … IH … HT01 … HT02 (L1.ⓑ[I]V1) … (L2.ⓑ[I]V2)) [|*: /2 width=1 by fqup_fpbg, lpr_pair/ ]
#T #HT1 #HT2 -L0 -V0 -T0
/3 width=5 by cpms_bind_dx, ex2_intro/
qed-.

fact cnv_cpm_conf_lpr_bind_zeta_aux (h) (a) (G) (L) (V) (T):
     (∀G0,L0,T0. ❨G,L,+ⓓV.T❩ > ❨G0,L0,T0❩ → IH_cnv_cpms_conf_lpr h a G0 L0 T0) →
     ❨G,L❩ ⊢ +ⓓV.T ![h,a] →
     ∀V1. ❨G,L❩ ⊢V ➡[h,0] V1 → ∀n1,T1. ❨G,L.ⓓV❩ ⊢ T ➡[h,n1] T1 →
     ∀T2. ⇧[1]T2 ≘ T → ∀n2,XT2. ❨G,L❩ ⊢ T2 ➡[h,n2] XT2 →
     ∀L1. ❨G,L❩ ⊢ ➡[h,0] L1 → ∀L2. ❨G,L❩ ⊢ ➡[h,0] L2 →
     ∃∃T. ❨G,L1❩ ⊢ +ⓓV1.T1 ➡*[h,n2-n1] T & ❨G,L2❩ ⊢ XT2 ➡*[h,n1-n2] T.
#h #a #G0 #L0 #V0 #T0 #IH #H0
#V1 #HV01 #n1 #T1 #HT01 #T2 #HT20 #n2 #XT2 #HXT2
#L1 #HL01 #L2 #HL02
elim (cnv_inv_bind … H0) -H0 #_ #HT0
lapply (cnv_inv_lifts … HT0 (Ⓣ) … L0 … HT20) -HT0
[ /3 width=3 by drops_refl, drops_drop/ ] #HT2
elim (cpm_inv_lifts_sn … HT01 (Ⓣ) … L0 … HT20) -HT01
[| /3 width=1 by drops_refl, drops_drop/ ] #XT1 #HXT1 #HXT12
elim (cnv_cpm_conf_lpr_sub … IH … HXT12 … HXT2 … HL01 … HL02)
[|*: /3 width=1 by fqup_fpbg, fqup_zeta/ ] -L0 -T0 -V0 #T #HT1 #HT2
/3 width=3 by cpms_zeta, ex2_intro/
qed-.

fact cnv_cpm_conf_lpr_zeta_zeta_aux (h) (a) (G) (L) (V) (T):
     (∀G0,L0,T0. ❨G,L,+ⓓV.T❩ > ❨G0,L0,T0❩ → IH_cnv_cpms_conf_lpr h a G0 L0 T0) →
     ❨G,L❩ ⊢ +ⓓV.T ![h,a] →
     ∀T1. ⇧[1]T1 ≘ T → ∀T2. ⇧[1]T2 ≘ T →
     ∀n1,XT1. ❨G,L❩ ⊢ T1 ➡[h,n1] XT1 → ∀n2,XT2. ❨G,L❩ ⊢ T2 ➡[h,n2] XT2 →
     ∀L1. ❨G,L❩ ⊢ ➡[h,0] L1 → ∀L2. ❨G,L❩ ⊢ ➡[h,0] L2 →
     ∃∃T. ❨G,L1❩ ⊢ XT1 ➡*[h,n2-n1] T & ❨G,L2❩ ⊢ XT2 ➡*[h,n1-n2] T.
#h #a #G0 #L0 #V0 #T0 #IH #H0
#T1 #HT10 #T2 #HT20 #n1 #XT1 #HXT1 #n2 #XT2 #HXT2
#L1 #HL01 #L2 #HL02
elim (cnv_inv_bind … H0) -H0 #_ #HT0
lapply (lifts_inj … HT10 … HT20) -HT10 #H destruct
lapply (cnv_inv_lifts … HT0 (Ⓣ) … L0 … HT20) -HT0
[ /3 width=3 by drops_refl, drops_drop/ ] #HT2
elim (cnv_cpm_conf_lpr_sub … IH … HXT1 … HXT2 … HL01 … HL02)
[|*: /3 width=1 by fqup_fpbg, fqup_zeta/ ] -L0 -T0 #T #HT1 #HT2
/2 width=3 by ex2_intro/
qed-.

fact cnv_cpm_conf_lpr_appl_appl_aux (h) (a) (G) (L) (V) (T):
     (∀G0,L0,T0. ❨G,L,ⓐV.T❩ > ❨G0,L0,T0❩ → IH_cnv_cpms_conf_lpr h a G0 L0 T0) →
     ❨G,L❩ ⊢ ⓐV.T ![h,a] →
     ∀V1. ❨G,L❩ ⊢ V ➡[h,0] V1 → ∀V2. ❨G,L❩ ⊢ V ➡[h,0] V2 →
     ∀n1,T1. ❨G,L❩ ⊢ T ➡[h,n1] T1 → ∀n2,T2. ❨G,L❩ ⊢ T ➡[h,n2] T2 →
     ∀L1. ❨G,L❩ ⊢ ➡[h,0] L1 → ∀L2. ❨G,L❩ ⊢ ➡[h,0] L2 →
     ∃∃T. ❨G,L1❩ ⊢ ⓐV1.T1 ➡*[h,n2-n1] T & ❨G,L2❩ ⊢ ⓐV2.T2 ➡*[h,n1-n2] T.
#h #a #G0 #L0 #V0 #T0 #IH #H0
#V1 #HV01 #V2 #HV02 #n1 #T1 #HT01 #n2 #T2 #HT02
#L1 #HL01 #L2 #HL02
elim (cnv_inv_appl … H0) -H0 #n0 #p0 #X01 #X02 #_ #HV0 #HT0 #_ #_ -n0 -p0 -X01 -X02
elim (cpr_conf_lpr … HV01 … HV02 … HL01 … HL02) #V #HV1 #HV2
elim (cnv_cpm_conf_lpr_sub … IH … HT01 … HT02 … HL01 … HL02) [|*: /2 width=1 by fqup_fpbg/ ]
#T #HT1 #HT2 -L0 -V0 -T0
/3 width=5 by cpms_appl_dx, ex2_intro/
qed-.

fact cnv_cpm_conf_lpr_appl_beta_aux (h) (a) (p) (G) (L) (V) (W) (T):
     (∀G0,L0,T0. ❨G,L,ⓐV.ⓛ[p]W.T❩ > ❨G0,L0,T0❩ → IH_cnv_cpms_conf_lpr h a G0 L0 T0) →
     ❨G,L❩ ⊢ ⓐV.ⓛ[p]W.T ![h,a] →
     ∀V1. ❨G,L❩ ⊢ V ➡[h,0] V1 → ∀V2. ❨G,L❩ ⊢ V ➡[h,0] V2 →
     ∀W2. ❨G,L❩ ⊢ W ➡[h,0] W2 →
     ∀n1,T1. ❨G,L❩ ⊢ ⓛ[p]W.T ➡[h,n1] T1 → ∀n2,T2. ❨G,L.ⓛW❩ ⊢ T ➡[h,n2] T2 →
     ∀L1. ❨G,L❩ ⊢ ➡[h,0] L1 → ∀L2. ❨G,L❩ ⊢ ➡[h,0] L2 →
     ∃∃T. ❨G,L1❩ ⊢ ⓐV1.T1 ➡*[h,n2-n1] T & ❨G,L2❩ ⊢ ⓓ[p]ⓝW2.V2.T2 ➡*[h,n1-n2] T.
#h #a #p #G0 #L0 #V0 #W0 #T0 #IH #H0
#V1 #HV01 #V2 #HV02 #W2 #HW02 #n1 #X #HX #n2 #T2 #HT02
#L1 #HL01 #L2 #HL02
elim (cnv_inv_appl … H0) -H0 #n0 #p0 #X01 #X02 #_ #HV0 #H0 #_ #_ -n0 -p0 -X01 -X02
elim (cnv_inv_bind … H0) -H0 #HW0 #HT0
elim (cpm_inv_abst1 … HX) -HX #W1 #T1 #HW01 #HT01 #H destruct
elim (cpr_conf_lpr … HV01 … HV02 … HL01 … HL02) #V #HV1 #HV2
elim (cpr_conf_lpr … HW01 … HW02 … HL01 … HL02) #W #HW1 #HW2
elim (cnv_cpm_conf_lpr_sub … IH … HT01 … HT02 (L1.ⓛW1) … (L2.ⓛW2)) [|*: /2 width=1 by fqup_fpbg, lpr_pair/ ]
#T #HT1 #HT2 -L0 -V0 -W0 -T0
lapply (lsubr_cpms_trans … HT2 (L2.ⓓⓝW2.V2) ?) -HT2 [ /2 width=1 by lsubr_beta/ ] #HT2
/4 width=5 by cpms_beta_dx, cpms_bind_dx, cpm_cast, ex2_intro/
qed-.

fact cnv_cpm_conf_lpr_appl_theta_aux (h) (a) (p) (G) (L) (V) (W) (T):
     (∀G0,L0,T0. ❨G,L,ⓐV.ⓓ[p]W.T❩ > ❨G0,L0,T0❩ → IH_cnv_cpms_conf_lpr h a G0 L0 T0) →
     ❨G,L❩ ⊢ ⓐV.ⓓ[p]W.T ![h,a] →
     ∀V1. ❨G,L❩ ⊢ V ➡[h,0] V1 → ∀V2. ❨G,L❩ ⊢ V ➡[h,0] V2 →
     ∀W2. ❨G,L❩ ⊢ W ➡[h,0] W2 →
     ∀n1,T1. ❨G,L❩ ⊢ ⓓ[p]W.T ➡[h,n1] T1 → ∀n2,T2. ❨G,L.ⓓW❩ ⊢ T ➡[h,n2] T2 →
     ∀U2. ⇧[1]V2 ≘ U2 →
     ∀L1. ❨G,L❩ ⊢ ➡[h,0] L1 → ∀L2. ❨G,L❩ ⊢ ➡[h,0] L2 →
     ∃∃T. ❨G,L1❩ ⊢ ⓐV1.T1 ➡*[h,n2-n1] T & ❨G,L2❩ ⊢ ⓓ[p]W2.ⓐU2.T2 ➡*[h,n1-n2] T.
#h #a #p #G0 #L0 #V0 #W0 #T0 #IH #H0
#V1 #HV01 #V2 #HV02 #W2 #HW02 #n1 #X #HX #n2 #T2 #HT02 #U2 #HVU2
#L1 #HL01 #L2 #HL02
elim (cnv_inv_appl … H0) -H0 #n0 #p0 #X01 #X02 #_ #HV0 #H0 #_ #_ -n0 -p0 -X01 -X02
elim (cnv_inv_bind … H0) -H0 #HW0 #HT0
elim (cpr_conf_lpr … HV01 … HV02 … HL01 … HL02) #V #HV1 #HV2
elim (cpm_inv_abbr1 … HX) -HX *
[ #W1 #T1 #HW01 #HT01 #H destruct
  elim (cpm_lifts_sn … HV2 (Ⓣ) … (L2.ⓓW2) … HVU2) -HV2 -HVU2 [| /3 width=1 by drops_refl, drops_drop/ ] #U #HVU #HU2
  elim (cpr_conf_lpr … HW01 … HW02 … HL01 … HL02) #W #HW1 #HW2
  elim (cnv_cpm_conf_lpr_sub … IH … HT01 … HT02 (L1.ⓓW1) … (L2.ⓓW2)) [|*: /2 width=1 by fqup_fpbg, lpr_pair/ ]
  #T #HT1 #HT2 -L0 -V0 -W0 -T0
  /4 width=7 by cpms_theta_dx, cpms_appl_dx, cpms_bind_dx, ex2_intro/
| #X0 #HXT0 #H1X0 #H destruct
  lapply (cnv_inv_lifts … HT0 (Ⓣ) … L0 … HXT0) -HT0 [ /3 width=3 by drops_refl, drops_drop/ ] #H2X0
  elim (cpm_inv_lifts_sn … HT02 (Ⓣ) … L0 … HXT0) -HT02 [| /3 width=1 by drops_refl, drops_drop/ ] #X2 #HXT2 #HX02
  elim (cnv_cpm_conf_lpr_sub … IH … H1X0 … HX02 … HL01 … HL02)
  [|*: /4 width=5 by fqup_fpbg, fqup_strap1, fqu_drop/ ] #T #HT1 #HT2 -L0 -V0 -W0 -T0
  /4 width=8 by cpms_zeta, cpms_appl_dx, lifts_flat, ex2_intro/
]
qed-.

fact cnv_cpm_conf_lpr_beta_beta_aux (h) (a) (p) (G) (L) (V) (W) (T):
     (∀G0,L0,T0. ❨G,L,ⓐV.ⓛ[p]W.T❩ > ❨G0,L0,T0❩ → IH_cnv_cpms_conf_lpr h a G0 L0 T0) →
     ❨G,L❩ ⊢ ⓐV.ⓛ[p]W.T ![h,a] →
     ∀V1. ❨G,L❩ ⊢ V ➡[h,0] V1 → ∀V2. ❨G,L❩ ⊢ V ➡[h,0] V2 →
     ∀W1. ❨G,L❩ ⊢ W ➡[h,0] W1 → ∀W2. ❨G,L❩ ⊢ W ➡[h,0] W2 →
     ∀n1,T1. ❨G,L.ⓛW❩ ⊢ T ➡[h,n1] T1 → ∀n2,T2. ❨G,L.ⓛW❩ ⊢ T ➡[h,n2] T2 →
     ∀L1. ❨G,L❩ ⊢ ➡[h,0] L1 → ∀L2. ❨G,L❩ ⊢ ➡[h,0] L2 →
     ∃∃T. ❨G,L1❩ ⊢ ⓓ[p]ⓝW1.V1.T1 ➡*[h,n2-n1] T & ❨G,L2❩ ⊢ ⓓ[p]ⓝW2.V2.T2 ➡*[h,n1-n2] T.
#h #a #p #G0 #L0 #V0 #W0 #T0 #IH #H0
#V1 #HV01 #V2 #HV02 #W1 #HW01 #W2 #HW02 #n1 #T1 #HT01 #n2 #T2 #HT02
#L1 #HL01 #L2 #HL02
elim (cnv_inv_appl … H0) -H0 #n0 #p0 #X01 #X02 #_ #HV0 #H0 #_ #_ -n0 -p0 -X01 -X02
elim (cnv_inv_bind … H0) -H0 #HW0 #HT0
elim (cpr_conf_lpr … HV01 … HV02 … HL01 … HL02) #V #HV1 #HV2
elim (cpr_conf_lpr … HW01 … HW02 … HL01 … HL02) #W #HW1 #HW2
elim (cnv_cpm_conf_lpr_sub … IH … HT01 … HT02 (L1.ⓛW1) … (L2.ⓛW2)) [|*: /2 width=1 by fqup_fpbg, lpr_pair/ ]
#T #HT1 #HT2 -L0 -V0 -W0 -T0
lapply (lsubr_cpms_trans … HT1 (L1.ⓓⓝW1.V1) ?) -HT1 /2 width=1 by lsubr_beta/ #HT1
lapply (lsubr_cpms_trans … HT2 (L2.ⓓⓝW2.V2) ?) -HT2 /2 width=1 by lsubr_beta/ #HT2
/4 width=5 by cpms_bind_dx, cpm_eps, ex2_intro/
qed-.

fact cnv_cpm_conf_lpr_theta_theta_aux (h) (a) (p) (G) (L) (V) (W) (T):
     (∀G0,L0,T0. ❨G,L,ⓐV.ⓓ[p]W.T❩ > ❨G0,L0,T0❩ → IH_cnv_cpms_conf_lpr h a G0 L0 T0) →
     ❨G,L❩ ⊢ ⓐV.ⓓ[p]W.T ![h,a] →
     ∀V1. ❨G,L❩ ⊢ V ➡[h,0] V1 → ∀V2. ❨G,L❩ ⊢ V ➡[h,0] V2 →
     ∀W1. ❨G,L❩ ⊢ W ➡[h,0] W1 → ∀W2. ❨G,L❩ ⊢ W ➡[h,0] W2 →
     ∀n1,T1. ❨G,L.ⓓW❩ ⊢ T ➡[h,n1] T1 → ∀n2,T2. ❨G,L.ⓓW❩ ⊢ T ➡[h,n2] T2 →
     ∀U1. ⇧[1]V1 ≘ U1 → ∀U2. ⇧[1]V2 ≘ U2 →
     ∀L1. ❨G,L❩ ⊢ ➡[h,0] L1 → ∀L2. ❨G,L❩ ⊢ ➡[h,0] L2 →
     ∃∃T. ❨G,L1❩ ⊢ ⓓ[p]W1.ⓐU1.T1 ➡*[h,n2-n1] T & ❨G,L2❩ ⊢ ⓓ[p]W2.ⓐU2.T2 ➡*[h,n1-n2] T.
#h #a #p #G0 #L0 #V0 #W0 #T0 #IH #H0
#V1 #HV01 #V2 #HV02 #W1 #HW01 #W2 #HW02 #n1 #T1 #HT01 #n2 #T2 #HT02 #U1 #HVU1 #U2 #HVU2
#L1 #HL01 #L2 #HL02
elim (cnv_inv_appl … H0) -H0 #n0 #p0 #X01 #X02 #_ #HV0 #H0 #_ #_ -n0 -p0 -X01 -X02
elim (cnv_inv_bind … H0) -H0 #HW0 #HT0
elim (cpr_conf_lpr … HV01 … HV02 … HL01 … HL02) #V #HV1 #HV2
elim (cpr_conf_lpr … HW01 … HW02 … HL01 … HL02) #W #HW1 #HW2
elim (cnv_cpm_conf_lpr_sub … IH … HT01 … HT02 (L1.ⓓW1) … (L2.ⓓW2)) [|*: /2 width=1 by fqup_fpbg, lpr_pair/ ]
#T #HT1 #HT2 -L0 -V0 -W0 -T0
elim (cpm_lifts_sn … HV1 (Ⓣ) … (L1.ⓓW1) … HVU1) -V1 [| /3 width=1 by drops_refl, drops_drop/ ] #U #HVU #HU1
lapply (cpm_lifts_bi … HV2 (Ⓣ) … (L2.ⓓW2) … HVU2 … HVU) -V2 -V [ /3 width=1 by drops_refl, drops_drop/ ] #HU2
/4 width=7 by cpms_appl_dx, cpms_bind_dx, ex2_intro/
qed-.

fact cnv_cpm_conf_lpr_cast_cast_aux (h) (a) (G) (L) (V) (T):
     (∀G0,L0,T0. ❨G,L,ⓝV.T❩ > ❨G0,L0,T0❩ → IH_cnv_cpms_conf_lpr h a G0 L0 T0) →
     ❨G,L❩ ⊢ ⓝV.T ![h,a] →
     ∀n1,V1. ❨G,L❩ ⊢ V ➡[h,n1] V1 → ∀n2,V2. ❨G,L❩ ⊢ V ➡[h,n2] V2 →
     ∀T1. ❨G,L❩ ⊢ T ➡[h,n1] T1 → ∀T2. ❨G,L❩ ⊢ T ➡[h,n2] T2 →
     ∀L1. ❨G,L❩ ⊢ ➡[h,0] L1 → ∀L2. ❨G,L❩ ⊢ ➡[h,0] L2 →
     ∃∃T. ❨G,L1❩ ⊢ ⓝV1.T1 ➡*[h,n2-n1] T & ❨G,L2❩ ⊢ ⓝV2.T2 ➡*[h,n1-n2] T.
#h #a #G0 #L0 #V0 #T0 #IH #H0
#n1 #V1 #HV01 #n2 #V2 #HV02 #T1 #HT01 #T2 #HT02
#L1 #HL01 #L2 #HL02
elim (cnv_inv_cast … H0) -H0 #X0 #HV0 #HT0 #_ #_ -X0
elim (cnv_cpm_conf_lpr_sub … IH … HV01 … HV02 … HL01 … HL02) [|*: /2 width=1 by fqup_fpbg/ ]
elim (cnv_cpm_conf_lpr_sub … IH … HT01 … HT02 … HL01 … HL02) [|*: /2 width=1 by fqup_fpbg/ ]
#T #HT1 #HT2 #V #HV1 #HV2 -L0 -V0 -T0
/3 width=5 by cpms_cast, ex2_intro/
qed-.

fact cnv_cpm_conf_lpr_cast_epsilon_aux (h) (a) (G) (L) (V) (T):
     (∀G0,L0,T0. ❨G,L,ⓝV.T❩ > ❨G0,L0,T0❩ → IH_cnv_cpms_conf_lpr h a G0 L0 T0) →
     ❨G,L❩ ⊢ ⓝV.T ![h,a] →
     ∀n1,V1. ❨G,L❩ ⊢ V ➡[h,n1] V1 →
     ∀T1. ❨G,L❩ ⊢ T ➡[h,n1] T1 → ∀n2,T2. ❨G,L❩ ⊢ T ➡[h,n2] T2 →
     ∀L1. ❨G,L❩ ⊢ ➡[h,0] L1 → ∀L2. ❨G,L❩ ⊢ ➡[h,0] L2 →
     ∃∃T. ❨G,L1❩ ⊢ ⓝV1.T1 ➡*[h,n2-n1] T & ❨G,L2❩ ⊢ T2 ➡*[h,n1-n2] T.
#h #a #G0 #L0 #V0 #T0 #IH #H0
#n1 #V1 #HV01 #T1 #HT01 #n2 #T2 #HT02
#L1 #HL01 #L2 #HL02
elim (cnv_inv_cast … H0) -H0 #X0 #HV0 #HT0 #_ #_ -X0
elim (cnv_cpm_conf_lpr_sub … IH … HT01 … HT02 … HL01 … HL02) [|*: /2 width=1 by fqup_fpbg/ ]
#T #HT1 #HT2 -L0 -V0 -T0
/3 width=3 by cpms_eps, ex2_intro/
qed-.

fact cnv_cpm_conf_lpr_cast_ee_aux (h) (a) (G) (L) (V) (T):
     (∀G0,L0,T0. ❨G,L,ⓝV.T❩ > ❨G0,L0,T0❩ → IH_cnv_cpm_trans_lpr h a G0 L0 T0) →
     (∀G0,L0,T0. ❨G,L,ⓝV.T❩ > ❨G0,L0,T0❩ → IH_cnv_cpms_conf_lpr h a G0 L0 T0) →
     ❨G,L❩ ⊢ ⓝV.T ![h,a] →
     ∀n1,V1. ❨G,L❩ ⊢ V ➡[h,n1] V1 → ∀n2,V2. ❨G,L❩ ⊢ V ➡[h,n2] V2 →
     ∀T1. ❨G,L❩ ⊢ T ➡[h,n1] T1 →
     ∀L1. ❨G,L❩ ⊢ ➡[h,0] L1 → ∀L2. ❨G,L❩ ⊢ ➡[h,0] L2 →
     ∃∃T. ❨G,L1❩ ⊢ ⓝV1.T1 ➡*[h,↑n2-n1] T & ❨G,L2❩ ⊢ V2 ➡*[h,n1-↑n2] T.
#h #a #G0 #L0 #V0 #T0 #IH2 #IH1 #H0
#n1 #V1 #HV01 #n2 #V2 #HV02 #T1 #HT01
#L1 #HL01 #L2 #HL02 -HV01
elim (cnv_inv_cast … H0) -H0 #X0 #HV0 #HT0 #HVX0 #HTX0
lapply (cnv_cpms_trans_lpr_sub … IH2 … HVX0 … L0 ?) [4:|*: /2 width=1 by fqup_fpbg/ ] #HX0
elim (cnv_cpms_strip_lpr_sub … IH1 … HVX0 … HV02 … L0 … HL02) [|*: /2 width=1 by fqup_fpbg/ ]
elim (cnv_cpms_strip_lpr_sub … IH1 … HTX0 … HT01 … L0 … HL01) [|*: /2 width=1 by fqup_fpbg/ ]
-HV02 -HTX0 -HT01 <minus_O_n <minus_n_O #T #HT2 #HT1 #V #HV1 #HV2
elim (IH1 … HV1 … HT2 … HL02 … HL01) [|*: /2 width=5 by fqup_cpms_fwd_fpbg/ ]
-L0 -V0 -T0 -X0 #U #HVU #HTU
lapply (cpms_trans … HV2 … HVU) -V <plus_O_n >minus_plus #H2
lapply (cpms_trans … HT1 … HTU) -T <arith_l2 #H1
/3 width=3 by cpms_eps, ex2_intro/
qed-.

fact cnv_cpm_conf_lpr_epsilon_epsilon_aux (h) (a) (G) (L) (V) (T):
     (∀G0,L0,T0. ❨G,L,ⓝV.T❩ > ❨G0,L0,T0❩ → IH_cnv_cpms_conf_lpr h a G0 L0 T0) →
     ❨G,L❩ ⊢ ⓝV.T ![h,a] →
     ∀n1,T1. ❨G,L❩ ⊢ T ➡[h,n1] T1 → ∀n2,T2. ❨G,L❩ ⊢ T ➡[h,n2] T2 →
     ∀L1. ❨G,L❩ ⊢ ➡[h,0] L1 → ∀L2. ❨G,L❩ ⊢ ➡[h,0] L2 →
     ∃∃T. ❨G,L1❩ ⊢ T1 ➡*[h,n2-n1] T & ❨G,L2❩ ⊢ T2 ➡*[h,n1-n2] T.
#h #a #G0 #L0 #V0 #T0 #IH #H0
#n1 #T1 #HT01 #n2 #T2 #HT02
#L1 #HL01 #L2 #HL02
elim (cnv_inv_cast … H0) -H0 #X0 #_ #HT0 #_ #_ -X0
elim (cnv_cpm_conf_lpr_sub … IH … HT01 … HT02 … HL01 … HL02) [|*: /2 width=1 by fqup_fpbg/ ]
#T #HT1 #HT2 -L0 -V0 -T0
/2 width=3 by ex2_intro/
qed-.

fact cnv_cpm_conf_lpr_epsilon_ee_aux (h) (a) (G) (L) (V) (T):
     (∀G0,L0,T0. ❨G,L,ⓝV.T❩ > ❨G0,L0,T0❩ → IH_cnv_cpm_trans_lpr h a G0 L0 T0) →
     (∀G0,L0,T0. ❨G,L,ⓝV.T❩ > ❨G0,L0,T0❩ → IH_cnv_cpms_conf_lpr h a G0 L0 T0) →
     ❨G,L❩ ⊢ ⓝV.T ![h,a] →
     ∀n1,T1. ❨G,L❩ ⊢ T ➡[h,n1] T1 → ∀n2,V2. ❨G,L❩ ⊢ V ➡[h,n2] V2 →
     ∀L1. ❨G,L❩ ⊢ ➡[h,0] L1 → ∀L2. ❨G,L❩ ⊢ ➡[h,0] L2 →
     ∃∃T. ❨G,L1❩ ⊢ T1 ➡*[h,↑n2-n1] T & ❨G,L2❩ ⊢ V2 ➡*[h,n1-↑n2] T.
#h #a #G0 #L0 #V0 #T0 #IH2 #IH1 #H0
#n1 #T1 #HT01 #n2 #V2 #HV02
#L1 #HL01 #L2 #HL02
elim (cnv_inv_cast … H0) -H0 #X0 #HV0 #HT0 #HVX0 #HTX0
lapply (cnv_cpms_trans_lpr_sub … IH2 … HVX0 … L0 ?) [4:|*: /2 width=1 by fqup_fpbg/ ] #HX0
elim (cnv_cpms_strip_lpr_sub … IH1 … HVX0 … HV02 … L0 … HL02) [|*: /2 width=1 by fqup_fpbg/ ]
elim (cnv_cpms_strip_lpr_sub … IH1 … HTX0 … HT01 … L0 … HL01) [|*: /2 width=1 by fqup_fpbg/ ]
-HV02 -HTX0 -HT01 <minus_O_n <minus_n_O #T #HT2 #HT1 #V #HV1 #HV2
elim (IH1 … HV1 … HT2 … HL02 … HL01) [|*: /2 width=5 by fqup_cpms_fwd_fpbg/ ]
-L0 -V0 -T0 -X0 #U #HVU #HTU
lapply (cpms_trans … HV2 … HVU) -V <plus_O_n >minus_plus #H2
lapply (cpms_trans … HT1 … HTU) -T <arith_l2 #H1
/2 width=3 by ex2_intro/
qed-.

fact cnv_cpm_conf_lpr_ee_ee_aux (h) (a) (G) (L) (V) (T):
     (∀G0,L0,T0. ❨G,L,ⓝV.T❩ > ❨G0,L0,T0❩ → IH_cnv_cpms_conf_lpr h a G0 L0 T0) →
     ❨G,L❩ ⊢ ⓝV.T ![h,a] →
     ∀n1,V1. ❨G,L❩ ⊢ V ➡[h,n1] V1 → ∀n2,V2. ❨G,L❩ ⊢ V ➡[h,n2] V2 →
     ∀L1. ❨G,L❩ ⊢ ➡[h,0] L1 → ∀L2. ❨G,L❩ ⊢ ➡[h,0] L2 →
     ∃∃T. ❨G,L1❩ ⊢ V1 ➡*[h,n2-n1] T & ❨G,L2❩ ⊢ V2 ➡*[h,n1-n2] T.
#h #a #G0 #L0 #V0 #T0 #IH #H0
#n1 #V1 #HV01 #n2 #V2 #HV02
#L1 #HL01 #L2 #HL02
elim (cnv_inv_cast … H0) -H0 #X0 #HV0 #_ #_ #_ -X0
elim (cnv_cpm_conf_lpr_sub … IH … HV01 … HV02 … HL01 … HL02) [|*: /2 width=1 by fqup_fpbg/ ]
#V #HV1 #HV2 -L0 -V0 -T0
/2 width=3 by ex2_intro/
qed-.

fact cnv_cpm_conf_lpr_aux (h) (a):
     ∀G0,L0,T0.
     (∀G1,L1,T1. ❨G0,L0,T0❩ > ❨G1,L1,T1❩ → IH_cnv_cpm_trans_lpr h a G1 L1 T1) →
     (∀G1,L1,T1. ❨G0,L0,T0❩ > ❨G1,L1,T1❩ → IH_cnv_cpms_conf_lpr h a G1 L1 T1) →
     ∀G1,L1,T1. G0 = G1 → L0 = L1 → T0 = T1 → IH_cnv_cpm_conf_lpr h a G1 L1 T1.
#h #a #G0 #L0 #T0 #IH2 #IH1 #G #L * [| * [| * ]]
[ #I #HG0 #HL0 #HT0 #HT #n1 #X1 #HX1 #n2 #X2 #HX2 #L1 #HL1 #L2 #HL2 destruct
  elim (cpm_inv_atom1_drops … HX1) -HX1 *
  elim (cpm_inv_atom1_drops … HX2) -HX2 *
  [ #H21 #H22 #H11 #H12 destruct -a -L
    <minus_O_n
    /2 width=1 by cnv_cpm_conf_lpr_atom_atom_aux/
  | #s2 #H21 #H22 #H23 #H11 #H12 destruct -a -L
    <minus_O_n <minus_n_O
    /2 width=1 by cnv_cpm_conf_lpr_atom_ess_aux/
  | #K2 #V2 #XV2 #i #HLK2 #HVX2 #HXV2 #H21 #H11 #H12 destruct -IH2
    <minus_O_n <minus_n_O
    @(cnv_cpm_conf_lpr_atom_delta_aux … IH1) -IH1 /1 width=6 by/
  | #m2 #K2 #W2 #XW2 #i #HLK2 #HWX2 #HXW2 #H21 #H22 #H11 #H12 destruct -IH2
    <minus_O_n <minus_n_O
    @(cnv_cpm_conf_lpr_atom_ell_aux … IH1) -IH1 /1 width=6 by/
  | #H21 #H22 #s1 #H11 #H12 #H13 destruct -a -L
    <minus_O_n <minus_n_O
    /3 width=1 by cnv_cpm_conf_lpr_atom_ess_aux, ex2_commute/
  | #s2 #H21 #H22 #H23 #s1 #H11 #H12 #H13 destruct -a -L
    <minus_n_n
    /2 width=1 by cnv_cpm_conf_lpr_atom_atom_aux/
  | #K2 #V2 #XV2 #i2 #_ #_ #_ #H21 #s1 #H11 #H12 #H13 destruct
  | #m2 #K2 #W2 #XW2 #i2 #_ #_ #_ #H21 #H22 #s1 #H11 #H12 #H13 destruct
  | #H21 #H22 #K1 #V1 #XV1 #i1 #HLK1 #HVX1 #HXV1 #H11 destruct -IH2
    <minus_O_n <minus_n_O
    @ex2_commute @(cnv_cpm_conf_lpr_atom_delta_aux … IH1) -IH1 /1 width=6 by/
  | #s2 #H21 #H22 #H23 #K1 #V1 #XV1 #i1 #_ #_ #_ #H11 destruct
  | #K2 #V2 #XV2 #i2 #HLK2 #HVX2 #HXV2 #H21 #K1 #V1 #XV1 #i1 #HLK1 #HVX1 #HXV1 #H11 destruct -IH2
    @(cnv_cpm_conf_lpr_delta_delta_aux … IH1) -IH1 /1 width=13 by/
  | #m2 #K2 #W2 #XW2 #i2 #HLK2 #_ #_ #H21 #H22 #K1 #V1 #XV1 #i1 #HLK1 #_ #_ #H11 destruct -a -XW2 -XV1 -HL2 -HL1
    elim cnv_cpm_conf_lpr_delta_ell_aux /1 width=8 by/
  | #H21 #H22 #m1 #K1 #W1 #XW1 #i1 #HLK1 #HWX1 #HXW1 #H11 #H12 destruct -IH2
    <minus_O_n <minus_n_O
    @ex2_commute @(cnv_cpm_conf_lpr_atom_ell_aux … IH1) -IH1 /1 width=6 by/
  | #s2 #H21 #H22 #H23 #m1 #K1 #W1 #XW1 #i1 #_ #_ #_ #H11 #H12 destruct
  | #K2 #V2 #XV2 #i2 #HLK2 #_ #_ #H21 #m1 #K1 #W1 #XW1 #i1 #HLK1 #_ #_ #H11 #H12 destruct -a -XV2 -XW1 -HL2 -HL1
    elim cnv_cpm_conf_lpr_delta_ell_aux /1 width=8 by/
  | #m2 #K2 #W2 #XW2 #i2 #HLK2 #HWX2 #HXW2 #H21 #H22 #m1 #K1 #W1 #XW1 #i1 #HLK1 #HWX1 #HXW1 #H11 #H12 destruct -IH2
    >minus_S_S >minus_S_S
    @(cnv_cpm_conf_lpr_delta_delta_aux … IH1) -IH1 /1 width=13 by/
  ]
| #p #I #V #T #HG0 #HL0 #HT0 #HT #n1 #X1 #HX1 #n2 #X2 #HX2 #L1 #HL1 #L2 #HL2 destruct
  elim (cpm_inv_bind1 … HX1) -HX1 *
  elim (cpm_inv_bind1 … HX2) -HX2 *
  [ #V2 #T2 #HV2 #HT2 #H21 #V1 #T1 #HV1 #HT1 #H11 destruct -IH2
    @(cnv_cpm_conf_lpr_bind_bind_aux … IH1) -IH1 /1 width=1 by/
  | #T2 #HT2 #HTX2 #H21 #H22 #V1 #T1 #HV1 #HT1 #H11 destruct -IH2
    @(cnv_cpm_conf_lpr_bind_zeta_aux … IH1) -IH1 /1 width=3 by/
  | #V2 #T2 #HV2 #HT2 #H21 #T1 #HT1 #HTX1 #H11 #H12 destruct -IH2
    @ex2_commute @(cnv_cpm_conf_lpr_bind_zeta_aux … IH1) -IH1 /1 width=3 by/
  | #T2 #HT2 #HTX2 #H21 #H22 #T1 #HT1 #HTX1 #H11 #H12 destruct -IH2
    @(cnv_cpm_conf_lpr_zeta_zeta_aux … IH1) -IH1 /1 width=3 by/
  ]
| #V #T #HG0 #HL0 #HT0 #HT #n1 #X1 #HX1 #n2 #X2 #HX2 #L1 #HL1 #L2 #HL2 destruct
  elim (cpm_inv_appl1 … HX1) -HX1 *
  elim (cpm_inv_appl1 … HX2) -HX2 *
  [ #V2 #T2 #HV2 #HT2 #H21 #V1 #T1 #HV1 #HT1 #H11 destruct -IH2
    @(cnv_cpm_conf_lpr_appl_appl_aux … IH1) -IH1 /1 width=1 by/
  | #p2 #V2 #XW2 #W2 #XT2 #T2 #HV2 #HW2 #HT2 #H21 #H22 #V1 #T1 #HV1 #HT1 #H11 destruct -IH2
    @(cnv_cpm_conf_lpr_appl_beta_aux … IH1) -IH1 /1 width=1 by/
  | #p2 #V2 #XV2 #XW2 #W2 #XT2 #T2 #HV2 #HXV2 #HW2 #HT2 #H21 #H22 #V1 #T1 #HV1 #HT1 #H11 destruct -IH2
    @(cnv_cpm_conf_lpr_appl_theta_aux … IH1) -IH1 /1 width=3 by/
  | #V2 #T2 #HV2 #HT2 #H21 #p1 #V1 #XW1 #W1 #XT1 #T1 #HV1 #HW1 #HT1 #H11 #H12 destruct -IH2
    @ex2_commute @(cnv_cpm_conf_lpr_appl_beta_aux … IH1) -IH1 /1 width=1 by/
  | #p2 #V2 #XW2 #W2 #XT2 #T2 #HV2 #HW2 #HT2 #H21 #H22 #p1 #V1 #XW1 #W1 #XT1 #T1 #HV1 #HW1 #HT1 #H11 #H12 destruct -IH2
    @(cnv_cpm_conf_lpr_beta_beta_aux … IH1) -IH1 /1 width=1 by/
  | #p2 #V2 #XV2 #XW2 #W2 #XT2 #T2 #HV2 #HXV2 #HW2 #HT2 #H21 #H22 #p1 #V1 #XW1 #W1 #XT1 #T1 #HV1 #HW1 #HT1 #H11 #H12 destruct
  | #V2 #T2 #HV2 #HT2 #H21 #p1 #V1 #XV1 #XW1 #W1 #XT1 #T1 #HV1 #HXV1 #HW1 #HT1 #H11 #H12 destruct -IH2
    @ex2_commute @(cnv_cpm_conf_lpr_appl_theta_aux … IH1) -IH1 /1 width=3 by/
  | #p2 #V2 #XW2 #W2 #XT2 #T2 #HV2 #HW2 #HT2 #H21 #H22 #p1 #V1 #XV1 #XW1 #W1 #XT1 #T1 #HV1 #HXV1 #HW1 #HT1 #H11 #H12 destruct
  | #p2 #V2 #XV2 #XW2 #W2 #XT2 #T2 #HV2 #HXV2 #HW2 #HT2 #H21 #H22 #p1 #V1 #XV1 #XW1 #W1 #XT1 #T1 #HV1 #HXV1 #HW1 #HT1 #H11 #H12 destruct -IH2
    @(cnv_cpm_conf_lpr_theta_theta_aux … IH1) -IH1 /1 width=3 by/
  ]
| #V #T #HG0 #HL0 #HT0 #HT #n1 #X1 #HX1 #n2 #X2 #HX2 #L1 #HL1 #L2 #HL2 destruct
  elim (cpm_inv_cast1 … HX1) -HX1 [ * || * ]
  elim (cpm_inv_cast1 … HX2) -HX2 [ * || * | * || * | * || * ]
  [ #V2 #T2 #HV2 #HT2 #H21 #V1 #T1 #HV1 #HT1 #H11 destruct -IH2
    @(cnv_cpm_conf_lpr_cast_cast_aux … IH1) -IH1 /1 width=1 by/
  | #HT2 #V1 #T1 #HV1 #HT1 #H11 destruct -IH2
    @(cnv_cpm_conf_lpr_cast_epsilon_aux … IH1) -IH1 /1 width=1 by/
  | #m2 #HV2 #H21 #V1 #T1 #HV1 #HT1 #H11 destruct
    @(cnv_cpm_conf_lpr_cast_ee_aux … IH2 IH1) -IH2 -IH1 /1 width=1 by/
  | #V2 #T2 #HV2 #HT2 #H21 #HT1 destruct -IH2
    @ex2_commute @(cnv_cpm_conf_lpr_cast_epsilon_aux … IH1) -IH1 /1 width=1 by/
  | #HT2 #HT1 -IH2
    @(cnv_cpm_conf_lpr_epsilon_epsilon_aux … IH1) -IH1 /1 width=1 by/
  | #m2 #HV2 #H21 #HT1 destruct
    @(cnv_cpm_conf_lpr_epsilon_ee_aux … IH2 IH1) -IH2 -IH1 /1 width=1 by/
  | #V2 #T2 #HV2 #HT2 #H21 #m1 #HV1 #H11 destruct
    @ex2_commute @(cnv_cpm_conf_lpr_cast_ee_aux … IH2 IH1) -IH2 -IH1 /1 width=1 by/
  | #HT2 #m1 #HV1 #H11 destruct
    @ex2_commute @(cnv_cpm_conf_lpr_epsilon_ee_aux … IH2 IH1) -IH2 -IH1 /1 width=1 by/
  | #m2 #HV2 #H21 #m1 #HV1 #H11 destruct -IH2
    >minus_S_S >minus_S_S
    @(cnv_cpm_conf_lpr_ee_ee_aux … IH1) -IH1 /1 width=1 by/
  ]
]
qed-.
