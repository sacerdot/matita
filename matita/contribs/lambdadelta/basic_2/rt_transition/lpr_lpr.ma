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

include "static_2/relocation/lex_lex.ma".
include "basic_2/rt_transition/cpm_lsubr.ma".
include "basic_2/rt_transition/cpr.ma".
include "basic_2/rt_transition/cpr_drops.ma".
include "basic_2/rt_transition/lpr_drops.ma".

(* PARALLEL R-TRANSITION FOR FULL LOCAL ENVIRONMENTS ************************)

definition IH_cpr_conf_lpr (h): relation3 genv lenv term ≝ λG,L,T.
                           ∀T1. ❪G,L❫ ⊢ T ➡[h,0] T1 → ∀T2. ❪G,L❫ ⊢ T ➡[h,0] T2 →
                           ∀L1. ❪G,L❫ ⊢ ➡[h,0] L1 → ∀L2. ❪G,L❫ ⊢ ➡[h,0] L2 →
                           ∃∃T0. ❪G,L1❫ ⊢ T1 ➡[h,0] T0 & ❪G,L2❫ ⊢ T2 ➡[h,0] T0.

(* Main properties with context-sensitive parallel reduction for terms ******)

fact cpr_conf_lpr_atom_atom (h):
   ∀I,G,L1,L2. ∃∃T. ❪G,L1❫ ⊢ ⓪[I] ➡[h,0] T & ❪G,L2❫ ⊢ ⓪[I] ➡[h,0] T.
/2 width=3 by cpr_refl, ex2_intro/ qed-.

fact cpr_conf_lpr_atom_delta (h):
   ∀G0,L0,i. (
      ∀G,L,T. ❪G0,L0,#i❫ ⬂+ ❪G,L,T❫ → IH_cpr_conf_lpr h G L T
   ) →
   ∀K0,V0. ⇩[i] L0 ≘ K0.ⓓV0 →
   ∀V2. ❪G0,K0❫ ⊢ V0 ➡[h,0] V2 → ∀T2. ⇧[↑i] V2 ≘ T2 →
   ∀L1. ❪G0,L0❫ ⊢ ➡[h,0] L1 → ∀L2. ❪G0,L0❫ ⊢ ➡[h,0] L2 →
   ∃∃T. ❪G0,L1❫ ⊢ #i ➡[h,0] T & ❪G0,L2❫ ⊢ T2 ➡[h,0] T.
#h #G0 #L0 #i #IH #K0 #V0 #HLK0 #V2 #HV02 #T2 #HVT2 #L1 #HL01 #L2 #HL02
elim (lpr_drops_conf … HLK0 … HL01) -HL01 // #X1 #H1 #HLK1
elim (lpr_inv_pair_sn … H1) -H1 #K1 #V1 #HK01 #HV01 #H destruct
elim (lpr_drops_conf … HLK0 … HL02) -HL02 // #X2 #H2 #HLK2
elim (lpr_inv_pair_sn … H2) -H2 #K2 #W2 #HK02 #_ #H destruct
lapply (drops_isuni_fwd_drop2 … HLK2) -W2 // #HLK2
lapply (fqup_lref (Ⓣ) … G0 … HLK0) -HLK0 #HLK0
elim (IH … HLK0 … HV01 … HV02 … HK01 … HK02) -L0 -K0 -V0 #V #HV1 #HV2
elim (cpm_lifts_sn … HV2 … HLK2 … HVT2) -V2 -HLK2 #T #HVT #HT2
/3 width=6 by cpm_delta_drops, ex2_intro/
qed-.

(* Basic_1: includes: pr0_delta_delta pr2_delta_delta *)
fact cpr_conf_lpr_delta_delta (h):
   ∀G0,L0,i. (
      ∀G,L,T. ❪G0,L0,#i❫ ⬂+ ❪G,L,T❫ → IH_cpr_conf_lpr h G L T
   ) →
   ∀K0,V0. ⇩[i] L0 ≘ K0.ⓓV0 →
   ∀V1. ❪G0,K0❫ ⊢ V0 ➡[h,0] V1 → ∀T1. ⇧[↑i] V1 ≘ T1 →
   ∀KX,VX. ⇩[i] L0 ≘ KX.ⓓVX →
   ∀V2. ❪G0,KX❫ ⊢ VX ➡[h,0] V2 → ∀T2. ⇧[↑i] V2 ≘ T2 →
   ∀L1. ❪G0,L0❫ ⊢ ➡[h,0] L1 → ∀L2. ❪G0,L0❫ ⊢ ➡[h,0] L2 →
   ∃∃T. ❪G0,L1❫ ⊢ T1 ➡[h,0] T & ❪G0,L2❫ ⊢ T2 ➡[h,0] T.
#h #G0 #L0 #i #IH #K0 #V0 #HLK0 #V1 #HV01 #T1 #HVT1
#KX #VX #H #V2 #HV02 #T2 #HVT2 #L1 #HL01 #L2 #HL02
lapply (drops_mono … H … HLK0) -H #H destruct
elim (lpr_drops_conf … HLK0 … HL01) -HL01 // #X1 #H1 #HLK1
elim (lpr_inv_pair_sn … H1) -H1 #K1 #W1 #HK01 #_ #H destruct
lapply (drops_isuni_fwd_drop2 … HLK1) -W1 // #HLK1
elim (lpr_drops_conf … HLK0 … HL02) -HL02 // #X2 #H2 #HLK2
elim (lpr_inv_pair_sn … H2) -H2 #K2 #W2 #HK02 #_ #H destruct
lapply (drops_isuni_fwd_drop2 … HLK2) -W2 // #HLK2
lapply (fqup_lref (Ⓣ) … G0 … HLK0) -HLK0 #HLK0
elim (IH … HLK0 … HV01 … HV02 … HK01 … HK02) -L0 -K0 -V0 #V #HV1 #HV2
elim (cpm_lifts_sn … HV1 … HLK1 … HVT1) -V1 -HLK1 #T #HVT #HT1
/3 width=11 by cpm_lifts_bi, ex2_intro/
qed-.

fact cpr_conf_lpr_bind_bind (h):
   ∀p,I,G0,L0,V0,T0. (
      ∀G,L,T. ❪G0,L0,ⓑ[p,I]V0.T0❫ ⬂+ ❪G,L,T❫ → IH_cpr_conf_lpr h G L T
   ) →
   ∀V1. ❪G0,L0❫ ⊢ V0 ➡[h,0] V1 → ∀T1. ❪G0,L0.ⓑ[I]V0❫ ⊢ T0 ➡[h,0] T1 →
   ∀V2. ❪G0,L0❫ ⊢ V0 ➡[h,0] V2 → ∀T2. ❪G0,L0.ⓑ[I]V0❫ ⊢ T0 ➡[h,0] T2 →
   ∀L1. ❪G0,L0❫ ⊢ ➡[h,0] L1 → ∀L2. ❪G0,L0❫ ⊢ ➡[h,0] L2 →
   ∃∃T. ❪G0,L1❫ ⊢ ⓑ[p,I]V1.T1 ➡[h,0] T & ❪G0,L2❫ ⊢ ⓑ[p,I]V2.T2 ➡[h,0] T.
#h #p #I #G0 #L0 #V0 #T0 #IH #V1 #HV01 #T1 #HT01
#V2 #HV02 #T2 #HT02 #L1 #HL01 #L2 #HL02
elim (IH … HV01 … HV02 … HL01 … HL02) //
elim (IH … HT01 … HT02 (L1.ⓑ[I]V1) … (L2.ⓑ[I]V2)) -IH
/3 width=5 by lpr_pair, cpm_bind, ex2_intro/
qed-.

fact cpr_conf_lpr_bind_zeta (h):
   ∀G0,L0,V0,T0. (
      ∀G,L,T. ❪G0,L0,+ⓓV0.T0❫ ⬂+ ❪G,L,T❫ → IH_cpr_conf_lpr h G L T
   ) →
   ∀V1. ❪G0,L0❫ ⊢ V0 ➡[h,0] V1 → ∀T1. ❪G0,L0.ⓓV0❫ ⊢ T0 ➡[h,0] T1 →
   ∀T2. ⇧[1]T2 ≘ T0 → ∀X2. ❪G0,L0❫ ⊢ T2 ➡[h,0] X2 →
   ∀L1. ❪G0,L0❫ ⊢ ➡[h,0] L1 → ∀L2. ❪G0,L0❫ ⊢ ➡[h,0] L2 →
   ∃∃T. ❪G0,L1❫ ⊢ +ⓓV1.T1 ➡[h,0] T & ❪G0,L2❫ ⊢ X2 ➡[h,0] T.
#h #G0 #L0 #V0 #T0 #IH #V1 #HV01 #T1 #HT01
#T2 #HT20 #X2 #HTX2 #L1 #HL01 #L2 #HL02
elim (cpm_inv_lifts_sn … HT01 (Ⓣ) … L0 … HT20) -HT01 [| /3 width=1 by drops_refl, drops_drop/ ] #T #HT1 #HT2
elim (IH … HT2 … HTX2 … HL01 … HL02) [| /2 width=1 by fqup_zeta/ ] -L0 -V0 -T0 -T2 #T2 #HT2 #HXT2
/3 width=3 by cpm_zeta, ex2_intro/
qed-.

fact cpr_conf_lpr_zeta_zeta (h):
   ∀G0,L0,V0,T0. (
      ∀G,L,T. ❪G0,L0,+ⓓV0.T0❫ ⬂+ ❪G,L,T❫ → IH_cpr_conf_lpr h G L T
   ) →
   ∀T1. ⇧[1] T1 ≘ T0 → ∀X1. ❪G0,L0❫ ⊢ T1 ➡[h,0] X1 →
   ∀T2. ⇧[1] T2 ≘ T0 → ∀X2. ❪G0,L0❫ ⊢ T2 ➡[h,0] X2 →
   ∀L1. ❪G0,L0❫ ⊢ ➡[h,0] L1 → ∀L2. ❪G0,L0❫ ⊢ ➡[h,0] L2 →
   ∃∃T. ❪G0,L1❫ ⊢ X1 ➡[h,0] T & ❪G0,L2❫ ⊢ X2 ➡[h,0] T.
#h #G0 #L0 #V0 #T0 #IH #T1 #HT10 #X1 #HTX1
#T2 #HT20 #X2 #HTX2 #L1 #HL01 #L2 #HL02
lapply (lifts_inj … HT20 … HT10) -HT20 #H destruct
elim (IH … HTX1 … HTX2 … HL01 … HL02) [| /2 width=1 by fqup_zeta/ ] -L0 -V0 -T0 -T1 #X #HX1 #HX2
/2 width=3 by ex2_intro/
qed-.

fact cpr_conf_lpr_flat_flat (h):
   ∀I,G0,L0,V0,T0. (
      ∀G,L,T. ❪G0,L0,ⓕ[I]V0.T0❫ ⬂+ ❪G,L,T❫ → IH_cpr_conf_lpr h G L T
   ) →
   ∀V1. ❪G0,L0❫ ⊢ V0 ➡[h,0] V1 → ∀T1. ❪G0,L0❫ ⊢ T0 ➡[h,0] T1 →
   ∀V2. ❪G0,L0❫ ⊢ V0 ➡[h,0] V2 → ∀T2. ❪G0,L0❫ ⊢ T0 ➡[h,0] T2 →
   ∀L1. ❪G0,L0❫ ⊢ ➡[h,0] L1 → ∀L2. ❪G0,L0❫ ⊢ ➡[h,0] L2 →
   ∃∃T. ❪G0,L1❫ ⊢ ⓕ[I]V1.T1 ➡[h,0] T & ❪G0,L2❫ ⊢ ⓕ[I]V2.T2 ➡[h,0] T.
#h #I #G0 #L0 #V0 #T0 #IH #V1 #HV01 #T1 #HT01
#V2 #HV02 #T2 #HT02 #L1 #HL01 #L2 #HL02
elim (IH … HV01 … HV02 … HL01 … HL02) //
elim (IH … HT01 … HT02 … HL01 … HL02) //
/3 width=5 by cpr_flat, ex2_intro/
qed-.

fact cpr_conf_lpr_flat_eps (h):
   ∀G0,L0,V0,T0. (
      ∀G,L,T. ❪G0,L0,ⓝV0.T0❫ ⬂+ ❪G,L,T❫ → IH_cpr_conf_lpr h G L T
   ) →
   ∀V1,T1. ❪G0,L0❫ ⊢ T0 ➡[h,0] T1 → ∀T2. ❪G0,L0❫ ⊢ T0 ➡[h,0] T2 →
   ∀L1. ❪G0,L0❫ ⊢ ➡[h,0] L1 → ∀L2. ❪G0,L0❫ ⊢ ➡[h,0] L2 →
   ∃∃T. ❪G0,L1❫ ⊢ ⓝV1.T1 ➡[h,0] T & ❪G0,L2❫ ⊢ T2 ➡[h,0] T.
#h #G0 #L0 #V0 #T0 #IH #V1 #T1 #HT01
#T2 #HT02 #L1 #HL01 #L2 #HL02
elim (IH … HT01 … HT02 … HL01 … HL02) // -L0 -V0 -T0
/3 width=3 by cpm_eps, ex2_intro/
qed-.

fact cpr_conf_lpr_eps_eps (h):
   ∀G0,L0,V0,T0. (
      ∀G,L,T. ❪G0,L0,ⓝV0.T0❫ ⬂+ ❪G,L,T❫ → IH_cpr_conf_lpr h G L T
   ) →
   ∀T1. ❪G0,L0❫ ⊢ T0 ➡[h,0] T1 → ∀T2. ❪G0,L0❫ ⊢ T0 ➡[h,0] T2 →
   ∀L1. ❪G0,L0❫ ⊢ ➡[h,0] L1 → ∀L2. ❪G0,L0❫ ⊢ ➡[h,0] L2 →
   ∃∃T. ❪G0,L1❫ ⊢ T1 ➡[h,0] T & ❪G0,L2❫ ⊢ T2 ➡[h,0] T.
#h #G0 #L0 #V0 #T0 #IH #T1 #HT01
#T2 #HT02 #L1 #HL01 #L2 #HL02
elim (IH … HT01 … HT02 … HL01 … HL02) // -L0 -V0 -T0
/2 width=3 by ex2_intro/
qed-.

fact cpr_conf_lpr_flat_beta (h):
   ∀p,G0,L0,V0,W0,T0. (
      ∀G,L,T. ❪G0,L0,ⓐV0.ⓛ[p]W0.T0❫ ⬂+ ❪G,L,T❫ → IH_cpr_conf_lpr h G L T
   ) →
   ∀V1. ❪G0,L0❫ ⊢ V0 ➡[h,0] V1 → ∀T1. ❪G0,L0❫ ⊢ ⓛ[p]W0.T0 ➡[h,0] T1 →
   ∀V2. ❪G0,L0❫ ⊢ V0 ➡[h,0] V2 → ∀W2. ❪G0,L0❫ ⊢ W0 ➡[h,0] W2 → ∀T2. ❪G0,L0.ⓛW0❫ ⊢ T0 ➡[h,0] T2 →
   ∀L1. ❪G0,L0❫ ⊢ ➡[h,0] L1 → ∀L2. ❪G0,L0❫ ⊢ ➡[h,0] L2 →
   ∃∃T. ❪G0,L1❫ ⊢ ⓐV1.T1 ➡[h,0] T & ❪G0,L2❫ ⊢ ⓓ[p]ⓝW2.V2.T2 ➡[h,0] T.
#h #p #G0 #L0 #V0 #W0 #T0 #IH #V1 #HV01 #X #H
#V2 #HV02 #W2 #HW02 #T2 #HT02 #L1 #HL01 #L2 #HL02
elim (cpm_inv_abst1 … H) -H #W1 #T1 #HW01 #HT01 #H destruct
elim (IH … HV01 … HV02 … HL01 … HL02) -HV01 -HV02 /2 width=1 by/ #V #HV1 #HV2
elim (IH … HW01 … HW02 … HL01 … HL02) /2 width=1 by/ #W #HW1 #HW2
elim (IH … HT01 … HT02 (L1.ⓛW1) … (L2.ⓛW2)) /2 width=1 by lpr_pair/ -L0 -V0 -W0 -T0 #T #HT1 #HT2
lapply (lsubr_cpm_trans … HT2 (L2.ⓓⓝW2.V2) ?) -HT2 /2 width=1 by lsubr_beta/ (**) (* full auto not tried *)
/4 width=5 by cpm_bind, cpr_flat, cpm_beta, ex2_intro/
qed-.

(* Basic-1: includes:
            pr0_cong_upsilon_refl pr0_cong_upsilon_zeta
            pr0_cong_upsilon_cong pr0_cong_upsilon_delta
*)
fact cpr_conf_lpr_flat_theta (h):
   ∀p,G0,L0,V0,W0,T0. (
      ∀G,L,T. ❪G0,L0,ⓐV0.ⓓ[p]W0.T0❫ ⬂+ ❪G,L,T❫ → IH_cpr_conf_lpr h G L T
   ) →
   ∀V1. ❪G0,L0❫ ⊢ V0 ➡[h,0] V1 → ∀T1. ❪G0,L0❫ ⊢ ⓓ[p]W0.T0 ➡[h,0] T1 →
   ∀V2. ❪G0,L0❫ ⊢ V0 ➡[h,0] V2 → ∀U2. ⇧[1] V2 ≘ U2 →
   ∀W2. ❪G0,L0❫ ⊢ W0 ➡[h,0] W2 → ∀T2. ❪G0,L0.ⓓW0❫ ⊢ T0 ➡[h,0] T2 →
   ∀L1. ❪G0,L0❫ ⊢ ➡[h,0] L1 → ∀L2. ❪G0,L0❫ ⊢ ➡[h,0] L2 →
   ∃∃T. ❪G0,L1❫ ⊢ ⓐV1.T1 ➡[h,0] T & ❪G0,L2❫ ⊢ ⓓ[p]W2.ⓐU2.T2 ➡[h,0] T.
#h #p #G0 #L0 #V0 #W0 #T0 #IH #V1 #HV01 #X #H
#V2 #HV02 #U2 #HVU2 #W2 #HW02 #T2 #HT02 #L1 #HL01 #L2 #HL02
elim (IH … HV01 … HV02 … HL01 … HL02) -HV01 -HV02 /2 width=1 by/ #V #HV1 #HV2
elim (cpm_inv_abbr1 … H) -H *
[ #W1 #T1 #HW01 #HT01 #H destruct
  elim (cpm_lifts_sn … HV2 (Ⓣ) … (L2.ⓓW2) … HVU2) -HVU2 [| /3 width=2 by drops_refl, drops_drop/ ] #U #HVU #HU2
  elim (IH … HW01 … HW02 … HL01 … HL02) /2 width=1 by/
  elim (IH … HT01 … HT02 (L1.ⓓW1) … (L2.ⓓW2)) /2 width=1 by lpr_pair/ -L0 -V0 -W0 -T0
  /4 width=7 by cpm_bind, cpm_appl, cpm_theta, ex2_intro/
| #X0 #HXT0 #HX0 #H destruct
  elim (cpm_inv_lifts_sn … HT02 (Ⓣ) … L0 … HXT0) -HT02 [| /3 width=2 by drops_refl, drops_drop/ ] #X2 #HXT2 #HX02
  elim (IH … HX0 … HX02 … HL01 … HL02) [| /3 width=5 by fqup_strap1, fqu_drop/ ] -L0 -V0 -W0 -T0 #T #H1T #H2T
  /4 width=8 by cpm_appl, cpm_zeta, lifts_flat, ex2_intro/
]
qed-.

fact cpr_conf_lpr_beta_beta (h):
   ∀p,G0,L0,V0,W0,T0. (
      ∀G,L,T. ❪G0,L0,ⓐV0.ⓛ[p]W0.T0❫ ⬂+ ❪G,L,T❫ → IH_cpr_conf_lpr h G L T
   ) →
   ∀V1. ❪G0,L0❫ ⊢ V0 ➡[h,0] V1 → ∀W1. ❪G0,L0❫ ⊢ W0 ➡[h,0] W1 → ∀T1. ❪G0,L0.ⓛW0❫ ⊢ T0 ➡[h,0] T1 →
   ∀V2. ❪G0,L0❫ ⊢ V0 ➡[h,0] V2 → ∀W2. ❪G0,L0❫ ⊢ W0 ➡[h,0] W2 → ∀T2. ❪G0,L0.ⓛW0❫ ⊢ T0 ➡[h,0] T2 →
   ∀L1. ❪G0,L0❫ ⊢ ➡[h,0] L1 → ∀L2. ❪G0,L0❫ ⊢ ➡[h,0] L2 →
   ∃∃T. ❪G0,L1❫ ⊢ ⓓ[p]ⓝW1.V1.T1 ➡[h,0] T & ❪G0,L2❫ ⊢ ⓓ[p]ⓝW2.V2.T2 ➡[h,0] T.
#h #p #G0 #L0 #V0 #W0 #T0 #IH #V1 #HV01 #W1 #HW01 #T1 #HT01
#V2 #HV02 #W2 #HW02 #T2 #HT02 #L1 #HL01 #L2 #HL02
elim (IH … HV01 … HV02 … HL01 … HL02) -HV01 -HV02 /2 width=1 by/ #V #HV1 #HV2
elim (IH … HW01 … HW02 … HL01 … HL02) /2 width=1 by/ #W #HW1 #HW2
elim (IH … HT01 … HT02 (L1.ⓛW1) … (L2.ⓛW2)) /2 width=1 by lpr_pair/ -L0 -V0 -W0 -T0 #T #HT1 #HT2
lapply (lsubr_cpm_trans … HT1 (L1.ⓓⓝW1.V1) ?) -HT1 /2 width=1 by lsubr_beta/
lapply (lsubr_cpm_trans … HT2 (L2.ⓓⓝW2.V2) ?) -HT2 /2 width=1 by lsubr_beta/
/4 width=5 by cpm_bind, cpr_flat, ex2_intro/ (**) (* full auto not tried *)
qed-.

(* Basic_1: was: pr0_upsilon_upsilon *)
fact cpr_conf_lpr_theta_theta (h):
   ∀p,G0,L0,V0,W0,T0. (
      ∀G,L,T. ❪G0,L0,ⓐV0.ⓓ[p]W0.T0❫ ⬂+ ❪G,L,T❫ → IH_cpr_conf_lpr h G L T
   ) →
   ∀V1. ❪G0,L0❫ ⊢ V0 ➡[h,0] V1 → ∀U1. ⇧[1] V1 ≘ U1 →
   ∀W1. ❪G0,L0❫ ⊢ W0 ➡[h,0] W1 → ∀T1. ❪G0,L0.ⓓW0❫ ⊢ T0 ➡[h,0] T1 →
   ∀V2. ❪G0,L0❫ ⊢ V0 ➡[h,0] V2 → ∀U2. ⇧[1] V2 ≘ U2 →
   ∀W2. ❪G0,L0❫ ⊢ W0 ➡[h,0] W2 → ∀T2. ❪G0,L0.ⓓW0❫ ⊢ T0 ➡[h,0] T2 →
   ∀L1. ❪G0,L0❫ ⊢ ➡[h,0] L1 → ∀L2. ❪G0,L0❫ ⊢ ➡[h,0] L2 →
   ∃∃T. ❪G0,L1❫ ⊢ ⓓ[p]W1.ⓐU1.T1 ➡[h,0] T & ❪G0,L2❫ ⊢ ⓓ[p]W2.ⓐU2.T2 ➡[h,0] T.
#h #p #G0 #L0 #V0 #W0 #T0 #IH #V1 #HV01 #U1 #HVU1 #W1 #HW01 #T1 #HT01
#V2 #HV02 #U2 #HVU2 #W2 #HW02 #T2 #HT02 #L1 #HL01 #L2 #HL02
elim (IH … HV01 … HV02 … HL01 … HL02) -HV01 -HV02 /2 width=1 by/ #V #HV1 #HV2
elim (IH … HW01 … HW02 … HL01 … HL02) /2 width=1 by/ #W #HW1 #HW2
elim (IH … HT01 … HT02 (L1.ⓓW1) … (L2.ⓓW2)) /2 width=1 by lpr_pair/ -L0 -V0 -W0 -T0
elim (cpm_lifts_sn … HV1 (Ⓣ) … (L1.ⓓW1) … HVU1) -HVU1 /3 width=2 by drops_refl, drops_drop/ #U #HVU #HU1
lapply (cpm_lifts_bi … HV2 (Ⓣ) … (L2.ⓓW2) … HVU2 … HVU) -HVU2 /3 width=2 by drops_refl, drops_drop/
/4 width=7 by cpm_bind, cpm_appl, ex2_intro/ (**) (* full auto not tried *)
qed-.

theorem cpr_conf_lpr (h): ∀G. lex_confluent (λL.cpm h G L 0) (λL.cpm h G L 0).
#h #G0 #L0 #T0 @(fqup_wf_ind_eq (Ⓣ) … G0 L0 T0) -G0 -L0 -T0
#G #L #T #IH #G0 #L0 * [| * ]
[ #I0 #HG #HL #HT #T1 #H1 #T2 #H2 #L1 #HL01 #L2 #HL02 destruct
  elim (cpr_inv_atom1_drops … H1) -H1
  elim (cpr_inv_atom1_drops … H2) -H2
  [ #H2 #H1 destruct
    @cpr_conf_lpr_atom_atom
  | * #K0 #V0 #V2 #i2 #HLK0 #HV02 #HVT2 #H2 #H1 destruct
    @(cpr_conf_lpr_atom_delta … IH) -IH /width=6 by/
  | #H2 * #K0 #V0 #V1 #i1 #HLK0 #HV01 #HVT1 #H1 destruct
    @ex2_commute @(cpr_conf_lpr_atom_delta … IH) -IH /width=6 by/
  | * #X #Y #V2 #z #H #HV02 #HVT2 #H2
    * #K0 #V0 #V1 #i #HLK0 #HV01 #HVT1 #H1 destruct
    @(cpr_conf_lpr_delta_delta … IH) -IH /width=6 by/
  ]
| #p #I #V0 #T0 #HG #HL #HT #X1 #H1 #X2 #H2 #L1 #HL01 #L2 #HL02 destruct
  elim (cpm_inv_bind1 … H1) -H1 *
  [ #V1 #T1 #HV01 #HT01 #H1
  | #T1 #HT10 #HTX1 #H11 #H12
  ]
  elim (cpm_inv_bind1 … H2) -H2 *
  [1,3: #V2 #T2 #HV02 #HT02 #H2
  |2,4: #T2 #HT20 #HTX2 #H21 #H22
  ] destruct
  [ @(cpr_conf_lpr_bind_bind … IH) -IH /width=1 by/
  | @ex2_commute @(cpr_conf_lpr_bind_zeta … IH) -IH /width=3 by/
  | @(cpr_conf_lpr_bind_zeta … IH) -IH /width=3 by/
  | @(cpr_conf_lpr_zeta_zeta … IH) -IH /width=3 by/
  ]
| #I #V0 #T0 #HG #HL #HT #X1 #H1 #X2 #H2 #L1 #HL01 #L2 #HL02 destruct
  elim (cpr_inv_flat1 … H1) -H1 *
  [ #V1 #T1 #HV01 #HT01 #H1
  | #HX1 #H1
  | #p1 #V1 #Y1 #W1 #Z1 #T1 #HV01 #HYW1 #HZT1 #H11 #H12 #H13
  | #p1 #V1 #U1 #Y1 #W1 #Z1 #T1 #HV01 #HVU1 #HYW1 #HZT1 #H11 #H12 #H13
  ]
  elim (cpr_inv_flat1 … H2) -H2 *
  [1,5,9,13: #V2 #T2 #HV02 #HT02 #H2
  |2,6,10,14: #HX2 #H2
  |3,7,11,15: #p2 #V2 #Y2 #W2 #Z2 #T2 #HV02 #HYW2 #HZT2 #H21 #H22 #H23
  |4,8,12,16: #p2 #V2 #U2 #Y2 #W2 #Z2 #T2 #HV02 #HVU2 #HYW2 #HZT2 #H21 #H22 #H23
  ] destruct
  [ @(cpr_conf_lpr_flat_flat … IH) -IH /width=1 by/
  | @ex2_commute @(cpr_conf_lpr_flat_eps … IH) -IH /width=1 by/
  | @ex2_commute @(cpr_conf_lpr_flat_beta … IH) -IH /width=1 by/
  | @ex2_commute @(cpr_conf_lpr_flat_theta … IH) -IH /width=3 by/
  | @(cpr_conf_lpr_flat_eps … IH) -IH /width=1 by/
  | @(cpr_conf_lpr_eps_eps … IH) -IH /width=1 by/
  | @(cpr_conf_lpr_flat_beta … IH) -IH /width=1 by/
  | @(cpr_conf_lpr_beta_beta … IH) -IH /width=1 by/
  | @(cpr_conf_lpr_flat_theta … IH) -IH /width=3 by/
  | @(cpr_conf_lpr_theta_theta … IH) -IH /width=3 by/
  ]
]
qed-.

(* Properties with context-sensitive parallel reduction for terms ***********)

lemma lpr_cpr_conf_dx (h) (G): ∀L0. ∀T0,T1:term. ❪G,L0❫ ⊢ T0 ➡[h,0] T1 → ∀L1. ❪G,L0❫ ⊢ ➡[h,0] L1 →
                               ∃∃T. ❪G,L1❫ ⊢ T0 ➡[h,0] T & ❪G,L1❫ ⊢ T1 ➡[h,0] T.
#h #G #L0 #T0 #T1 #HT01 #L1 #HL01
elim (cpr_conf_lpr … HT01 T0 … HL01 … HL01) -HT01 -HL01
/2 width=3 by ex2_intro/
qed-.

lemma lpr_cpr_conf_sn (h) (G): ∀L0. ∀T0,T1:term. ❪G,L0❫ ⊢ T0 ➡[h,0] T1 → ∀L1. ❪G,L0❫ ⊢ ➡[h,0] L1 →
                               ∃∃T. ❪G,L1❫ ⊢ T0 ➡[h,0] T & ❪G,L0❫ ⊢ T1 ➡[h,0] T.
#h #G #L0 #T0 #T1 #HT01 #L1 #HL01
elim (cpr_conf_lpr … HT01 T0 … L0 … HL01) -HT01 -HL01
/2 width=3 by ex2_intro/
qed-.

(* Main properties **********************************************************)

theorem lpr_conf (h) (G): confluent … (lpr h 0 G).
/3 width=6 by lex_conf, cpr_conf_lpr/
qed-.
