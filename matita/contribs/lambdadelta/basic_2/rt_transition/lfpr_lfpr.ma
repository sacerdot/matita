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

include "basic_2/static/lfxs_lfxs.ma".
include "basic_2/rt_transition/cpm_lsubr.ma".
include "basic_2/rt_transition/cpm_lfxs.ma".
include "basic_2/rt_transition/cpr.ma".
include "basic_2/rt_transition/cpr_drops.ma".
include "basic_2/rt_transition/lfpr_drops.ma".
include "basic_2/rt_transition/lfpr_fqup.ma".

(* PARALLEL R-TRANSITION FOR LOCAL ENV.S ON REFERRED ENTRIES ****************)

(* Main properties with context-sensitive parallel r-transition for terms ***)

fact cpr_conf_lfpr_atom_atom:
   ∀h,I,G,L1,L2. ∃∃T. ⦃G, L1⦄ ⊢ ⓪{I} ➡[h] T & ⦃G, L2⦄ ⊢ ⓪{I} ➡[h] T.
/2 width=3 by ex2_intro/ qed-.

fact cpr_conf_lfpr_atom_delta:
   ∀h,G,L0,i. (
      ∀L,T. ⦃G, L0, #i⦄ ⊐+ ⦃G, L, T⦄ →
      ∀T1. ⦃G, L⦄ ⊢ T ➡[h] T1 → ∀T2. ⦃G, L⦄ ⊢ T ➡[h] T2 →
      ∀L1. ⦃G, L⦄ ⊢ ➡[h, T] L1 → ∀L2. ⦃G, L⦄ ⊢ ➡[h, T] L2 →
      ∃∃T0. ⦃G, L1⦄ ⊢ T1 ➡[h] T0 & ⦃G, L2⦄ ⊢ T2 ➡[h] T0
   ) →
   ∀K0,V0. ⬇*[i] L0 ≡ K0.ⓓV0 →
   ∀V2. ⦃G, K0⦄ ⊢ V0 ➡[h] V2 → ∀T2. ⬆*[⫯i] V2 ≡ T2 →
   ∀L1. ⦃G, L0⦄ ⊢ ➡[h, #i] L1 → ∀L2. ⦃G, L0⦄ ⊢ ➡[h, #i] L2 →
   ∃∃T. ⦃G, L1⦄ ⊢ #i ➡[h] T & ⦃G, L2⦄ ⊢ T2 ➡[h] T.
#h #G #L0 #i #IH #K0 #V0 #HLK0 #V2 #HV02 #T2 #HVT2 #L1 #HL01 #L2 #HL02
elim (lfpr_inv_lref_pair_sn … HL01 … HLK0) -HL01 #K1 #V1 #HLK1 #HK01 #HV01
elim (lfpr_inv_lref_pair_sn … HL02 … HLK0) -HL02 #K2 #W2 #HLK2 #HK02 #_
lapply (drops_isuni_fwd_drop2 … HLK2) // -W2 #HLK2
lapply (fqup_lref (Ⓣ) … G … HLK0) -HLK0 #HLK0
elim (IH … HLK0 … HV01 … HV02 … HK01 … HK02) -L0 -K0 -V0 #V #HV1 #HV2
elim (cpm_lifts_sn … HV2 … HLK2 … HVT2) -K2 -V2
/3 width=6 by cpm_delta_drops, ex2_intro/
qed-.

(* Note: we don't use cpm_lifts_bi to preserve visual symmetry *)
fact cpr_conf_lfpr_delta_delta:
   ∀h,G,L0,i. (
      ∀L,T. ⦃G, L0, #i⦄ ⊐+ ⦃G, L, T⦄ →
      ∀T1. ⦃G, L⦄ ⊢ T ➡[h] T1 → ∀T2. ⦃G, L⦄ ⊢ T ➡[h] T2 →
      ∀L1. ⦃G, L⦄ ⊢ ➡[h, T] L1 → ∀L2. ⦃G, L⦄ ⊢ ➡[h, T] L2 →
      ∃∃T0. ⦃G, L1⦄ ⊢ T1 ➡[h] T0 & ⦃G, L2⦄ ⊢ T2 ➡[h] T0
   ) →
   ∀K0,V0. ⬇*[i] L0 ≡ K0.ⓓV0 →
   ∀V1. ⦃G, K0⦄ ⊢ V0 ➡[h] V1 → ∀T1. ⬆*[⫯i] V1 ≡ T1 →
   ∀KX,VX. ⬇*[i] L0 ≡ KX.ⓓVX →
   ∀V2. ⦃G, KX⦄ ⊢ VX ➡[h] V2 → ∀T2. ⬆*[⫯i] V2 ≡ T2 →
   ∀L1. ⦃G, L0⦄ ⊢ ➡[h, #i] L1 → ∀L2. ⦃G, L0⦄ ⊢ ➡[h, #i] L2 →
   ∃∃T. ⦃G, L1⦄ ⊢ T1 ➡[h] T & ⦃G, L2⦄ ⊢ T2 ➡[h] T.
#h #G #L0 #i #IH #K0 #V0 #HLK0 #V1 #HV01 #T1 #HVT1
#KX #VX #H #V2 #HV02 #T2 #HVT2 #L1 #HL01 #L2 #HL02
lapply (drops_mono … H … HLK0) -H #H destruct
elim (lfpr_inv_lref_pair_sn … HL01 … HLK0) -HL01 #K1 #W1 #HLK1 #HK01 #_
lapply (drops_isuni_fwd_drop2 … HLK1) -W1 // #HLK1
elim (lfpr_inv_lref_pair_sn … HL02 … HLK0) -HL02 #K2 #W2 #HLK2 #HK02 #_
lapply (drops_isuni_fwd_drop2 … HLK2) -W2 // #HLK2
lapply (fqup_lref (Ⓣ) … G … HLK0) -HLK0 #HLK0
elim (IH … HLK0 … HV01 … HV02 … HK01 … HK02) -L0 -K0 -V0 #V #HV1 #HV2
elim (cpm_lifts_sn … HV1 … HLK1 … HVT1) -K1 -V1 #T #HVT #HT1
elim (cpm_lifts_sn … HV2 … HLK2 … HVT2) -K2 -V2 #X #HX #HT2
lapply (lifts_mono … HX … HVT) #H destruct
/2 width=3 by ex2_intro/
qed-.

fact cpr_conf_lfpr_bind_bind:
   ∀h,p,I,G,L0,V0,T0. (
      ∀L,T. ⦃G, L0, ⓑ{p,I}V0.T0⦄ ⊐+ ⦃G, L, T⦄ →
      ∀T1. ⦃G, L⦄ ⊢ T ➡[h] T1 → ∀T2. ⦃G, L⦄ ⊢ T ➡[h] T2 →
      ∀L1. ⦃G, L⦄ ⊢ ➡[h, T] L1 → ∀L2. ⦃G, L⦄ ⊢ ➡[h, T] L2 →
      ∃∃T0. ⦃G, L1⦄ ⊢ T1 ➡[h] T0 & ⦃G, L2⦄ ⊢ T2 ➡[h] T0
   ) →
   ∀V1. ⦃G, L0⦄ ⊢ V0 ➡[h] V1 → ∀T1. ⦃G, L0.ⓑ{I}V0⦄ ⊢ T0 ➡[h] T1 →
   ∀V2. ⦃G, L0⦄ ⊢ V0 ➡[h] V2 → ∀T2. ⦃G, L0.ⓑ{I}V0⦄ ⊢ T0 ➡[h] T2 →
   ∀L1. ⦃G, L0⦄ ⊢ ➡[h, ⓑ{p,I}V0.T0] L1 → ∀L2. ⦃G, L0⦄ ⊢ ➡[h, ⓑ{p,I}V0.T0] L2 →
   ∃∃T. ⦃G, L1⦄ ⊢ ⓑ{p,I}V1.T1 ➡[h] T & ⦃G, L2⦄ ⊢ ⓑ{p,I}V2.T2 ➡[h] T.
#h #p #I #G #L0 #V0 #T0 #IH #V1 #HV01 #T1 #HT01
#V2 #HV02 #T2 #HT02 #L1 #HL01 #L2 #HL02
elim (lfpr_inv_bind … HL01) -HL01 #H1V0 #H1T0
elim (lfpr_inv_bind … HL02) -HL02 #H2V0 #H2T0
elim (IH … HV01 … HV02 … H1V0 … H2V0) //
elim (IH … HT01 … HT02 (L1.ⓑ{I}V1) … (L2.ⓑ{I}V2)) -IH
/3 width=5 by lfpr_bind_repl_dx, cpm_bind, ext2_pair, ex2_intro/
qed-.

fact cpr_conf_lfpr_bind_zeta:
   ∀h,G,L0,V0,T0. (
      ∀L,T. ⦃G, L0, +ⓓV0.T0⦄ ⊐+ ⦃G, L, T⦄ →
      ∀T1. ⦃G, L⦄ ⊢ T ➡[h] T1 → ∀T2. ⦃G, L⦄ ⊢ T ➡[h] T2 →
      ∀L1. ⦃G, L⦄ ⊢ ➡[h, T] L1 → ∀L2. ⦃G, L⦄ ⊢ ➡[h, T] L2 →
      ∃∃T0. ⦃G, L1⦄ ⊢ T1 ➡[h] T0 & ⦃G, L2⦄ ⊢ T2 ➡[h] T0
   ) →
   ∀V1. ⦃G, L0⦄ ⊢ V0 ➡[h] V1 → ∀T1. ⦃G, L0.ⓓV0⦄ ⊢ T0 ➡[h] T1 →
   ∀T2. ⦃G, L0.ⓓV0⦄ ⊢ T0 ➡[h] T2 → ∀X2. ⬆*[1] X2 ≡ T2 →
   ∀L1. ⦃G, L0⦄ ⊢ ➡[h, +ⓓV0.T0] L1 → ∀L2. ⦃G, L0⦄ ⊢ ➡[h, +ⓓV0.T0] L2 →
   ∃∃T. ⦃G, L1⦄ ⊢ +ⓓV1.T1 ➡[h] T & ⦃G, L2⦄ ⊢ X2 ➡[h] T.
#h #G #L0 #V0 #T0 #IH #V1 #HV01 #T1 #HT01
#T2 #HT02 #X2 #HXT2 #L1 #HL01 #L2 #HL02
elim (lfpr_inv_bind … HL01) -HL01 #H1V0 #H1T0
elim (lfpr_inv_bind … HL02) -HL02 #H2V0 #H2T0
elim (IH … HT01 … HT02 (L1.ⓓV1) … (L2.ⓓV1)) -IH -HT01 -HT02 /3 width=4 by lfpr_bind_repl_dx, ext2_pair/ -L0 -V0 -T0 #T #HT1 #HT2
elim (cpm_inv_lifts_sn … HT2 … L2 … HXT2) -T2 /3 width=3 by drops_refl, drops_drop, cpm_zeta, ex2_intro/
qed-.

(* Note: we don't use cpm_inv_lifts_bi to preserve visual symmetry *)
fact cpr_conf_lfpr_zeta_zeta:
   ∀h,G,L0,V0,T0. (
      ∀L,T. ⦃G, L0, +ⓓV0.T0⦄ ⊐+ ⦃G, L, T⦄ →
      ∀T1. ⦃G, L⦄ ⊢ T ➡[h] T1 → ∀T2. ⦃G, L⦄ ⊢ T ➡[h] T2 →
      ∀L1. ⦃G, L⦄ ⊢ ➡[h, T] L1 → ∀L2. ⦃G, L⦄ ⊢ ➡[h, T] L2 →
      ∃∃T0. ⦃G, L1⦄ ⊢ T1 ➡[h] T0 & ⦃G, L2⦄ ⊢ T2 ➡[h] T0
   ) →
   ∀T1. ⦃G, L0.ⓓV0⦄ ⊢ T0 ➡[h] T1 → ∀X1. ⬆*[1] X1 ≡ T1 →
   ∀T2. ⦃G, L0.ⓓV0⦄ ⊢ T0 ➡[h] T2 → ∀X2. ⬆*[1] X2 ≡ T2 →
   ∀L1. ⦃G, L0⦄ ⊢ ➡[h, +ⓓV0.T0] L1 → ∀L2. ⦃G, L0⦄ ⊢ ➡[h, +ⓓV0.T0] L2 →
   ∃∃T. ⦃G, L1⦄ ⊢ X1 ➡[h] T & ⦃G, L2⦄ ⊢ X2 ➡[h] T.
#h #G #L0 #V0 #T0 #IH #T1 #HT01 #X1 #HXT1
#T2 #HT02 #X2 #HXT2 #L1 #HL01 #L2 #HL02
elim (lfpr_inv_bind … HL01) -HL01 #H1V0 #H1T0
elim (lfpr_inv_bind … HL02) -HL02 #H2V0 #H2T0
elim (IH … HT01 … HT02 (L1.ⓓV0) … (L2.ⓓV0)) -IH -HT01 -HT02 /3 width=4 by lfpr_bind_repl_dx, ext2_pair/ -L0 -T0 #T #HT1 #HT2
elim (cpm_inv_lifts_sn … HT1 … L1 … HXT1) -T1 /3 width=2 by drops_refl, drops_drop/ #T1 #HT1 #HXT1
elim (cpm_inv_lifts_sn … HT2 … L2 … HXT2) -T2 /3 width=2 by drops_refl, drops_drop/ #T2 #HT2 #HXT2
lapply (lifts_inj … HT2 … HT1) -T #H destruct /2 width=3 by ex2_intro/
qed-.

fact cpr_conf_lfpr_flat_flat:
   ∀h,I,G,L0,V0,T0. (
      ∀L,T. ⦃G, L0, ⓕ{I}V0.T0⦄ ⊐+ ⦃G, L, T⦄ →
      ∀T1. ⦃G, L⦄ ⊢ T ➡[h] T1 → ∀T2. ⦃G, L⦄ ⊢ T ➡[h] T2 →
      ∀L1. ⦃G, L⦄ ⊢ ➡[h, T] L1 → ∀L2. ⦃G, L⦄ ⊢ ➡[h, T] L2 →
      ∃∃T0. ⦃G, L1⦄ ⊢ T1 ➡[h] T0 & ⦃G, L2⦄ ⊢ T2 ➡[h] T0
   ) →
   ∀V1. ⦃G, L0⦄ ⊢ V0 ➡[h] V1 → ∀T1. ⦃G, L0⦄ ⊢ T0 ➡[h] T1 →
   ∀V2. ⦃G, L0⦄ ⊢ V0 ➡[h] V2 → ∀T2. ⦃G, L0⦄ ⊢ T0 ➡[h] T2 →
   ∀L1. ⦃G, L0⦄ ⊢ ➡[h, ⓕ{I}V0.T0] L1 → ∀L2. ⦃G, L0⦄ ⊢ ➡[h, ⓕ{I}V0.T0] L2 →
   ∃∃T. ⦃G, L1⦄ ⊢ ⓕ{I}V1.T1 ➡[h] T & ⦃G, L2⦄ ⊢ ⓕ{I}V2.T2 ➡[h] T.
#h #I #G #L0 #V0 #T0 #IH #V1 #HV01 #T1 #HT01
#V2 #HV02 #T2 #HT02 #L1 #HL01 #L2 #HL02
elim (lfpr_inv_flat … HL01) -HL01 #H1V0 #H1T0
elim (lfpr_inv_flat … HL02) -HL02 #H2V0 #H2T0
elim (IH … HV01 … HV02 … H1V0 … H2V0) //
elim (IH … HT01 … HT02 … H1T0 … H2T0) /3 width=5 by cpr_flat, ex2_intro/
qed-.

fact cpr_conf_lfpr_flat_epsilon:
   ∀h,G,L0,V0,T0. (
      ∀L,T. ⦃G, L0, ⓝV0.T0⦄ ⊐+ ⦃G, L, T⦄ →
      ∀T1. ⦃G, L⦄ ⊢ T ➡[h] T1 → ∀T2. ⦃G, L⦄ ⊢ T ➡[h] T2 →
      ∀L1. ⦃G, L⦄ ⊢ ➡[h, T] L1 → ∀L2. ⦃G, L⦄ ⊢ ➡[h, T] L2 →
      ∃∃T0. ⦃G, L1⦄ ⊢ T1 ➡[h] T0 & ⦃G, L2⦄ ⊢ T2 ➡[h] T0
   ) →
   ∀V1,T1. ⦃G, L0⦄ ⊢ T0 ➡[h] T1 → ∀T2. ⦃G, L0⦄ ⊢ T0 ➡[h] T2 →
   ∀L1. ⦃G, L0⦄ ⊢ ➡[h, ⓝV0.T0] L1 → ∀L2. ⦃G, L0⦄ ⊢ ➡[h, ⓝV0.T0] L2 →
   ∃∃T. ⦃G, L1⦄ ⊢ ⓝV1.T1 ➡[h] T & ⦃G, L2⦄ ⊢ T2 ➡[h] T.
#h #G #L0 #V0 #T0 #IH #V1 #T1 #HT01
#T2 #HT02 #L1 #HL01 #L2 #HL02
elim (lfpr_inv_flat … HL01) -HL01 #_ #H1T0
elim (lfpr_inv_flat … HL02) -HL02 #_ #H2T0
elim (IH … HT01 … HT02 … H1T0 … H2T0) // -L0 -V0 -T0 /3 width=3 by cpm_eps, ex2_intro/
qed-.

fact cpr_conf_lfpr_epsilon_epsilon:
   ∀h,G,L0,V0,T0. (
      ∀L,T. ⦃G, L0, ⓝV0.T0⦄ ⊐+ ⦃G, L, T⦄ →
      ∀T1. ⦃G, L⦄ ⊢ T ➡[h] T1 → ∀T2. ⦃G, L⦄ ⊢ T ➡[h] T2 →
      ∀L1. ⦃G, L⦄ ⊢ ➡[h, T] L1 → ∀L2. ⦃G, L⦄ ⊢ ➡[h, T] L2 →
      ∃∃T0. ⦃G, L1⦄ ⊢ T1 ➡[h] T0 & ⦃G, L2⦄ ⊢ T2 ➡[h] T0
   ) →
   ∀T1. ⦃G, L0⦄ ⊢ T0 ➡[h] T1 → ∀T2. ⦃G, L0⦄ ⊢ T0 ➡[h] T2 →
   ∀L1. ⦃G, L0⦄ ⊢ ➡[h, ⓝV0.T0] L1 → ∀L2. ⦃G, L0⦄ ⊢ ➡[h, ⓝV0.T0] L2 →
   ∃∃T. ⦃G, L1⦄ ⊢ T1 ➡[h] T & ⦃G, L2⦄ ⊢ T2 ➡[h] T.
#h #G #L0 #V0 #T0 #IH #T1 #HT01
#T2 #HT02 #L1 #HL01 #L2 #HL02
elim (lfpr_inv_flat … HL01) -HL01 #_ #H1T0
elim (lfpr_inv_flat … HL02) -HL02 #_ #H2T0
elim (IH … HT01 … HT02 … H1T0 … H2T0) // -L0 -V0 -T0 /2 width=3 by ex2_intro/
qed-.

fact cpr_conf_lfpr_flat_beta:
   ∀h,p,G,L0,V0,W0,T0. (
      ∀L,T. ⦃G, L0, ⓐV0.ⓛ{p}W0.T0⦄ ⊐+ ⦃G, L, T⦄ →
      ∀T1. ⦃G, L⦄ ⊢ T ➡[h] T1 → ∀T2. ⦃G, L⦄ ⊢ T ➡[h] T2 →
      ∀L1. ⦃G, L⦄ ⊢ ➡[h, T] L1 → ∀L2. ⦃G, L⦄ ⊢ ➡[h, T] L2 →
      ∃∃T0. ⦃G, L1⦄ ⊢ T1 ➡[h] T0 & ⦃G, L2⦄ ⊢ T2 ➡[h] T0
   ) →
   ∀V1. ⦃G, L0⦄ ⊢ V0 ➡[h] V1 → ∀T1. ⦃G, L0⦄ ⊢ ⓛ{p}W0.T0 ➡[h] T1 →
   ∀V2. ⦃G, L0⦄ ⊢ V0 ➡[h] V2 → ∀W2. ⦃G, L0⦄ ⊢ W0 ➡[h] W2 → ∀T2. ⦃G, L0.ⓛW0⦄ ⊢ T0 ➡[h] T2 →
   ∀L1. ⦃G, L0⦄ ⊢ ➡[h, ⓐV0.ⓛ{p}W0.T0] L1 → ∀L2. ⦃G, L0⦄ ⊢ ➡[h, ⓐV0.ⓛ{p}W0.T0] L2 →
   ∃∃T. ⦃G, L1⦄ ⊢ ⓐV1.T1 ➡[h] T & ⦃G, L2⦄ ⊢ ⓓ{p}ⓝW2.V2.T2 ➡[h] T.
#h #p #G #L0 #V0 #W0 #T0 #IH #V1 #HV01 #X #H
#V2 #HV02 #W2 #HW02 #T2 #HT02 #L1 #HL01 #L2 #HL02
elim (cpm_inv_abst1 … H) -H #W1 #T1 #HW01 #HT01 #H destruct
elim (lfpr_inv_flat … HL01) -HL01 #H1V0 #HL01
elim (lfpr_inv_bind … HL01) -HL01 #H1W0 #H1T0
elim (lfpr_inv_flat … HL02) -HL02 #H2V0 #HL02
elim (lfpr_inv_bind … HL02) -HL02 #H2W0 #H2T0
elim (IH … HV01 … HV02 … H1V0 … H2V0) -HV01 -HV02 /2 width=1 by/ #V #HV1 #HV2
elim (IH … HW01 … HW02 … H1W0 … H2W0) /2 width=1 by/ #W #HW1 #HW2
elim (IH … HT01 … HT02 (L1.ⓛW1) … (L2.ⓛW2)) /3 width=4 by lfpr_bind_repl_dx, ext2_pair/ -L0 -V0 -W0 -T0 #T #HT1 #HT2
lapply (lsubr_cpm_trans … HT2 (L2.ⓓⓝW2.V2) ?) -HT2 /2 width=1 by lsubr_beta/ (**) (* full auto not tried *)
/4 width=5 by cpm_bind, cpr_flat, cpm_beta, ex2_intro/
qed-.

fact cpr_conf_lfpr_flat_theta:
   ∀h,p,G,L0,V0,W0,T0. (
      ∀L,T. ⦃G, L0, ⓐV0.ⓓ{p}W0.T0⦄ ⊐+ ⦃G, L, T⦄ →
      ∀T1. ⦃G, L⦄ ⊢ T ➡[h] T1 → ∀T2. ⦃G, L⦄ ⊢ T ➡[h] T2 →
      ∀L1. ⦃G, L⦄ ⊢ ➡[h, T] L1 → ∀L2. ⦃G, L⦄ ⊢ ➡[h, T] L2 →
      ∃∃T0. ⦃G, L1⦄ ⊢ T1 ➡[h] T0 & ⦃G, L2⦄ ⊢ T2 ➡[h] T0
   ) →
   ∀V1. ⦃G, L0⦄ ⊢ V0 ➡[h] V1 → ∀T1. ⦃G, L0⦄ ⊢ ⓓ{p}W0.T0 ➡[h] T1 →
   ∀V2. ⦃G, L0⦄ ⊢ V0 ➡[h] V2 → ∀U2. ⬆*[1] V2 ≡ U2 →
   ∀W2. ⦃G, L0⦄ ⊢ W0 ➡[h] W2 → ∀T2. ⦃G, L0.ⓓW0⦄ ⊢ T0 ➡[h] T2 →
   ∀L1. ⦃G, L0⦄ ⊢ ➡[h, ⓐV0.ⓓ{p}W0.T0] L1 → ∀L2. ⦃G, L0⦄ ⊢ ➡[h, ⓐV0.ⓓ{p}W0.T0] L2 →
   ∃∃T. ⦃G, L1⦄ ⊢ ⓐV1.T1 ➡[h] T & ⦃G, L2⦄ ⊢ ⓓ{p}W2.ⓐU2.T2 ➡[h] T.
#h #p #G #L0 #V0 #W0 #T0 #IH #V1 #HV01 #X #H
#V2 #HV02 #U2 #HVU2 #W2 #HW02 #T2 #HT02 #L1 #HL01 #L2 #HL02
elim (lfpr_inv_flat … HL01) -HL01 #H1V0 #HL01
elim (lfpr_inv_bind … HL01) -HL01 #H1W0 #H1T0
elim (lfpr_inv_flat … HL02) -HL02 #H2V0 #HL02
elim (lfpr_inv_bind … HL02) -HL02 #H2W0 #H2T0
elim (IH … HV01 … HV02 … H1V0 … H2V0) -HV01 -HV02 /2 width=1 by/ #V #HV1 #HV2
elim (cpm_lifts_sn … HV2 … (L2.ⓓW2) … HVU2) -HVU2 /3 width=2 by drops_refl, drops_drop/ #U #HVU #HU2
elim (cpm_inv_abbr1 … H) -H *
[ #W1 #T1 #HW01 #HT01 #H destruct
  elim (IH … HW01 … HW02 … H1W0 … H2W0) /2 width=1 by/
  elim (IH … HT01 … HT02 (L1.ⓓW1) … (L2.ⓓW2)) /3 width=4 by lfpr_bind_repl_dx, ext2_pair/ -L0 -V0 -W0 -T0
  /4 width=7 by cpm_bind, cpr_flat, cpm_theta, ex2_intro/
| #T1 #HT01 #HXT1 #H destruct
  elim (IH … HT01 … HT02 (L1.ⓓW2) … (L2.ⓓW2)) /3 width=4 by lfpr_bind_repl_dx, ext2_pair/ -L0 -V0 -W0 -T0 #T #HT1 #HT2
  elim (cpm_inv_lifts_sn … HT1 … L1 … HXT1) -HXT1
  /4 width=9 by cpr_flat, cpm_zeta, drops_refl, drops_drop, lifts_flat, ex2_intro/
]
qed-.

fact cpr_conf_lfpr_beta_beta:
   ∀h,p,G,L0,V0,W0,T0. (
      ∀L,T. ⦃G, L0, ⓐV0.ⓛ{p}W0.T0⦄ ⊐+ ⦃G, L, T⦄ →
      ∀T1. ⦃G, L⦄ ⊢ T ➡[h] T1 → ∀T2. ⦃G, L⦄ ⊢ T ➡[h] T2 →
      ∀L1. ⦃G, L⦄ ⊢ ➡[h, T] L1 → ∀L2. ⦃G, L⦄ ⊢ ➡[h, T] L2 →
      ∃∃T0. ⦃G, L1⦄ ⊢ T1 ➡[h] T0 & ⦃G, L2⦄ ⊢ T2 ➡[h] T0
   ) →
   ∀V1. ⦃G, L0⦄ ⊢ V0 ➡[h] V1 → ∀W1. ⦃G, L0⦄ ⊢ W0 ➡[h] W1 → ∀T1. ⦃G, L0.ⓛW0⦄ ⊢ T0 ➡[h] T1 →
   ∀V2. ⦃G, L0⦄ ⊢ V0 ➡[h] V2 → ∀W2. ⦃G, L0⦄ ⊢ W0 ➡[h] W2 → ∀T2. ⦃G, L0.ⓛW0⦄ ⊢ T0 ➡[h] T2 →
   ∀L1. ⦃G, L0⦄ ⊢ ➡[h, ⓐV0.ⓛ{p}W0.T0] L1 → ∀L2. ⦃G, L0⦄ ⊢ ➡[h, ⓐV0.ⓛ{p}W0.T0] L2 →
   ∃∃T. ⦃G, L1⦄ ⊢ ⓓ{p}ⓝW1.V1.T1 ➡[h] T & ⦃G, L2⦄ ⊢ ⓓ{p}ⓝW2.V2.T2 ➡[h] T.
#h #p #G #L0 #V0 #W0 #T0 #IH #V1 #HV01 #W1 #HW01 #T1 #HT01
#V2 #HV02 #W2 #HW02 #T2 #HT02 #L1 #HL01 #L2 #HL02
elim (lfpr_inv_flat … HL01) -HL01 #H1V0 #HL01
elim (lfpr_inv_bind … HL01) -HL01 #H1W0 #H1T0
elim (lfpr_inv_flat … HL02) -HL02 #H2V0 #HL02
elim (lfpr_inv_bind … HL02) -HL02 #H2W0 #H2T0
elim (IH … HV01 … HV02 … H1V0 … H2V0) -HV01 -HV02 /2 width=1 by/ #V #HV1 #HV2
elim (IH … HW01 … HW02 … H1W0 … H2W0) /2 width=1/ #W #HW1 #HW2
elim (IH … HT01 … HT02 (L1.ⓛW1) … (L2.ⓛW2)) /3 width=4 by lfpr_bind_repl_dx, ext2_pair/ -L0 -V0 -W0 -T0 #T #HT1 #HT2
lapply (lsubr_cpm_trans … HT1 (L1.ⓓⓝW1.V1) ?) -HT1 /2 width=1 by lsubr_beta/
lapply (lsubr_cpm_trans … HT2 (L2.ⓓⓝW2.V2) ?) -HT2 /2 width=1 by lsubr_beta/
/4 width=5 by cpm_bind, cpr_flat, ex2_intro/ (**) (* full auto not tried *)
qed-.

(* Note: we don't use cpm_lifts_bi to preserve visual symmetry *)
fact cpr_conf_lfpr_theta_theta:
   ∀h,p,G,L0,V0,W0,T0. (
      ∀L,T. ⦃G, L0, ⓐV0.ⓓ{p}W0.T0⦄ ⊐+ ⦃G, L, T⦄ →
      ∀T1. ⦃G, L⦄ ⊢ T ➡[h] T1 → ∀T2. ⦃G, L⦄ ⊢ T ➡[h] T2 →
      ∀L1. ⦃G, L⦄ ⊢ ➡[h, T] L1 → ∀L2. ⦃G, L⦄ ⊢ ➡[h, T] L2 →
      ∃∃T0. ⦃G, L1⦄ ⊢ T1 ➡[h] T0 & ⦃G, L2⦄ ⊢ T2 ➡[h] T0
   ) →
   ∀V1. ⦃G, L0⦄ ⊢ V0 ➡[h] V1 → ∀U1. ⬆*[1] V1 ≡ U1 →
   ∀W1. ⦃G, L0⦄ ⊢ W0 ➡[h] W1 → ∀T1. ⦃G, L0.ⓓW0⦄ ⊢ T0 ➡[h] T1 →
   ∀V2. ⦃G, L0⦄ ⊢ V0 ➡[h] V2 → ∀U2. ⬆*[1] V2 ≡ U2 →
   ∀W2. ⦃G, L0⦄ ⊢ W0 ➡[h] W2 → ∀T2. ⦃G, L0.ⓓW0⦄ ⊢ T0 ➡[h] T2 →
   ∀L1. ⦃G, L0⦄ ⊢ ➡[h, ⓐV0.ⓓ{p}W0.T0] L1 → ∀L2. ⦃G, L0⦄ ⊢ ➡[h, ⓐV0.ⓓ{p}W0.T0] L2 →
   ∃∃T. ⦃G, L1⦄ ⊢ ⓓ{p}W1.ⓐU1.T1 ➡[h] T & ⦃G, L2⦄ ⊢ ⓓ{p}W2.ⓐU2.T2 ➡[h] T.
#h #p #G #L0 #V0 #W0 #T0 #IH #V1 #HV01 #U1 #HVU1 #W1 #HW01 #T1 #HT01
#V2 #HV02 #U2 #HVU2 #W2 #HW02 #T2 #HT02 #L1 #HL01 #L2 #HL02
elim (lfpr_inv_flat … HL01) -HL01 #H1V0 #HL01
elim (lfpr_inv_bind … HL01) -HL01 #H1W0 #H1T0
elim (lfpr_inv_flat … HL02) -HL02 #H2V0 #HL02
elim (lfpr_inv_bind … HL02) -HL02 #H2W0 #H2T0
elim (IH … HV01 … HV02 … H1V0 … H2V0) -HV01 -HV02 /2 width=1 by/ #V #HV1 #HV2
elim (IH … HW01 … HW02 … H1W0 … H2W0) /2 width=1 by/
elim (IH … HT01 … HT02 (L1.ⓓW1) … (L2.ⓓW2)) /3 width=4 by lfpr_bind_repl_dx, ext2_pair/ -L0 -V0 -W0 -T0
elim (cpm_lifts_sn … HV1 … (L1.ⓓW1) … HVU1) -HVU1 /3 width=2 by drops_refl, drops_drop/ #U #HVU
elim (cpm_lifts_sn … HV2 … (L2.ⓓW2) … HVU2) -HVU2 /3 width=2 by drops_refl, drops_drop/ #X #HX
lapply (lifts_mono … HX … HVU) -HX #H destruct
/4 width=7 by cpm_bind, cpr_flat, ex2_intro/ (**) (* full auto not tried *)
qed-.

theorem cpr_conf_lfpr: ∀h,G. R_confluent2_lfxs (cpm 0 h G) (cpm 0 h G) (cpm 0 h G) (cpm 0 h G).
#h #G #L0 #T0 @(fqup_wf_ind_eq (Ⓣ) … G L0 T0) -G -L0 -T0 #G #L #T #IH #G0 #L0 * [| * ]
[ #I0 #HG #HL #HT #T1 #H1 #T2 #H2 #L1 #HL01 #L2 #HL02 destruct
  elim (cpr_inv_atom1_drops … H1) -H1
  elim (cpr_inv_atom1_drops … H2) -H2
  [ #H2 #H1 destruct
    /2 width=1 by cpr_conf_lfpr_atom_atom/
  | * #K0 #V0 #V2 #i2 #HLK0 #HV02 #HVT2 #H2 #H1 destruct
    /3 width=10 by cpr_conf_lfpr_atom_delta/
  | #H2 * #K0 #V0 #V1 #i1 #HLK0 #HV01 #HVT1 #H1 destruct
    /4 width=10 by ex2_commute, cpr_conf_lfpr_atom_delta/
  | * #X #Y #V2 #z #H #HV02 #HVT2 #H2
    * #K0 #V0 #V1 #i #HLK0 #HV01 #HVT1 #H1 destruct
    /3 width=17 by cpr_conf_lfpr_delta_delta/
  ]
| #p #I #V0 #T0 #HG #HL #HT #X1 #H1 #X2 #H2 #L1 #HL01 #L2 #HL02 destruct
  elim (cpm_inv_bind1 … H1) -H1 *
  [ #V1 #T1 #HV01 #HT01 #H1
  | #T1 #HT01 #HXT1 #H11 #H12
  ]
  elim (cpm_inv_bind1 … H2) -H2 *
  [1,3: #V2 #T2 #HV02 #HT02 #H2
  |2,4: #T2 #HT02 #HXT2 #H21 #H22
  ] destruct
  [ /3 width=10 by cpr_conf_lfpr_bind_bind/
  | /4 width=11 by ex2_commute, cpr_conf_lfpr_bind_zeta/
  | /3 width=11 by cpr_conf_lfpr_bind_zeta/
  | /3 width=12 by cpr_conf_lfpr_zeta_zeta/
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
  [ /3 width=10 by cpr_conf_lfpr_flat_flat/
  | /4 width=8 by ex2_commute, cpr_conf_lfpr_flat_epsilon/
  | /4 width=12 by ex2_commute, cpr_conf_lfpr_flat_beta/
  | /4 width=14 by ex2_commute, cpr_conf_lfpr_flat_theta/
  | /3 width=8 by cpr_conf_lfpr_flat_epsilon/
  | /3 width=8 by cpr_conf_lfpr_epsilon_epsilon/
  | /3 width=12 by cpr_conf_lfpr_flat_beta/
  | /3 width=13 by cpr_conf_lfpr_beta_beta/
  | /3 width=14 by cpr_conf_lfpr_flat_theta/
  | /3 width=17 by cpr_conf_lfpr_theta_theta/
  ]
]
qed-.

(* Basic_1: includes: pr0_confluence pr2_confluence *)
theorem cpr_conf: ∀h,G,L. confluent … (cpm 0 h G L).
/2 width=6 by cpr_conf_lfpr/ qed-.

(* Properties with context-sensitive parallel r-transition for terms ********)

lemma lfpr_cpr_conf_dx: ∀h,G,L0,T0,T1. ⦃G, L0⦄ ⊢ T0 ➡[h] T1 → ∀L1. ⦃G, L0⦄ ⊢ ➡[h, T0] L1 →
                        ∃∃T. ⦃G, L1⦄ ⊢ T0 ➡[h] T & ⦃G, L1⦄ ⊢ T1 ➡[h] T.
#h #G #L0 #T0 #T1 #HT01 #L1 #HL01
elim (cpr_conf_lfpr … HT01 T0 … HL01 … HL01) /2 width=3 by ex2_intro/
qed-.

lemma lfpr_cpr_conf_sn: ∀h,G,L0,T0,T1. ⦃G, L0⦄ ⊢ T0 ➡[h] T1 → ∀L1. ⦃G, L0⦄ ⊢ ➡[h, T0] L1 →
                        ∃∃T. ⦃G, L1⦄ ⊢ T0 ➡[h] T & ⦃G, L0⦄ ⊢ T1 ➡[h] T.
#h #G #L0 #T0 #T1 #HT01 #L1 #HL01
elim (cpr_conf_lfpr … HT01 T0 … L0 … HL01) /2 width=3 by ex2_intro/
qed-.

(* Main properties **********************************************************)

theorem lfpr_conf: ∀h,G,T. confluent … (lfpr h G T).
/3 width=6 by cpr_conf_lfpr, lfpr_fsle_comp, lfxs_conf/ qed-.

theorem lfpr_bind: ∀h,G,L1,L2,V1. ⦃G, L1⦄ ⊢ ➡[h, V1] L2 →
                   ∀I,V2,T. ⦃G, L1.ⓑ{I}V1⦄ ⊢ ➡[h, T] L2.ⓑ{I}V2 →
                   ∀p. ⦃G, L1⦄ ⊢ ➡[h, ⓑ{p,I}V1.T] L2.
/2 width=2 by lfxs_bind/ qed.

theorem lfpr_flat: ∀h,G,L1,L2,V. ⦃G, L1⦄ ⊢ ➡[h, V] L2 →
                   ∀I,T. ⦃G, L1⦄ ⊢ ➡[h, T] L2 → ⦃G, L1⦄ ⊢ ➡[h, ⓕ{I}V.T] L2.
/2 width=1 by lfxs_flat/ qed.

theorem lfpr_bind_void: ∀h,G,L1,L2,V. ⦃G, L1⦄ ⊢ ➡[h, V] L2 →
                        ∀T. ⦃G, L1.ⓧ⦄ ⊢ ➡[h, T] L2.ⓧ →
                        ∀p,I. ⦃G, L1⦄ ⊢ ➡[h, ⓑ{p,I}V.T] L2.
/2 width=1 by lfxs_bind_void/ qed.
