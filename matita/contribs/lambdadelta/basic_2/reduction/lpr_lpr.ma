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

include "basic_2/substitution/lpx_sn_lpx_sn.ma".
include "basic_2/multiple/fqup.ma".
include "basic_2/reduction/lpr_drop.ma".

(* SN PARALLEL REDUCTION FOR LOCAL ENVIRONMENTS *****************************)

(* Main properties on context-sensitive parallel reduction for terms ********)

fact cpr_conf_lpr_atom_atom:
   ∀I,G,L1,L2. ∃∃T. ⦃G, L1⦄ ⊢ ⓪{I} ➡ T & ⦃G, L2⦄ ⊢ ⓪{I} ➡ T.
/2 width=3 by cpr_atom, ex2_intro/ qed-.

fact cpr_conf_lpr_atom_delta:
   ∀G,L0,i. (
      ∀L,T. ⦃G, L0, #i⦄ ⊐+ ⦃G, L, T⦄ →
      ∀T1. ⦃G, L⦄ ⊢ T ➡ T1 → ∀T2. ⦃G, L⦄ ⊢ T ➡ T2 →
      ∀L1. ⦃G, L⦄ ⊢ ➡ L1 → ∀L2. ⦃G, L⦄ ⊢ ➡ L2 →
      ∃∃T0. ⦃G, L1⦄ ⊢ T1 ➡ T0 & ⦃G, L2⦄ ⊢ T2 ➡ T0
   ) →
   ∀K0,V0. ⇩[i] L0 ≡ K0.ⓓV0 →
   ∀V2. ⦃G, K0⦄ ⊢ V0 ➡ V2 → ∀T2. ⇧[O, i + 1] V2 ≡ T2 →
   ∀L1. ⦃G, L0⦄ ⊢ ➡ L1 → ∀L2. ⦃G, L0⦄ ⊢ ➡ L2 →
   ∃∃T. ⦃G, L1⦄ ⊢ #i ➡ T & ⦃G, L2⦄ ⊢ T2 ➡ T.
#G #L0 #i #IH #K0 #V0 #HLK0 #V2 #HV02 #T2 #HVT2 #L1 #HL01 #L2 #HL02
elim (lpr_drop_conf … HLK0 … HL01) -HL01 #X1 #H1 #HLK1
elim (lpr_inv_pair1 … H1) -H1 #K1 #V1 #HK01 #HV01 #H destruct
elim (lpr_drop_conf … HLK0 … HL02) -HL02 #X2 #H2 #HLK2
elim (lpr_inv_pair1 … H2) -H2 #K2 #W2 #HK02 #_ #H destruct
lapply (drop_fwd_drop2 … HLK2) -W2 #HLK2
lapply (fqup_lref … G … HLK0) -HLK0 #HLK0
elim (IH … HLK0 … HV01 … HV02 … HK01 … HK02) -L0 -K0 -V0 #V #HV1 #HV2
elim (lift_total V 0 (i+1))
/3 width=12 by cpr_lift, cpr_delta, ex2_intro/
qed-.

(* Basic_1: includes: pr0_delta_delta pr2_delta_delta *)
fact cpr_conf_lpr_delta_delta:
   ∀G,L0,i. (
      ∀L,T. ⦃G, L0, #i⦄ ⊐+ ⦃G, L, T⦄ →
      ∀T1. ⦃G, L⦄ ⊢ T ➡ T1 → ∀T2. ⦃G, L⦄ ⊢ T ➡ T2 →
      ∀L1. ⦃G, L⦄ ⊢ ➡ L1 → ∀L2. ⦃G, L⦄ ⊢ ➡ L2 →
      ∃∃T0. ⦃G, L1⦄ ⊢ T1 ➡ T0 & ⦃G, L2⦄ ⊢ T2 ➡ T0
   ) →
   ∀K0,V0. ⇩[i] L0 ≡ K0.ⓓV0 →
   ∀V1. ⦃G, K0⦄ ⊢ V0 ➡ V1 → ∀T1. ⇧[O, i + 1] V1 ≡ T1 →
   ∀KX,VX. ⇩[i] L0 ≡ KX.ⓓVX →
   ∀V2. ⦃G, KX⦄ ⊢ VX ➡ V2 → ∀T2. ⇧[O, i + 1] V2 ≡ T2 →
   ∀L1. ⦃G, L0⦄ ⊢ ➡ L1 → ∀L2. ⦃G, L0⦄ ⊢ ➡ L2 →
   ∃∃T. ⦃G, L1⦄ ⊢ T1 ➡ T & ⦃G, L2⦄ ⊢ T2 ➡ T.
#G #L0 #i #IH #K0 #V0 #HLK0 #V1 #HV01 #T1 #HVT1
#KX #VX #H #V2 #HV02 #T2 #HVT2 #L1 #HL01 #L2 #HL02
lapply (drop_mono … H … HLK0) -H #H destruct
elim (lpr_drop_conf … HLK0 … HL01) -HL01 #X1 #H1 #HLK1
elim (lpr_inv_pair1 … H1) -H1 #K1 #W1 #HK01 #_ #H destruct
lapply (drop_fwd_drop2 … HLK1) -W1 #HLK1
elim (lpr_drop_conf … HLK0 … HL02) -HL02 #X2 #H2 #HLK2
elim (lpr_inv_pair1 … H2) -H2 #K2 #W2 #HK02 #_ #H destruct
lapply (drop_fwd_drop2 … HLK2) -W2 #HLK2
lapply (fqup_lref … G … HLK0) -HLK0 #HLK0
elim (IH … HLK0 … HV01 … HV02 … HK01 … HK02) -L0 -K0 -V0 #V #HV1 #HV2
elim (lift_total V 0 (i+1)) /3 width=12 by cpr_lift, ex2_intro/
qed-.

fact cpr_conf_lpr_bind_bind:
   ∀a,I,G,L0,V0,T0. (
      ∀L,T. ⦃G, L0, ⓑ{a,I}V0.T0⦄ ⊐+ ⦃G, L, T⦄ →
      ∀T1. ⦃G, L⦄ ⊢ T ➡ T1 → ∀T2. ⦃G, L⦄ ⊢ T ➡ T2 →
      ∀L1. ⦃G, L⦄ ⊢ ➡ L1 → ∀L2. ⦃G, L⦄ ⊢ ➡ L2 →
      ∃∃T0. ⦃G, L1⦄ ⊢ T1 ➡ T0 & ⦃G, L2⦄ ⊢ T2 ➡ T0
   ) →
   ∀V1. ⦃G, L0⦄ ⊢ V0 ➡ V1 → ∀T1. ⦃G, L0.ⓑ{I}V0⦄ ⊢ T0 ➡ T1 →
   ∀V2. ⦃G, L0⦄ ⊢ V0 ➡ V2 → ∀T2. ⦃G, L0.ⓑ{I}V0⦄ ⊢ T0 ➡ T2 →
   ∀L1. ⦃G, L0⦄ ⊢ ➡ L1 → ∀L2. ⦃G, L0⦄ ⊢ ➡ L2 →
   ∃∃T. ⦃G, L1⦄ ⊢ ⓑ{a,I}V1.T1 ➡ T & ⦃G, L2⦄ ⊢ ⓑ{a,I}V2.T2 ➡ T.
#a #I #G #L0 #V0 #T0 #IH #V1 #HV01 #T1 #HT01
#V2 #HV02 #T2 #HT02 #L1 #HL01 #L2 #HL02
elim (IH … HV01 … HV02 … HL01 … HL02) //
elim (IH … HT01 … HT02 (L1.ⓑ{I}V1) … (L2.ⓑ{I}V2)) -IH
/3 width=5 by lpr_pair, cpr_bind, ex2_intro/
qed-.

fact cpr_conf_lpr_bind_zeta:
   ∀G,L0,V0,T0. (
      ∀L,T. ⦃G, L0, +ⓓV0.T0⦄ ⊐+ ⦃G, L, T⦄ →
      ∀T1. ⦃G, L⦄ ⊢ T ➡ T1 → ∀T2. ⦃G, L⦄ ⊢ T ➡ T2 →
      ∀L1. ⦃G, L⦄ ⊢ ➡ L1 → ∀L2. ⦃G, L⦄ ⊢ ➡ L2 →
      ∃∃T0. ⦃G, L1⦄ ⊢ T1 ➡ T0 & ⦃G, L2⦄ ⊢ T2 ➡ T0
   ) →
   ∀V1. ⦃G, L0⦄ ⊢ V0 ➡ V1 → ∀T1. ⦃G, L0.ⓓV0⦄ ⊢ T0 ➡ T1 →
   ∀T2. ⦃G, L0.ⓓV0⦄ ⊢ T0 ➡ T2 → ∀X2. ⇧[O, 1] X2 ≡ T2 →
   ∀L1. ⦃G, L0⦄ ⊢ ➡ L1 → ∀L2. ⦃G, L0⦄ ⊢ ➡ L2 →
   ∃∃T. ⦃G, L1⦄ ⊢ +ⓓV1.T1 ➡ T & ⦃G, L2⦄ ⊢ X2 ➡ T.
#G #L0 #V0 #T0 #IH #V1 #HV01 #T1 #HT01
#T2 #HT02 #X2 #HXT2 #L1 #HL01 #L2 #HL02
elim (IH … HT01 … HT02 (L1.ⓓV1) … (L2.ⓓV1)) -IH -HT01 -HT02 /2 width=1 by lpr_pair/ -L0 -V0 -T0 #T #HT1 #HT2
elim (cpr_inv_lift1 … HT2 L2 … HXT2) -T2 /3 width=3 by cpr_zeta, drop_drop, ex2_intro/
qed-.

fact cpr_conf_lpr_zeta_zeta:
   ∀G,L0,V0,T0. (
      ∀L,T. ⦃G, L0, +ⓓV0.T0⦄ ⊐+ ⦃G, L, T⦄ →
      ∀T1. ⦃G, L⦄ ⊢ T ➡ T1 → ∀T2. ⦃G, L⦄ ⊢ T ➡ T2 →
      ∀L1. ⦃G, L⦄ ⊢ ➡ L1 → ∀L2. ⦃G, L⦄ ⊢ ➡ L2 →
      ∃∃T0. ⦃G, L1⦄ ⊢ T1 ➡ T0 & ⦃G, L2⦄ ⊢ T2 ➡ T0
   ) →
   ∀T1. ⦃G, L0.ⓓV0⦄ ⊢ T0 ➡ T1 → ∀X1. ⇧[O, 1] X1 ≡ T1 →
   ∀T2. ⦃G, L0.ⓓV0⦄ ⊢ T0 ➡ T2 → ∀X2. ⇧[O, 1] X2 ≡ T2 →
   ∀L1. ⦃G, L0⦄ ⊢ ➡ L1 → ∀L2. ⦃G, L0⦄ ⊢ ➡ L2 →
   ∃∃T. ⦃G, L1⦄ ⊢ X1 ➡ T & ⦃G, L2⦄ ⊢ X2 ➡ T.
#G #L0 #V0 #T0 #IH #T1 #HT01 #X1 #HXT1
#T2 #HT02 #X2 #HXT2 #L1 #HL01 #L2 #HL02
elim (IH … HT01 … HT02 (L1.ⓓV0) … (L2.ⓓV0)) -IH -HT01 -HT02 /2 width=1 by lpr_pair/ -L0 -T0 #T #HT1 #HT2
elim (cpr_inv_lift1 … HT1 L1 … HXT1) -T1 /2 width=2 by drop_drop/ #T1 #HT1 #HXT1
elim (cpr_inv_lift1 … HT2 L2 … HXT2) -T2 /2 width=2 by drop_drop/ #T2 #HT2 #HXT2
lapply (lift_inj … HT2 … HT1) -T #H destruct /2 width=3 by ex2_intro/
qed-.

fact cpr_conf_lpr_flat_flat:
   ∀I,G,L0,V0,T0. (
      ∀L,T. ⦃G, L0, ⓕ{I}V0.T0⦄ ⊐+ ⦃G, L, T⦄ →
      ∀T1. ⦃G, L⦄ ⊢ T ➡ T1 → ∀T2. ⦃G, L⦄ ⊢ T ➡ T2 →
      ∀L1. ⦃G, L⦄ ⊢ ➡ L1 → ∀L2. ⦃G, L⦄ ⊢ ➡ L2 →
      ∃∃T0. ⦃G, L1⦄ ⊢ T1 ➡ T0 & ⦃G, L2⦄ ⊢ T2 ➡ T0
   ) →
   ∀V1. ⦃G, L0⦄ ⊢ V0 ➡ V1 → ∀T1. ⦃G, L0⦄ ⊢ T0 ➡ T1 →
   ∀V2. ⦃G, L0⦄ ⊢ V0 ➡ V2 → ∀T2. ⦃G, L0⦄ ⊢ T0 ➡ T2 →
   ∀L1. ⦃G, L0⦄ ⊢ ➡ L1 → ∀L2. ⦃G, L0⦄ ⊢ ➡ L2 →
   ∃∃T. ⦃G, L1⦄ ⊢ ⓕ{I}V1.T1 ➡ T & ⦃G, L2⦄ ⊢ ⓕ{I}V2.T2 ➡ T.
#I #G #L0 #V0 #T0 #IH #V1 #HV01 #T1 #HT01
#V2 #HV02 #T2 #HT02 #L1 #HL01 #L2 #HL02
elim (IH … HV01 … HV02 … HL01 … HL02) //
elim (IH … HT01 … HT02 … HL01 … HL02) /3 width=5 by cpr_flat, ex2_intro/
qed-.

fact cpr_conf_lpr_flat_eps:
   ∀G,L0,V0,T0. (
      ∀L,T. ⦃G, L0, ⓝV0.T0⦄ ⊐+ ⦃G, L, T⦄ →
      ∀T1. ⦃G, L⦄ ⊢ T ➡ T1 → ∀T2. ⦃G, L⦄ ⊢ T ➡ T2 →
      ∀L1. ⦃G, L⦄ ⊢ ➡ L1 → ∀L2. ⦃G, L⦄ ⊢ ➡ L2 →
      ∃∃T0. ⦃G, L1⦄ ⊢ T1 ➡ T0 & ⦃G, L2⦄ ⊢ T2 ➡ T0
   ) →
   ∀V1,T1. ⦃G, L0⦄ ⊢ T0 ➡ T1 → ∀T2. ⦃G, L0⦄ ⊢ T0 ➡ T2 →
   ∀L1. ⦃G, L0⦄ ⊢ ➡ L1 → ∀L2. ⦃G, L0⦄ ⊢ ➡ L2 →
   ∃∃T. ⦃G, L1⦄ ⊢ ⓝV1.T1 ➡ T & ⦃G, L2⦄ ⊢ T2 ➡ T.
#G #L0 #V0 #T0 #IH #V1 #T1 #HT01
#T2 #HT02 #L1 #HL01 #L2 #HL02
elim (IH … HT01 … HT02 … HL01 … HL02) // -L0 -V0 -T0 /3 width=3 by cpr_eps, ex2_intro/
qed-.

fact cpr_conf_lpr_eps_eps:
   ∀G,L0,V0,T0. (
      ∀L,T. ⦃G, L0, ⓝV0.T0⦄ ⊐+ ⦃G, L, T⦄ →
      ∀T1. ⦃G, L⦄ ⊢ T ➡ T1 → ∀T2. ⦃G, L⦄ ⊢ T ➡ T2 →
      ∀L1. ⦃G, L⦄ ⊢ ➡ L1 → ∀L2. ⦃G, L⦄ ⊢ ➡ L2 →
      ∃∃T0. ⦃G, L1⦄ ⊢ T1 ➡ T0 & ⦃G, L2⦄ ⊢ T2 ➡ T0
   ) →
   ∀T1. ⦃G, L0⦄ ⊢ T0 ➡ T1 → ∀T2. ⦃G, L0⦄ ⊢ T0 ➡ T2 →
   ∀L1. ⦃G, L0⦄ ⊢ ➡ L1 → ∀L2. ⦃G, L0⦄ ⊢ ➡ L2 →
   ∃∃T. ⦃G, L1⦄ ⊢ T1 ➡ T & ⦃G, L2⦄ ⊢ T2 ➡ T.
#G #L0 #V0 #T0 #IH #T1 #HT01
#T2 #HT02 #L1 #HL01 #L2 #HL02
elim (IH … HT01 … HT02 … HL01 … HL02) // -L0 -V0 -T0 /2 width=3 by ex2_intro/
qed-.

fact cpr_conf_lpr_flat_beta:
   ∀a,G,L0,V0,W0,T0. (
      ∀L,T. ⦃G, L0, ⓐV0.ⓛ{a}W0.T0⦄ ⊐+ ⦃G, L, T⦄ →
      ∀T1. ⦃G, L⦄ ⊢ T ➡ T1 → ∀T2. ⦃G, L⦄ ⊢ T ➡ T2 →
      ∀L1. ⦃G, L⦄ ⊢ ➡ L1 → ∀L2. ⦃G, L⦄ ⊢ ➡ L2 →
      ∃∃T0. ⦃G, L1⦄ ⊢ T1 ➡ T0 & ⦃G, L2⦄ ⊢ T2 ➡ T0
   ) →
   ∀V1. ⦃G, L0⦄ ⊢ V0 ➡ V1 → ∀T1. ⦃G, L0⦄ ⊢ ⓛ{a}W0.T0 ➡ T1 →
   ∀V2. ⦃G, L0⦄ ⊢ V0 ➡ V2 → ∀W2. ⦃G, L0⦄ ⊢ W0 ➡ W2 → ∀T2. ⦃G, L0.ⓛW0⦄ ⊢ T0 ➡ T2 →
   ∀L1. ⦃G, L0⦄ ⊢ ➡ L1 → ∀L2. ⦃G, L0⦄ ⊢ ➡ L2 →
   ∃∃T. ⦃G, L1⦄ ⊢ ⓐV1.T1 ➡ T & ⦃G, L2⦄ ⊢ ⓓ{a}ⓝW2.V2.T2 ➡ T.
#a #G #L0 #V0 #W0 #T0 #IH #V1 #HV01 #X #H
#V2 #HV02 #W2 #HW02 #T2 #HT02 #L1 #HL01 #L2 #HL02
elim (cpr_inv_abst1 … H) -H #W1 #T1 #HW01 #HT01 #H destruct
elim (IH … HV01 … HV02 … HL01 … HL02) -HV01 -HV02 /2 width=1 by/ #V #HV1 #HV2
elim (IH … HW01 … HW02 … HL01 … HL02) /2 width=1 by/ #W #HW1 #HW2
elim (IH … HT01 … HT02 (L1.ⓛW1) … (L2.ⓛW2)) /2 width=1 by lpr_pair/ -L0 -V0 -W0 -T0 #T #HT1 #HT2
lapply (lsubr_cpr_trans … HT2 (L2.ⓓⓝW2.V2) ?) -HT2 /2 width=1 by lsubr_beta/ (**) (* full auto not tried *)
/4 width=5 by cpr_bind, cpr_flat, cpr_beta, ex2_intro/
qed-.

(* Basic-1: includes:
            pr0_cong_upsilon_refl pr0_cong_upsilon_zeta
            pr0_cong_upsilon_cong pr0_cong_upsilon_delta
*)
fact cpr_conf_lpr_flat_theta:
   ∀a,G,L0,V0,W0,T0. (
      ∀L,T. ⦃G, L0, ⓐV0.ⓓ{a}W0.T0⦄ ⊐+ ⦃G, L, T⦄ →
      ∀T1. ⦃G, L⦄ ⊢ T ➡ T1 → ∀T2. ⦃G, L⦄ ⊢ T ➡ T2 →
      ∀L1. ⦃G, L⦄ ⊢ ➡ L1 → ∀L2. ⦃G, L⦄ ⊢ ➡ L2 →
      ∃∃T0. ⦃G, L1⦄ ⊢ T1 ➡ T0 & ⦃G, L2⦄ ⊢ T2 ➡ T0
   ) →
   ∀V1. ⦃G, L0⦄ ⊢ V0 ➡ V1 → ∀T1. ⦃G, L0⦄ ⊢ ⓓ{a}W0.T0 ➡ T1 →
   ∀V2. ⦃G, L0⦄ ⊢ V0 ➡ V2 → ∀U2. ⇧[O, 1] V2 ≡ U2 →
   ∀W2. ⦃G, L0⦄ ⊢ W0 ➡ W2 → ∀T2. ⦃G, L0.ⓓW0⦄ ⊢ T0 ➡ T2 →
   ∀L1. ⦃G, L0⦄ ⊢ ➡ L1 → ∀L2. ⦃G, L0⦄ ⊢ ➡ L2 →
   ∃∃T. ⦃G, L1⦄ ⊢ ⓐV1.T1 ➡ T & ⦃G, L2⦄ ⊢ ⓓ{a}W2.ⓐU2.T2 ➡ T.
#a #G #L0 #V0 #W0 #T0 #IH #V1 #HV01 #X #H
#V2 #HV02 #U2 #HVU2 #W2 #HW02 #T2 #HT02 #L1 #HL01 #L2 #HL02
elim (IH … HV01 … HV02 … HL01 … HL02) -HV01 -HV02 /2 width=1 by/ #V #HV1 #HV2
elim (lift_total V 0 1) #U #HVU
lapply (cpr_lift … HV2 (L2.ⓓW2) … HVU2 … HVU) -HVU2 /2 width=2 by drop_drop/ #HU2
elim (cpr_inv_abbr1 … H) -H *
[ #W1 #T1 #HW01 #HT01 #H destruct
  elim (IH … HW01 … HW02 … HL01 … HL02) /2 width=1 by/
  elim (IH … HT01 … HT02 (L1.ⓓW1) … (L2.ⓓW2)) /2 width=1 by lpr_pair/ -L0 -V0 -W0 -T0
  /4 width=7 by cpr_bind, cpr_flat, cpr_theta, ex2_intro/
| #T1 #HT01 #HXT1 #H destruct
  elim (IH … HT01 … HT02 (L1.ⓓW2) … (L2.ⓓW2)) /2 width=1 by lpr_pair/ -L0 -V0 -W0 -T0 #T #HT1 #HT2
  elim (cpr_inv_lift1 … HT1 L1 … HXT1) -HXT1
  /4 width=9 by cpr_flat, cpr_zeta, drop_drop, lift_flat, ex2_intro/
]
qed-.

fact cpr_conf_lpr_beta_beta:
   ∀a,G,L0,V0,W0,T0. (
      ∀L,T. ⦃G, L0, ⓐV0.ⓛ{a}W0.T0⦄ ⊐+ ⦃G, L, T⦄ →
      ∀T1. ⦃G, L⦄ ⊢ T ➡ T1 → ∀T2. ⦃G, L⦄ ⊢ T ➡ T2 →
      ∀L1. ⦃G, L⦄ ⊢ ➡ L1 → ∀L2. ⦃G, L⦄ ⊢ ➡ L2 →
      ∃∃T0. ⦃G, L1⦄ ⊢ T1 ➡ T0 & ⦃G, L2⦄ ⊢ T2 ➡ T0
   ) →
   ∀V1. ⦃G, L0⦄ ⊢ V0 ➡ V1 → ∀W1. ⦃G, L0⦄ ⊢ W0 ➡ W1 → ∀T1. ⦃G, L0.ⓛW0⦄ ⊢ T0 ➡ T1 →
   ∀V2. ⦃G, L0⦄ ⊢ V0 ➡ V2 → ∀W2. ⦃G, L0⦄ ⊢ W0 ➡ W2 → ∀T2. ⦃G, L0.ⓛW0⦄ ⊢ T0 ➡ T2 →
   ∀L1. ⦃G, L0⦄ ⊢ ➡ L1 → ∀L2. ⦃G, L0⦄ ⊢ ➡ L2 →
   ∃∃T. ⦃G, L1⦄ ⊢ ⓓ{a}ⓝW1.V1.T1 ➡ T & ⦃G, L2⦄ ⊢ ⓓ{a}ⓝW2.V2.T2 ➡ T.
#a #G #L0 #V0 #W0 #T0 #IH #V1 #HV01 #W1 #HW01 #T1 #HT01
#V2 #HV02 #W2 #HW02 #T2 #HT02 #L1 #HL01 #L2 #HL02
elim (IH … HV01 … HV02 … HL01 … HL02) -HV01 -HV02 /2 width=1 by/ #V #HV1 #HV2
elim (IH … HW01 … HW02 … HL01 … HL02) /2 width=1/ #W #HW1 #HW2
elim (IH … HT01 … HT02 (L1.ⓛW1) … (L2.ⓛW2)) /2 width=1 by lpr_pair/ -L0 -V0 -W0 -T0 #T #HT1 #HT2
lapply (lsubr_cpr_trans … HT1 (L1.ⓓⓝW1.V1) ?) -HT1 /2 width=1 by lsubr_beta/
lapply (lsubr_cpr_trans … HT2 (L2.ⓓⓝW2.V2) ?) -HT2 /2 width=1 by lsubr_beta/
/4 width=5 by cpr_bind, cpr_flat, ex2_intro/ (**) (* full auto not tried *)
qed-.

(* Basic_1: was: pr0_upsilon_upsilon *)
fact cpr_conf_lpr_theta_theta:
   ∀a,G,L0,V0,W0,T0. (
      ∀L,T. ⦃G, L0, ⓐV0.ⓓ{a}W0.T0⦄ ⊐+ ⦃G, L, T⦄ →
      ∀T1. ⦃G, L⦄ ⊢ T ➡ T1 → ∀T2. ⦃G, L⦄ ⊢ T ➡ T2 →
      ∀L1. ⦃G, L⦄ ⊢ ➡ L1 → ∀L2. ⦃G, L⦄ ⊢ ➡ L2 →
      ∃∃T0. ⦃G, L1⦄ ⊢ T1 ➡ T0 & ⦃G, L2⦄ ⊢ T2 ➡ T0
   ) →
   ∀V1. ⦃G, L0⦄ ⊢ V0 ➡ V1 → ∀U1. ⇧[O, 1] V1 ≡ U1 →
   ∀W1. ⦃G, L0⦄ ⊢ W0 ➡ W1 → ∀T1. ⦃G, L0.ⓓW0⦄ ⊢ T0 ➡ T1 →
   ∀V2. ⦃G, L0⦄ ⊢ V0 ➡ V2 → ∀U2. ⇧[O, 1] V2 ≡ U2 →
   ∀W2. ⦃G, L0⦄ ⊢ W0 ➡ W2 → ∀T2. ⦃G, L0.ⓓW0⦄ ⊢ T0 ➡ T2 →
   ∀L1. ⦃G, L0⦄ ⊢ ➡ L1 → ∀L2. ⦃G, L0⦄ ⊢ ➡ L2 →
   ∃∃T. ⦃G, L1⦄ ⊢ ⓓ{a}W1.ⓐU1.T1 ➡ T & ⦃G, L2⦄ ⊢ ⓓ{a}W2.ⓐU2.T2 ➡ T.
#a #G #L0 #V0 #W0 #T0 #IH #V1 #HV01 #U1 #HVU1 #W1 #HW01 #T1 #HT01
#V2 #HV02 #U2 #HVU2 #W2 #HW02 #T2 #HT02 #L1 #HL01 #L2 #HL02
elim (IH … HV01 … HV02 … HL01 … HL02) -HV01 -HV02 /2 width=1 by/ #V #HV1 #HV2
elim (IH … HW01 … HW02 … HL01 … HL02) /2 width=1 by/
elim (IH … HT01 … HT02 (L1.ⓓW1) … (L2.ⓓW2)) /2 width=1 by lpr_pair/ -L0 -V0 -W0 -T0
elim (lift_total V 0 1) #U #HVU
lapply (cpr_lift … HV1 (L1.ⓓW1) … HVU1 … HVU) -HVU1 /2 width=2 by drop_drop/
lapply (cpr_lift … HV2 (L2.ⓓW2) … HVU2 … HVU) -HVU2 /2 width=2 by drop_drop/
/4 width=7 by cpr_bind, cpr_flat, ex2_intro/ (**) (* full auto not tried *)
qed-.

theorem cpr_conf_lpr: ∀G. lpx_sn_confluent (cpr G) (cpr G).
#G #L0 #T0 @(fqup_wf_ind_eq … G L0 T0) -G -L0 -T0 #G #L #T #IH #G0 #L0 * [| * ]
[ #I0 #HG #HL #HT #T1 #H1 #T2 #H2 #L1 #HL01 #L2 #HL02 destruct
  elim (cpr_inv_atom1 … H1) -H1
  elim (cpr_inv_atom1 … H2) -H2
  [ #H2 #H1 destruct
    /2 width=1 by cpr_conf_lpr_atom_atom/
  | * #K0 #V0 #V2 #i2 #HLK0 #HV02 #HVT2 #H2 #H1 destruct
    /3 width=10 by cpr_conf_lpr_atom_delta/
  | #H2 * #K0 #V0 #V1 #i1 #HLK0 #HV01 #HVT1 #H1 destruct
    /4 width=10 by ex2_commute, cpr_conf_lpr_atom_delta/
  | * #X #Y #V2 #z #H #HV02 #HVT2 #H2
    * #K0 #V0 #V1 #i #HLK0 #HV01 #HVT1 #H1 destruct
    /3 width=17 by cpr_conf_lpr_delta_delta/
  ]
| #a #I #V0 #T0 #HG #HL #HT #X1 #H1 #X2 #H2 #L1 #HL01 #L2 #HL02 destruct
  elim (cpr_inv_bind1 … H1) -H1 *
  [ #V1 #T1 #HV01 #HT01 #H1
  | #T1 #HT01 #HXT1 #H11 #H12
  ]
  elim (cpr_inv_bind1 … H2) -H2 *
  [1,3: #V2 #T2 #HV02 #HT02 #H2
  |2,4: #T2 #HT02 #HXT2 #H21 #H22
  ] destruct
  [ /3 width=10 by cpr_conf_lpr_bind_bind/
  | /4 width=11 by ex2_commute, cpr_conf_lpr_bind_zeta/
  | /3 width=11 by cpr_conf_lpr_bind_zeta/
  | /3 width=12 by cpr_conf_lpr_zeta_zeta/
  ]
| #I #V0 #T0 #HG #HL #HT #X1 #H1 #X2 #H2 #L1 #HL01 #L2 #HL02 destruct
  elim (cpr_inv_flat1 … H1) -H1 *
  [ #V1 #T1 #HV01 #HT01 #H1
  | #HX1 #H1
  | #a1 #V1 #Y1 #W1 #Z1 #T1 #HV01 #HYW1 #HZT1 #H11 #H12 #H13
  | #a1 #V1 #U1 #Y1 #W1 #Z1 #T1 #HV01 #HVU1 #HYW1 #HZT1 #H11 #H12 #H13
  ]
  elim (cpr_inv_flat1 … H2) -H2 *
  [1,5,9,13: #V2 #T2 #HV02 #HT02 #H2
  |2,6,10,14: #HX2 #H2
  |3,7,11,15: #a2 #V2 #Y2 #W2 #Z2 #T2 #HV02 #HYW2 #HZT2 #H21 #H22 #H23
  |4,8,12,16: #a2 #V2 #U2 #Y2 #W2 #Z2 #T2 #HV02 #HVU2 #HYW2 #HZT2 #H21 #H22 #H23
  ] destruct
  [ /3 width=10 by cpr_conf_lpr_flat_flat/
  | /4 width=8 by ex2_commute, cpr_conf_lpr_flat_eps/
  | /4 width=12 by ex2_commute, cpr_conf_lpr_flat_beta/
  | /4 width=14 by ex2_commute, cpr_conf_lpr_flat_theta/
  | /3 width=8 by cpr_conf_lpr_flat_eps/
  | /3 width=7 by cpr_conf_lpr_eps_eps/
  | /3 width=12 by cpr_conf_lpr_flat_beta/
  | /3 width=13 by cpr_conf_lpr_beta_beta/
  | /3 width=14 by cpr_conf_lpr_flat_theta/
  | /3 width=17 by cpr_conf_lpr_theta_theta/
  ]
]
qed-.

(* Basic_1: includes: pr0_confluence pr2_confluence *)
theorem cpr_conf: ∀G,L. confluent … (cpr G L).
/2 width=6 by cpr_conf_lpr/ qed-.

(* Properties on context-sensitive parallel reduction for terms *************)

lemma lpr_cpr_conf_dx: ∀G,L0,T0,T1. ⦃G, L0⦄ ⊢ T0 ➡ T1 → ∀L1. ⦃G, L0⦄ ⊢ ➡ L1 →
                       ∃∃T. ⦃G, L1⦄ ⊢ T0 ➡ T & ⦃G, L1⦄ ⊢ T1 ➡ T.
#G #L0 #T0 #T1 #HT01 #L1 #HL01
elim (cpr_conf_lpr … HT01 T0 … HL01 … HL01) /2 width=3 by ex2_intro/
qed-.

lemma lpr_cpr_conf_sn: ∀G,L0,T0,T1. ⦃G, L0⦄ ⊢ T0 ➡ T1 → ∀L1. ⦃G, L0⦄ ⊢ ➡ L1 →
                       ∃∃T. ⦃G, L1⦄ ⊢ T0 ➡ T & ⦃G, L0⦄ ⊢ T1 ➡ T.
#G #L0 #T0 #T1 #HT01 #L1 #HL01
elim (cpr_conf_lpr … HT01 T0 … L0 … HL01) /2 width=3 by ex2_intro/
qed-.

(* Main properties **********************************************************)

theorem lpr_conf: ∀G. confluent … (lpr G).
/3 width=6 by lpx_sn_conf, cpr_conf_lpr/
qed-.
