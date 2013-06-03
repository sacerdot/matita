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

include "basic_2/grammar/lpx_sn_lpx_sn.ma".
include "basic_2/substitution/fsupp.ma".
include "basic_2/substitution/lpss_ldrop.ma".
include "basic_2/reduction/lpr_ldrop.ma".

(* SN PARALLEL REDUCTION FOR LOCAL ENVIRONMENTS *****************************)

(* Properties on context-sensitive parallel substitution for terms **********)

fact cpr_cpss_conf_lpr_lpss_atom_atom:
   ∀I,L1,L2. ∃∃T. L1 ⊢ ⓪{I} ▶* T & L2 ⊢ ⓪{I} ➡ T.
/2 width=3/ qed-.

fact cpr_cpss_conf_lpr_lpss_atom_delta:
   ∀L0,i. (
      ∀L,T. ⦃L0, #i⦄ ⊃+ ⦃L, T⦄ →
      ∀T1. L ⊢ T ➡ T1 → ∀T2. L ⊢ T ▶* T2 →
      ∀L1. L ⊢ ➡ L1 → ∀L2. L ⊢ ▶* L2 →
      ∃∃T0. L1 ⊢ T1 ▶* T0 & L2 ⊢ T2 ➡ T0
   ) →
   ∀K0,V0. ⇩[O, i] L0 ≡ K0.ⓓV0 →
   ∀V2. K0 ⊢ V0 ▶* V2 → ∀T2. ⇧[O, i + 1] V2 ≡ T2 →
   ∀L1. L0 ⊢ ➡ L1 → ∀L2. L0 ⊢ ▶* L2 →
   ∃∃T. L1 ⊢ #i ▶* T & L2 ⊢ T2 ➡ T.
#L0 #i #IH #K0 #V0 #HLK0 #V2 #HV02 #T2 #HVT2 #L1 #HL01 #L2 #HL02
elim (lpr_ldrop_conf … HLK0 … HL01) -HL01 #X1 #H1 #HLK1
elim (lpr_inv_pair1 … H1) -H1 #K1 #V1 #HK01 #HV01 #H destruct
elim (lpss_ldrop_conf … HLK0 … HL02) -HL02 #X2 #H2 #HLK2
elim (lpss_inv_pair1 … H2) -H2 #K2 #W2 #HK02 #_ #H destruct
lapply (ldrop_fwd_ldrop2 … HLK2) -W2 #HLK2
lapply (fsupp_lref … HLK0) -HLK0 #HLK0
elim (IH … HLK0 … HV01 … HV02 … HK01 … HK02) -L0 -K0 -V0 #V #HV1 #HV2
elim (lift_total V 0 (i+1)) #T #HVT
lapply (cpr_lift … HV2 … HLK2 … HVT2 … HVT) -K2 -V2 /3 width=6/
qed-.

fact cpr_cpss_conf_lpr_lpss_delta_atom:
   ∀L0,i. (
      ∀L,T.⦃L0, #i⦄ ⊃+ ⦃L, T⦄ →
      ∀T1. L ⊢ T ➡ T1 → ∀T2. L ⊢ T ▶* T2 →
      ∀L1. L ⊢ ➡ L1 → ∀L2. L ⊢ ▶* L2 →
      ∃∃T0. L1 ⊢ T1 ▶* T0 & L2 ⊢ T2 ➡ T0
   ) →
   ∀K0,V0. ⇩[O, i] L0 ≡ K0.ⓓV0 →
   ∀V1. K0 ⊢ V0 ➡ V1 → ∀T1. ⇧[O, i + 1] V1 ≡ T1 →
   ∀L1. L0 ⊢ ➡ L1 → ∀L2. L0 ⊢ ▶* L2 →
   ∃∃T. L1 ⊢ T1 ▶* T & L2 ⊢ #i ➡ T.
#L0 #i #IH #K0 #V0 #HLK0 #V1 #HV01 #T1 #HVT1 #L1 #HL01 #L2 #HL02
elim (lpss_ldrop_conf … HLK0 … HL02) -HL02 #X2 #H2 #HLK2
elim (lpss_inv_pair1 … H2) -H2 #K2 #V2 #HK02 #HV02 #H destruct
elim (lpr_ldrop_conf … HLK0 … HL01) -HL01 #X1 #H1 #HLK1
elim (lpr_inv_pair1 … H1) -H1 #K1 #W1 #HK01 #_ #H destruct
lapply (ldrop_fwd_ldrop2 … HLK1) -W1 #HLK1
lapply (fsupp_lref … HLK0) -HLK0 #HLK0
elim (IH … HLK0 … HV01 … HV02 … HK01 … HK02) -L0 -K0 -V0 #V #HV1 #HV2
elim (lift_total V 0 (i+1)) #T #HVT
lapply (cpss_lift … HV1 … HLK1 … HVT1 … HVT) -K1 -V1 /3 width=9/
qed-.

fact cpr_cpss_conf_lpr_lpss_delta_delta:
   ∀L0,i. (
      ∀L,T. ⦃L0, #i⦄ ⊃+ ⦃L, T⦄ →
      ∀T1. L ⊢ T ➡ T1 → ∀T2. L ⊢ T ▶* T2 →
      ∀L1. L ⊢ ➡ L1 → ∀L2. L ⊢ ▶* L2 →
      ∃∃T0. L1 ⊢ T1 ▶* T0 & L2 ⊢ T2 ➡ T0
   ) →
   ∀K0,V0. ⇩[O, i] L0 ≡ K0.ⓓV0 →
   ∀V1. K0 ⊢ V0 ➡ V1 → ∀T1. ⇧[O, i + 1] V1 ≡ T1 →
   ∀KX,VX. ⇩[O, i] L0 ≡ KX.ⓓVX →
   ∀V2. KX ⊢ VX ▶* V2 → ∀T2. ⇧[O, i + 1] V2 ≡ T2 →
   ∀L1. L0 ⊢ ➡ L1 → ∀L2. L0 ⊢ ▶* L2 →
   ∃∃T. L1 ⊢ T1 ▶* T & L2 ⊢ T2 ➡ T.
#L0 #i #IH #K0 #V0 #HLK0 #V1 #HV01 #T1 #HVT1
#KX #VX #H #V2 #HV02 #T2 #HVT2 #L1 #HL01 #L2 #HL02
lapply (ldrop_mono … H … HLK0) -H #H destruct
elim (lpr_ldrop_conf … HLK0 … HL01) -HL01 #X1 #H1 #HLK1
elim (lpr_inv_pair1 … H1) -H1 #K1 #W1 #HK01 #_ #H destruct
lapply (ldrop_fwd_ldrop2 … HLK1) -W1 #HLK1
elim (lpss_ldrop_conf … HLK0 … HL02) -HL02 #X2 #H2 #HLK2
elim (lpss_inv_pair1 … H2) -H2 #K2 #W2 #HK02 #_ #H destruct
lapply (ldrop_fwd_ldrop2 … HLK2) -W2 #HLK2
lapply (fsupp_lref … HLK0) -HLK0 #HLK0
elim (IH … HLK0 … HV01 … HV02 … HK01 … HK02) -L0 -K0 -V0 #V #HV1 #HV2
elim (lift_total V 0 (i+1)) #T #HVT
lapply (cpss_lift … HV1 … HLK1 … HVT1 … HVT) -K1 -V1
lapply (cpr_lift … HV2 … HLK2 … HVT2 … HVT) -K2 -V2 -V /2 width=3/
qed-.

fact cpr_cpss_conf_lpr_lpss_bind_bind:
   ∀a,I,L0,V0,T0. (
      ∀L,T. ⦃L0,ⓑ{a,I}V0.T0⦄ ⊃+ ⦃L, T⦄ →
      ∀T1. L ⊢ T ➡ T1 → ∀T2. L ⊢ T ▶* T2 →
      ∀L1. L ⊢ ➡ L1 → ∀L2. L ⊢ ▶* L2 →
      ∃∃T0. L1 ⊢ T1 ▶* T0 & L2 ⊢ T2 ➡ T0
   ) →
   ∀V1. L0 ⊢ V0 ➡ V1 → ∀T1. L0.ⓑ{I}V0 ⊢ T0 ➡ T1 →
   ∀V2. L0 ⊢ V0 ▶* V2 → ∀T2. L0.ⓑ{I}V0 ⊢ T0 ▶* T2 →
   ∀L1. L0 ⊢ ➡ L1 → ∀L2. L0 ⊢ ▶* L2 →
   ∃∃T. L1 ⊢ ⓑ{a,I}V1.T1 ▶* T & L2 ⊢ ⓑ{a,I}V2.T2 ➡ T.
#a #I #L0 #V0 #T0 #IH #V1 #HV01 #T1 #HT01
#V2 #HV02 #T2 #HT02 #L1 #HL01 #L2 #HL02
elim (IH … HV01 … HV02 … HL01 … HL02) //
elim (IH … HT01 … HT02 (L1.ⓑ{I}V1) … (L2.ⓑ{I}V2)) -IH // /2 width=1/ /3 width=5/
qed-.

fact cpr_cpss_conf_lpr_lpss_bind_zeta:
   ∀L0,V0,T0. (
      ∀L,T. ⦃L0,+ⓓV0.T0⦄ ⊃+ ⦃L, T⦄ →
      ∀T1. L ⊢ T ➡ T1 → ∀T2. L ⊢ T ▶* T2 →
      ∀L1. L ⊢ ➡ L1 → ∀L2. L ⊢ ▶* L2 →
      ∃∃T0. L1 ⊢ T1 ▶* T0 & L2 ⊢ T2 ➡ T0
   ) →
   ∀T1. L0.ⓓV0 ⊢ T0 ➡ T1 → ∀X1. ⇧[O, 1] X1 ≡ T1 →
   ∀V2. L0 ⊢ V0 ▶* V2 → ∀T2. L0.ⓓV0 ⊢ T0 ▶* T2 →
   ∀L1. L0 ⊢ ➡ L1 → ∀L2. L0 ⊢ ▶* L2 →
   ∃∃T. L1 ⊢ X1 ▶* T & L2 ⊢ +ⓓV2.T2 ➡ T.
#L0 #V0 #T0 #IH #T1 #HT01 #X1 #HXT1
#V2 #HV02 #T2 #HT02 #L1 #HL01 #L2 #HL02
elim (IH … HT01 … HT02 (L1.ⓓV2) … (L2.ⓓV2)) -IH -HT01 -HT02 // /2 width=1/ /3 width=1/ -L0 -V0 -T0 #T #HT1 #HT2
elim (cpss_inv_lift1 … HT1 L1 … HXT1) -T1 /2 width=1/ /3 width=9/
qed-.

fact cpr_cpss_conf_lpr_lpss_flat_flat:
   ∀I,L0,V0,T0. (
      ∀L,T. ⦃L0,ⓕ{I}V0.T0⦄ ⊃+ ⦃L, T⦄ →
      ∀T1. L ⊢ T ➡ T1 → ∀T2. L ⊢ T ▶* T2 →
      ∀L1. L ⊢ ➡ L1 → ∀L2. L ⊢ ▶* L2 →
      ∃∃T0. L1 ⊢ T1 ▶* T0 & L2 ⊢ T2 ➡ T0
   ) →
   ∀V1. L0 ⊢ V0 ➡ V1 → ∀T1. L0 ⊢ T0 ➡ T1 →
   ∀V2. L0 ⊢ V0 ▶* V2 → ∀T2. L0 ⊢ T0 ▶* T2 →
   ∀L1. L0 ⊢ ➡ L1 → ∀L2. L0 ⊢ ▶* L2 →
   ∃∃T. L1 ⊢ ⓕ{I}V1.T1 ▶* T & L2 ⊢ ⓕ{I}V2.T2 ➡ T.
#I #L0 #V0 #T0 #IH #V1 #HV01 #T1 #HT01
#V2 #HV02 #T2 #HT02 #L1 #HL01 #L2 #HL02
elim (IH … HV01 … HV02 … HL01 … HL02) //
elim (IH … HT01 … HT02 … HL01 … HL02) // /3 width=5/
qed-.

fact cpr_cpss_conf_lpr_lpss_flat_tau:
   ∀L0,V0,T0. (
      ∀L,T. ⦃L0,ⓝV0.T0⦄ ⊃+ ⦃L, T⦄ →
      ∀T1. L ⊢ T ➡ T1 → ∀T2. L ⊢ T ▶* T2 →
      ∀L1. L ⊢ ➡ L1 → ∀L2. L ⊢ ▶* L2 →
      ∃∃T0. L1 ⊢ T1 ▶* T0 & L2 ⊢ T2 ➡ T0
   ) →
   ∀T1. L0 ⊢ T0 ➡ T1 → ∀V2,T2. L0 ⊢ T0 ▶* T2 → 
   ∀L1. L0 ⊢ ➡ L1 → ∀L2. L0 ⊢ ▶* L2 →
   ∃∃T. L1 ⊢ T1 ▶* T & L2 ⊢ ⓝV2.T2 ➡ T.
#L0 #V0 #T0 #IH #T1 #HT01
#V2 #T2 #HT02 #L1 #HL01 #L2 #HL02
elim (IH … HT01 … HT02 … HL01 … HL02) // -L0 -V0 -T0 /3 width=3/
qed-.

fact cpr_cpss_conf_lpr_lpss_flat_beta:
   ∀a,L0,V0,W0,T0. (
      ∀L,T. ⦃L0,ⓐV0.ⓛ{a}W0.T0⦄ ⊃+ ⦃L, T⦄ →
      ∀T1. L ⊢ T ➡ T1 → ∀T2. L ⊢ T ▶* T2 →
      ∀L1. L ⊢ ➡ L1 → ∀L2. L ⊢ ▶* L2 →
      ∃∃T0. L1 ⊢ T1 ▶* T0 & L2 ⊢ T2 ➡ T0
   ) →
   ∀V1. L0 ⊢ V0 ➡ V1 → ∀T1. L0.ⓛW0 ⊢ T0 ➡ T1 →
   ∀V2. L0 ⊢ V0 ▶* V2 → ∀T2. L0 ⊢ ⓛ{a}W0.T0 ▶* T2 →
   ∀L1. L0 ⊢ ➡ L1 → ∀L2. L0 ⊢ ▶* L2 →
   ∃∃T. L1 ⊢ ⓓ{a}V1.T1 ▶* T & L2 ⊢ ⓐV2.T2 ➡ T.
#a #L0 #V0 #W0 #T0 #IH #V1 #HV01 #T1 #HT01 
#V2 #HV02 #X #H #L1 #HL01 #L2 #HL02
elim (cpss_inv_bind1 … H) -H #W2 #T2 #HW02 #HT02 #H destruct
elim (IH … HV01 … HV02 … HL01 … HL02) -HV01 -HV02 /2 width=1/ #V #HV1 #HV2
elim (IH … HT01 … HT02 (L1.ⓛW2) … (L2.ⓛW2)) /2 width=1/ /3 width=1/ -L0 -V0 -W0 -T0 #T #HT1 #HT2
lapply (cpss_lsubr_trans … HT1 (L1.ⓓV1) ?) -HT1 /2 width=1/ /3 width=5/
qed-.

fact cpr_cpss_conf_lpr_lpss_flat_theta:
   ∀a,L0,V0,W0,T0. (
      ∀L,T. ⦃L0,ⓐV0.ⓓ{a}W0.T0⦄ ⊃+ ⦃L, T⦄ →
      ∀T1. L ⊢ T ➡ T1 → ∀T2. L ⊢ T ▶* T2 →
      ∀L1. L ⊢ ➡ L1 → ∀L2. L ⊢ ▶* L2 →
      ∃∃T0. L1 ⊢ T1 ▶* T0 & L2 ⊢ T2 ➡ T0
   ) →
   ∀V1. L0 ⊢ V0 ➡ V1 → ∀U1. ⇧[O, 1] V1 ≡ U1 →
   ∀W1. L0 ⊢ W0 ➡ W1 → ∀T1. L0.ⓓW0 ⊢ T0 ➡ T1 →
   ∀V2. L0 ⊢ V0 ▶* V2 → ∀T2. L0 ⊢ ⓓ{a}W0.T0 ▶* T2 →
   ∀L1. L0 ⊢ ➡ L1 → ∀L2. L0 ⊢ ▶* L2 →
   ∃∃T. L1 ⊢ ⓓ{a}W1.ⓐU1.T1 ▶* T & L2 ⊢ ⓐV2.T2 ➡ T.
#a #L0 #V0 #W0 #T0 #IH #V1 #HV01 #U1 #HVU1 #W1 #HW01 #T1 #HT01
#V2 #HV02 #X #H #L1 #HL01 #L2 #HL02
elim (IH … HV01 … HV02 … HL01 … HL02) -HV01 -HV02 /2 width=1/ #V #HV1 #HV2
elim (lift_total V 0 1) #U #HVU
lapply (cpss_lift … HV1 (L1.ⓓW1) … HVU1 … HVU) -HVU1 /2 width=1/ #HU1
elim (cpss_inv_bind1 … H) -H #W2 #T2 #HW02 #HT02 #H destruct
elim (IH … HW01 … HW02 … HL01 … HL02) /2 width=1/
elim (IH … HT01 … HT02 (L1.ⓓW1) … (L2.ⓓW2)) /2 width=1/ -L0 -V0 -W0 -T0
/4 width=9 by ex2_intro, cpr_theta, cpss_bind, cpss_flat/ (**) (* auto too slow without trace *)
qed-.

lemma cpr_cpss_conf_lpr_lpss: lpx_sn_confluent cpr cpss.
#L0 #T0 @(fsupp_wf_ind … L0 T0) -L0 -T0 #L #T #IH #L0 * [|*]
[ #I0 #HL #HT #T1 #H1 #T2 #H2 #L1 #HL01 #L2 #HL02 destruct
  elim (cpr_inv_atom1 … H1) -H1
  elim (cpss_inv_atom1 … H2) -H2
  [ #H2 #H1 destruct
    /2 width=1 by cpr_cpss_conf_lpr_lpss_atom_atom/
  | * #K0 #V0 #V2 #i2 #HLK0 #HV02 #HVT2 #H2 #H1 destruct
    /3 width=10 by cpr_cpss_conf_lpr_lpss_atom_delta/
  | #H2 * #K0 #V0 #V1 #i1 #HLK0 #HV01 #HVT1 #H1 destruct
    /3 width=10 by cpr_cpss_conf_lpr_lpss_delta_atom/
  | * #X #Y #V2 #z #H #HV02 #HVT2 #H2
    * #K0 #V0 #V1 #i #HLK0 #HV01 #HVT1 #H1 destruct
    /3 width=17 by cpr_cpss_conf_lpr_lpss_delta_delta/
  ]
| #a #I #V0 #T0 #HL #HT #X1 #H1 #X2 #H2 #L1 #HL01 #L2 #HL02 destruct
  elim (cpss_inv_bind1 … H2) -H2 #V2 #T2 #HV02 #HT02 #H2
  elim (cpr_inv_bind1 … H1) -H1 *
  [ #V1 #T1 #HV01 #HT01 #H1
  | #T1 #HT01 #HXT1 #H11 #H12
  ] destruct
  [ /3 width=10 by cpr_cpss_conf_lpr_lpss_bind_bind/
  | /3 width=11 by cpr_cpss_conf_lpr_lpss_bind_zeta/
  ]
| #I #V0 #T0 #HL #HT #X1 #H1 #X2 #H2 #L1 #HL01 #L2 #HL02 destruct
  elim (cpss_inv_flat1 … H2) -H2 #V2 #T2 #HV02 #HT02 #H2
  elim (cpr_inv_flat1 … H1) -H1 *
  [ #V1 #T1 #HV01 #HT01 #H1
  | #HX1 #H1
  | #a1 #V1 #Y1 #Z1 #T1 #HV01 #HZT1 #H11 #H12 #H13
  | #a1 #V1 #U1 #Y1 #W1 #Z1 #T1 #HV01 #HVU1 #HYW1 #HZT1 #H11 #H12 #H13
  ] destruct
  [ /3 width=10 by cpr_cpss_conf_lpr_lpss_flat_flat/
  | /3 width=8 by cpr_cpss_conf_lpr_lpss_flat_tau/
  | /3 width=11 by cpr_cpss_conf_lpr_lpss_flat_beta/
  | /3 width=14 by cpr_cpss_conf_lpr_lpss_flat_theta/
  ]
]
qed-.

(* Basic_1: includes: pr0_subst1 *)
(* Basic_1: was: pr2_subst1 *)
lemma cpr_cpss_conf: ∀L. confluent2 … (cpr L) (cpss L).
/2 width=6 by cpr_cpss_conf_lpr_lpss/ qed-.

lemma cpr_lpss_conf_dx: ∀L0,T0,T1. L0 ⊢ T0 ➡ T1 → ∀L1. L0 ⊢ ▶* L1 →
                        ∃∃T. L1 ⊢ T1 ▶* T & L1 ⊢ T0 ➡ T.
#L0 #T0 #T1 #HT01 #L1 #HL01
elim (cpr_cpss_conf_lpr_lpss … HT01 T0 … L1 … HL01) // /2 width=1/ -L0 /2 width=3/
qed-.

lemma cpr_lpss_conf_sn: ∀L0,T0,T1. L0 ⊢ T0 ➡ T1 → ∀L1. L0 ⊢ ▶* L1 →
                        ∃∃T. L0 ⊢ T1 ▶* T & L1 ⊢ T0 ➡ T.
#L0 #T0 #T1 #HT01 #L1 #HL01
elim (cpr_cpss_conf_lpr_lpss … HT01 T0 … L0 … HL01) // -HT01 -HL01 /2 width=3/
qed-.

(* Basic_1: includes: pr0_subst1_fwd *)
lemma lpr_cpss_conf: ∀L0,T0,T1. L0 ⊢ T0 ▶* T1 → ∀L1. L0 ⊢ ➡ L1 →
                     ∃∃T. L1 ⊢ T0 ▶* T & L0 ⊢ T1 ➡ T.
#L0 #T0 #T1 #HT01 #L1 #HL01
elim (cpr_cpss_conf_lpr_lpss ?? T0 … HT01 … HL01 L0) // -HT01 -HL01 /2 width=3/
qed-.

(* Properties on sn parallel substitution on local environments *************)

lemma lpr_lpss_conf: confluent2 … lpr lpss.
/3 width=6 by lpx_sn_conf, cpr_cpss_conf_lpr_lpss/
qed-.
