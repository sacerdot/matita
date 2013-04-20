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

include "basic_2/relocation/fsup.ma".
include "basic_2/substitution/lpss_ldrop.ma".

(* SN PARALLEL SUBSTITUTION FOR LOCAL ENVIRONMENTS **************************)

(* Main properties on context-sensitive parallel substitution for terms *****)

fact cpss_conf_lpss_atom_atom:
   ∀I,L1,L2. ∃∃T. L1 ⊢ ⓪{I} ▶* T & L2 ⊢ ⓪{I} ▶* T.
/2 width=3/ qed-.

fact cpss_conf_lpss_atom_delta:
   ∀L0,i. (
      ∀L,T.♯{L, T} < ♯{L0, #i} →
      ∀T1. L ⊢ T ▶* T1 → ∀T2. L ⊢ T ▶* T2 →
      ∀L1. L ⊢ ▶* L1 → ∀L2. L ⊢ ▶* L2 →
      ∃∃T0. L1 ⊢ T1 ▶* T0 & L2 ⊢ T2 ▶* T0
   ) →
   ∀K0,V0. ⇩[O, i] L0 ≡ K0.ⓓV0 →
   ∀V2. K0 ⊢ V0 ▶* V2 → ∀T2. ⇧[O, i + 1] V2 ≡ T2 →
   ∀L1. L0 ⊢ ▶* L1 → ∀L2. L0 ⊢ ▶* L2 →
   ∃∃T. L1 ⊢ #i ▶* T & L2 ⊢ T2 ▶* T.
#L0 #i #IH #K0 #V0 #HLK0 #V2 #HV02 #T2 #HVT2 #L1 #HL01 #L2 #HL02
elim (lpss_ldrop_conf … HLK0 … HL01) -HL01 #X1 #H1 #HLK1
elim (lpss_inv_pair1 … H1) -H1 #K1 #V1 #HK01 #HV01 #H destruct
elim (lpss_ldrop_conf … HLK0 … HL02) -HL02 #X2 #H2 #HLK2
elim (lpss_inv_pair1 … H2) -H2 #K2 #W2 #HK02 #_ #H destruct
lapply (ldrop_fwd_ldrop2 … HLK2) -W2 #HLK2
lapply (ldrop_pair2_fwd_fw … HLK0 (#i)) -HLK0 #HLK0
elim (IH … HLK0 … HV01 … HV02 … HK01 … HK02) -L0 -K0 -V0 #V #HV1 #HV2
elim (lift_total V 0 (i+1)) #T #HVT
lapply (cpss_lift … HV2 … HLK2 … HVT2 … HVT) -K2 -V2 /3 width=6/
qed-.

fact cpss_conf_lpss_delta_delta:
   ∀L0,i. (
      ∀L,T.♯{L, T} < ♯{L0, #i} →
      ∀T1. L ⊢ T ▶* T1 → ∀T2. L ⊢ T ▶* T2 →
      ∀L1. L ⊢ ▶* L1 → ∀L2. L ⊢ ▶* L2 →
      ∃∃T0. L1 ⊢ T1 ▶* T0 & L2 ⊢ T2 ▶* T0
   ) →
   ∀K0,V0. ⇩[O, i] L0 ≡ K0.ⓓV0 →
   ∀V1. K0 ⊢ V0 ▶* V1 → ∀T1. ⇧[O, i + 1] V1 ≡ T1 →
   ∀KX,VX. ⇩[O, i] L0 ≡ KX.ⓓVX →
   ∀V2. KX ⊢ VX ▶* V2 → ∀T2. ⇧[O, i + 1] V2 ≡ T2 →
   ∀L1. L0 ⊢ ▶* L1 → ∀L2. L0 ⊢ ▶* L2 →
   ∃∃T. L1 ⊢ T1 ▶* T & L2 ⊢ T2 ▶* T.
#L0 #i #IH #K0 #V0 #HLK0 #V1 #HV01 #T1 #HVT1
#KX #VX #H #V2 #HV02 #T2 #HVT2 #L1 #HL01 #L2 #HL02
lapply (ldrop_mono … H … HLK0) -H #H destruct
elim (lpss_ldrop_conf … HLK0 … HL01) -HL01 #X1 #H1 #HLK1
elim (lpss_inv_pair1 … H1) -H1 #K1 #W1 #HK01 #_ #H destruct
lapply (ldrop_fwd_ldrop2 … HLK1) -W1 #HLK1
elim (lpss_ldrop_conf … HLK0 … HL02) -HL02 #X2 #H2 #HLK2
elim (lpss_inv_pair1 … H2) -H2 #K2 #W2 #HK02 #_ #H destruct
lapply (ldrop_fwd_ldrop2 … HLK2) -W2 #HLK2
lapply (ldrop_pair2_fwd_fw … HLK0 (#i)) -HLK0 #HLK0
elim (IH … HLK0 … HV01 … HV02 … HK01 … HK02) -L0 -K0 -V0 #V #HV1 #HV2
elim (lift_total V 0 (i+1)) #T #HVT
lapply (cpss_lift … HV1 … HLK1 … HVT1 … HVT) -K1 -V1
lapply (cpss_lift … HV2 … HLK2 … HVT2 … HVT) -K2 -V2 -V /2 width=3/
qed-.

fact cpss_conf_lpss_bind_bind:
   ∀a,I,L0,V0,T0. (
      ∀L,T.♯{L,T} < ♯{L0,ⓑ{a,I}V0.T0} →
      ∀T1. L ⊢ T ▶* T1 → ∀T2. L ⊢ T ▶* T2 →
      ∀L1. L ⊢ ▶* L1 → ∀L2. L ⊢ ▶* L2 →
      ∃∃T0. L1 ⊢ T1 ▶* T0 & L2 ⊢ T2 ▶* T0
   ) →
   ∀V1. L0 ⊢ V0 ▶* V1 → ∀T1. L0.ⓑ{I}V0 ⊢ T0 ▶* T1 →
   ∀V2. L0 ⊢ V0 ▶* V2 → ∀T2. L0.ⓑ{I}V0 ⊢ T0 ▶* T2 →
   ∀L1. L0 ⊢ ▶* L1 → ∀L2. L0 ⊢ ▶* L2 →
   ∃∃T. L1 ⊢ ⓑ{a,I}V1.T1 ▶* T & L2 ⊢ ⓑ{a,I}V2.T2 ▶* T.
#a #I #L0 #V0 #T0 #IH #V1 #HV01 #T1 #HT01
#V2 #HV02 #T2 #HT02 #L1 #HL01 #L2 #HL02
elim (IH … HV01 … HV02 … HL01 … HL02) //
elim (IH … HT01 … HT02 (L1.ⓑ{I}V1) … (L2.ⓑ{I}V2)) -IH // /2 width=1/ /3 width=5/
qed-.

fact cpss_conf_lpss_flat_flat:
   ∀I,L0,V0,T0. (
      ∀L,T.♯{L,T} < ♯{L0,ⓕ{I}V0.T0} →
      ∀T1. L ⊢ T ▶* T1 → ∀T2. L ⊢ T ▶* T2 →
      ∀L1. L ⊢ ▶* L1 → ∀L2. L ⊢ ▶* L2 →
      ∃∃T0. L1 ⊢ T1 ▶* T0 & L2 ⊢ T2 ▶* T0
   ) →
   ∀V1. L0 ⊢ V0 ▶* V1 → ∀T1. L0 ⊢ T0 ▶* T1 →
   ∀V2. L0 ⊢ V0 ▶* V2 → ∀T2. L0 ⊢ T0 ▶* T2 →
   ∀L1. L0 ⊢ ▶* L1 → ∀L2. L0 ⊢ ▶* L2 →
   ∃∃T. L1 ⊢ ⓕ{I}V1.T1 ▶* T & L2 ⊢ ⓕ{I}V2.T2 ▶* T.
#I #L0 #V0 #T0 #IH #V1 #HV01 #T1 #HT01
#V2 #HV02 #T2 #HT02 #L1 #HL01 #L2 #HL02
elim (IH … HV01 … HV02 … HL01 … HL02) //
elim (IH … HT01 … HT02 … HL01 … HL02) // /3 width=5/
qed-.

theorem cpss_conf_lpss: lpx_sn_confluent cpss cpss.
#L0 #T0 @(f2_ind … fw … L0 T0) -L0 -T0 #n #IH #L0 * [|*]
[ #I0 #Hn #T1 #H1 #T2 #H2 #L1 #HL01 #L2 #HL02 destruct
  elim (cpss_inv_atom1 … H1) -H1
  elim (cpss_inv_atom1 … H2) -H2
  [ #H2 #H1 destruct
    /2 width=1 by cpss_conf_lpss_atom_atom/
  | * #K0 #V0 #V2 #i2 #HLK0 #HV02 #HVT2 #H2 #H1 destruct
    /3 width=10 by cpss_conf_lpss_atom_delta/
  | #H2 * #K0 #V0 #V1 #i1 #HLK0 #HV01 #HVT1 #H1 destruct
    /4 width=10 by ex2_commute, cpss_conf_lpss_atom_delta/
  | * #X #Y #V2 #z #H #HV02 #HVT2 #H2
    * #K0 #V0 #V1 #i #HLK0 #HV01 #HVT1 #H1 destruct
    /3 width=17 by cpss_conf_lpss_delta_delta/
  ]
| #a #I #V0 #T0 #Hn #X1 #H1 #X2 #H2 #L1 #HL01 #L2 #HL02 destruct
  elim (cpss_inv_bind1 … H1) -H1 #V1 #T1 #HV01 #HT01 #H destruct
  elim (cpss_inv_bind1 … H2) -H2 #V2 #T2 #HV02 #HT02 #H destruct
  /3 width=10 by cpss_conf_lpss_bind_bind/
| #I #V0 #T0 #Hn #X1 #H1 #X2 #H2 #L1 #HL01 #L2 #HL02 destruct
  elim (cpss_inv_flat1 … H1) -H1 #V1 #T1 #HV01 #HT01 #H destruct
  elim (cpss_inv_flat1 … H2) -H2 #V2 #T2 #HV02 #HT02 #H destruct
  /3 width=10 by cpss_conf_lpss_flat_flat/
]
qed-.

(* Basic_1: was only: subst1_confluence_eq *)
theorem cpss_conf: ∀L. confluent … (cpss L).
/2 width=6 by cpss_conf_lpss/ qed-.

theorem cpss_trans_lpss: lpx_sn_transitive cpss cpss.
#L1 #T1 @(f2_ind … fw … L1 T1) -L1 -T1 #n #IH #L1 * [|*]
[ #I #Hn #T #H1 #L2 #HL12 #T2 #HT2 destruct
  elim (cpss_inv_atom1 … H1) -H1
  [ #H destruct
    elim (cpss_inv_atom1 … HT2) -HT2
    [ #H destruct //
    | * #K2 #V #V2 #i #HLK2 #HV2 #HVT2 #H destruct
      elim (lpss_ldrop_trans_O1 … HL12 … HLK2) -L2 #X #HLK1 #H
      elim (lpss_inv_pair2 … H) -H #K1 #V1 #HK12 #HV1 #H destruct
      lapply (ldrop_pair2_fwd_fw … HLK1 (#i)) /3 width=9/
    ]
  | * #K1 #V1 #V #i #HLK1 #HV1 #HVT #H destruct
    elim (lpss_ldrop_conf … HLK1 … HL12) -HL12 #X #H #HLK2
    elim (lpss_inv_pair1 … H) -H #K2 #W2 #HK12 #_ #H destruct
    lapply (ldrop_fwd_ldrop2 … HLK2) -W2 #HLK2
    elim (cpss_inv_lift1 … HT2 … HLK2 … HVT) -L2 -T
    lapply (ldrop_pair2_fwd_fw … HLK1 (#i)) /3 width=9/
  ]
| #a #I #V1 #T1 #Hn #X1 #H1 #L2 #HL12 #X2 #H2
  elim (cpss_inv_bind1 … H1) -H1 #V #T #HV1 #HT1 #H destruct
  elim (cpss_inv_bind1 … H2) -H2 #V2 #T2 #HV2 #HT2 #H destruct /4 width=5/
| #I #V1 #T1 #Hn #X1 #H1 #L2 #HL12 #X2 #H2
  elim (cpss_inv_flat1 … H1) -H1 #V #T #HV1 #HT1 #H destruct
  elim (cpss_inv_flat1 … H2) -H2 #V2 #T2 #HV2 #HT2 #H destruct /3 width=5/
]
qed-.

(* Basic_1: was only: subst1_trans *)
theorem cpss_trans: ∀L. Transitive … (cpss L).
/2 width=5 by cpss_trans_lpss/ qed-.

(* Properties on context-sensitive parallel substitution for terms **********)

(* Basic_1: was only: subst1_subst1_back *)
lemma lpss_cpss_conf_dx: ∀L0,T0,T1. L0 ⊢ T0 ▶* T1 → ∀L1. L0 ⊢ ▶* L1 →
                         ∃∃T. L1 ⊢ T0 ▶* T & L1 ⊢ T1 ▶* T.
#L0 #T0 #T1 #HT01 #L1 #HL01
elim (cpss_conf_lpss … HT01 T0 … HL01 … HL01) // -L0 /2 width=3/
qed-.

lemma lpss_cpss_conf_sn: ∀L0,T0,T1. L0 ⊢ T0 ▶* T1 → ∀L1. L0 ⊢ ▶* L1 →
                         ∃∃T. L1 ⊢ T0 ▶* T & L0 ⊢ T1 ▶* T.
#L0 #T0 #T1 #HT01 #L1 #HL01
elim (cpss_conf_lpss … HT01 T0 … L0 … HL01) // -HT01 -HL01 /2 width=3/
qed-.

(* Basic_1: was only: subst1_subst1 *)
lemma lpss_cpss_trans: ∀L1,L2. L1 ⊢ ▶* L2 →
                       ∀T1,T2. L2 ⊢ T1 ▶* T2 → L1 ⊢ T1 ▶* T2.
/2 width=5 by cpss_trans_lpss/ qed-.

lemma fsup_cpss_trans: ∀L1,L2,T1,T2. ⦃L1, T1⦄ ⊃ ⦃L2, T2⦄ → ∀U2. L2 ⊢ T2 ▶* U2 →
                       ∃∃L,U1. L1 ⊢ ▶* L & L ⊢ T1 ▶* U1 & ⦃L, U1⦄ ⊃ ⦃L2, U2⦄.
#L1 #L2 #T1 #T2 #H elim H -L1 -L2 -T1 -T2 [1,2,3,4,5: /3 width=5/ ]
#L1 #K1 #K2 #T1 #T2 #U1 #d #e #HLK1 #HTU1 #_ #IHT12 #U2 #HTU2
elim (IHT12 … HTU2) -IHT12 -HTU2 #K #T #HK1 #HT1 #HT2
elim (lift_total T d e) #U #HTU
elim (ldrop_lpss_trans … HLK1 … HK1) -HLK1 -HK1 #L2 #HL12 #HL2K
lapply (cpss_lift … HT1 … HL2K … HTU1 … HTU) -HT1 -HTU1 /3 width=11/
qed-.
