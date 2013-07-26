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

include "basic_2/unfold/lpqs_cpqs.ma".

(* SN RESTRICTED PARALLEL COMPUTATION ON LOCAL ENVIRONMENTS *****************)

(* Main properties on context-sensitive rest parallel computation for terms *)

fact cpqs_conf_lpqs_atom_atom:
   ∀I,L1,L2. ∃∃T. L1 ⊢ ⓪{I} ➤* T & L2 ⊢ ⓪{I} ➤* T.
/2 width=3/ qed-.

fact cpqs_conf_lpqs_atom_delta:
   ∀L0,i. (
      ∀L,T. ⦃L0, #i⦄ ⊃+ ⦃L, T⦄ →
      ∀T1. L ⊢ T ➤* T1 → ∀T2. L ⊢ T ➤* T2 →
      ∀L1. L ⊢ ➤* L1 → ∀L2. L ⊢ ➤* L2 →
      ∃∃T0. L1 ⊢ T1 ➤* T0 & L2 ⊢ T2 ➤* T0
   ) →
   ∀K0,V0. ⇩[O, i] L0 ≡ K0.ⓓV0 →
   ∀V2. K0 ⊢ V0 ➤* V2 → ∀T2. ⇧[O, i + 1] V2 ≡ T2 →
   ∀L1. L0 ⊢ ➤* L1 → ∀L2. L0 ⊢ ➤* L2 →
   ∃∃T. L1 ⊢ #i ➤* T & L2 ⊢ T2 ➤* T.
#L0 #i #IH #K0 #V0 #HLK0 #V2 #HV02 #T2 #HVT2 #L1 #HL01 #L2 #HL02
elim (lpqs_ldrop_conf … HLK0 … HL01) -HL01 #X1 #H1 #HLK1
elim (lpqs_inv_pair1 … H1) -H1 #K1 #V1 #HK01 #HV01 #H destruct
elim (lpqs_ldrop_conf … HLK0 … HL02) -HL02 #X2 #H2 #HLK2
elim (lpqs_inv_pair1 … H2) -H2 #K2 #W2 #HK02 #_ #H destruct
lapply (ldrop_fwd_ldrop2 … HLK2) -W2 #HLK2
lapply (fsupp_lref … HLK0) -HLK0 #HLK0
elim (IH … HLK0 … HV01 … HV02 … HK01 … HK02) -L0 -K0 -V0 #V #HV1 #HV2
elim (lift_total V 0 (i+1)) #T #HVT
lapply (cpqs_lift … HV2 … HLK2 … HVT2 … HVT) -K2 -V2 /3 width=6/
qed-.

fact cpqs_conf_lpqs_delta_delta:
   ∀L0,i. (
      ∀L,T. ⦃L0, #i⦄ ⊃+ ⦃L, T⦄ →
      ∀T1. L ⊢ T ➤* T1 → ∀T2. L ⊢ T ➤* T2 →
      ∀L1. L ⊢ ➤* L1 → ∀L2. L ⊢ ➤* L2 →
      ∃∃T0. L1 ⊢ T1 ➤* T0 & L2 ⊢ T2 ➤* T0
   ) →
   ∀K0,V0. ⇩[O, i] L0 ≡ K0.ⓓV0 →
   ∀V1. K0 ⊢ V0 ➤* V1 → ∀T1. ⇧[O, i + 1] V1 ≡ T1 →
   ∀KX,VX. ⇩[O, i] L0 ≡ KX.ⓓVX →
   ∀V2. KX ⊢ VX ➤* V2 → ∀T2. ⇧[O, i + 1] V2 ≡ T2 →
   ∀L1. L0 ⊢ ➤* L1 → ∀L2. L0 ⊢ ➤* L2 →
   ∃∃T. L1 ⊢ T1 ➤* T & L2 ⊢ T2 ➤* T.
#L0 #i #IH #K0 #V0 #HLK0 #V1 #HV01 #T1 #HVT1
#KX #VX #H #V2 #HV02 #T2 #HVT2 #L1 #HL01 #L2 #HL02
lapply (ldrop_mono … H … HLK0) -H #H destruct
elim (lpqs_ldrop_conf … HLK0 … HL01) -HL01 #X1 #H1 #HLK1
elim (lpqs_inv_pair1 … H1) -H1 #K1 #W1 #HK01 #_ #H destruct
lapply (ldrop_fwd_ldrop2 … HLK1) -W1 #HLK1
elim (lpqs_ldrop_conf … HLK0 … HL02) -HL02 #X2 #H2 #HLK2
elim (lpqs_inv_pair1 … H2) -H2 #K2 #W2 #HK02 #_ #H destruct
lapply (ldrop_fwd_ldrop2 … HLK2) -W2 #HLK2
lapply (fsupp_lref … HLK0) -HLK0 #HLK0
elim (IH … HLK0 … HV01 … HV02 … HK01 … HK02) -L0 -K0 -V0 #V #HV1 #HV2
elim (lift_total V 0 (i+1)) #T #HVT
lapply (cpqs_lift … HV1 … HLK1 … HVT1 … HVT) -K1 -V1
lapply (cpqs_lift … HV2 … HLK2 … HVT2 … HVT) -K2 -V2 -V /2 width=3/
qed-.

fact cpqs_conf_lpqs_bind_bind:
   ∀a,I,L0,V0,T0. (
      ∀L,T. ⦃L0,ⓑ{a,I}V0.T0⦄ ⊃+ ⦃L,T⦄ →
      ∀T1. L ⊢ T ➤* T1 → ∀T2. L ⊢ T ➤* T2 →
      ∀L1. L ⊢ ➤* L1 → ∀L2. L ⊢ ➤* L2 →
      ∃∃T0. L1 ⊢ T1 ➤* T0 & L2 ⊢ T2 ➤* T0
   ) →
   ∀V1. L0 ⊢ V0 ➤* V1 → ∀T1. L0.ⓑ{I}V0 ⊢ T0 ➤* T1 →
   ∀V2. L0 ⊢ V0 ➤* V2 → ∀T2. L0.ⓑ{I}V0 ⊢ T0 ➤* T2 →
   ∀L1. L0 ⊢ ➤* L1 → ∀L2. L0 ⊢ ➤* L2 →
   ∃∃T. L1 ⊢ ⓑ{a,I}V1.T1 ➤* T & L2 ⊢ ⓑ{a,I}V2.T2 ➤* T.
#a #I #L0 #V0 #T0 #IH #V1 #HV01 #T1 #HT01
#V2 #HV02 #T2 #HT02 #L1 #HL01 #L2 #HL02
elim (IH … HV01 … HV02 … HL01 … HL02) //
elim (IH … HT01 … HT02 (L1.ⓑ{I}V1) … (L2.ⓑ{I}V2)) -IH // /2 width=1/ /3 width=5/
qed-.

fact cpqs_conf_lpqs_bind_zeta:
   ∀L0,V0,T0. (
      ∀L,T. ⦃L0,+ⓓV0.T0⦄ ⊃+ ⦃L,T⦄ →
      ∀T1. L ⊢ T ➤* T1 → ∀T2. L ⊢ T ➤* T2 →
      ∀L1. L ⊢ ➤* L1 → ∀L2. L ⊢ ➤* L2 →
      ∃∃T0. L1 ⊢ T1 ➤* T0 & L2 ⊢ T2 ➤* T0
   ) →
   ∀V1. L0 ⊢ V0 ➤* V1 → ∀T1. L0.ⓓV0 ⊢ T0 ➤* T1 →
   ∀T2. L0.ⓓV0 ⊢ T0 ➤* T2 → ∀X2. ⇧[O, 1] X2 ≡ T2 →
   ∀L1. L0 ⊢ ➤* L1 → ∀L2. L0 ⊢ ➤* L2 →
   ∃∃T. L1 ⊢ +ⓓV1.T1 ➤* T & L2 ⊢ X2 ➤* T.
#L0 #V0 #T0 #IH #V1 #HV01 #T1 #HT01
#T2 #HT02 #X2 #HXT2 #L1 #HL01 #L2 #HL02
elim (IH … HT01 … HT02 (L1.ⓓV1) … (L2.ⓓV1)) -IH -HT01 -HT02 // /2 width=1/ -L0 -V0 -T0 #T #HT1 #HT2
elim (cpqs_inv_lift1 … HT2 L2 … HXT2) -T2 /2 width=1/ /3 width=3/
qed-.

fact cpqs_conf_lpqs_zeta_zeta:
   ∀L0,V0,T0. (
      ∀L,T. ⦃L0,+ⓓV0.T0⦄ ⊃+ ⦃L,T⦄ →
      ∀T1. L ⊢ T ➤* T1 → ∀T2. L ⊢ T ➤* T2 →
      ∀L1. L ⊢ ➤* L1 → ∀L2. L ⊢ ➤* L2 →
      ∃∃T0. L1 ⊢ T1 ➤* T0 & L2 ⊢ T2 ➤* T0
   ) →
   ∀T1. L0.ⓓV0 ⊢ T0 ➤* T1 → ∀X1. ⇧[O, 1] X1 ≡ T1 →
   ∀T2. L0.ⓓV0 ⊢ T0 ➤* T2 → ∀X2. ⇧[O, 1] X2 ≡ T2 →
   ∀L1. L0 ⊢ ➤* L1 → ∀L2. L0 ⊢ ➤* L2 →
   ∃∃T. L1 ⊢ X1 ➤* T & L2 ⊢ X2 ➤* T.
#L0 #V0 #T0 #IH #T1 #HT01 #X1 #HXT1
#T2 #HT02 #X2 #HXT2 #L1 #HL01 #L2 #HL02
elim (IH … HT01 … HT02 (L1.ⓓV0) … (L2.ⓓV0)) -IH -HT01 -HT02 // /2 width=1/ -L0 -T0 #T #HT1 #HT2
elim (cpqs_inv_lift1 … HT1 L1 … HXT1) -T1 /2 width=1/ #T1 #HT1 #HXT1
elim (cpqs_inv_lift1 … HT2 L2 … HXT2) -T2 /2 width=1/ #T2 #HT2 #HXT2 
lapply (lift_inj … HT2 … HT1) -T #H destruct /2 width=3/
qed-.

fact cpqs_conf_lpqs_flat_flat:
   ∀I,L0,V0,T0. (
      ∀L,T. ⦃L0,ⓕ{I}V0.T0⦄ ⊃+ ⦃L,T⦄ →
      ∀T1. L ⊢ T ➤* T1 → ∀T2. L ⊢ T ➤* T2 →
      ∀L1. L ⊢ ➤* L1 → ∀L2. L ⊢ ➤* L2 →
      ∃∃T0. L1 ⊢ T1 ➤* T0 & L2 ⊢ T2 ➤* T0
   ) →
   ∀V1. L0 ⊢ V0 ➤* V1 → ∀T1. L0 ⊢ T0 ➤* T1 →
   ∀V2. L0 ⊢ V0 ➤* V2 → ∀T2. L0 ⊢ T0 ➤* T2 →
   ∀L1. L0 ⊢ ➤* L1 → ∀L2. L0 ⊢ ➤* L2 →
   ∃∃T. L1 ⊢ ⓕ{I}V1.T1 ➤* T & L2 ⊢ ⓕ{I}V2.T2 ➤* T.
#I #L0 #V0 #T0 #IH #V1 #HV01 #T1 #HT01
#V2 #HV02 #T2 #HT02 #L1 #HL01 #L2 #HL02
elim (IH … HV01 … HV02 … HL01 … HL02) //
elim (IH … HT01 … HT02 … HL01 … HL02) // /3 width=5/
qed-.

fact cpqs_conf_lpqs_flat_tau:
   ∀L0,V0,T0. (
      ∀L,T. ⦃L0,ⓝV0.T0⦄ ⊃+ ⦃L,T⦄ →
      ∀T1. L ⊢ T ➤* T1 → ∀T2. L ⊢ T ➤* T2 →
      ∀L1. L ⊢ ➤* L1 → ∀L2. L ⊢ ➤* L2 →
      ∃∃T0. L1 ⊢ T1 ➤* T0 & L2 ⊢ T2 ➤* T0
   ) →
   ∀V1,T1. L0 ⊢ T0 ➤* T1 → ∀T2. L0 ⊢ T0 ➤* T2 →
   ∀L1. L0 ⊢ ➤* L1 → ∀L2. L0 ⊢ ➤* L2 →
   ∃∃T. L1 ⊢ ⓝV1.T1 ➤* T & L2 ⊢ T2 ➤* T.
#L0 #V0 #T0 #IH #V1 #T1 #HT01
#T2 #HT02 #L1 #HL01 #L2 #HL02
elim (IH … HT01 … HT02 … HL01 … HL02) // -L0 -V0 -T0 /3 width=3/
qed-.

fact cpqs_conf_lpqs_tau_tau:
   ∀L0,V0,T0. (
      ∀L,T. ⦃L0,ⓝV0.T0⦄ ⊃+ ⦃L,T⦄ →
      ∀T1. L ⊢ T ➤* T1 → ∀T2. L ⊢ T ➤* T2 →
      ∀L1. L ⊢ ➤* L1 → ∀L2. L ⊢ ➤* L2 →
      ∃∃T0. L1 ⊢ T1 ➤* T0 & L2 ⊢ T2 ➤* T0
   ) →
   ∀T1. L0 ⊢ T0 ➤* T1 → ∀T2. L0 ⊢ T0 ➤* T2 →
   ∀L1. L0 ⊢ ➤* L1 → ∀L2. L0 ⊢ ➤* L2 →
   ∃∃T. L1 ⊢ T1 ➤* T & L2 ⊢ T2 ➤* T.
#L0 #V0 #T0 #IH #T1 #HT01
#T2 #HT02 #L1 #HL01 #L2 #HL02
elim (IH … HT01 … HT02 … HL01 … HL02) // -L0 -V0 -T0 /2 width=3/
qed-.

theorem cpqs_conf_lpqs: lpx_sn_confluent cpqs cpqs.
#L0 #T0 @(fsupp_wf_ind … L0 T0) -L0 -T0 #L #T #IH #L0 * [|*]
[ #I0 #HL #HT #T1 #H1 #T2 #H2 #L1 #HL01 #L2 #HL02 destruct
  elim (cpqs_inv_atom1 … H1) -H1
  elim (cpqs_inv_atom1 … H2) -H2
  [ #H2 #H1 destruct
    /2 width=1 by cpqs_conf_lpqs_atom_atom/
  | * #K0 #V0 #V2 #i2 #HLK0 #HV02 #HVT2 #H2 #H1 destruct
    /3 width=10 by cpqs_conf_lpqs_atom_delta/
  | #H2 * #K0 #V0 #V1 #i1 #HLK0 #HV01 #HVT1 #H1 destruct
    /4 width=10 by ex2_commute, cpqs_conf_lpqs_atom_delta/
  | * #X #Y #V2 #z #H #HV02 #HVT2 #H2
    * #K0 #V0 #V1 #i #HLK0 #HV01 #HVT1 #H1 destruct
    /3 width=17 by cpqs_conf_lpqs_delta_delta/
  ]
| #a #I #V0 #T0 #HL #HT #X1 #H1 #X2 #H2 #L1 #HL01 #L2 #HL02 destruct
  elim (cpqs_inv_bind1 … H1) -H1 *
  [ #V1 #T1 #HV01 #HT01 #H1
  | #T1 #HT01 #HXT1 #H11 #H12
  ]
  elim (cpqs_inv_bind1 … H2) -H2 *
  [1,3: #V2 #T2 #HV02 #HT02 #H2
  |2,4: #T2 #HT02 #HXT2 #H21 #H22
  ] destruct
  [ /3 width=10 by cpqs_conf_lpqs_bind_bind/
  | /4 width=11 by ex2_commute, cpqs_conf_lpqs_bind_zeta/
  | /3 width=11 by cpqs_conf_lpqs_bind_zeta/
  | /3 width=12 by cpqs_conf_lpqs_zeta_zeta/
  ]
| #I #V0 #T0 #HL #HT #X1 #H1 #X2 #H2 #L1 #HL01 #L2 #HL02 destruct
  elim (cpqs_inv_flat1 … H1) -H1 *
  [ #V1 #T1 #HV01 #HT01 #H1
  | #HX1 #H1
  ]
  elim (cpqs_inv_flat1 … H2) -H2 *
  [1,3: #V2 #T2 #HV02 #HT02 #H2
  |2,4: #HX2 #H2
  ] destruct
  [ /3 width=10 by cpqs_conf_lpqs_flat_flat/
  | /4 width=8 by ex2_commute, cpqs_conf_lpqs_flat_tau/
  | /3 width=8 by cpqs_conf_lpqs_flat_tau/
  | /3 width=7 by cpqs_conf_lpqs_tau_tau/
  ]
]
qed-.

theorem cpqs_conf: ∀L. confluent … (cpqs L).
/2 width=6 by cpqs_conf_lpqs/ qed-.

(* Properties on context-sensitive rest. parallel computation for terms *****)

lemma lpqs_cpqs_conf_dx: ∀L0,T0,T1. L0 ⊢ T0 ➤* T1 → ∀L1. L0 ⊢ ➤* L1 →
                         ∃∃T. L1 ⊢ T0 ➤* T & L1 ⊢ T1 ➤* T.
#L0 #T0 #T1 #HT01 #L1 #HL01
elim (cpqs_conf_lpqs … HT01 T0 … HL01 … HL01) // -L0 /2 width=3/
qed-.

lemma lpqs_cpqs_conf_sn: ∀L0,T0,T1. L0 ⊢ T0 ➤* T1 → ∀L1. L0 ⊢ ➤* L1 →
                         ∃∃T. L1 ⊢ T0 ➤* T & L0 ⊢ T1 ➤* T.
#L0 #T0 #T1 #HT01 #L1 #HL01
elim (cpqs_conf_lpqs … HT01 T0 … L0 … HL01) // -HT01 -HL01 /2 width=3/
qed-.

(* Main properties **********************************************************)

theorem lpqs_conf: confluent … lpqs.
/3 width=6 by lpx_sn_conf, cpqs_conf_lpqs/
qed-.

theorem lpqs_trans: Transitive … lpqs.
/3 width=5 by lpx_sn_trans, cpqs_trans_lpqs/
qed-.

(* Advanced forward lemmas **************************************************)

lemma cpqs_fwd_shift1: ∀L1,L,T1,T. L ⊢ L1 @@ T1 ➤* T →
                       ∃∃L2,T2. L @@ L1 ⊢ ➤* L @@ L2 & L @@ L1 ⊢ T1 ➤* T2 &
                                T = L2 @@ T2.
#L1 @(lenv_ind_dx … L1) -L1
[ #L #T1 #T #HT1
  @ex3_2_intro [3: // |4,5: // |1,2: skip ] (**) (* /2 width=4/ does not work *)
| #I #L1 #V1 #IH #L #T1 #T >shift_append_assoc #H <append_assoc
  elim (cpqs_inv_bind1 … H) -H *
  [ #V2 #T2 #HV12 #HT12 #H destruct
    elim (IH … HT12) -IH -HT12 #L2 #T #HL12 #HT1 #H destruct
    lapply (lpqs_trans … HL12 (L.ⓑ{I}V2@@L2) ?) -HL12 /3 width=1/ #HL12
    @(ex3_2_intro … (⋆.ⓑ{I}V2@@L2)) [4: /2 width=3/ | skip ] <append_assoc // (**) (* explicit constructor *)
  | #T #_ #_ #H destruct
  ]
]
qed-.
