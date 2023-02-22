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

include "basic_2/unfold/tpss_tpss.ma".
include "basic_2/unfold/ltpss_sn_tpss.ma".

(* PARTIAL UNFOLD ON LOCAL ENVIRONMENTS *************************************)

(* Advanced properties ******************************************************)

lemma ltpss_sn_tpss_trans_eq: ∀L1,T2,U2,d,e. L1 ⊢ T2 ▶* [d, e] U2 →
                              ∀L0. L0 ⊢ ▶* [d, e] L1 → L0 ⊢ T2 ▶* [d, e] U2.
#L1 #T2 @(f2_ind … fw … L1 T2) -L1 -T2 #n #IH #L1 *
[ #I #Hn #W2 #d #e #H #L0 #HL01 destruct
  elim (tpss_inv_atom1 … H) -H // *
  #K1 #V1 #V2 #i #Hdi #Hide #HLK1 #HV12 #HVW2 #H destruct
  lapply (ldrop_fwd_lw … HLK1) #H1 normalize in H1;
  elim (ltpss_sn_ldrop_trans_be … HL01 … HLK1 ? ?) -HL01 -HLK1 // /2 width=2/ #X #H #HLK0
  elim (ltpss_sn_inv_tpss22 … H ?) -H /2 width=1/ #K0 #V0 #HK01 #HV01 #H destruct
  lapply (IH … HV12 … HK01) -IH -HV12 -HK01 [ normalize /2 width=1/ ] #HV12
  lapply (tpss_trans_eq … HV01 HV12) -V1 /2 width=6/
| * [ #a ] #I #V2 #T2 #Hn #X #d #e #H #L0 #HL0 destruct
  [ elim (tpss_inv_bind1 … H) -H #W2 #U2 #HVW2 #HTU2 #H destruct
    lapply (tpss_lsubr_trans … HTU2 (L1. ⓑ{I} V2) ?) -HTU2 /2 width=1/ #HTU2
    lapply (IH … HVW2 … HL0) -HVW2 [ /2 width=2/ ] #HVW2
    lapply (IH … HTU2 (L0. ⓑ{I} V2) ?) -IH -HTU2 // /2 width=2/ -HL0 #HTU2
    lapply (tpss_lsubr_trans … HTU2 (L0. ⓑ{I} W2) ?) -HTU2 /2 width=1/
  | elim (tpss_inv_flat1 … H) -H #W2 #U2 #HVW2 #HTU2 #H destruct
    lapply (IH … HVW2 … HL0) -HVW2 //
    lapply (IH … HTU2 … HL0) -IH -HTU2 // -HL0 /2 width=1/
]
qed.

lemma ltpss_sn_tps_trans_eq: ∀L0,L1,T2,U2,d,e. L0 ⊢ ▶* [d, e] L1 →
                             L1 ⊢ T2 ▶ [d, e] U2 → L0 ⊢ T2 ▶* [d, e] U2.
/3 width=3/ qed.

(* Main properties **********************************************************)

theorem ltpss_sn_trans_eq: ∀L1,L,d,e. L1 ⊢ ▶* [d, e] L →
                           ∀L2. L ⊢ ▶* [d, e] L2 → L1 ⊢ ▶* [d, e] L2.
#L1 #L #d #e #H elim H -L1 -L -d -e //
[ #L1 #L #I #V1 #V #e #HL1 #HV1 #IHL1 #X #H
  elim (ltpss_sn_inv_tpss21 … H ?) -H // <minus_plus_m_m #L2 #V2 #HL2 #HV2 #H destruct
  lapply (ltpss_sn_tpss_trans_eq … HV2 … HL1) -HV2 -HL1 #HV2
  lapply (tpss_trans_eq … HV1 … HV2) -V /3 width=1/
| #L1 #L #I #V1 #V #d #e #HL1 #HV1 #IHL1 #X #H
  elim (ltpss_sn_inv_tpss11 … H ?) -H // <minus_plus_m_m #L2 #V2 #HL2 #HV2 #H destruct
  lapply (ltpss_sn_tpss_trans_eq … HV2 … HL1) -HV2 -HL1 #HV2
  lapply (tpss_trans_eq … HV1 … HV2) -V /3 width=1/
]
qed.

(* Advanced forward lemmas **************************************************)

lemma tps_fwd_shift1: ∀L1,L,T1,T,d,e. L ⊢ L1 @@ T1 ▶ [d, e] T →
                      ∃∃L2,T2. L @@ L1 ⊢ ▶* [d + |L1|, e] L @@ L2 &
                               L @@ L2 ⊢ T1 ▶ [d + |L1|, e] T2 &
                               T = L2 @@ T2.
#L1 @(lenv_ind_dx … L1) -L1
[ #L #T1 #T #d #e #HT1
  @ex3_2_intro [3: // |5: // |4: normalize /2 width=1/ |1,2: skip ] (**) (* /2 width=4/ does not work *)
| #I #L1 #V1 #IH #L #T1 #T #d #e >shift_append_assoc #H
  elim (tps_inv_bind1 … H) -H #V2 #T2 #HV12 #HT12 #H destruct
  elim (IH … HT12) -IH -HT12 #L2 #T #HL12 #HT1 #H destruct
  <append_assoc >append_length <associative_plus
  lapply (ltpss_sn_trans_eq (L.ⓑ{I}V1@@L1) … HL12) -HL12 /3 width=1/ #HL12
  @(ex3_2_intro … (⋆.ⓑ{I}V2@@L2)) [4: /2 width=3/ | skip ] <append_assoc // (**) (* explicit constructor *)
]
qed-.
