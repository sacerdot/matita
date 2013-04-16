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

include "basic_2/reducibility/ltpr_tpss.ma".

(* CONTEXT-FREE PARALLEL REDUCTION ON TERMS *********************************)

(* Confluence lemmas ********************************************************)

fact tpr_conf_atom_atom: ∀I. ∃∃X. ⓪{I} ➡ X & ⓪{I} ➡ X.
/2 width=3/ qed.

fact tpr_conf_flat_flat:
   ∀I,V0,V1,T0,T1,V2,T2. (
      ∀X0:term. ♯{X0} < ♯{V0} + ♯{T0} + 1 →
      ∀X1,X2. X0 ➡ X1 → X0 ➡ X2 →
      ∃∃X. X1 ➡ X & X2 ➡ X
   ) →
   V0 ➡ V1 → V0 ➡ V2 → T0 ➡ T1 → T0 ➡ T2 →
   ∃∃T0. ⓕ{I} V1. T1 ➡ T0 & ⓕ{I} V2. T2 ➡ T0.
#I #V0 #V1 #T0 #T1 #V2 #T2 #IH #HV01 #HV02 #HT01 #HT02
elim (IH … HV01 … HV02) -HV01 -HV02 // #V #HV1 #HV2
elim (IH … HT01 … HT02) -HT01 -HT02 -IH // /3 width=5/
qed.

fact tpr_conf_flat_beta:
   ∀a,V0,V1,T1,V2,W0,U0,T2. (
      ∀X0:term. ♯{X0} < ♯{V0} + (♯{W0} + ♯{U0} + 1) + 1 →
      ∀X1,X2. X0 ➡ X1 → X0 ➡ X2 →
      ∃∃X. X1 ➡ X & X2 ➡ X
   ) →
   V0 ➡ V1 → V0 ➡ V2 →
   U0 ➡ T2 → ⓛ{a}W0. U0 ➡ T1 →
   ∃∃X. ⓐV1. T1 ➡ X & ⓓ{a}V2. T2 ➡ X.
#a #V0 #V1 #T1 #V2 #W0 #U0 #T2 #IH #HV01 #HV02 #HT02 #H
elim (tpr_inv_abst1 … H) -H #W1 #U1 #HW01 #HU01 #H destruct
elim (IH … HV01 … HV02) -HV01 -HV02 /2 width=1/ #V #HV1 #HV2
elim (IH … HT02 … HU01) -HT02 -HU01 -IH /2 width=1/ /3 width=5/
qed.

(* Basic-1: was:
            pr0_cong_upsilon_refl pr0_cong_upsilon_zeta
            pr0_cong_upsilon_cong pr0_cong_upsilon_delta
*)
fact tpr_conf_flat_theta:
   ∀a,V0,V1,T1,V2,V,W0,W2,U0,U2. (
      ∀X0:term. ♯{X0} < ♯{V0} + (♯{W0} + ♯{U0} + 1) + 1 →
      ∀X1,X2. X0 ➡ X1 → X0 ➡ X2 →
      ∃∃X. X1 ➡ X & X2 ➡ X
   ) →
   V0 ➡ V1 → V0 ➡ V2 → ⇧[O,1] V2 ≡ V →
   W0 ➡ W2 → U0 ➡ U2 →  ⓓ{a}W0. U0 ➡ T1 →
   ∃∃X. ⓐV1. T1 ➡ X & ⓓ{a}W2. ⓐV. U2 ➡ X.
#a #V0 #V1 #T1 #V2 #V #W0 #W2 #U0 #U2 #IH #HV01 #HV02 #HV2 #HW02 #HU02 #H
elim (IH … HV01 … HV02) -HV01 -HV02 /2 width=1/ #VV #HVV1 #HVV2
elim (lift_total VV 0 1) #VVV #HVV
lapply (tpr_lift … HVV2 … HV2 … HVV) #HVVV
elim (tpr_inv_abbr1 … H) -H *
(* case 1: delta *)
[ -HV2 -HVV2 #WW2 #UU2 #UU #HWW2 #HUU02 #HUU2 #H destruct
  elim (IH … HW02 … HWW2) -HW02 -HWW2 /2 width=1/ #W #HW02 #HWW2
  elim (IH … HU02 … HUU02) -HU02 -HUU02 -IH /2 width=1/ #U #HU2 #HUUU2
  elim (tpr_tps_conf_bind … HWW2 HUUU2 … HUU2) -UU2 #UUU #HUUU2 #HUUU1
  @ex2_intro
  [2: @tpr_theta [6: @HVV |7: @HWW2 |8: @HUUU2 |1,2,3,4: skip | // ]
  |1:skip
  |3: @tpr_delta [3: @tpr_flat |1: skip ] /2 width=5/
  ] (**) (* /5 width=14/ is too slow *)
(* case 3: zeta *)
| -HV2 -HW02 -HVV2 #U1 #HU01 #HTU1
  elim (IH … HU01 … HU02) -HU01 -HU02 -IH // -U0 #U #HU1 #HU2
  elim (tpr_inv_lift1 … HU1 … HTU1) -U1 #UU #HUU #HT1UU #H destruct
  @(ex2_intro … (ⓐVV.UU)) /2 width=1/ /3 width=5/ (**) (* /4 width=9/ is too slow *)
]
qed.

fact tpr_conf_flat_cast:
   ∀X2,V0,V1,T0,T1. (
      ∀X0:term. ♯{X0} < ♯{V0} + ♯{T0} + 1 →
      ∀X1,X2. X0 ➡ X1 → X0 ➡ X2 →
      ∃∃X. X1 ➡ X & X2 ➡ X
   ) →
   V0 ➡ V1 → T0 ➡ T1 → T0 ➡ X2 →
   ∃∃X. ⓝV1. T1 ➡ X & X2 ➡ X.
#X2 #V0 #V1 #T0 #T1 #IH #_ #HT01 #HT02
elim (IH … HT01 … HT02) -HT01 -HT02 -IH // /3 width=3/
qed.

fact tpr_conf_beta_beta:
   ∀a. ∀W0:term. ∀V0,V1,T0,T1,V2,T2. (
      ∀X0:term. ♯{X0} < ♯{V0} + (♯{W0} + ♯{T0} + 1) + 1 →
      ∀X1,X2. X0 ➡ X1 → X0 ➡ X2 →
      ∃∃X. X1 ➡ X & X2 ➡ X
   ) →
   V0 ➡ V1 → V0 ➡ V2 → T0 ➡ T1 → T0 ➡ T2 →
   ∃∃X. ⓓ{a}V1. T1 ➡X & ⓓ{a}V2. T2 ➡ X.
#a #W0 #V0 #V1 #T0 #T1 #V2 #T2 #IH #HV01 #HV02 #HT01 #HT02
elim (IH … HV01 … HV02) -HV01 -HV02 /2 width=1/
elim (IH … HT01 … HT02) -HT01 -HT02 -IH /2 width=1/ /3 width=5/
qed.

(* Basic_1: was: pr0_cong_delta pr0_delta_delta *)
fact tpr_conf_delta_delta:
   ∀a,I1,V0,V1,T0,T1,TT1,V2,T2,TT2. (
      ∀X0:term. ♯{X0} < ♯{V0} + ♯{T0} + 1 →
      ∀X1,X2. X0 ➡ X1 → X0 ➡ X2 →
      ∃∃X. X1 ➡ X & X2 ➡ X
   ) →
   V0 ➡ V1 → V0 ➡ V2 → T0 ➡ T1 → T0 ➡ T2 →
   ⋆. ⓑ{I1} V1 ⊢ T1 ▶ [O, 1] TT1 →
   ⋆. ⓑ{I1} V2 ⊢ T2 ▶ [O, 1] TT2 →
   ∃∃X. ⓑ{a,I1} V1. TT1 ➡ X & ⓑ{a,I1} V2. TT2 ➡ X.
#a #I1 #V0 #V1 #T0 #T1 #TT1 #V2 #T2 #TT2 #IH #HV01 #HV02 #HT01 #HT02 #HTT1 #HTT2
elim (IH … HV01 … HV02) -HV01 -HV02 // #V #HV1 #HV2
elim (IH … HT01 … HT02) -HT01 -HT02 -IH // #T #HT1 #HT2
elim (tpr_tps_conf_bind … HV1 HT1 … HTT1) -T1 #U1 #TTU1 #HTU1
elim (tpr_tps_conf_bind … HV2 HT2 … HTT2) -T2 #U2 #TTU2 #HTU2
elim (tps_conf_eq … HTU1 … HTU2) -T #U #HU1 #HU2
@ex2_intro [2,3: @tpr_delta |1: skip ] /width=10/ (**) (* /3 width=10/ is too slow *)
qed.

fact tpr_conf_delta_zeta:
   ∀X2,V0,V1,T0,T1,TT1,T2. (
      ∀X0:term. ♯{X0} < ♯{V0} + ♯{T0} + 1 →
      ∀X1,X2. X0 ➡ X1 → X0 ➡ X2 →
      ∃∃X. X1 ➡ X & X2 ➡ X
   ) →
   V0 ➡ V1 → T0 ➡ T1 → ⋆. ⓓV1 ⊢ T1 ▶ [O,1] TT1 →
   T0 ➡ T2 → ⇧[O, 1] X2 ≡ T2 →
   ∃∃X. +ⓓV1. TT1 ➡ X & X2 ➡ X.
#X2 #V0 #V1 #T0 #T1 #TT1 #T2 #IH #_ #HT01 #HTT1 #HT02 #HXT2
elim (IH … HT01 … HT02) -IH -HT01 -HT02 // -V0 -T0 #T #HT1 #HT2
elim (tpr_tps_conf_bind ? ? V1 … HT1 HTT1) -T1 // #TT #HTT1 #HTT
elim (tpr_inv_lift1 … HT2 … HXT2) -T2 #X #HXT #HX2
lapply (tps_inv_lift1_eq … HTT … HXT) -HTT #H destruct /3 width=3/
qed.

(* Basic_1: was: pr0_upsilon_upsilon *)
fact tpr_conf_theta_theta:
   ∀a,VV1,V0,V1,W0,W1,T0,T1,V2,VV2,W2,T2. (
      ∀X0:term. ♯{X0} < ♯{V0} + (♯{W0} + ♯{T0} + 1) + 1 →
      ∀X1,X2. X0 ➡ X1 → X0 ➡ X2 →
      ∃∃X. X1 ➡ X & X2 ➡ X
   ) →
   V0 ➡ V1 → V0 ➡ V2 → W0 ➡ W1 → W0 ➡ W2 → T0 ➡ T1 → T0 ➡ T2 →
   ⇧[O, 1] V1 ≡ VV1 → ⇧[O, 1] V2 ≡ VV2 →
   ∃∃X. ⓓ{a}W1. ⓐVV1. T1 ➡ X & ⓓ{a}W2. ⓐVV2. T2 ➡ X.
#a #VV1 #V0 #V1 #W0 #W1 #T0 #T1 #V2 #VV2 #W2 #T2 #IH #HV01 #HV02 #HW01 #HW02 #HT01 #HT02 #HVV1 #HVV2
elim (IH … HV01 … HV02) -HV01 -HV02 /2 width=1/ #V #HV1 #HV2
elim (IH … HW01 … HW02) -HW01 -HW02 /2 width=1/ #W #HW1 #HW2
elim (IH … HT01 … HT02) -HT01 -HT02 -IH /2 width=1/ #T #HT1 #HT2
elim (lift_total V 0 1) #VV #HVV
lapply (tpr_lift … HV1 … HVV1 … HVV) -V1 #HVV1
lapply (tpr_lift … HV2 … HVV2 … HVV) -V2 -HVV #HVV2
@ex2_intro [2,3: @tpr_bind |1:skip ] /2 width=5/ (**) (* /4 width=5/ is too slow *)
qed.

fact tpr_conf_zeta_zeta:
   ∀V0:term. ∀X2,TT0,T0,T1,TT2. (
      ∀X0:term. ♯{X0} < ♯{V0} + ♯{TT0} + 1 →
      ∀X1,X2. X0 ➡ X1 → X0 ➡ X2 →
      ∃∃X. X1 ➡ X & X2 ➡ X
   ) →
   TT0 ➡ T0 → ⇧[O, 1] T1 ≡ T0 →
   TT0 ➡ TT2 → ⇧[O, 1] X2 ≡ TT2 →
   ∃∃X. T1 ➡ X & X2 ➡ X.
#V0 #X2 #TT0 #T0 #T1 #TT2 #IH #HTT0 #HT10 #HTT02 #HXTT2
elim (IH … HTT0 … HTT02) -IH -HTT0 -HTT02 // -V0 -TT0 #T #HT0 #HTT2
elim (tpr_inv_lift1 … HT0 … HT10) -T0 #T0 #HT0 #HT10
elim (tpr_inv_lift1 … HTT2 … HXTT2) -TT2 #TT2 #HTT2 #HXTT2
lapply (lift_inj … HTT2 … HT0) -HTT2 #H destruct /2 width=3/
qed.

fact tpr_conf_tau_tau:
   ∀V0,T0:term. ∀X2,T1. (
      ∀X0:term. ♯{X0} < ♯{V0} + ♯{T0} + 1 →
      ∀X1,X2. X0 ➡ X1 → X0 ➡ X2 →
      ∃∃X. X1 ➡ X & X2 ➡ X
   ) →
   T0 ➡ T1 → T0 ➡ X2 →
   ∃∃X. T1 ➡ X & X2 ➡ X.
#V0 #T0 #X2 #T1 #IH #HT01 #HT02
elim (IH … HT01 … HT02) -HT01 -HT02 -IH // /2 width=3/
qed.

(* Confluence ***************************************************************)

(* Basic_1: was: pr0_confluence *)
theorem tpr_conf: ∀T0:term. ∀T1,T2. T0 ➡ T1 → T0 ➡ T2 →
                  ∃∃T. T1 ➡ T & T2 ➡ T.
#T0 @(f_ind … tw … T0) -T0 #n #IH *
[ #I #_ #X1 #X2 #H1 #H2 -n
  >(tpr_inv_atom1 … H1) -X1
  >(tpr_inv_atom1 … H2) -X2
(* case 1: atom, atom *)
  //
| * [ #a ] #I #V0 #T0 #Hn #X1 #X2 #H1 #H2
  [ elim (tpr_inv_bind1 … H1) -H1 *
    [ #V1 #T1 #U1 #HV01 #HT01 #HTU1 #H1
    | #T1 #HT01 #HXT1 #H11 #H12
    ]
    elim (tpr_inv_bind1 … H2) -H2 *
    [1,3: #V2 #T2 #U2 #HV02 #HT02 #HTU2 #H2
    |2,4: #T2 #HT02 #HXT2 #H21 #H22
    ] destruct
(* case 2: delta, delta *)
    [ /3 width=11 by tpr_conf_delta_delta/ (**) (* /3 width=11/ is too slow *)
(* case 3: zeta, delta (repeated) *)
    | @ex2_commute /3 width=10 by tpr_conf_delta_zeta/
(* case 4: delta, zeta *)
    | /3 width=10 by tpr_conf_delta_zeta/ (**) (* /3 width=10/ is too slow *)
(* case 5: zeta, zeta *)
    | /3 width=9 by tpr_conf_zeta_zeta/ (**) (* /3 width=9/ is too slow *)
    ]
  | elim (tpr_inv_flat1 … H1) -H1 *
    [ #V1 #T1 #HV01 #HT01 #H1
    | #b1 #V1 #W1 #U1 #T1 #HV01 #HUT1 #H11 #H12 #H13
    | #b1 #V1 #Y1 #W1 #Z1 #U1 #T1 #HV01 #HWZ1 #HUT1 #HVY1 #H11 #H12 #H13
    | #HX1 #H1
    ]
    elim (tpr_inv_flat1 … H2) -H2 *
    [1,5,9,13: #V2 #T2 #HV02 #HT02 #H2
    |2,6,10,14: #b2 #V2 #W2 #U2 #T2 #HV02 #HUT2 #H21 #H22 #H23
    |3,7,11,15: #b2 #V2 #Y2 #W2 #Z2 #U2 #T2 #HV02 #HWZ2 #HUT2 #HVY2 #H21 #H22 #H23
    |4,8,12,16: #HX2 #H2
    ] destruct
(* case 6: flat, flat *)
    [ /3 width=7 by tpr_conf_flat_flat/ (**) (* /3 width=7/ is too slow *)
(* case 7: beta, flat (repeated) *)
    | @ex2_commute /3 width=8 by tpr_conf_flat_beta/
(* case 8: theta, flat (repeated) *)
    | @ex2_commute /3 width=11 by tpr_conf_flat_theta/
(* case 9: tau, flat (repeated) *)
    | @ex2_commute /3 width=6 by tpr_conf_flat_cast/
(* case 10: flat, beta *)
    | /3 width=8 by tpr_conf_flat_beta/ (**) (* /3 width=8/ is too slow *)
(* case 11: beta, beta *)
    | /3 width=8 by tpr_conf_beta_beta/ (**) (* /3 width=8/ is too slow *)
(* case 12: flat, theta *)
    | /3 width=11 by tpr_conf_flat_theta/ (**) (* /3 width=11/ is too slow *)
(* case 13: theta, theta *)
    | /3 width=14 by tpr_conf_theta_theta/ (**) (* /3 width=14/ is too slow *)
(* case 14: flat, tau *)
    | /3 width=6 by tpr_conf_flat_cast/ (**) (* /3 width=6/ is too slow *)
(* case 15: tau, tau *)
    | /3 width=5 by tpr_conf_tau_tau/
    ]
  ]
]
qed-.
