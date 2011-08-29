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

include "Basic-2/substitution/tps_tps.ma".
include "Basic-2/reduction/tpr_lift.ma".
include "Basic-2/reduction/tpr_tps.ma".

(* CONTEXT-FREE PARALLEL REDUCTION ON TERMS *********************************)

(* Confluence lemmas ********************************************************)

fact tpr_conf_atom_atom: ∀I. ∃∃X. 𝕒{I} ⇒ X & 𝕒{I} ⇒ X.
/2/ qed.

fact tpr_conf_flat_flat:
   ∀I,V0,V1,T0,T1,V2,T2. (
      ∀X0:term. #[X0] < #[V0] + #[T0] + 1 →
      ∀X1,X2. X0 ⇒ X1 → X0 ⇒ X2 →
      ∃∃X. X1 ⇒ X & X2 ⇒ X
   ) →
   V0 ⇒ V1 → V0 ⇒ V2 → T0 ⇒ T1 → T0 ⇒ T2 →
   ∃∃T0. 𝕗{I} V1. T1 ⇒ T0 & 𝕗{I} V2. T2 ⇒ T0.
#I #V0 #V1 #T0 #T1 #V2 #T2 #IH #HV01 #HV02 #HT01 #HT02
elim (IH … HV01 … HV02) -HV01 HV02 // #V #HV1 #HV2
elim (IH … HT01 … HT02) -HT01 HT02 /3 width=5/
qed.

fact tpr_conf_flat_beta:
   ∀V0,V1,T1,V2,W0,U0,T2. (
      ∀X0:term. #[X0] < #[V0] + (#[W0] + #[U0] + 1) + 1 →
      ∀X1,X2. X0 ⇒ X1 → X0 ⇒ X2 →
      ∃∃X. X1 ⇒ X & X2 ⇒ X
   ) →
   V0 ⇒ V1 → V0 ⇒ V2 →
   U0 ⇒ T2 → 𝕔{Abst} W0. U0 ⇒ T1 →
   ∃∃X. 𝕔{Appl} V1. T1 ⇒ X & 𝕔{Abbr} V2. T2 ⇒ X.
#V0 #V1 #T1 #V2 #W0 #U0 #T2 #IH #HV01 #HV02 #HT02 #H
elim (tpr_inv_abst1 … H) -H #W1 #U1 #HW01 #HU01 #H destruct -T1;
elim (IH … HV01 … HV02) -HV01 HV02 // #V #HV1 #HV2
elim (IH … HT02 … HU01) -HT02 HU01 IH /3 width=5/
qed.

fact tpr_conf_flat_theta:
   ∀V0,V1,T1,V2,V,W0,W2,U0,U2. (
      ∀X0:term. #[X0] < #[V0] + (#[W0] + #[U0] + 1) + 1 →
      ∀X1,X2. X0 ⇒ X1 → X0 ⇒ X2 →
      ∃∃X. X1 ⇒ X & X2 ⇒ X
   ) →
   V0 ⇒ V1 → V0 ⇒ V2 → ↑[O,1] V2 ≡ V →
   W0 ⇒ W2 → U0 ⇒ U2 →  𝕔{Abbr} W0. U0 ⇒ T1 →
   ∃∃X. 𝕔{Appl} V1. T1 ⇒ X & 𝕔{Abbr} W2. 𝕔{Appl} V. U2 ⇒ X.
#V0 #V1 #T1 #V2 #V #W0 #W2 #U0 #U2 #IH #HV01 #HV02 #HV2 #HW02 #HU02 #H
elim (IH … HV01 … HV02) -HV01 HV02 // #VV #HVV1 #HVV2
elim (lift_total VV 0 1) #VVV #HVV
lapply (tpr_lift … HVV2 … HV2 … HVV) #HVVV
elim (tpr_inv_abbr1 … H) -H *
(* case 1: delta *)
[ -HV2 HVV2 #WW2 #UU2 #UU #HWW2 #HUU02 #HUU2 #H destruct -T1;
  elim (IH … HW02 … HWW2) -HW02 HWW2 // #W #HW02 #HWW2
  elim (IH … HU02 … HUU02) -HU02 HUU02 IH // #U #HU2 #HUUU2
  elim (tpr_tps_bind … HWW2 HUUU2 … HUU2) -HUU2 HUUU2 #UUU #HUUU2 #HUUU1
  @ex2_1_intro
  [2: @tpr_theta [6: @HVV |7: @HWW2 |8: @HUUU2 |1,2,3,4: skip | // ]
  |1:skip
  |3: @tpr_delta [3: @tpr_flat |1: skip ] /2 width=5/
  ] (**) (* /5 width=14/ is too slow *)
(* case 3: zeta *)
| -HW02 HVV HVVV #UU1 #HUU10 #HUUT1
  elim (tpr_inv_lift … HU02 … HUU10) -HU02 #UU #HUU2 #HUU1
  lapply (tw_lift … HUU10) -HUU10 #HUU10
  elim (IH … HUUT1 … HUU1) -HUUT1 HUU1 IH // -HUU10 #U #HU2 #HUUU2
  @ex2_1_intro
  [2: @tpr_flat
  |1: skip 
  |3: @tpr_zeta [2: @lift_flat |1: skip |3: @tpr_flat ]
  ] /2 width=5/ (**) (* /5 width=5/ is too slow *)
]
qed.

fact tpr_conf_flat_cast:
   ∀X2,V0,V1,T0,T1. (
      ∀X0:term. #[X0] < #[V0] + #[T0] + 1 →
      ∀X1,X2. X0 ⇒ X1 → X0 ⇒ X2 →
      ∃∃X. X1 ⇒ X & X2 ⇒ X
   ) →
   V0 ⇒ V1 → T0 ⇒ T1 → T0 ⇒ X2 →
   ∃∃X. 𝕔{Cast} V1. T1 ⇒ X & X2 ⇒ X.
#X2 #V0 #V1 #T0 #T1 #IH #_ #HT01 #HT02
elim (IH … HT01 … HT02) -HT01 HT02 IH /3/
qed.

fact tpr_conf_beta_beta:
   ∀W0:term. ∀V0,V1,T0,T1,V2,T2. (
      ∀X0:term. #[X0] < #[V0] + (#[W0] + #[T0] + 1) + 1 →
      ∀X1,X2. X0 ⇒ X1 → X0 ⇒ X2 →
      ∃∃X. X1 ⇒ X & X2 ⇒ X
   ) →
   V0 ⇒ V1 → V0 ⇒ V2 → T0 ⇒ T1 → T0 ⇒ T2 →
   ∃∃X. 𝕔{Abbr} V1. T1 ⇒X & 𝕔{Abbr} V2. T2 ⇒ X.
#W0 #V0 #V1 #T0 #T1 #V2 #T2 #IH #HV01 #HV02 #HT01 #HT02
elim (IH … HV01 … HV02) -HV01 HV02 //
elim (IH … HT01 … HT02) -HT01 HT02 IH /3 width=5/
qed.

fact tpr_conf_delta_delta:
   ∀I1,V0,V1,T0,T1,TT1,V2,T2,TT2. (
      ∀X0:term. #[X0] < #[V0] + #[T0] + 1 →
      ∀X1,X2. X0 ⇒ X1 → X0 ⇒ X2 →
      ∃∃X. X1 ⇒ X & X2 ⇒ X
   ) →
   V0 ⇒ V1 → V0 ⇒ V2 → T0 ⇒ T1 → T0 ⇒ T2 →
   ⋆. 𝕓{I1} V1 ⊢ T1 [O, 1] ≫ TT1 →
   ⋆. 𝕓{I1} V2 ⊢ T2 [O, 1] ≫ TT2 →
   ∃∃X. 𝕓{I1} V1. TT1 ⇒ X & 𝕓{I1} V2. TT2 ⇒ X.
#I1 #V0 #V1 #T0 #T1 #TT1 #V2 #T2 #TT2 #IH #HV01 #HV02 #HT01 #HT02 #HTT1 #HTT2
elim (IH … HV01 … HV02) -HV01 HV02 // #V #HV1 #HV2
elim (IH … HT01 … HT02) -HT01 HT02 IH // #T #HT1 #HT2
elim (tpr_tps_bind … HV1 HT1 … HTT1) -HT1 HTT1 #U1 #TTU1 #HTU1
elim (tpr_tps_bind … HV2 HT2 … HTT2) -HT2 HTT2 #U2 #TTU2 #HTU2
elim (tps_conf … HTU1 … HTU2) -HTU1 HTU2 #U #HU1 #HU2
@ex2_1_intro [2,3: @tpr_delta |1: skip ] /width=10/ (**) (* /3 width=10/ is too slow *)
qed.

fact tpr_conf_delta_zeta:
   ∀X2,V0,V1,T0,T1,TT1,T2. (
      ∀X0:term. #[X0] < #[V0] + #[T0] + 1 →
      ∀X1,X2. X0 ⇒ X1 → X0 ⇒ X2 →
      ∃∃X. X1 ⇒ X & X2 ⇒ X
   ) →
   V0 ⇒ V1 → T0 ⇒ T1 → ⋆. 𝕓{Abbr} V1 ⊢ T1 [O,1] ≫ TT1 →
   T2 ⇒ X2 → ↑[O, 1] T2 ≡ T0 →
   ∃∃X. 𝕓{Abbr} V1. TT1 ⇒ X & X2 ⇒ X.
#X2 #V0 #V1 #T0 #T1 #TT1 #T2 #IH #_ #HT01 #HTT1 #HTX2 #HTT20
elim (tpr_inv_lift … HT01 … HTT20) -HT01 #TT2 #HTT21 #HTT2
lapply (tps_inv_lift1_eq … HTT1 … HTT21) -HTT1 #HTT1 destruct -T1;
lapply (tw_lift … HTT20) -HTT20 #HTT20
elim (IH … HTX2 … HTT2) -HTX2 HTT2 IH /3/
qed.

fact tpr_conf_theta_theta:
   ∀VV1,V0,V1,W0,W1,T0,T1,V2,VV2,W2,T2. (
      ∀X0:term. #[X0] < #[V0] + (#[W0] + #[T0] + 1) + 1 →
      ∀X1,X2. X0 ⇒ X1 → X0 ⇒ X2 →
      ∃∃X. X1 ⇒ X & X2 ⇒ X
   ) →
   V0 ⇒ V1 → V0 ⇒ V2 → W0 ⇒ W1 → W0 ⇒ W2 → T0 ⇒ T1 → T0 ⇒ T2 →
   ↑[O, 1] V1 ≡ VV1 → ↑[O, 1] V2 ≡ VV2 →
   ∃∃X. 𝕔{Abbr} W1. 𝕔{Appl} VV1. T1 ⇒ X & 𝕔{Abbr} W2. 𝕔{Appl} VV2. T2 ⇒ X.
#VV1 #V0 #V1 #W0 #W1 #T0 #T1 #V2 #VV2 #W2 #T2 #IH #HV01 #HV02 #HW01 #HW02 #HT01 #HT02 #HVV1 #HVV2
elim (IH … HV01 … HV02) -HV01 HV02 // #V #HV1 #HV2
elim (IH … HW01 … HW02) -HW01 HW02 // #W #HW1 #HW2
elim (IH … HT01 … HT02) -HT01 HT02 IH // #T #HT1 #HT2
elim (lift_total V 0 1) #VV #HVV
lapply (tpr_lift … HV1 … HVV1 … HVV) -HV1 HVV1 #HVV1
lapply (tpr_lift … HV2 … HVV2 … HVV) -HV2 HVV2 HVV #HVV2
@ex2_1_intro [2,3: @tpr_bind |1:skip ] /2 width=5/ (**) (* /4 width=5/ is too slow *)
qed.

fact tpr_conf_zeta_zeta:
   ∀V0:term. ∀X2,TT0,T0,T1,T2. (
      ∀X0:term. #[X0] < #[V0] + #[TT0] + 1 →
      ∀X1,X2. X0 ⇒ X1 → X0 ⇒ X2 →
      ∃∃X. X1 ⇒ X & X2 ⇒ X
   ) →
   T0 ⇒ T1 → T2 ⇒ X2 →
   ↑[O, 1] T0 ≡ TT0 → ↑[O, 1] T2 ≡ TT0 →
   ∃∃X. T1 ⇒ X & X2 ⇒ X.
#V0 #X2 #TT0 #T0 #T1 #T2 #IH #HT01 #HTX2 #HTT0 #HTT20
lapply (lift_inj … HTT0 … HTT20) -HTT0 #H destruct -T0;
lapply (tw_lift … HTT20) -HTT20 #HTT20
elim (IH … HT01 … HTX2) -HT01 HTX2 IH /2/
qed.

fact tpr_conf_tau_tau:
   ∀V0,T0:term. ∀X2,T1. (
      ∀X0:term. #[X0] < #[V0] + #[T0] + 1 →
      ∀X1,X2. X0 ⇒ X1 → X0 ⇒ X2 →
      ∃∃X. X1 ⇒ X & X2 ⇒ X
   ) →
   T0 ⇒ T1 → T0 ⇒ X2 →
   ∃∃X. T1 ⇒ X & X2 ⇒ X.
#V0 #T0 #X2 #T1 #IH #HT01 #HT02
elim (IH … HT01 … HT02) -HT01 HT02 IH /2/
qed.

(* Confluence ***************************************************************)

fact tpr_conf_aux:
   ∀Y0:term. (
      ∀X0:term. #[X0] < #[Y0] →
      ∀X1,X2. X0 ⇒ X1 → X0 ⇒ X2 →
      ∃∃X. X1 ⇒ X & X2 ⇒ X
         ) →
   ∀X0,X1,X2. X0 ⇒ X1 → X0 ⇒ X2 → X0 = Y0 →
   ∃∃X. X1 ⇒ X & X2 ⇒ X.
#Y0 #IH #X0 #X1 #X2 * -X0 X1
[ #I1 #H1 #H2 destruct -Y0;
  lapply (tpr_inv_atom1 … H1) -H1
(* case 1: atom, atom *)
  #H1 destruct -X2 //
| #I #V0 #V1 #T0 #T1 #HV01 #HT01 #H1 #H2 destruct -Y0;
  elim (tpr_inv_flat1 … H1) -H1 *
(* case 2: flat, flat *)
  [ #V2 #T2 #HV02 #HT02 #H destruct -X2
    /3 width=7 by tpr_conf_flat_flat/ (**) (* /3 width=7/ is too slow *)
(* case 3: flat, beta *)
  | #V2 #W #U0 #T2 #HV02 #HT02 #H1 #H2 #H3 destruct -T0 X2 I
    /3 width=8 by tpr_conf_flat_beta/ (**) (* /3 width=8/ is too slow *)
(* case 4: flat, theta *)
  | #V2 #V #W0 #W2 #U0 #U2 #HV02 #HW02 #HT02 #HV2 #H1 #H2 #H3 destruct -T0 X2 I
    /3 width=11 by tpr_conf_flat_theta/ (**) (* /3 width=11/ is too slow *)
(* case 5: flat, tau *)
  | #HT02 #H destruct -I
    /3 width=6 by tpr_conf_flat_cast/ (**) (* /3 width=6/ is too slow *)
  ]
| #V0 #V1 #W0 #T0 #T1 #HV01 #HT01 #H1 #H2 destruct -Y0;
  elim (tpr_inv_appl1 … H1) -H1 *
(* case 6: beta, flat (repeated) *)
  [ #V2 #T2 #HV02 #HT02 #H destruct -X2
    @ex2_1_comm /3 width=8 by tpr_conf_flat_beta/
(* case 7: beta, beta *)
  | #V2 #WW0 #TT0 #T2 #HV02 #HT02 #H1 #H2 destruct -W0 T0 X2
    /3 width=8 by tpr_conf_beta_beta/ (**) (* /3 width=8/ is too slow *)
(* case 8, beta, theta (excluded) *)
  | #V2 #VV2 #WW0 #W2 #TT0 #T2 #_ #_ #_ #_ #H destruct
  ]
| #I1 #V0 #V1 #T0 #T1 #TT1 #HV01 #HT01 #HTT1 #H1 #H2 destruct -Y0;
  elim (tpr_inv_bind1 … H1) -H1 *
(* case 9: delta, delta *)
  [ #V2 #T2 #TT2 #HV02 #HT02 #HTT2 #H destruct -X2
    /3 width=11 by tpr_conf_delta_delta/ (**) (* /3 width=11/ is too slow *)
(* case 10: delta, zata *)
  | #T2 #HT20 #HTX2 #H destruct -I1;
    /3 width=10 by tpr_conf_delta_zeta/ (**) (* /3 width=10/ is too slow *)
  ]
| #VV1 #V0 #V1 #W0 #W1 #T0 #T1 #HV01 #HVV1 #HW01 #HT01 #H1 #H2 destruct -Y0;
  elim (tpr_inv_appl1 … H1) -H1 *
(* case 11: theta, flat (repeated) *)
  [ #V2 #T2 #HV02 #HT02 #H destruct -X2
    @ex2_1_comm /3 width=11 by tpr_conf_flat_theta/
(* case 12: theta, beta (repeated) *)
  | #V2 #WW0 #TT0 #T2 #_ #_ #H destruct
(* case 13: theta, theta *)
  | #V2 #VV2 #WW0 #W2 #TT0 #T2 #V02 #HW02 #HT02 #HVV2 #H1 #H2 destruct -W0 T0 X2
    /3 width=14 by tpr_conf_theta_theta/ (**) (* /3 width=14/ is too slow *)
  ]
| #V0 #TT0 #T0 #T1 #HTT0 #HT01 #H1 #H2 destruct -Y0;
  elim (tpr_inv_abbr1 … H1) -H1 *
(* case 14: zeta, delta (repeated) *)
  [ #V2 #T2 #TT2 #HV02 #HT02 #HTT2 #H destruct -X2
    @ex2_1_comm /3 width=10 by tpr_conf_delta_zeta/
(* case 15: zeta, zeta *)
  | #T2 #HTT20 #HTX2
    /3 width=9 by tpr_conf_zeta_zeta/ (**) (* /3 width=9/ is too slow *)
  ] 
| #V0 #T0 #T1 #HT01 #H1 #H2 destruct -Y0;
  elim (tpr_inv_cast1 … H1) -H1
(* case 16: tau, flat (repeated) *)
  [ * #V2 #T2 #HV02 #HT02 #H destruct -X2
    @ex2_1_comm /3 width=6 by tpr_conf_flat_cast/
(* case 17: tau, tau *)
  | #HT02
    /2 by tpr_conf_tau_tau/
  ]
]
qed.

theorem tpr_conf: ∀T0:term. ∀T1,T2. T0 ⇒ T1 → T0 ⇒ T2 →
                  ∃∃T. T1 ⇒ T & T2 ⇒ T.
#T @(tw_wf_ind … T) -T /3 width=6 by tpr_conf_aux/
qed.
