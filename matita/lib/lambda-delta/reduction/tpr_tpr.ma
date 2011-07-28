(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic
    ||A||  Library of Mathematics, developed at the Computer Science
    ||T||  Department of the University of Bologna, Italy.
    ||I||
    ||T||
    ||A||  This file is distributed under the terms of the
    \   /  GNU General Public License Version 2
     \ /
      V_______________________________________________________________ *)

include "lambda-delta/substitution/lift_fun.ma".
include "lambda-delta/substitution/lift_weight.ma".
include "lambda-delta/reduction/tpr_main.ma".
include "lambda-delta/reduction/tpr_ps.ma".

(* CONTEXT-FREE PARALLEL REDUCTION ON TERMS *********************************)

(* Confluence lemmas ********************************************************)

lemma tpr_conf_sort_sort: ∀k. ∃∃X. ⋆k ⇒ X & ⋆k ⇒ X.
/2/ qed.

lemma tpr_conf_lref_lref: ∀i. ∃∃X. #i ⇒ X & #i ⇒ X.
/2/ qed.

lemma tpr_conf_bind_bind:
   ∀I,V0,V1,T0,T1,V2,T2. (
      ∀X0:term. #X0 < #V0 + #T0 + 1 →
      ∀X1,X2. X0 ⇒ X1 → X0 ⇒ X2 →
      ∃∃X. X1 ⇒ X & X2 ⇒ X
   ) →
   V0 ⇒ V1 → V0 ⇒ V2 → T0 ⇒ T1 → T0 ⇒ T2 →
   ∃∃X. 𝕓{I} V1. T1 ⇒ X & 𝕓{I} V2. T2 ⇒ X.
#I #V0 #V1 #T0 #T1 #V2 #T2 #IH #HV01 #HV02 #HT01 #HT02
elim (IH … HV01 … HV02) -HV01 HV02 // #V #HV1 #HV2
elim (IH … HT01 … HT02) -HT01 HT02 IH /3 width=5/
qed.

lemma tpr_conf_bind_delta:
   ∀V0,V1,T0,T1,V2,T2,T. (
      ∀X0:term. #X0 < #V0 + #T0 + 1 →
      ∀X1,X2. X0 ⇒ X1 → X0 ⇒ X2 →
      ∃∃X. X1 ⇒ X & X2 ⇒ X
   ) →
   V0 ⇒ V1 → V0 ⇒ V2 →
   T0 ⇒ T1 → T0 ⇒ T2 → ⋆. 𝕓{Abbr} V2 ⊢ T2 [O,1] ≫ T →
   ∃∃X. 𝕓{Abbr} V1. T1 ⇒ X & 𝕓{Abbr} V2. T ⇒ X.
#V0 #V1 #T0 #T1 #V2 #T2 #T #IH #HV01 #HV02 #HT01 #HT02 #HT2
elim (IH … HV01 … HV02) -HV01 HV02 // #V #HV1 #HV2
elim (IH … HT01 … HT02) -HT01 HT02 IH // -V0 T0 #T0 #HT10 #HT20
elim (tpr_ps_bind … HV2 HT20 … HT2) -HT20 HT2 /3 width=5/
qed.

lemma tpr_conf_bind_zeta:
   ∀X2,V0,V1,T0,T1,T. (
      ∀X0:term. #X0 < #V0 + #T0 +1 →
      ∀X1,X2. X0 ⇒ X1 → X0 ⇒ X2 →
      ∃∃X. X1 ⇒ X & X2 ⇒ X
   ) →
   V0 ⇒ V1 → T0 ⇒ T1 → T ⇒ X2 → ↑[O, 1] T ≡ T0 →
   ∃∃X. 𝕓{Abbr} V1. T1 ⇒ X & X2 ⇒ X.
#X2 #V0 #V1 #T0 #T1 #T #IH #HV01 #HT01 #HTX2 #HT0
elim (tpr_inv_lift … HT01 … HT0) -HT01 #U #HUT1 #HTU
lapply (tw_lift … HT0) -HT0 #HT0
elim (IH … HTX2 … HTU) -HTX2 HTU IH /3/
qed.

lemma tpr_conf_flat_flat:
   ∀I,V0,V1,T0,T1,V2,T2. (
      ∀X0:term. #X0 < #V0 + #T0 + 1 →
      ∀X1,X2. X0 ⇒ X1 → X0 ⇒ X2 →
      ∃∃X. X1 ⇒ X & X2 ⇒ X
   ) →
   V0 ⇒ V1 → V0 ⇒ V2 → T0 ⇒ T1 → T0 ⇒ T2 →
   ∃∃T0. 𝕗{I} V1. T1 ⇒ T0 & 𝕗{I} V2. T2 ⇒ T0.
#I #V0 #V1 #T0 #T1 #V2 #T2 #IH #HV01 #HV02 #HT01 #HT02
elim (IH … HV01 … HV02) -HV01 HV02 // #V #HV1 #HV2
elim (IH … HT01 … HT02) -HT01 HT02 /3 width=5/
qed.

lemma tpr_conf_flat_beta:
   ∀V0,V1,T1,V2,W0,U0,T2. (
      ∀X0:term. #X0 < #V0 + (#W0 + #U0 + 1) + 1 →
      ∀X1,X2. X0 ⇒ X1 → X0 ⇒ X2 →
      ∃∃X. X1 ⇒ X & X2 ⇒ X
   ) →
   V0 ⇒ V1 → V0 ⇒ V2 →
   U0 ⇒ T2 → 𝕓{Abst} W0. U0 ⇒ T1 →
   ∃∃X. 𝕗{Appl} V1. T1 ⇒ X & 𝕓{Abbr} V2. T2 ⇒ X.
#V0 #V1 #T1 #V2 #W0 #U0 #T2 #IH #HV01 #HV02 #HT02 #H
elim (tpr_inv_abst1 … H) -H #W1 #U1 #HW01 #HU01 #H destruct -T1;
elim (IH … HV01 … HV02) -HV01 HV02 // #V #HV1 #HV2
elim (IH … HT02 … HU01) -HT02 HU01 IH /3 width=5/
qed.

lemma tpr_conf_flat_theta:
   ∀V0,V1,T1,V2,V,W0,W2,U0,U2. (
      ∀X0:term. #X0 < #V0 + (#W0 + #U0 + 1) + 1 →
      ∀X1,X2. X0 ⇒ X1 → X0 ⇒ X2 →
      ∃∃X. X1 ⇒ X & X2 ⇒ X
   ) →
   V0 ⇒ V1 → V0 ⇒ V2 → ↑[O,1] V2 ≡ V →
   W0 ⇒ W2 → U0 ⇒ U2 →  𝕓{Abbr} W0. U0 ⇒ T1 →
   ∃∃X. 𝕗{Appl} V1. T1 ⇒ X & 𝕓{Abbr} W2. 𝕗{Appl} V. U2 ⇒ X.
#V0 #V1 #T1 #V2 #V #W0 #W2 #U0 #U2 #IH #HV01 #HV02 #HV2 #HW02 #HU02 #H
elim (IH … HV01 … HV02) -HV01 HV02 // #VV #HVV1 #HVV2
elim (lift_total VV 0 1) #VVV #HVV
lapply (tpr_lift … HVV2 … HV2 … HVV) #HVVV
elim (tpr_inv_abbr1 … H) -H *
(* case 1: bind *)
[ -HV2 HVV2 #WW #UU #HWW0 #HUU0 #H destruct -T1;
  elim (IH … HW02 … HWW0) -HW02 HWW0 // #W #HW2 #HWW
  elim (IH … HU02 … HUU0) -HU02 HUU0 IH // #U #HU2 #HUU
  @ex2_1_intro [2: @tpr_theta |1:skip |3: @tpr_bind ] /2 width=7/ (**) (* /4 width=7/ is too slow *)
(* case 2: delta *)
| -HV2 HVV2 #WW2 #UU2 #UU #HWW2 #HUU02 #HUU2 #H destruct -T1;
  elim (IH … HW02 … HWW2) -HW02 HWW2 // #W #HW02 #HWW2
  elim (IH … HU02 … HUU02) -HU02 HUU02 IH // #U #HU2 #HUUU2
  elim (tpr_ps_bind … HWW2 HUUU2 … HUU2) -HUU2 HUUU2 #UUU #HUUU2 #HUUU1
  @ex2_1_intro
  [2: @tpr_theta
  |1:skip
  |3: @tpr_delta [3: @tpr_flat |1: skip ]
  ] /2 width=14/ (**) (* /5 width=14/ is too slow *) 
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

lemma tpr_conf_flat_cast:
   ∀X2,V0,V1,T0,T1. (
      ∀X0:term. #X0 < #V0 + # T0 + 1 →
      ∀X1,X2. X0 ⇒ X1 → X0 ⇒ X2 →
      ∃∃X. X1 ⇒ X & X2 ⇒ X
   ) →
   V0 ⇒ V1 → T0 ⇒ T1 → T0 ⇒ X2 →
   ∃∃X. 𝕗{Cast} V1. T1 ⇒ X & X2 ⇒ X.
#X2 #V0 #V1 #T0 #T1 #IH #_ #HT01 #HT02
elim (IH … HT01 … HT02) -HT01 HT02 IH /3/
qed.

lemma tpr_conf_beta_beta:
   ∀W0:term. ∀V0,V1,T0,T1,V2,T2. (
      ∀X0:term. #X0 < #V0 + (#W0 + #T0 + 1) + 1 →
      ∀X1,X2. X0 ⇒ X1 → X0 ⇒ X2 →
      ∃∃X. X1 ⇒ X & X2 ⇒ X
   ) →
   V0 ⇒ V1 → V0 ⇒ V2 → T0 ⇒ T1 → T0 ⇒ T2 →
   ∃∃X. 𝕓{Abbr} V1. T1 ⇒X & 𝕓{Abbr} V2. T2 ⇒ X.
#W0 #V0 #V1 #T0 #T1 #V2 #T2 #IH #HV01 #HV02 #HT01 #HT02
elim (IH … HV01 … HV02) -HV01 HV02 //
elim (IH … HT01 … HT02) -HT01 HT02 IH /3 width=5/
qed.

(* Confluence ***************************************************************)

lemma tpr_conf_aux:
   ∀Y0:term. (
      ∀X0:term. #X0 < #Y0 → ∀X1,X2. X0 ⇒ X1 → X0 ⇒ X2 →
      ∃∃X. X1 ⇒ X & X2 ⇒ X
         ) →
   ∀X0,X1,X2. X0 ⇒ X1 → X0 ⇒ X2 → X0 = Y0 →
   ∃∃X. X1 ⇒ X & X2 ⇒ X.
#Y0 #IH #X0 #X1 #X2 * -X0 X1
[ #k1 #H1 #H2 destruct -Y0;
  lapply (tpr_inv_sort1 … H1) -H1
(* case 1: sort, sort *)
  #H1 destruct -X2 //
| #i1 #H1 #H2 destruct -Y0;
  lapply (tpr_inv_lref1 … H1) -H1
(* case 2: lref, lref *)
  #H1 destruct -X2 //
| #I #V0 #V1 #T0 #T1 #HV01 #HT01 #H1 #H2 destruct -Y0;
  elim (tpr_inv_bind1 … H1) -H1 *
(* case 3: bind, bind *)
  [ #V2 #T2 #HV02 #HT02 #H destruct -X2
    @tpr_conf_bind_bind /2 width=7/ (**) (* /3 width=7/ is too slow *)
(* case 4: bind, delta *)
  | #V2 #T2 #T #HV02 #HT02 #HT2 #H1 #H2 destruct -X2 I
    @tpr_conf_bind_delta /2 width=9/ (**) (* /3 width=9/ is too slow *)
(* case 5: bind, zeta *)
  | #T #HT0 #HTX2 #H destruct -I
    @tpr_conf_bind_zeta /2 width=8/ (**) (* /3 width=8/ is too slow *)
  ]
| #I #V0 #V1 #T0 #T1 #HV01 #HT01 #H1 #H2 destruct -Y0;
  elim (tpr_inv_flat1 … H1) -H1 *
(* case 6: flat, flat *)
  [ #V2 #T2 #HV02 #HT02 #H destruct -X2
    @tpr_conf_flat_flat /2 width=7/ (**) (* /3 width=7/ is too slow *)
(* case 7: flat, beta *)
  | #V2 #W #U0 #T2 #HV02 #HT02 #H1 #H2 #H3 destruct -T0 X2 I
    @tpr_conf_flat_beta /2 width=8/ (**) (* /3 width=8/ is too slow *)
(* case 8: flat, theta *)
  | #V2 #V #W0 #W2 #U0 #U2 #HV02 #HW02 #HT02 #HV2 #H1 #H2 #H3 destruct -T0 X2 I
    @tpr_conf_flat_theta /2 width=11/ (**) (* /3 width=11/ is too slow *)
(* case 9: flat, tau *)
  | #HT02 #H destruct -I
    @tpr_conf_flat_cast /2 width=6/ (**) (* /3 width=6/ is too slow *)
  ]
| #V0 #V1 #W0 #T0 #T1 #HV01 #HT01 #H1 #H2 destruct -Y0;
  elim (tpr_inv_appl1 … H1) -H1 *
(* case 10: beta, flat (repeated) *)
  [ #V2 #T2 #HV02 #HT02 #H destruct -X2
    @ex2_1_comm @tpr_conf_flat_beta /2 width=8/
(* case 11: beta, beta *)
  | #V2 #WW0 #TT0 #T2 #HV02 #HT02 #H1 #H2 destruct -W0 T0 X2
    @tpr_conf_beta_beta /2 width=8/ (**) (* /3 width=8/ is too slow *)
(* case 12, beta, theta (excluded) *)
  | #V2 #VV2 #WW0 #W2 #TT0 #T2 #_ #_ #_ #_ #H destruct
  ]
| #V0 #V1 #T0 #T1 #TT1 #HV01 #T01 #HTT1 #H1 #H2 destruct -Y0
  elim (tpr_inv_abbr1 … H1) -H1 *
(* case 13: delta, bind (repeated) *)
  [ #V2 #T2 #HV02 #T02 #H destruct -X2
    @ex2_1_comm @tpr_conf_bind_delta /2 width=9/
    
    

lemma tpr_conf_beta_beta:
   ∀V0,V1,W0,T0,T1,V2,T2. (
      ∀X0:term. #X0 ≤ #V0 + (#W0 + #T0 + 1) + 1 →
      ∀X1,X2. X0 ⇒ X1 → X0 ⇒ X2 →
      ∃∃X. X1 ⇒ X & X2 ⇒ X
   ) →
   V0 ⇒ V1 → V0 ⇒ V2 → T0 ⇒ T1 → T0 ⇒ T2 →
   ∃∃X. 𝕓{Abbr} V1. T1 ⇒X & 𝕓{Abbr} V2. T2 ⇒ X.
#V0 #V1 #W0 #T0 #T1 #V2 #T2 #IH #HV01 #HV02 #HT01 #HT02 

 


theorem tpr_conf: ∀T0,T1,T2. T0 ⇒ T1 → T0 ⇒ T2 →
                  ∃∃T. T1 ⇒ T & T2 ⇒ T.
#T @(tw_wf_ind … T) -T /3 width=6/
qed.
