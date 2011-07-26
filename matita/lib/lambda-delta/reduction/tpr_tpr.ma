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
  @ex2_1_intro
  [2: @tpr_theta [5: @HVV1 |6: @HVV |7:// by {}; (*@HWW*) |8: @HUU |1,2,3,4:skip ]
  |3: @tpr_bind [ @HW2 | @tpr_flat [ @HVVV | @HU2 ] ]
  | skip 
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
    //
theorem tpr_conf: ∀T0,T1,T2. T0 ⇒ T1 → T0 ⇒ T2 →
                  ∃∃T. T1 ⇒ T & T2 ⇒ T.
#T @(tw_wf_ind … T) -T /3 width=6/
qed.
*)
lemma tpr_conf_aux:
   ∀T. (
      ∀T1. #T1 < #T → ∀T3,T4. T1 ⇒ T3 → T1 ⇒ T4 →
      ∃∃T0. T3 ⇒ T0 & T4 ⇒ T0
         ) →
   ∀U1,T1,U2,T2. U1 ⇒ T1 → U2 ⇒ T2 →
   U1 = T → U2 = T →
   ∃∃T0. T1 ⇒ T0 & T2 ⇒ T0.
#T #IH  #U1 #T1 #U2 #T2
* -U1 T1
[ #k1 * -U2 T2
(* case 1: sort, sort *)
  [ #k2 #H1 #H2 destruct -T k2 //
(* case 2: sort, lref (excluded) *)
  | #i2 #H1 #H2 destruct
(* case 3: sort, bind (excluded) *)
  | #I2 #V21 #V22 #T21 #T22 #_ #_ #H1 #H2 destruct
(* case 4: sort, flat (excluded) *)
  | #I2 #V21 #V22 #T21 #T22 #_ #_ #H1 #H2 destruct
(* case 5: sort, beta (excluded) *)
  | #V21 #V22 #W2 #T21 #T22 #_ #_ #H1 #H2 destruct
(* case 6: sort, delta (excluded) *)
  | #V21 #V22 #T21 #T22 #T20 #_ #_ #_ #H1 #H2 destruct
(* case 7: sort, theta (excluded) *)
  | #V2 #V21 #V22 #W21 #W22 #T21 #T22 #_ #_ #_ #_ #H1 #H2 destruct
(* case 8: sort, zeta (excluded) *)
  | #V2 #T21 #T22 #T20 #_ #_ #H1 #H2 destruct
(* case 9: sort, tau (excluded) *)
  | #V2 #T21 #T22 #_ #H1 #H2 destruct
  ]
| #i1 * -U2 T2
(* case 10: lref, sort (excluded) broken *)
  [ #k2 #H1 #H2 destruct
(* case 11: lref, sort (excluded) *)
  | #i2 #H1 #H2 destruct -T i2 //
(* case 12: lref, bind (excluded) *)
  | #I2 #V21 #V22 #T21 #T22 #_ #_ #H1 #H2 destruct
(* case 13: lref, flat (excluded) *)
  | #I2 #V21 #V22 #T21 #T22 #_ #_ #H1 #H2 destruct
(* case 14: lref, beta (excluded) *)
  | #V21 #V22 #W2 #T21 #T22 #_ #_ #H1 #H2 destruct
(* case 15: lref, delta (excluded) *)
  | #V21 #V22 #T21 #T22 #T20 #_ #_ #_ #H1 #H2 destruct
(* case 16: lref, theta (excluded) *)
  | #V2 #V21 #V22 #W21 #W22 #T21 #T22 #_ #_ #_ #_ #H1 #H2 destruct
(* case 17: lref, zeta (excluded) *)
  | #V2 #T21 #T22 #T20 #_ #_ #H1 #H2 destruct
(* case 18: lref, tau (excluded) *)
  | #V2 #T21 #T22 #_ #H1 #H2 destruct
  ]
| #I1 #V11 #V12 #T11 #T12 #HV112 #HT112 * -U2 T2
(* case 19: bind, sort (excluded) *)
  [ #k2 #H1 #H2 destruct
(* case 20: bind, lref (excluded) *)
  | #i2 #H1 #H2 destruct
(* case 21: bind, bind *)
  | #I2 #V21 #V22 #T21 #T22 #HV212 #HT212 #H1 #H2
    destruct -T I2 V21 T21 /3 width=7/
(* case 22: bind, flat (excluded) *)
  | #I2 #V21 #V22 #T21 #T22 #_ #_ #H1 #H2 destruct
(* case 23: bind, beta (excluded) *)
  | #V21 #V22 #W2 #T21 #T22 #_ #_ #H1 #H2 destruct
(* case 24: bind, delta (excluded) *)
  | #V21 #V22 #T21 #T22 #T20 #_ #_ #_ #H1 #H2 destruct
(* case 25: bind, theta (excluded) *)
  | #V2 #V21 #V22 #W21 #W22 #T21 #T22 #_ #_ #_ #_ #H1 #H2 destruct
(* case 26: bind, zeta *)
  | #V2 #T21 #T22 #T20 #HT212 #HT220 #H1 #H2
    destruct -I1 V2 T21 T /3 width=8/
(* case 27: bind, tau (excluded) *)
  | #V2 #T21 #T22 #_ #H1 #H2 destruct
  ]
| #I1 #V11 #V12 #T11 #T12 #HV112 #HT112 * -U2 T2
(* case 28: flat, sort (excluded) *)
  [ #k2 #H1 #H2 destruct
(* case 29: flat, lref (excluded) *)
  | #i2 #H1 #H2 destruct
(* case 30: flat, bind (excluded) *)
  | #I2 #V21 #V22 #T21 #T22 #_ #_ #H1 #H2 destruct
(* case 31: flat, flat *)
  | #I2 #V21 #V22 #T21 #T22 #HV212 #HT212 #H1 #H2
    destruct -T I2 V21 T21 /3 width=7/
(* case 32: flat, beta *)
  | #V21 #V22 #W2 #T21 #T22 #HV212 #HT212 #H1 #H2
    destruct -I1 V21 T11 T /3 width=8/ (**) (* slow *)
(* case 33: flat, delta (excluded) *)
  | #V21 #V22 #T21 #T22 #T20 #_ #_ #_ #H1 #H2 destruct
(* case 34: flat, theta *)
  | #V2 #V21 #V22 #W21 #W22 #T21 #T22 #H212 #HV222 #HW212 #HT212 #H1 #H2
    destruct -I1 V21 T11 T //

lemma tpr_conf_flat_theta:
   ∀V11,V12,T12,V2,V22,W21,W22,T21,T22. (
      ∀T1. #T1 < #V11 + (#W21 + #T21 + 1) + 1 →
      ∀T3,T4. T1 ⇒ T3 → T1 ⇒ T4 →
      ∃∃T0. T3 ⇒ T0 & T4 ⇒T0
   ) →
   V11 ⇒ V12 → V11 ⇒ V22 → ↑[O,1] V22 ≡ V2 →
   W21 ⇒ W22 → T21 ⇒ T22 →  𝕓{Abbr} W21. T21 ⇒ T12 →
   ∃∃T0. 𝕗{Appl} V12. T12 ⇒ T0 & 𝕓{Abbr} W22. 𝕗{Appl} V2. T22 ⇒T0.

lemma tpr_conf_bind_delta:
   ∀V0,V1,T0,T1,V2,T2,T. (
      ∀X. #X < #V0 + #T0 + 1 →
      ∀X1,X2. X0 ⇒ X1 → X0 ⇒ X2 →
      ∃∃X. X1 ⇒ X & X2⇒X
   ) →
   V0 ⇒ V1 → V0 ⇒ V2 →
   T0 ⇒ T1 → T0 ⇒ T2 → ⋆. 𝕓{Abbr} V2 ⊢ T2 [O,1] ≫ T →
   ∃∃X. 𝕓{Abbr} V1. T1 ⇒ X & 𝕓{Abbr} V2. T ⇒ X.