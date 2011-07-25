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

include "lambda-delta/substitution/lift_weight.ma".
include "lambda-delta/reduction/tpr_main.ma".

(* CONTEXT-FREE PARALLEL REDUCTION ON TERMS *********************************)

(* Confluence lemmas ********************************************************)

lemma tpr_conf_sort_sort: ∀k1. ∃∃T0. ⋆k1 ⇒ T0 & ⋆k1 ⇒ T0.
/2/ qed.

lemma tpr_conf_lref_lref: ∀i1. ∃∃T0. #i1 ⇒ T0 & #i1 ⇒ T0.
/2/ qed.

lemma tpr_conf_bind_bind:
   ∀I1,V11,V12,T11,T12,V22,T22. (
      ∀T1. #T1 < #V11 + #T11 + 1 →
      ∀T3,T4. T1 ⇒ T3 → T1 ⇒ T4 →
      ∃∃T0. T3 ⇒ T0 & T4 ⇒ T0
   ) →
   V11 ⇒ V12 → T11 ⇒ T12 →
   V11 ⇒ V22 → T11 ⇒ T22 →
   ∃∃T0. 𝕓{I1} V12. T12 ⇒ T0 & 𝕓{I1} V22. T22 ⇒ T0.
#I1 #V11 #V12 #T11 #T12 #V22 #T22 #IH #HV1 #HT1 #HV2 #HT2
elim (IH … HV1 … HV2) -HV1 HV2 // #V #HV1 #HV2
elim (IH … HT1 … HT2) -HT1 HT2 IH /3 width=5/
qed.

lemma tpr_conf_bind_zeta:
   ∀V11,V12,T11,T12,T22,T20. (
      ∀T1. #T1 < #V11 + #T11 +1 →
      ∀T3,T4. T1 ⇒ T3 → T1 ⇒ T4 →
      ∃∃T0. T3 ⇒ T0 & T4 ⇒ T0
   ) →
   V11 ⇒ V12 → T22 ⇒ T20 → T11 ⇒ T12 → ↑[O, 1] T22 ≡ T11 →
   ∃∃T0. 𝕓{Abbr} V12. T12 ⇒ T0 & T20 ⇒ T0.
#V11 #V12 #T11 #T12 #T22 #T20 #IH #HV112 #HT202 #HT112 #HT
elim (tpr_inv_lift … HT112 … HT) -HT112 #T #HT12 #HT22
lapply (tw_lift … HT) -HT #HT
elim (IH … HT202 … HT22) -HT202 HT22 IH /3/
qed.

lemma tpr_conf_flat_flat:
   ∀I1,V11,V12,T11,T12,V22,T22. (
      ∀T1. #T1 < #V11 + #T11 + 1 →
      ∀T3,T4. T1 ⇒ T3 → T1 ⇒ T4 →
      ∃∃T0. T3 ⇒ T0 & T4 ⇒ T0
   ) →
   V11 ⇒ V12 → T11 ⇒ T12 →
   V11 ⇒ V22 → T11 ⇒ T22 →
   ∃∃T0. 𝕗{I1} V12. T12 ⇒ T0 & 𝕗{I1} V22. T22 ⇒ T0.
#I1 #V11 #V12 #T11 #T12 #V22 #T22 #IH #HV1 #HT1 #HV2 #HT2
elim (IH … HV1 … HV2) -HV1 HV2 // #V #HV1 #HV2
elim (IH … HT1 … HT2) -HT1 HT2 /3 width=5/
qed.

lemma tpr_conf_flat_beta:
   ∀V11,V12,T12,V22,W2,T21,T22. (
      ∀T1. #T1 < #V11 + (#W2 + #T21 + 1) + 1 →
      ∀T3,T4. T1 ⇒ T3 → T1 ⇒ T4 →
      ∃∃T0. T3 ⇒ T0 & T4 ⇒ T0
   ) →
   V11 ⇒ V12 → V11 ⇒ V22 →
   T21 ⇒ T22 → 𝕓{Abst} W2. T21 ⇒ T12 →
   ∃∃T0. 𝕗{Appl} V12. T12 ⇒ T0 & 𝕓{Abbr} V22. T22 ⇒ T0.
#V11 #V12 #T12 #V22 #W2 #T21 #T22 #IH #HV1 #HV2 #HT1 #HT2
elim (tpr_inv_abst1 … HT2) -HT2 #W1 #T1 #HW21 #HT21 #H destruct -T12;
elim (IH … HV1 … HV2) -HV1 HV2 // #V #HV12 #HV22
elim (IH … HT21 … HT1) -HT21 HT1 IH /3 width=5/
qed.

lemma tpr_conf_flat_theta:
   ∀V11,V12,T12,V2,V22,W21,W22,T21,T22. (
      ∀T1. #T1 < #V11 + (#W21 + #T21 + 1) + 1 →
      ∀T3,T4. T1 ⇒ T3 → T1 ⇒ T4 →
      ∃∃T0. T3 ⇒ T0 & T4 ⇒T0
   ) →
   V11 ⇒ V12 → V11 ⇒ V22 → ↑[O,1] V22 ≡ V2 →
   W21 ⇒ W22 → T21 ⇒ T22 →  𝕓{Abbr} W21. T21 ⇒ T12 →
   ∃∃T0. 𝕗{Appl} V12. T12 ⇒ T0 & 𝕓{Abbr} W22. 𝕗{Appl} V2. T22 ⇒T0.


(* Confluence ***************************************************************)

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

theorem tpr_conf: ∀T,T1,T2. T ⇒ T1 → T ⇒ T2 →
                 ∃∃T0. T1 ⇒ T0 & T2 ⇒ T0.
#T @(tw_wf_ind … T) -T /3 width=8/
qed.
