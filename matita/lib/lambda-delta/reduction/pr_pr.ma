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

include "lambda-delta/syntax/weight.ma".
include "lambda-delta/reduction/pr_lift.ma".

(* SINGLE STEP PARALLEL REDUCTION ON TERMS **********************************)

(* Confluence lemmas ********************************************************)

lemma pr_conf_sort_sort: ∀L,k1. ∃∃T0. L ⊢ (⋆k1) ⇒ T0 & L ⊢ (⋆k1) ⇒ T0.
/2/ qed.

lemma pr_conf_lref_lref: ∀L,i1. ∃∃T0. L ⊢ (#i1) ⇒ T0 & L ⊢ (#i1) ⇒ T0.
/2/ qed.

lemma pr_conf_bind_bind:
   ∀L,I1,V11,V12,T11,T12,V22,T22. (
      ∀L1,T1. #L1 + #T1 < #L + (#V11 + #T11 + 1) →
      ∀T3,T4. L1 ⊢ T1 ⇒ T3 → L1 ⊢ T1 ⇒ T4 →
      ∃∃T0. L1 ⊢ T3 ⇒ T0 & L1 ⊢ T4 ⇒ T0
   ) →
   L ⊢ V11 ⇒ V12 → L. 𝕓{I1} V11 ⊢ T11 ⇒ T12 →
   L ⊢ V11 ⇒ V22 → L. 𝕓{I1} V11 ⊢ T11 ⇒ T22 →
   ∃∃T0. L ⊢ 𝕓{I1} V12. T12 ⇒ T0 & L ⊢ 𝕓{I1} V22. T22 ⇒ T0.
#L #I1 #V11 #V12 #T11 #T12 #V22 #T22 #IH #HV1 #HT1 #HV2 #HT2
elim (IH … HV1 … HV2) [2: /2/ ] #V #HV1 #HV2
elim (IH … HT1 … HT2) [2: normalize // ] -HT1 HT2 T11 IH #T #HT1 #HT2
@ex2_1_intro [2: @pr_bind [3: @HV1 |1: skip |4: 

(* Confluence ***************************************************************)

lemma pr_conf_aux:
   ∀L,T. (
      ∀L1,T1. #[L1, T1] < #[L, T] → 
      ∀T3,T4. L1 ⊢ T1 ⇒ T3 → L1 ⊢ T1 ⇒ T4 →
      ∃∃T0. L1 ⊢ T3 ⇒ T0 & L1 ⊢ T4 ⇒ T0
         ) →
   ∀K1,U1,T1,K2,U2,T2. K1 ⊢ U1 ⇒ T1 → K2 ⊢ U2 ⇒ T2 →
   K1 = L → U1 = T → K2 = L → U2 = T →
   ∃∃T0. L ⊢ T1 ⇒ T0 & L ⊢ T2 ⇒ T0.
#L #T #IH #K1 #U1 #T1 #K2 #U2 #T2
* -K1 U1 T1
[ #K1 #k1 * -K2 U2 T2
(* case 1: sort, sort *)
  [ #K2 #k2 #H1 #H2 #H3 #H4 destruct -K1 K2 T k2 //
(* case 2: sort, lref (excluded) *)
  | #K2 #i2 #H1 #H2 #H3 #H4 destruct
(* case 3: sort, bind (excluded) *)
  | #K2 #I2 #V21 #V22 #T21 #T22 #_ #_ #H1 #H2 #H3 #H4 destruct
(* case 4: sort, flat (excluded) *)
  | #K2 #I2 #V21 #V22 #T21 #T22 #_ #_ #H1 #H2 #H3 #H4 destruct
(* case 5: sort, beta (excluded) *)
  | #K2 #V21 #V22 #W2 #T21 #T22 #_ #_ #H1 #H2 #H3 #H4 destruct
(* case 6: sort, delta (excluded) *)
  | #K2 #K22 #V21 #V22 #V2 #i2 #_ #_ #_ #H1 #H2 #H3 #H4 destruct
(* case 7: sort, theta (excluded) *)
  | #K2 #V2 #V21 #V22 #W21 #W22 #T21 #T22 #_ #_ #_ #_ #H1 #H2 #H3 #H4 destruct
(* case 8: sort, zeta (excluded) *)
  | #K2 #V2 #T21 #T22 #T20 #_ #_ #H1 #H2 #H3 #H4 destruct
(* case 9: sort, tau (excluded) *)
  | #K2 #V2 #T21 #T22 #_ #H1 #H2 #H3 #H4 destruct
  ]
| #K1 #i1 * -K2 U2 T2
(* case 10: lref, sort (excluded) broken *)
  [ #K2 #k2 #H1 #H2 #H3 #H4 destruct
(* case 11: lref, sort (excluded) *)
  | #K2 #i2 #H1 #H2 #H3 #H4 destruct -K1 K2 T i2 //
(* case 12: lref, bind (excluded) *)
  | #K2 #I2 #V21 #V22 #T21 #T22 #_ #_ #H1 #H2 #H3 #H4 destruct
(* case 13: lref, flat (excluded) *)
  | #K2 #I2 #V21 #V22 #T21 #T22 #_ #_ #H1 #H2 #H3 #H4 destruct
(* case 14: lref, beta (excluded) *)
  | #K2 #V21 #V22 #W2 #T21 #T22 #_ #_ #H1 #H2 #H3 #H4 destruct
(* case 15: lref, delta (excluded) *)
  | #K2 #K22 #V21 #V22 #V2 #i2 #_ #_ #_ #H1 #H2 #H3 #H4 destruct
(* case 16: lref, theta (excluded) *)
  | #K2 #V2 #V21 #V22 #W21 #W22 #T21 #T22 #_ #_ #_ #_ #H1 #H2 #H3 #H4 destruct
(* case 17: lref, zeta (excluded) *)
  | #K2 #V2 #T21 #T22 #T20 #_ #_ #H1 #H2 #H3 #H4 destruct
(* case 18: lref, tau (excluded) *)
  | #K2 #V2 #T21 #T22 #_ #H1 #H2 #H3 #H4 destruct
  ]
| #K1 #I1 #V11 #V12 #T11 #T12 #HV112 #HT112 * -K2 U2 T2
(* case 19: bind, sort (excluded) broken *)
  [ #K2 #k2 #H1 #H2 #H3 #H4 destruct
(* case 20: bind, lref (excluded) *)
  | #K2 #i2 #H1 #H2 #H3 #H4 destruct
(* case 21: bind, bind *)
  | #K2 #I2 #V21 #V22 #T21 #T22 #HV212 #HT212 #H1 #H2 #H3 #H4
    destruct -T K1 K2 I2 V21 T21;


theorem pr_conf: ∀L,T,T1,T2. L ⊢ T ⇒ T1 → L ⊢ T ⇒ T2 →
                 ∃∃T0. L ⊢ T1 ⇒ T0 & L ⊢ T2 ⇒ T0.
#L #T @(cw_wf_ind … L T) -L T /3 width=12/
qed.

lemma pr_conf_bind_bind:
   ∀L,I1,V11,V12,T11,T12,V22,T22. (
      ∀L1,T1. #L1 + #T1 < #L + (#V11 + #T11 + 1) →
      ∀T3,T4. L1 ⊢ T1 ⇒ T3 → L1 ⊢ T1 ⇒ T4 →
      ∃∃T0. L1 ⊢ T3 ⇒ T0 & L1 ⊢ T4 ⇒ T0
   ) →
   L ⊢ V11 ⇒ V12 → L. 𝕓{I1} V11 ⊢ T11 ⇒ T12 →
   L ⊢ V11 ⇒ V22 → L. 𝕓{I1} V11 ⊢ T11 ⇒ T22 →
   ∃∃T0. L ⊢ 𝕓{I1} V12. T12 ⇒ T0 & L ⊢ 𝕓{I1} V22. T22 ⇒ T0.
