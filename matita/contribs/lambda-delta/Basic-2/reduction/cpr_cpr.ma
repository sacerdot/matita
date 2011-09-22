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

include "Basic-2/reduction/tpr_tpr.ma".
include "Basic-2/reduction/cpr.ma".

(* CONTEXT-SENSITIVE PARALLEL REDUCTION ON TERMS ****************************)

(* Advanced properties ******************************************************)

lemma cpr_bind_sn: ∀I,L,V1,V2,T1,T2. L ⊢ V1 ⇒ V2 → T1 ⇒ T2 →
                   L ⊢ 𝕓{I} V1. T1 ⇒ 𝕓{I} V2. T2.
#I #L #V1 #V2 #T1 #T2 * #V #HV1 #HV2 #HT12 
@ex2_1_intro [2: @(tpr_delta … HV1 HT12) | skip ] /2/ (* /3 width=5/ is too slow *)
qed.

(* Basic-1: was only: pr2_gen_cbind *)
lemma cpr_bind_dx: ∀I,L,V1,V2,T1,T2. V1 ⇒ V2 → L. 𝕓{I} V2 ⊢ T1 ⇒ T2 →
                   L ⊢ 𝕓{I} V1. T1 ⇒ 𝕓{I} V2. T2.
#I #L #V1 #V2 #T1 #T2 #HV12 * #T #HT1 normalize #HT2
elim (tpss_split_up … HT2 1 ? ?) -HT2 // #T0 <minus_n_O #HT0 normalize <minus_plus_m_m #HT02
lapply (tpss_leq_repl_dx … HT0 (⋆. 𝕓{I} V2) ?) -HT0 /2/ #HT0
lapply (tpss_tps … HT0) -HT0 #HT0
@ex2_1_intro [2: @(tpr_delta … HV12 HT1 HT0) | skip | /2/ ] (**) (* /3 width=5/ is too slow *)
qed.

(* Advanced forward lemmas **************************************************)

lemma cpr_shift_fwd: ∀L,T1,T2. L ⊢ T1 ⇒ T2 → L @ T1 ⇒ L @ T2.
#L elim L -L
[ /2/
| normalize /3/
].
qed.

(* Main properties **********************************************************)

(* Basic-1: was: pr2_confluence *)
theorem cpr_conf: ∀L,U0,T1,T2. L ⊢ U0 ⇒ T1 → L ⊢ U0 ⇒ T2 →
                  ∃∃T. L ⊢ T1 ⇒ T & L ⊢ T2 ⇒ T.
#L #U0 #T1 #T2 * #U1 #HU01 #HUT1 * #U2 #HU02 #HUT2
elim (tpr_conf … HU01 HU02) -U0 #U #HU1 #HU2 
elim (tpr_tpss_ltpr ? L … HU1 … HUT1) -U1 // #U1 #HTU1 #HU1
elim (tpr_tpss_ltpr ? L … HU2 … HUT2) -U2 // #U2 #HTU2 #HU2
elim (tpss_conf_eq … HU1 … HU2) -U /3 width=5/
qed.

