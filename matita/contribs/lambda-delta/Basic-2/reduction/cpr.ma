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

include "Basic-2/grammar/cl_shift.ma".
include "Basic-2/reduction/tpr.ma".

(* CONTEXT-SENSITIVE PARALLEL REDUCTION ON TERMS ****************************)

definition cpr: lenv → term → term → Prop ≝
   λL,T1,T2. ∃∃T. T1 ⇒ T & L ⊢ T [0, |L|] ≫ T2.

interpretation
   "context-sensitive parallel reduction (term)"
   'PRed L T1 T2 = (cpr L T1 T2).

(* Basic properties *********************************************************)

lemma cpr_pr: ∀T1,T2. T1 ⇒ T2 → ∀L. L ⊢ T1 ⇒ T2.
/2/ qed.

lemma cpr_tps: ∀L,T1,T2,d,e. L ⊢ T1 [d, e] ≫ T2 → L ⊢ T1 ⇒ T2.
/3 width=5/ qed.

lemma cpr_refl: ∀L,T. L ⊢ T ⇒ T.
/2/ qed.

lemma cpr_bind_sn: ∀I,L,V1,V2,T1,T2. L ⊢ V1 ⇒ V2 → T1 ⇒ T2 →
                   L ⊢ 𝕓{I} V1. T1 ⇒ 𝕓{I} V2. T2.
#I #L #V1 #V2 #T1 #T2 * /3 width=5/
qed.

lemma cpr_bind_dx: ∀I,L,V1,V2,T1,T2. V1 ⇒ V2 → L. 𝕓{I} V2 ⊢ T1 ⇒ T2 →
                   L ⊢ 𝕓{I} V1. T1 ⇒ 𝕓{I} V2. T2.
#I #L #V1 #V2 #T1 #T2 #HV12 * #T #HT1 normalize #HT2
elim (tps_split_up … HT2 1 ? ?) -HT2 // #T0 <minus_n_O #HT0 normalize <minus_plus_m_m #HT02
lapply (tps_leq_repl … HT0 (⋆. 𝕓{I} V2) ?) -HT0 /2/ #HT0 /3 width=5/
qed.

(* NOTE: new property *)
lemma cpr_flat: ∀I,L,V1,V2,T1,T2.
                L ⊢ V1 ⇒ V2 → L ⊢ T1 ⇒ T2 → L ⊢ 𝕗{I} V1. T1 ⇒ 𝕗{I} V2. T2.
#I #L #V1 #V2 #T1 #T2 * #V #HV1 #HV2 * /3 width=5/
qed.

lemma cpr_delta: ∀L,K,V,W,i.
                 ↓[0, i] L ≡ K. 𝕓{Abbr} V → ↑[0, i + 1] V ≡ W → L ⊢ #i ⇒ W.
/3/
qed.

lemma cpr_cast: ∀L,V,T1,T2.
                L ⊢ T1 ⇒ T2 → L ⊢ 𝕗{Cast} V. T1 ⇒ T2.
#L #V #T1 #T2 * /3/
qed.

(* Basic inversion lemmas ***************************************************)

lemma cpr_inv_lsort: ∀T1,T2. ⋆ ⊢ T1 ⇒ T2 → T1 ⇒ T2.
#T1 #T2 * #T #HT normalize #HT2
<(tps_inv_refl0 … HT2) -HT2 //
qed.

(* Basic forward lemmas *****************************************************)

lemma cpr_shift_fwd: ∀L,T1,T2. L ⊢ T1 ⇒ T2 → L @ T1 ⇒ L @ T2.
#L elim L -L
[ /2/
| normalize /3/
].
qed.
