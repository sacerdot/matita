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

(* Basic-1: includes: pr2_delta1 *)
definition cpr: lenv → relation term ≝
   λL,T1,T2. ∃∃T. T1 ⇒ T & L ⊢ T [0, |L|] ≫ T2.

interpretation
   "context-sensitive parallel reduction (term)"
   'PRed L T1 T2 = (cpr L T1 T2).

(* Basic properties *********************************************************)

(* Basic-1: was by definition: pr2_free *)
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

(* Basic-1: was only: pr2_gen_cbind *)
lemma cpr_bind_dx: ∀I,L,V1,V2,T1,T2. V1 ⇒ V2 → L. 𝕓{I} V2 ⊢ T1 ⇒ T2 →
                   L ⊢ 𝕓{I} V1. T1 ⇒ 𝕓{I} V2. T2.
#I #L #V1 #V2 #T1 #T2 #HV12 * #T #HT1 normalize #HT2
elim (tps_split_up … HT2 1 ? ?) -HT2 // #T0 <minus_n_O #HT0 normalize <minus_plus_m_m #HT02
lapply (tps_leq_repl_dx … HT0 (⋆. 𝕓{I} V2) ?) -HT0 /2/ #HT0
/3 width=5/
qed.

(* Note: new property *)
(* Basic-1: was only: pr2_thin_dx *) 
lemma cpr_flat: ∀I,L,V1,V2,T1,T2.
                L ⊢ V1 ⇒ V2 → L ⊢ T1 ⇒ T2 → L ⊢ 𝕗{I} V1. T1 ⇒ 𝕗{I} V2. T2.
#I #L #V1 #V2 #T1 #T2 * #V #HV1 #HV2 * /3 width=5/
qed.

lemma cpr_delta: ∀L,K,V,W,i.
                 ↓[0, i] L ≡ K. 𝕓{Abbr} V → ↑[0, i + 1] V ≡ W → L ⊢ #i ⇒ W.
/3/
qed.

lemma cpr_cast: ∀L,V,T1,T2.
                L ⊢ T1 ⇒ T2 → L ⊢ 𝕔{Cast} V. T1 ⇒ T2.
#L #V #T1 #T2 * /3/
qed.

(* Basic inversion lemmas ***************************************************)

(* Basic-1: was: pr2_gen_csort *)
lemma cpr_inv_atom: ∀T1,T2. ⋆ ⊢ T1 ⇒ T2 → T1 ⇒ T2.
#T1 #T2 * #T #HT normalize #HT2
<(tps_inv_refl_O2 … HT2) -HT2 //
qed.

(* Basic-1: was: pr2_gen_sort *)
lemma cpr_inv_sort1: ∀L,T2,k. L ⊢ ⋆k ⇒ T2 → T2 = ⋆k.
#L #T2 #k * #X #H
>(tpr_inv_atom1 … H) -H #H
>(tps_inv_sort1 … H) -H //
qed.

(* Basic-1: was: pr2_gen_lref *)
lemma cpr_inv_lref1: ∀L,T2,i. L ⊢ #i ⇒ T2 →
                     T2 = #i ∨
                     ∃∃K,T. ↓[0, i] L ≡ K. 𝕓{Abbr} T & ↑[0, i + 1] T ≡ T2 &
                            i < |L|.
#L #T2 #i * #X #H
>(tpr_inv_atom1 … H) -H #H
elim (tps_inv_lref1 … H) -H /2/
* #K #T #_ #Hi #HLK #HTT2 /3/
qed.
(*
(* Basic-1: was: pr2_gen_cast *)
lemma cpr_inv_cast1: ∀L,V1,T1,U2. L ⊢ 𝕔{Cast} V1. T1 ⇒ U2 → (
                        ∃∃V2,T2. L ⊢ V1 ⇒ V2 & L ⊢ T1 ⇒ T2 &
                                 U2 = 𝕔{Cast} V2. T2
                     ) ∨ L ⊢ T1 ⇒ U2.
#L #V1 #T1 #U2 * #X #H #HU2
elim (tpr_inv_cast1 … H) -H /3/
* #V #T #HV1 #HT1 #H whd  (* >H in HU2; *) destruct -X;
elim (tps_inv_flat1 … HU2) -HU2 #V2 #T2 #HV2 #HT2 #H
*)
(* Basic forward lemmas *****************************************************)

lemma cpr_shift_fwd: ∀L,T1,T2. L ⊢ T1 ⇒ T2 → L @ T1 ⇒ L @ T2.
#L elim L -L
[ /2/
| normalize /3/
].
qed.

(* Basic-1: removed theorems 5: 
            pr2_head_1 pr2_head_2 pr2_cflat pr2_gen_cflat clear_pr2_trans
*)

(*
pr2/fwd pr2_gen_appl
pr2/fwd pr2_gen_abbr
pr2/pr2 pr2_confluence__pr2_free_free
pr2/pr2 pr2_confluence__pr2_free_delta
pr2/pr2 pr2_confluence__pr2_delta_delta
pr2/pr2 pr2_confluence
pr2/props pr2_change
pr2/subst1 pr2_subst1
pr2/subst1 pr2_gen_cabbr
*)
