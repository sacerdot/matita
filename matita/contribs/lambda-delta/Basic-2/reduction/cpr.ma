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

(* NOTE: new property *)
lemma cpr_flat: ∀I,L,V1,V2,T1,T2.
                L ⊢ V1 ⇒ V2 → L ⊢ T1 ⇒ T2 → L ⊢ 𝕗{I} V1. T1 ⇒ 𝕗{I} V2. T2.
#I #L #V1 #V2 #T1 #T2 * #V #HV1 #HV2 * /3 width=5/
qed.

lemma cpr_delta: ∀L,K,V1,V2,V,i.
                 ↓[0, i] L ≡ K. 𝕓{Abbr} V1 → K ⊢ V1 [0, |L| - i - 1] ≫ V2 →
                 ↑[0, i + 1] V2 ≡ V → L ⊢ #i ⇒ V.
#L #K #V1 #V2 #V #i #HLK #HV12 #HV2
@ex2_1_intro [2: // | skip ] /3 width=8/ (**) (* /4/ is too slow *)
qed.

lemma cpr_cast: ∀L,V,T1,T2.
                L ⊢ T1 ⇒ T2 → L ⊢ 𝕗{Cast} V. T1 ⇒ T2.
#L #V #T1 #T2 * /3/
qed.

(* Basic inversion lemmas ***************************************************)
