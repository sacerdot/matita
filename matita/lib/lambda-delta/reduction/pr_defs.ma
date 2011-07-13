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

include "lambda-delta/substitution/drop_defs.ma".

(* SINGLE STEP PARALLEL REDUCTION ON TERMS **********************************)

inductive pr: lenv → term → term → Prop ≝
| pr_sort : ∀L,k. pr L (⋆k) (⋆k)
| pr_lref : ∀L,i. pr L (#i) (#i)
| pr_bind : ∀L,I,V1,V2,T1,T2. pr L V1 V2 → pr (L. 𝕓{I} V1) T1 T2 →
            pr L (𝕓{I} V1. T1) (𝕓{I} V2. T2)
| pr_flat : ∀L,I,V1,V2,T1,T2. pr L V1 V2 → pr L T1 T2 →
            pr L (𝕗{I} V1. T1) (𝕗{I} V2. T2)
| pr_beta : ∀L,V1,V2,W,T1,T2.
            pr L V1 V2 → pr (L. 𝕓{Abst} W) T1 T2 → (*𝕓*)
            pr L (𝕚{Appl} V1. 𝕚{Abst} W. T1) (𝕚{Abbr} V2. T2)
| pr_delta: ∀L,K,V1,V2,V,i.
            ↑[0,i] K. 𝕓{Abbr} V1 ≡ L → pr K V1 V2 → ↑[0,i+1] V2 ≡ V →
            pr L (#i) V
| pr_theta: ∀L,V,V1,V2,W1,W2,T1,T2.
            pr L V1 V2 → ↑[0,1] V2 ≡ V → pr L W1 W2 → pr (L. 𝕓{Abbr} W1) T1 T2 → (*𝕓*)
            pr L (𝕚{Appl} V1. 𝕚{Abbr} W1. T1) (𝕚{Abbr} W2. 𝕚{Appl} V. T2)
| pr_zeta : ∀L,V,T,T1,T2. ↑[0,1] T1 ≡ T → pr L T1 T2 →
            pr L (𝕚{Abbr} V. T) T2
| pr_tau  : ∀L,V,T1,T2. pr L T1 T2 → pr L (𝕚{Cast} V. T1) T2
.

interpretation
   "single step parallel reduction (term)"
   'PR L T1 T2 = (pr L T1 T2).

(* The basic properties *****************************************************)

lemma pr_refl: ∀T,L. L ⊢ T ⇒ T.
#T elim T -T //
#I elim I -I /2/
qed.
