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

include "lambda-delta/syntax/lenv.ma".
include "lambda-delta/substitution/lift_defs.ma".

(* TELESCOPIC SUBSTITUTION **************************************************)

inductive subst: lenv → term → nat → nat → term → Prop ≝
| subst_sort   : ∀L,k,d,e. subst L (⋆k) d e (⋆k)
| subst_lref_lt: ∀L,i,d,e. i < d → subst L (#i) d e (#i)
| subst_lref_O : ∀L,V1,V2,e. subst L V1 0 e V2 →
                 subst (L. 𝕓{Abbr} V1) #0 0 (e + 1) V2
| subst_lref_S : ∀L,I,V,i,T1,T2,d,e.
                 d ≤ i → i < d + e → subst L #i d e T1 → ↑[d,1] T1 ≡ T2 →
                 subst (L. 𝕓{I} V) #(i + 1) (d + 1) e T2
| subst_lref_ge: ∀L,i,d,e. d + e ≤ i → subst L (#i) d e (#(i - e))
| subst_bind   : ∀L,I,V1,V2,T1,T2,d,e.
                 subst L V1 d e V2 → subst (L. 𝕓{I} V1) T1 (d + 1) e T2 →
                 subst L (𝕓{I} V1. T1) d e (𝕓{I} V2. T2)
| subst_flat   : ∀L,I,V1,V2,T1,T2,d,e.
                 subst L V1 d e V2 → subst L T1 d e T2 →
                 subst L (𝕗{I} V1. T1) d e (𝕗{I} V2. T2)
.

interpretation "telescopic substritution" 'RSubst L T1 d e T2 = (subst L T1 d e T2).

(* The basic properties *****************************************************)

lemma subst_lift_inv: ∀d,e,T1,T2. ↑[d,e] T1 ≡ T2 → ∀L. L ⊢ ↓[d,e] T2 ≡ T1.
#d #e #T1 #T2 #H elim H -H d e T1 T2 /2/
#i #d #e #Hdi #L >(minus_plus_m_m i e) in ⊢ (? ? ? ? ? %) /3/ (**) (* use \ldots *)
qed.
