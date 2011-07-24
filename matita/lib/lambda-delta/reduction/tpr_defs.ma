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

include "lambda-delta/substitution/subst_defs.ma".

(* CONTEXT-FREE PARALLEL REDUCTION ON TERMS *********************************)

inductive tpr: term → term → Prop ≝
| tpr_sort : ∀k. tpr (⋆k) (⋆k)
| tpr_lref : ∀i. tpr (#i) (#i)
| tpr_bind : ∀I,V1,V2,T1,T2. tpr V1 V2 → tpr T1 T2 →
             tpr (𝕓{I} V1. T1) (𝕓{I} V2. T2)
| tpr_flat : ∀I,V1,V2,T1,T2. tpr V1 V2 → tpr T1 T2 →
             tpr (𝕗{I} V1. T1) (𝕗{I} V2. T2)
| tpr_beta : ∀V1,V2,W,T1,T2.
             tpr V1 V2 → tpr T1 T2 →
             tpr (𝕚{Appl} V1. 𝕚{Abst} W. T1) (𝕚{Abbr} V2. T2)
| tpr_delta: ∀V1,V2,T1,T2,T0,T.
             tpr V1 V2 → tpr T1 T2 →
             ⋆.  𝕓{Abbr} V2 ⊢ ↓[0, 1] T2 ≡ T0 → ↑[0, 1] T0 ≡ T →
             tpr (𝕚{Abbr} V1. T1) (𝕚{Abbr} V2. T)
| tpr_theta: ∀V,V1,V2,W1,W2,T1,T2.
             tpr V1 V2 → ↑[0,1] V2 ≡ V → tpr W1 W2 → tpr T1 T2 →
             tpr (𝕚{Appl} V1. 𝕚{Abbr} W1. T1) (𝕚{Abbr} W2. 𝕚{Appl} V. T2)
| tpr_zeta : ∀V,T,T1,T2. ↑[0,1] T1 ≡ T → tpr T1 T2 →
             tpr (𝕚{Abbr} V. T) T2
| tpr_tau  : ∀V,T1,T2. tpr T1 T2 → tpr (𝕚{Cast} V. T1) T2
.

interpretation
   "context-free parallel reduction (term)"
   'PR T1 T2 = (tpr T1 T2).

(* Basic properties *********************************************************)

lemma tpr_refl: ∀T. T ⇒ T.
#T elim T -T //
#I elim I -I /2/
qed.

(* The basic inversion lemmas ***********************************************)

lemma tpr_inv_lref2_aux: ∀T1,T2. T1 ⇒ T2 → ∀i. T2 = #i →
                         ∨∨           T1 = #i
                          | ∃∃V,T,T0. ↑[O,1] T0 ≡ T & T0 ⇒ #i &
                                      T1 = 𝕓{Abbr} V. T
                          | ∃∃V,T.    T ⇒ #i & T1 = 𝕗{Cast} V. T.
#T1 #T2 #H elim H -H T1 T2
[ #k #i #H destruct
| #j #i /2/
| #I #V1 #V2 #T1 #T2 #_ #_ #_ #_ #i #H destruct
| #I #V1 #V2 #T1 #T2 #_ #_ #_ #_ #i #H destruct
| #V1 #V2 #W #T1 #T2 #_ #_ #_ #_ #i #H destruct
| #V1 #V2 #T1 #T2 #T0 #T #_ #_ #_ #_ #_ #_ #i #H destruct
| #V #V1 #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #_ #_ #_ #_ #i #H destruct
| #V #T #T1 #T2 #HT1 #HT12 #_ #i #H destruct /3 width=6/
| #V #T1 #T2 #HT12 #_ #i #H destruct /3/
]
qed.

lemma tpr_inv_lref2: ∀T1,i. T1 ⇒ #i →
                     ∨∨           T1 = #i
                      | ∃∃V,T,T0. ↑[O,1] T0 ≡ T & T0 ⇒ #i &
                                  T1 = 𝕓{Abbr} V. T
                      | ∃∃V,T.    T ⇒ #i & T1 = 𝕗{Cast} V. T.
/2/ qed.
