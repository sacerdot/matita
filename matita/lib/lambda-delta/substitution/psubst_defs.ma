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

(* PARALLEL SUBSTITUTION ****************************************************)

inductive ps: lenv → term → nat → nat → term → Prop ≝
| ps_sort : ∀L,k,d,e. ps L (⋆k) d e (⋆k)
| ps_lref : ∀L,i,d,e. ps L (#i) d e (#i)
| ps_subst: ∀L,K,V,U1,U2,i,d,e.
            d ≤ i → i < d + e →
            ↓[0, i] L ≡ K. 𝕓{Abbr} V → ps K V 0 (d + e - i - 1) U1 →
            ↑[0, i + 1] U1 ≡ U2 → ps L (#i) d e U2
| ps_bind : ∀L,I,V1,V2,T1,T2,d,e.
            ps L V1 d e V2 → ps (L. 𝕓{I} V1) T1 (d + 1) e T2 →
            ps L (𝕓{I} V1. T1) d e (𝕓{I} V2. T2)
| ps_flat : ∀L,I,V1,V2,T1,T2,d,e.
            ps L V1 d e V2 → ps L T1 d e T2 →
            ps L (𝕗{I} V1. T1) d e (𝕗{I} V2. T2)
.

interpretation "parallel substritution" 'PSubst L T1 d e T2 = (ps L T1 d e T2).

(* Basic properties *********************************************************)

lemma subst_refl: ∀T,L,d,e. L ⊢ T [d, e] ≫ T.
#T elim T -T //
#I elim I -I /2/
qed.

(* Basic inversion lemmas ***************************************************)

lemma ps_inv_bind1_aux: ∀d,e,L,U1,U2. L ⊢ U1 [d, e] ≫ U2 →
                        ∀I,V1,T1. U1 = 𝕓{I} V1. T1 →
                        ∃∃V2,T2. L ⊢ V1 [d, e] ≫ V2 & 
                                 L. 𝕓{I} V1 ⊢ T1 [d + 1, e] ≫ T2 &
                                 U2 =  𝕓{I} V2. T2.
#d #e #L #U1 #U2 #H elim H -H d e L U1 U2
[ #L #k #d #e #I #V1 #T1 #H destruct
| #L #i #d #e #I #V1 #T1 #H destruct
| #L #K #V #U1 #U2 #i #d #e #_ #_ #_ #_ #_ #_ #I #V1 #T1 #H destruct
| #L #J #V1 #V2 #T1 #T2 #d #e #HV12 #HT12 #_ #_ #I #V #T #H destruct /2 width=5/
| #L #J #V1 #V2 #T1 #T2 #d #e #_ #_ #_ #_ #I #V #T #H destruct
]
qed.

lemma subst_inv_bind1: ∀d,e,L,I,V1,T1,U2. L ⊢ 𝕓{I} V1. T1 [d, e] ≫ U2 →
                       ∃∃V2,T2. L ⊢ V1 [d, e] ≫ V2 & 
                                L. 𝕓{I} V1 ⊢ T1 [d + 1, e] ≫ T2 &
                                U2 =  𝕓{I} V2. T2.
/2/ qed.

lemma subst_inv_flat1_aux: ∀d,e,L,U1,U2. L ⊢ U1 [d, e] ≫ U2 →
                           ∀I,V1,T1. U1 = 𝕗{I} V1. T1 →
                           ∃∃V2,T2. L ⊢ V1 [d, e] ≫ V2 & L ⊢ T1 [d, e] ≫ T2 &
                                    U2 =  𝕗{I} V2. T2.
#d #e #L #U1 #U2 #H elim H -H d e L U1 U2
[ #L #k #d #e #I #V1 #T1 #H destruct
| #L #i #d #e #I #V1 #T1 #H destruct
| #L #K #V #U1 #U2 #i #d #e #_ #_ #_ #_ #_ #_ #I #V1 #T1 #H destruct
| #L #J #V1 #V2 #T1 #T2 #d #e #_ #_ #_ #_ #I #V #T #H destruct
| #L #J #V1 #V2 #T1 #T2 #d #e #HV12 #HT12 #_ #_ #I #V #T #H destruct /2 width=5/
]
qed.

lemma subst_inv_flat1: ∀d,e,L,I,V1,T1,U2. L ⊢ 𝕗{I} V1. T1 [d, e] ≫ U2 →
                       ∃∃V2,T2. L ⊢ V1 [d, e] ≫ V2 & L ⊢ T1 [d, e] ≫ T2 &
                                U2 =  𝕗{I} V2. T2.
/2/ qed.
