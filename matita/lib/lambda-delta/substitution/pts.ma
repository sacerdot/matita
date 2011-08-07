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

include "lambda-delta/substitution/drop.ma".

(* PARTIAL TELESCOPIC SUBSTITUTION ******************************************)

inductive pts: lenv → term → nat → nat → term → Prop ≝
| pts_sort : ∀L,k,d,e. pts L (⋆k) d e (⋆k)
| pts_lref : ∀L,i,d,e. pts L (#i) d e (#i)
| pts_subst: ∀L,K,V,U1,U2,i,d,e.
             d ≤ i → i < d + e →
             ↓[0, i] L ≡ K. 𝕓{Abbr} V → pts K V 0 (d + e - i - 1) U1 →
             ↑[0, i + 1] U1 ≡ U2 → pts L (#i) d e U2
| pts_bind : ∀L,I,V1,V2,T1,T2,d,e.
             pts L V1 d e V2 → pts (L. 𝕓{I} V1) T1 (d + 1) e T2 →
             pts L (𝕓{I} V1. T1) d e (𝕓{I} V2. T2)
| pts_flat : ∀L,I,V1,V2,T1,T2,d,e.
             pts L V1 d e V2 → pts L T1 d e T2 →
             pts L (𝕗{I} V1. T1) d e (𝕗{I} V2. T2)
.

interpretation "partial telescopic substritution"
   'PSubst L T1 d e T2 = (pts L T1 d e T2).

(* Basic properties *********************************************************)

lemma pts_leq_repl: ∀L1,T1,T2,d,e. L1 ⊢ T1 [d, e] ≫ T2 →
                    ∀L2. L1 [d, e] ≈ L2 → L2 ⊢ T1 [d, e] ≫ T2.
#L1 #T1 #T2 #d #e #H elim H -H L1 T1 T2 d e
[ //
| //
| #L1 #K1 #V #V1 #V2 #i #d #e #Hdi #Hide #HLK1 #_ #HV12 #IHV12 #L2 #HL12
  elim (drop_leq_drop1 … HL12 … HLK1 ? ?) -HL12 HLK1 // #K2 #HK12 #HLK2
  @pts_subst [4,5,6,8: // |1,2,3: skip | /2/ ] (**) (* /3 width=6/ is too slow *)
| /4/
| /3/
]
qed.

lemma pts_refl: ∀T,L,d,e. L ⊢ T [d, e] ≫ T.
#T elim T -T //
#I elim I -I /2/
qed.

lemma pts_weak: ∀L,T1,T2,d1,e1. L ⊢ T1 [d1, e1] ≫ T2 →
                ∀d2,e2. d2 ≤ d1 → d1 + e1 ≤ d2 + e2 →
                L ⊢ T1 [d2, e2] ≫ T2.
#L #T1 #T #d1 #e1 #H elim H -L T1 T d1 e1
[ //
| //
| #L #K #V #V1 #V2 #i #d1 #e1 #Hid1 #Hide1 #HLK #_ #HV12 #IHV12 #d2 #e2 #Hd12 #Hde12
  lapply (transitive_le … Hd12 … Hid1) -Hd12 Hid1 #Hid2
  lapply (lt_to_le_to_lt … Hide1 … Hde12) -Hide1 #Hide2
  @pts_subst [4,5,6,8: // |1,2,3: skip | @IHV12 /2/ ] (**) (* /4 width=6/ is too slow *)
| /4/
| /4/
]
qed.

(* Basic inversion lemmas ***************************************************)

lemma pts_inv_bind1_aux: ∀d,e,L,U1,U2. L ⊢ U1 [d, e] ≫ U2 →
                         ∀I,V1,T1. U1 = 𝕓{I} V1. T1 →
                         ∃∃V2,T2. L ⊢ V1 [d, e] ≫ V2 & 
                                  L. 𝕓{I} V1 ⊢ T1 [d + 1, e] ≫ T2 &
                                  U2 =  𝕓{I} V2. T2.
#d #e #L #U1 #U2 * -d e L U1 U2
[ #L #k #d #e #I #V1 #T1 #H destruct
| #L #i #d #e #I #V1 #T1 #H destruct
| #L #K #V #U1 #U2 #i #d #e #_ #_ #_ #_ #_ #I #V1 #T1 #H destruct
| #L #J #V1 #V2 #T1 #T2 #d #e #HV12 #HT12 #I #V #T #H destruct /2 width=5/
| #L #J #V1 #V2 #T1 #T2 #d #e #_ #_ #I #V #T #H destruct
]
qed.

lemma pts_inv_bind1: ∀d,e,L,I,V1,T1,U2. L ⊢ 𝕓{I} V1. T1 [d, e] ≫ U2 →
                     ∃∃V2,T2. L ⊢ V1 [d, e] ≫ V2 & 
                              L. 𝕓{I} V1 ⊢ T1 [d + 1, e] ≫ T2 &
                              U2 =  𝕓{I} V2. T2.
/2/ qed.

lemma pts_inv_flat1_aux: ∀d,e,L,U1,U2. L ⊢ U1 [d, e] ≫ U2 →
                         ∀I,V1,T1. U1 = 𝕗{I} V1. T1 →
                         ∃∃V2,T2. L ⊢ V1 [d, e] ≫ V2 & L ⊢ T1 [d, e] ≫ T2 &
                                  U2 =  𝕗{I} V2. T2.
#d #e #L #U1 #U2 * -d e L U1 U2
[ #L #k #d #e #I #V1 #T1 #H destruct
| #L #i #d #e #I #V1 #T1 #H destruct
| #L #K #V #U1 #U2 #i #d #e #_ #_ #_ #_ #_ #I #V1 #T1 #H destruct
| #L #J #V1 #V2 #T1 #T2 #d #e #_ #_ #I #V #T #H destruct
| #L #J #V1 #V2 #T1 #T2 #d #e #HV12 #HT12 #I #V #T #H destruct /2 width=5/
]
qed.

lemma pts_inv_flat1: ∀d,e,L,I,V1,T1,U2. L ⊢ 𝕗{I} V1. T1 [d, e] ≫ U2 →
                     ∃∃V2,T2. L ⊢ V1 [d, e] ≫ V2 & L ⊢ T1 [d, e] ≫ T2 &
                              U2 =  𝕗{I} V2. T2.
/2/ qed.
