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

include "Basic-2/substitution/drop.ma".

(* PARTIAL SUBSTITUTION ON TERMS ********************************************)

inductive tps: lenv → term → nat → nat → term → Prop ≝
| tps_sort : ∀L,k,d,e. tps L (⋆k) d e (⋆k)
| tps_lref : ∀L,i,d,e. tps L (#i) d e (#i)
| tps_subst: ∀L,K,V,U1,U2,i,d,e.
             d ≤ i → i < d + e →
             ↓[0, i] L ≡ K. 𝕓{Abbr} V → tps K V 0 (d + e - i - 1) U1 →
             ↑[0, i + 1] U1 ≡ U2 → tps L (#i) d e U2
| tps_bind : ∀L,I,V1,V2,T1,T2,d,e.
             tps L V1 d e V2 → tps (L. 𝕓{I} V1) T1 (d + 1) e T2 →
             tps L (𝕓{I} V1. T1) d e (𝕓{I} V2. T2)
| tps_flat : ∀L,I,V1,V2,T1,T2,d,e.
             tps L V1 d e V2 → tps L T1 d e T2 →
             tps L (𝕗{I} V1. T1) d e (𝕗{I} V2. T2)
.

interpretation "partial telescopic substritution"
   'PSubst L T1 d e T2 = (tps L T1 d e T2).

(* Basic properties *********************************************************)

lemma tps_leq_repl: ∀L1,T1,T2,d,e. L1 ⊢ T1 [d, e] ≫ T2 →
                    ∀L2. L1 [d, e] ≈ L2 → L2 ⊢ T1 [d, e] ≫ T2.
#L1 #T1 #T2 #d #e #H elim H -H L1 T1 T2 d e
[ //
| //
| #L1 #K1 #V #V1 #V2 #i #d #e #Hdi #Hide #HLK1 #_ #HV12 #IHV12 #L2 #HL12
  elim (drop_leq_drop1 … HL12 … HLK1 ? ?) -HL12 HLK1 // #K2 #HK12 #HLK2
  @tps_subst [4,5,6,8: // |1,2,3: skip | /2/ ] (**) (* /3 width=6/ is too slow *)
| /4/
| /3/
]
qed.

lemma tps_refl: ∀T,L,d,e. L ⊢ T [d, e] ≫ T.
#T elim T -T //
#I elim I -I /2/
qed.

lemma tps_weak: ∀L,T1,T2,d1,e1. L ⊢ T1 [d1, e1] ≫ T2 →
                ∀d2,e2. d2 ≤ d1 → d1 + e1 ≤ d2 + e2 →
                L ⊢ T1 [d2, e2] ≫ T2.
#L #T1 #T #d1 #e1 #H elim H -L T1 T d1 e1
[ //
| //
| #L #K #V #V1 #V2 #i #d1 #e1 #Hid1 #Hide1 #HLK #_ #HV12 #IHV12 #d2 #e2 #Hd12 #Hde12
  lapply (transitive_le … Hd12 … Hid1) -Hd12 Hid1 #Hid2
  lapply (lt_to_le_to_lt … Hide1 … Hde12) -Hide1 #Hide2
  @tps_subst [4,5,6,8: // |1,2,3: skip | @IHV12 /2/ ] (**) (* /4 width=6/ is too slow *)
| /4/
| /4/
]
qed.

lemma tps_weak_top: ∀L,T1,T2,d,e.
                    L ⊢ T1 [d, e] ≫ T2 → L ⊢ T1 [d, |L| - d] ≫ T2.
#L #T1 #T #d #e #H elim H -L T1 T d e
[ //
| //
| #L #K #V #V1 #V2 #i #d #e #Hdi #_ #HLK #_ #HV12 #IHV12
  lapply (drop_fwd_drop2_length … HLK) #Hi
  lapply (le_to_lt_to_lt … Hdi Hi) #Hd
  lapply (plus_minus_m_m_comm (|L|) d ?) [ /2/ ] -Hd #Hd
  lapply (drop_fwd_O1_length … HLK) normalize #HKL
  lapply (tps_weak … IHV12 0 (|L| - i - 1) ? ?) -IHV12 // -HKL /2 width=6/
| normalize /2/
| /2/
]
qed.

lemma tps_weak_all: ∀L,T1,T2,d,e.
                    L ⊢ T1 [d, e] ≫ T2 → L ⊢ T1 [0, |L|] ≫ T2.
#L #T1 #T #d #e #HT12
lapply (tps_weak … HT12 0 (d + e) ? ?) -HT12 // #HT12
lapply (tps_weak_top … HT12) //
qed.     

(* Basic inversion lemmas ***************************************************)

lemma tps_inv_lref1_aux: ∀L,T1,T2,d,e. L ⊢ T1 [d, e] ≫ T2 → ∀i. T1 = #i →
                         T2 = #i ∨ 
                         ∃∃K,V1,V2,i. d ≤ i & i < d + e &
                                      ↓[O, i] L ≡ K. 𝕓{Abbr} V1 &
                                      K ⊢ V1 [O, d + e - i - 1] ≫ V2 &
                                      ↑[O, i + 1] V2 ≡ T2.
#L #T1 #T2 #d #e * -L T1 T2 d e
[ #L #k #d #e #i #H destruct
| /2/
| #L #K #V1 #V2 #T2 #i #d #e #Hdi #Hide #HLK #HV12 #HVT2 #j #H destruct -i /3 width=9/
| #L #I #V1 #V2 #T1 #T2 #d #e #_ #_ #i #H destruct
| #L #I #V1 #V2 #T1 #T2 #d #e #_ #_ #i #H destruct
]
qed.

lemma tps_inv_lref1: ∀L,T2,i,d,e. L ⊢ #i [d, e] ≫ T2 →
                     T2 = #i ∨ 
                     ∃∃K,V1,V2,i. d ≤ i & i < d + e &
                                  ↓[O, i] L ≡ K. 𝕓{Abbr} V1 &
                                  K ⊢ V1 [O, d + e - i - 1] ≫ V2 &
                                  ↑[O, i + 1] V2 ≡ T2.
/2/ qed.

lemma tps_inv_bind1_aux: ∀d,e,L,U1,U2. L ⊢ U1 [d, e] ≫ U2 →
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

lemma tps_inv_bind1: ∀d,e,L,I,V1,T1,U2. L ⊢ 𝕓{I} V1. T1 [d, e] ≫ U2 →
                     ∃∃V2,T2. L ⊢ V1 [d, e] ≫ V2 & 
                              L. 𝕓{I} V1 ⊢ T1 [d + 1, e] ≫ T2 &
                              U2 =  𝕓{I} V2. T2.
/2/ qed.

lemma tps_inv_flat1_aux: ∀d,e,L,U1,U2. L ⊢ U1 [d, e] ≫ U2 →
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

lemma tps_inv_flat1: ∀d,e,L,I,V1,T1,U2. L ⊢ 𝕗{I} V1. T1 [d, e] ≫ U2 →
                     ∃∃V2,T2. L ⊢ V1 [d, e] ≫ V2 & L ⊢ T1 [d, e] ≫ T2 &
                              U2 =  𝕗{I} V2. T2.
/2/ qed.
