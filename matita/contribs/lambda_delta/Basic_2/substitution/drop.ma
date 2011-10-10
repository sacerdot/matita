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

include "Basic-2/grammar/lenv_weight.ma".
include "Basic-2/grammar/leq.ma".
include "Basic-2/substitution/lift.ma".

(* DROPPING *****************************************************************)

(* Basic-1: includes: drop_skip_bind *)
inductive drop: nat → nat → relation lenv ≝
| drop_atom: ∀d,e. drop d e (⋆) (⋆)
| drop_pair: ∀L,I,V. drop 0 0 (L. 𝕓{I} V) (L. 𝕓{I} V)
| drop_drop: ∀L1,L2,I,V,e. drop 0 e L1 L2 → drop 0 (e + 1) (L1. 𝕓{I} V) L2
| drop_skip: ∀L1,L2,I,V1,V2,d,e.
             drop d e L1 L2 → ↑[d,e] V2 ≡ V1 →
             drop (d + 1) e (L1. 𝕓{I} V1) (L2. 𝕓{I} V2)
.

interpretation "dropping" 'RDrop d e L1 L2 = (drop d e L1 L2).

(* Basic inversion lemmas ***************************************************)

fact drop_inv_refl_aux: ∀d,e,L1,L2. ↓[d, e] L1 ≡ L2 → d = 0 → e = 0 → L1 = L2.
#d #e #L1 #L2 * -d e L1 L2
[ //
| //
| #L1 #L2 #I #V #e #_ #_ #H
  elim (plus_S_eq_O_false … H)
| #L1 #L2 #I #V1 #V2 #d #e #_ #_ #H
  elim (plus_S_eq_O_false … H)
]
qed.

(* Basic-1: was: drop_gen_refl *)
lemma drop_inv_refl: ∀L1,L2. ↓[0, 0] L1 ≡ L2 → L1 = L2.
/2 width=5/ qed.

fact drop_inv_atom1_aux: ∀d,e,L1,L2. ↓[d, e] L1 ≡ L2 → L1 = ⋆ →
                         L2 = ⋆.
#d #e #L1 #L2 * -d e L1 L2
[ //
| #L #I #V #H destruct
| #L1 #L2 #I #V #e #_ #H destruct
| #L1 #L2 #I #V1 #V2 #d #e #_ #_ #H destruct
]
qed.

(* Basic-1: was: drop_gen_sort *)
lemma drop_inv_atom1: ∀d,e,L2. ↓[d, e] ⋆ ≡ L2 → L2 = ⋆.
/2 width=5/ qed.

fact drop_inv_O1_aux: ∀d,e,L1,L2. ↓[d, e] L1 ≡ L2 → d = 0 →
                      ∀K,I,V. L1 = K. 𝕓{I} V → 
                      (e = 0 ∧ L2 = K. 𝕓{I} V) ∨
                      (0 < e ∧ ↓[d, e - 1] K ≡ L2).
#d #e #L1 #L2 * -d e L1 L2
[ #d #e #_ #K #I #V #H destruct
| #L #I #V #_ #K #J #W #HX destruct -L I V /3/
| #L1 #L2 #I #V #e #HL12 #_ #K #J #W #H destruct -L1 I V /3/
| #L1 #L2 #I #V1 #V2 #d #e #_ #_ #H elim (plus_S_eq_O_false … H)
]
qed.

lemma drop_inv_O1: ∀e,K,I,V,L2. ↓[0, e] K. 𝕓{I} V ≡ L2 →
                   (e = 0 ∧ L2 = K. 𝕓{I} V) ∨
                   (0 < e ∧ ↓[0, e - 1] K ≡ L2).
/2/ qed.

(* Basic-1: was: drop_gen_drop *)
lemma drop_inv_drop1: ∀e,K,I,V,L2.
                      ↓[0, e] K. 𝕓{I} V ≡ L2 → 0 < e → ↓[0, e - 1] K ≡ L2.
#e #K #I #V #L2 #H #He
elim (drop_inv_O1 … H) -H * // #H destruct -e;
elim (lt_refl_false … He)
qed.

fact drop_inv_skip1_aux: ∀d,e,L1,L2. ↓[d, e] L1 ≡ L2 → 0 < d →
                         ∀I,K1,V1. L1 = K1. 𝕓{I} V1 →
                         ∃∃K2,V2. ↓[d - 1, e] K1 ≡ K2 &
                                  ↑[d - 1, e] V2 ≡ V1 & 
                                  L2 = K2. 𝕓{I} V2.
#d #e #L1 #L2 * -d e L1 L2
[ #d #e #_ #I #K #V #H destruct
| #L #I #V #H elim (lt_refl_false … H)
| #L1 #L2 #I #V #e #_ #H elim (lt_refl_false … H)
| #X #L2 #Y #Z #V2 #d #e #HL12 #HV12 #_ #I #L1 #V1 #H destruct -X Y Z
  /2 width=5/
]
qed.

(* Basic-1: was: drop_gen_skip_l *)
lemma drop_inv_skip1: ∀d,e,I,K1,V1,L2. ↓[d, e] K1. 𝕓{I} V1 ≡ L2 → 0 < d →
                      ∃∃K2,V2. ↓[d - 1, e] K1 ≡ K2 &
                               ↑[d - 1, e] V2 ≡ V1 & 
                               L2 = K2. 𝕓{I} V2.
/2/ qed.

fact drop_inv_skip2_aux: ∀d,e,L1,L2. ↓[d, e] L1 ≡ L2 → 0 < d →
                         ∀I,K2,V2. L2 = K2. 𝕓{I} V2 →
                         ∃∃K1,V1. ↓[d - 1, e] K1 ≡ K2 &
                                  ↑[d - 1, e] V2 ≡ V1 & 
                                  L1 = K1. 𝕓{I} V1.
#d #e #L1 #L2 * -d e L1 L2
[ #d #e #_ #I #K #V #H destruct
| #L #I #V #H elim (lt_refl_false … H)
| #L1 #L2 #I #V #e #_ #H elim (lt_refl_false … H)
| #L1 #X #Y #V1 #Z #d #e #HL12 #HV12 #_ #I #L2 #V2 #H destruct -X Y Z
  /2 width=5/
]
qed.

(* Basic-1: was: drop_gen_skip_r *)
lemma drop_inv_skip2: ∀d,e,I,L1,K2,V2. ↓[d, e] L1 ≡ K2. 𝕓{I} V2 → 0 < d →
                      ∃∃K1,V1. ↓[d - 1, e] K1 ≡ K2 & ↑[d - 1, e] V2 ≡ V1 &
                               L1 = K1. 𝕓{I} V1.
/2/ qed.

(* Basic properties *********************************************************)

(* Basic-1: was by definition: drop_refl *)
lemma drop_refl: ∀L. ↓[0, 0] L ≡ L.
#L elim L -L //
qed.

lemma drop_drop_lt: ∀L1,L2,I,V,e.
                    ↓[0, e - 1] L1 ≡ L2 → 0 < e → ↓[0, e] L1. 𝕓{I} V ≡ L2.
#L1 #L2 #I #V #e #HL12 #He >(plus_minus_m_m e 1) /2/
qed.

lemma drop_leq_drop1: ∀L1,L2,d,e. L1 [d, e] ≈ L2 →
                      ∀I,K1,V,i. ↓[0, i] L1 ≡ K1. 𝕓{I} V →
                      d ≤ i → i < d + e →
                      ∃∃K2. K1 [0, d + e - i - 1] ≈ K2 &
                            ↓[0, i] L2 ≡ K2. 𝕓{I} V.
#L1 #L2 #d #e #H elim H -H L1 L2 d e
[ #d #e #I #K1 #V #i #H
  lapply (drop_inv_atom1 … H) -H #H destruct
| #L1 #L2 #I #K1 #V #i #_ #_ #H
  elim (lt_zero_false … H)
| #L1 #L2 #I #V #e #HL12 #IHL12 #J #K1 #W #i #H #_ #Hie
  elim (drop_inv_O1 … H) -H * #Hi #HLK1
  [ -IHL12 Hie; destruct -i K1 J W;
    <minus_n_O <minus_plus_m_m /2/
  | -HL12;
    elim (IHL12 … HLK1 ? ?) -IHL12 HLK1 // [2: /2/ ] -Hie >arith_g1 // /3/
  ]
| #L1 #L2 #I1 #I2 #V1 #V2 #d #e #_ #IHL12 #I #K1 #V #i #H #Hdi >plus_plus_comm_23 #Hide
  lapply (plus_S_le_to_pos … Hdi) #Hi
  lapply (drop_inv_drop1 … H ?) -H // #HLK1
  elim (IHL12 … HLK1 ? ?) -IHL12 HLK1 [2: /2/ |3: /2/ ] -Hdi Hide >arith_g1 // /3/
]
qed.

(* Basic forvard lemmas *****************************************************)

(* Basic-1: was: drop_S *)
lemma drop_fwd_drop2: ∀L1,I2,K2,V2,e. ↓[O, e] L1 ≡ K2. 𝕓{I2} V2 →
                      ↓[O, e + 1] L1 ≡ K2.
#L1 elim L1 -L1
[ #I2 #K2 #V2 #e #H lapply (drop_inv_atom1 … H) -H #H destruct
| #K1 #I1 #V1 #IHL1 #I2 #K2 #V2 #e #H
  elim (drop_inv_O1 … H) -H * #He #H
  [ -IHL1; destruct -e K2 I2 V2 /2/
  | @drop_drop >(plus_minus_m_m e 1) /2/
  ]
]
qed.

lemma drop_fwd_lw: ∀L1,L2,d,e. ↓[d, e] L1 ≡ L2 → #[L2] ≤ #[L1].
#L1 #L2 #d #e #H elim H -H L1 L2 d e // normalize
[ /2/
| #L1 #L2 #I #V1 #V2 #d #e #_ #HV21 #IHL12
  >(tw_lift … HV21) -HV21 /2/
]
qed. 

lemma drop_fwd_drop2_length: ∀L1,I2,K2,V2,e.
                             ↓[0, e] L1 ≡ K2. 𝕓{I2} V2 → e < |L1|.
#L1 elim L1 -L1
[ #I2 #K2 #V2 #e #H lapply (drop_inv_atom1 … H) -H #H destruct
| #K1 #I1 #V1 #IHL1 #I2 #K2 #V2 #e #H
  elim (drop_inv_O1 … H) -H * #He #H
  [ -IHL1; destruct -e K2 I2 V2 //
  | lapply (IHL1 … H) -IHL1 H #HeK1 whd in ⊢ (? ? %) /2/
  ]
]
qed.

lemma drop_fwd_O1_length: ∀L1,L2,e. ↓[0, e] L1 ≡ L2 → |L2| = |L1| - e.
#L1 elim L1 -L1
[ #L2 #e #H >(drop_inv_atom1 … H) -H //
| #K1 #I1 #V1 #IHL1 #L2 #e #H
  elim (drop_inv_O1 … H) -H * #He #H
  [ -IHL1; destruct -e L2 //
  | lapply (IHL1 … H) -IHL1 H #H >H -H; normalize
    >minus_le_minus_minus_comm //
  ]
]
qed.

(* Basic-1: removed theorems 49:
            drop_skip_flat
            cimp_flat_sx cimp_flat_dx cimp_bind cimp_getl_conf
            drop_clear drop_clear_O drop_clear_S
            clear_gen_sort clear_gen_bind clear_gen_flat clear_gen_flat_r
            clear_gen_all clear_clear clear_mono clear_trans clear_ctail clear_cle
            getl_ctail_clen getl_gen_tail clear_getl_trans getl_clear_trans
            getl_clear_bind getl_clear_conf getl_dec getl_drop getl_drop_conf_lt
            getl_drop_conf_ge getl_conf_ge_drop getl_drop_conf_rev
            drop_getl_trans_lt drop_getl_trans_le drop_getl_trans_ge
            getl_drop_trans getl_flt getl_gen_all getl_gen_sort getl_gen_O
            getl_gen_S getl_gen_2 getl_gen_flat getl_gen_bind getl_conf_le
            getl_trans getl_refl getl_head getl_flat getl_ctail getl_mono
*)
