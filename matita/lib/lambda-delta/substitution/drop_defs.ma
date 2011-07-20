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

(* DROPPING *****************************************************************)

inductive drop: lenv → nat → nat → lenv → Prop ≝
| drop_refl: ∀L. drop L 0 0 L
| drop_drop: ∀L1,L2,I,V,e. drop L1 0 e L2 → drop (L1. 𝕓{I} V) 0 (e + 1) L2
| drop_skip: ∀L1,L2,I,V1,V2,d,e.
             drop L1 d e L2 → ↑[d,e] V2 ≡ V1 →
             drop (L1. 𝕓{I} V1) (d + 1) e (L2. 𝕓{I} V2)
.

interpretation "dropping" 'RLift L2 d e L1 = (drop L1 d e L2).

(* Basic properties *********************************************************) 

lemma drop_drop_lt: ∀L1,L2,I,V,e. 
                    ↑[0, e - 1] L2 ≡ L1 → 0 < e → ↑[0, e] L2 ≡ L1. 𝕓{I} V.
#L1 #L2 #I #V #e #HL12 #He >(plus_minus_m_m e 1) /2/
qed.

(* Basic inversion lemmas ***************************************************)

lemma drop_inv_refl_aux: ∀d,e,L2,L1. ↑[d, e] L2 ≡ L1 → d = 0 → e = 0 → L1 = L2.
#d #e #L2 #L1 #H elim H -H d e L2 L1
[ //
| #L1 #L2 #I #V #e #_ #_ #_ #H
  elim (plus_S_eq_O_false … H)
| #L1 #L2 #I #V1 #V2 #d #e #_ #_ #_ #H
  elim (plus_S_eq_O_false … H)
]
qed.

lemma drop_inv_refl: ∀L2,L1. ↑[0, 0] L2 ≡ L1 → L1 = L2.
/2 width=5/ qed.

lemma drop_inv_O1_aux: ∀d,e,L2,L1. ↑[d, e] L2 ≡ L1 → d = 0 →
                       ∀K,I,V. L1 = K. 𝕓{I} V → 
                       (e = 0 ∧ L2 = K. 𝕓{I} V) ∨
                       (0 < e ∧ ↑[d, e - 1] L2 ≡ K).
#d #e #L2 #L1 #H elim H -H d e L2 L1
[ /3/
| #L1 #L2 #I #V #e #HL12 #_ #_ #K #J #W #H destruct -L1 I V /3/
| #L1 #L2 #I #V1 #V2 #d #e #_ #_ #_ #H elim (plus_S_eq_O_false … H)
]
qed.

lemma drop_inv_O1: ∀e,L2,K,I,V. ↑[0, e] L2 ≡ K. 𝕓{I} V →
                   (e = 0 ∧ L2 = K. 𝕓{I} V) ∨
                   (0 < e ∧ ↑[0, e - 1] L2 ≡ K).
/2/ qed.

lemma drop_inv_drop1: ∀e,L2,K,I,V.
                      ↑[0, e] L2 ≡ K. 𝕓{I} V → 0 < e → ↑[0, e - 1] L2 ≡ K.
#e #L2 #K #I #V #H #He
elim (drop_inv_O1 … H) -H * // #H destruct -e;
elim (lt_refl_false … He)
qed.

lemma drop_inv_skip2_aux: ∀d,e,L1,L2. ↑[d, e] L2 ≡ L1 → 0 < d →
                          ∀I,K2,V2. L2 = K2. 𝕓{I} V2 →
                          ∃∃K1,V1. ↑[d - 1, e] K2 ≡ K1 &
                                   ↑[d - 1, e] V2 ≡ V1 & 
                                   L1 = K1. 𝕓{I} V1.
#d #e #L1 #L2 #H elim H -H d e L1 L2
[ #L #H elim (lt_refl_false … H)
| #L1 #L2 #I #V #e #_ #_ #H elim (lt_refl_false … H)
| #L1 #X #Y #V1 #Z #d #e #HL12 #HV12 #_ #_ #I #L2 #V2 #H destruct -X Y Z;
  /2 width=5/
]
qed.

lemma drop_inv_skip2: ∀d,e,I,L1,K2,V2. ↑[d, e] K2. 𝕓{I} V2 ≡ L1 → 0 < d →
                      ∃∃K1,V1. ↑[d - 1, e] K2 ≡ K1 & ↑[d - 1, e] V2 ≡ V1 &
                               L1 = K1. 𝕓{I} V1.
/2/ qed.
