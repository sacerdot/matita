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

include "lambda-delta/substitution/subst.ma".

(* THINNING *****************************************************************)

inductive thin: lenv → nat → nat → lenv → Prop ≝
| thin_refl: ∀L. thin L 0 0 L
| thin_thin: ∀L1,L2,I,V,e. thin L1 0 e L2 → thin (L1. 𝕓{I} V) 0 (e + 1) L2
| thin_skip: ∀L1,L2,I,V1,V2,d,e.
             thin L1 d e L2 → L1 ⊢ ↓[d,e] V1 ≡ V2 →
             thin (L1. 𝕓{I} V1) (d + 1) e (L2. 𝕓{I} V2)
.

interpretation "thinning" 'RSubst L1 d e L2 = (thin L1 d e L2).

(* the basic inversion lemmas ***********************************************)

lemma thin_inv_skip2_aux: ∀d,e,L1,L2. ↓[d, e] L1 ≡ L2 → 0 < d →
                          ∀I,K2,V2. L2 = K2. 𝕓{I} V2 →
                          ∃∃K1,V1. ↓[d - 1, e] K1 ≡ K2 &
                                   K1 ⊢ ↓[d - 1, e] V1 ≡ V2 & 
                                   L1 = K1. 𝕓{I} V1.
#d #e #L1 #L2 #H elim H -H d e L1 L2
[ #L #H elim (lt_false … H)
| #L1 #L2 #I #V #e #_ #_ #H elim (lt_false … H)
| #L1 #X #Y #V1 #Z #d #e #HL12 #HV12 #_ #_ #I #L2 #V2 #H destruct -X Y Z;
  /2 width=5/
]
qed.

lemma thin_inv_skip2: ∀d,e,I,L1,K2,V2. ↓[d, e] L1 ≡ K2. 𝕓{I} V2 → 0 < d →
                      ∃∃K1,V1. ↓[d - 1, e] K1 ≡ K2 & K1 ⊢ ↓[d - 1, e] V1 ≡ V2 &
                               L1 = K1. 𝕓{I} V1.
/2/ qed.

(* the main properties ******************************************************)

axiom thin_conf_ge: ∀d1,e1,L,L1. ↓[d1,e1] L ≡ L1 →
                    ∀e2,L2. ↓[0,e2] L ≡ L2 → d1 + e1 ≤ e2 → ↓[0,e2-e1] L1 ≡ L2.

axiom thin_conf_lt: ∀d1,e1,L,L1. ↓[d1,e1] L ≡ L1 →
                    ∀e2,K2,I,V2. ↓[0,e2] L ≡ K2. 𝕓{I} V2 →
                    e2 < d1 → let d ≝ d1 - e2 - 1 in
                    ∃∃K1,V1. ↓[0,e2] L1 ≡ K1. 𝕓{I} V1 & ↓[d,e1] K2 ≡ K1 & ↑[d,e1] V1 ≡ V2.

axiom thin_trans_le: ∀d1,e1,L1,L. ↓[d1, e1] L1 ≡ L →
                     ∀e2,L2. ↓[0, e2] L ≡ L2 → e2 ≤ d1 →
                     ∃∃L0. ↓[0, e2] L1 ≡ L0 & ↓[d1 - e2, e1] L0 ≡ L2.

axiom thin_trans_ge: ∀d1,e1,L1,L. ↓[d1, e1] L1 ≡ L →
                     ∀e2,L2. ↓[0, e2] L ≡ L2 → d1 ≤ e2 → ↓[0, e1 + e2] L1 ≡ L2.
