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

include "lambda-delta/substitution/pts_defs.ma".

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
| tpr_delta: ∀V1,V2,T1,T2,T.
             tpr V1 V2 → tpr T1 T2 → ⋆.  𝕓{Abbr} V2 ⊢ T2 [0, 1] ≫ T →
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
   'PRed T1 T2 = (tpr T1 T2).

(* Basic properties *********************************************************)

lemma tpr_refl: ∀T. T ⇒ T.
#T elim T -T //
#I elim I -I /2/
qed.

(* Basic inversion lemmas ***************************************************)

lemma tpr_inv_sort1_aux: ∀U1,U2. U1 ⇒ U2 → ∀k. U1 = ⋆k → U2 = ⋆k.
#U1 #U2 * -U1 U2
[ #k0 #k #H destruct -k0 //
| #i #k #H destruct
| #I #V1 #V2 #T1 #T2 #_ #_ #k #H destruct
| #I #V1 #V2 #T1 #T2 #_ #_ #k #H destruct
| #V1 #V2 #W #T1 #T2 #_ #_ #k #H destruct
| #V1 #V2 #T1 #T2 #T #_ #_ #_ #k #H destruct
| #V #V1 #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #_ #k #H destruct
| #V #T #T1 #T2 #_ #_ #k #H destruct
| #V #T1 #T2 #_ #k #H destruct
]
qed.

lemma tpr_inv_sort1: ∀k,U2. ⋆k ⇒ U2 → U2 = ⋆k.
/2/ qed.

lemma tpr_inv_lref1_aux: ∀U1,U2. U1 ⇒ U2 → ∀i. U1 = #i → U2 = #i.
#U1 #U2 * -U1 U2
[ #k #i #H destruct
| #j #i #H destruct -j //
| #I #V1 #V2 #T1 #T2 #_ #_ #i #H destruct
| #I #V1 #V2 #T1 #T2 #_ #_ #i #H destruct
| #V1 #V2 #W #T1 #T2 #_ #_ #i #H destruct
| #V1 #V2 #T1 #T2 #T #_ #_ #_ #i #H destruct
| #V #V1 #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #_ #i #H destruct
| #V #T #T1 #T2 #_ #_ #i #H destruct
| #V #T1 #T2 #_ #i #H destruct
]
qed.

lemma tpr_inv_lref1: ∀i,U2. #i ⇒ U2 → U2 = #i.
/2/ qed.

lemma tpr_inv_abbr1_aux: ∀U1,U2. U1 ⇒ U2 → ∀V1,T1. U1 = 𝕚{Abbr} V1. T1 →
                         ∨∨ ∃∃V2,T2. V1 ⇒ V2 & T1 ⇒ T2 & U2 = 𝕚{Abbr} V2. T2
                          | ∃∃V2,T2,T. V1 ⇒ V2 & T1 ⇒ T2 &
                                       ⋆.  𝕓{Abbr} V2 ⊢ T2 [0, 1] ≫ T &
                                       U2 = 𝕚{Abbr} V2. T
                          | ∃∃T. ↑[0,1] T ≡ T1 & T ⇒ U2.
#U1 #U2 * -U1 U2
[ #k #V #T #H destruct
| #i #V #T #H destruct
| #I #V1 #V2 #T1 #T2 #HV12 #HT12 #V #T #H destruct -I V1 T1 /3 width=5/
| #I #V1 #V2 #T1 #T2 #_ #_ #V #T #H destruct
| #V1 #V2 #W #T1 #T2 #_ #_ #V #T #H destruct
| #V1 #V2 #T1 #T2 #T #HV12 #HT12 #HT2 #V0 #T0 #H destruct -V1 T1 /3 width=7/
| #V #V1 #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #_ #V0 #T0 #H destruct
| #V #T #T1 #T2 #HT1 #HT12 #V0 #T0 #H destruct -V T /3/
| #V #T1 #T2 #_ #V0 #T0 #H destruct
]
qed.

lemma tpr_inv_abbr1: ∀V1,T1,U2. 𝕚{Abbr} V1. T1 ⇒ U2 →
                     ∨∨ ∃∃V2,T2. V1 ⇒ V2 & T1 ⇒ T2 & U2 = 𝕚{Abbr} V2. T2
                      | ∃∃V2,T2,T. V1 ⇒ V2 & T1 ⇒ T2 &
                                   ⋆.  𝕓{Abbr} V2 ⊢ T2 [0, 1] ≫ T &
                                   U2 = 𝕚{Abbr} V2. T
                      | ∃∃T. ↑[0,1] T ≡ T1 & tpr T U2.
/2/ qed.

lemma tpr_inv_abst1_aux: ∀U1,U2. U1 ⇒ U2 → ∀V1,T1. U1 = 𝕚{Abst} V1. T1 →
                         ∃∃V2,T2. V1 ⇒ V2 & T1 ⇒ T2 & U2 = 𝕚{Abst} V2. T2.
#U1 #U2 * -U1 U2
[ #k #V #T #H destruct
| #i #V #T #H destruct
| #I #V1 #V2 #T1 #T2 #HV12 #HT12 #V #T #H destruct -I V1 T1 /2 width=5/
| #I #V1 #V2 #T1 #T2 #_ #_ #V #T #H destruct
| #V1 #V2 #W #T1 #T2 #_ #_ #V #T #H destruct
| #V1 #V2 #T1 #T2 #T #_ #_ #_ #V0 #T0 #H destruct
| #V #V1 #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #_ #V0 #T0 #H destruct
| #V #T #T1 #T2 #_ #_ #V0 #T0 #H destruct
| #V #T1 #T2 #_ #V0 #T0 #H destruct
]
qed.

lemma tpr_inv_abst1: ∀V1,T1,U2. 𝕚{Abst} V1. T1 ⇒ U2 →
                     ∃∃V2,T2. V1 ⇒ V2 & T1 ⇒ T2 & U2 = 𝕚{Abst} V2. T2.
/2/ qed.

lemma tpr_inv_bind1: ∀V1,T1,U2,I. 𝕓{I} V1. T1 ⇒ U2 →
                     ∨∨ ∃∃V2,T2. V1 ⇒ V2 & T1 ⇒ T2 & U2 = 𝕓{I} V2. T2
                      | ∃∃V2,T2,T. V1 ⇒ V2 & T1 ⇒ T2 &
                                   ⋆.  𝕓{Abbr} V2 ⊢ T2 [0, 1] ≫ T &
                                   U2 = 𝕚{Abbr} V2. T & I = Abbr
                      | ∃∃T. ↑[0,1] T ≡ T1 & tpr T U2 & I = Abbr.
#V1 #T1 #U2 * #H
[ elim (tpr_inv_abbr1 … H) -H * /3 width=7/
| /3/
]
qed.

lemma tpr_inv_appl1_aux: ∀U1,U2. U1 ⇒ U2 → ∀V1,U0. U1 = 𝕚{Appl} V1. U0 →
                         ∨∨ ∃∃V2,T2.            V1 ⇒ V2 & U0 ⇒ T2 &
                                                U2 = 𝕚{Appl} V2. T2
                          | ∃∃V2,W,T1,T2.       V1 ⇒ V2 & T1 ⇒ T2 &
                                                U0 = 𝕚{Abst} W. T1 &
                                                U2 = 𝕓{Abbr} V2. T2
                          | ∃∃V2,V,W1,W2,T1,T2. V1 ⇒ V2 & W1 ⇒ W2 & T1 ⇒ T2 &
                                                ↑[0,1] V2 ≡ V &
                                                U0 = 𝕚{Abbr} W1. T1 &
                                                U2 = 𝕚{Abbr} W2. 𝕚{Appl} V. T2.
#U1 #U2 * -U1 U2
[ #k #V #T #H destruct
| #i #V #T #H destruct
| #I #V1 #V2 #T1 #T2 #_ #_ #V #T #H destruct
| #I #V1 #V2 #T1 #T2 #HV12 #HT12 #V #T #H destruct -I V1 T1 /3 width=5/
| #V1 #V2 #W #T1 #T2 #HV12 #HT12 #V #T #H destruct -V1 T /3 width=8/
| #V1 #V2 #T1 #T2 #T #_ #_ #_ #V0 #T0 #H destruct
| #V #V1 #V2 #W1 #W2 #T1 #T2 #HV12 #HV2 #HW12 #HT12 #V0 #T0 #H
  destruct -V1 T0 /3 width=12/
| #V #T #T1 #T2 #_ #_ #V0 #T0 #H destruct
| #V #T1 #T2 #_ #V0 #T0 #H destruct
]
qed.

lemma tpr_inv_appl1: ∀V1,U0,U2. 𝕚{Appl} V1. U0 ⇒ U2 →
                     ∨∨ ∃∃V2,T2.            V1 ⇒ V2 & U0 ⇒ T2 &
                                            U2 = 𝕚{Appl} V2. T2
                      | ∃∃V2,W,T1,T2.       V1 ⇒ V2 & T1 ⇒ T2 &
                                            U0 = 𝕚{Abst} W. T1 &
                                            U2 = 𝕓{Abbr} V2. T2
                      | ∃∃V2,V,W1,W2,T1,T2. V1 ⇒ V2 & W1 ⇒ W2 & T1 ⇒ T2 &
                                            ↑[0,1] V2 ≡ V &
                                            U0 = 𝕚{Abbr} W1. T1 &
                                            U2 = 𝕚{Abbr} W2. 𝕚{Appl} V. T2.
/2/ qed.

lemma tpr_inv_cast1_aux: ∀U1,U2. U1 ⇒ U2 → ∀V1,T1. U1 = 𝕚{Cast} V1. T1 →
                           (∃∃V2,T2. V1 ⇒ V2 & T1 ⇒ T2 & U2 = 𝕚{Cast} V2. T2)
                         ∨ T1 ⇒ U2.
#U1 #U2 * -U1 U2
[ #k #V #T #H destruct
| #i #V #T #H destruct
| #I #V1 #V2 #T1 #T2 #_ #_ #V #T #H destruct
| #I #V1 #V2 #T1 #T2 #HV12 #HT12 #V #T #H destruct -I V1 T1 /3 width=5/
| #V1 #V2 #W #T1 #T2 #_ #_ #V #T #H destruct
| #V1 #V2 #T1 #T2 #T #_ #_ #_ #V0 #T0 #H destruct
| #V #V1 #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #_ #V0 #T0 #H destruct
| #V #T #T1 #T2 #_ #_ #V0 #T0 #H destruct
| #V #T1 #T2 #HT12 #V0 #T0 #H destruct -V T1 /2/
]
qed.

lemma tpr_inv_cast1: ∀V1,T1,U2. 𝕚{Cast} V1. T1 ⇒ U2 →
                       (∃∃V2,T2. V1 ⇒ V2 & T1 ⇒ T2 & U2 = 𝕚{Cast} V2. T2)
                     ∨ T1 ⇒ U2.
/2/ qed.

lemma tpr_inv_flat1: ∀V1,U0,U2,I. 𝕗{I} V1. U0 ⇒ U2 →
                     ∨∨ ∃∃V2,T2.            V1 ⇒ V2 & U0 ⇒ T2 &
                                            U2 = 𝕗{I} V2. T2
                      | ∃∃V2,W,T1,T2.       V1 ⇒ V2 & T1 ⇒ T2 &
                                            U0 = 𝕚{Abst} W. T1 &
                                            U2 = 𝕓{Abbr} V2. T2 & I = Appl
                      | ∃∃V2,V,W1,W2,T1,T2. V1 ⇒ V2 & W1 ⇒ W2 & T1 ⇒ T2 &
                                            ↑[0,1] V2 ≡ V &
                                            U0 = 𝕚{Abbr} W1. T1 &
                                            U2 = 𝕚{Abbr} W2. 𝕚{Appl} V. T2 &
                                            I = Appl
                      |                     (U0 ⇒ U2 ∧ I = Cast).
#V1 #U0 #U2 * #H
[ elim (tpr_inv_appl1 … H) -H * /3 width=12/
| elim (tpr_inv_cast1 … H) -H [1: *] /3 width=5/
]
qed.

lemma tpr_inv_lref2_aux: ∀T1,T2. T1 ⇒ T2 → ∀i. T2 = #i →
                         ∨∨           T1 = #i
                          | ∃∃V,T,T0. ↑[O,1] T0 ≡ T & T0 ⇒ #i &
                                      T1 = 𝕚{Abbr} V. T
                          | ∃∃V,T.    T ⇒ #i & T1 = 𝕚{Cast} V. T.
#T1 #T2 * -T1 T2
[ #k #i #H destruct
| #j #i /2/
| #I #V1 #V2 #T1 #T2 #_ #_ #i #H destruct
| #I #V1 #V2 #T1 #T2 #_ #_ #i #H destruct
| #V1 #V2 #W #T1 #T2 #_ #_ #i #H destruct
| #V1 #V2 #T1 #T2 #T #_ #_ #_ #i #H destruct
| #V #V1 #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #_ #i #H destruct
| #V #T #T1 #T2 #HT1 #HT12 #i #H destruct /3 width=6/
| #V #T1 #T2 #HT12 #i #H destruct /3/
]
qed.

lemma tpr_inv_lref2: ∀T1,i. T1 ⇒ #i →
                     ∨∨           T1 = #i
                      | ∃∃V,T,T0. ↑[O,1] T0 ≡ T & T0 ⇒ #i &
                                  T1 = 𝕓{Abbr} V. T
                      | ∃∃V,T.    T ⇒ #i & T1 = 𝕗{Cast} V. T.
/2/ qed.
