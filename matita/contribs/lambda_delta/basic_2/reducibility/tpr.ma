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

include "basic_2/substitution/tps.ma".

(* CONTEXT-FREE PARALLEL REDUCTION ON TERMS *********************************)

(* Basic_1: includes: pr0_delta1 *)
inductive tpr: relation term ≝
| tpr_atom : ∀I. tpr (⓪{I}) (⓪{I})
| tpr_flat : ∀I,V1,V2,T1,T2. tpr V1 V2 → tpr T1 T2 →
             tpr (ⓕ{I} V1. T1) (ⓕ{I} V2. T2)
| tpr_beta : ∀V1,V2,W,T1,T2.
             tpr V1 V2 → tpr T1 T2 → tpr (ⓐV1. ⓛW. T1) (ⓓV2. T2)
| tpr_delta: ∀I,V1,V2,T1,T2,T.
             tpr V1 V2 → tpr T1 T2 → ⋆. ⓑ{I} V2 ⊢ T2 ▶ [0, 1] T →
             tpr (ⓑ{I} V1. T1) (ⓑ{I} V2. T)
| tpr_theta: ∀V,V1,V2,W1,W2,T1,T2.
             tpr V1 V2 → ⇧[0,1] V2 ≡ V → tpr W1 W2 → tpr T1 T2 →
             tpr (ⓐV1. ⓓW1. T1) (ⓓW2. ⓐV. T2)
| tpr_zeta : ∀V,T,T1,T2. ⇧[0,1] T1 ≡ T → tpr T1 T2 → tpr (ⓓV. T) T2
| tpr_tau  : ∀V,T1,T2. tpr T1 T2 → tpr (ⓣV. T1) T2
.

interpretation
   "context-free parallel reduction (term)"
   'PRed T1 T2 = (tpr T1 T2).

(* Basic properties *********************************************************)

lemma tpr_bind: ∀I,V1,V2,T1,T2. V1 ➡ V2 → T1 ➡ T2 → ⓑ{I} V1. T1 ➡  ⓑ{I} V2. T2.
/2 width=3/ qed.

(* Basic_1: was by definition: pr0_refl *)
lemma tpr_refl: ∀T. T ➡ T.
#T elim T -T //
#I elim I -I /2 width=1/
qed.

(* Basic inversion lemmas ***************************************************)

fact tpr_inv_atom1_aux: ∀U1,U2. U1 ➡ U2 → ∀I. U1 = ⓪{I} → U2 = ⓪{I}.
#U1 #U2 * -U1 -U2
[ //
| #I #V1 #V2 #T1 #T2 #_ #_ #k #H destruct
| #V1 #V2 #W #T1 #T2 #_ #_ #k #H destruct
| #I #V1 #V2 #T1 #T2 #T #_ #_ #_ #k #H destruct
| #V #V1 #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #_ #k #H destruct
| #V #T #T1 #T2 #_ #_ #k #H destruct
| #V #T1 #T2 #_ #k #H destruct
]
qed.

(* Basic_1: was: pr0_gen_sort pr0_gen_lref *)
lemma tpr_inv_atom1: ∀I,U2. ⓪{I} ➡ U2 → U2 = ⓪{I}.
/2 width=3/ qed-.

fact tpr_inv_bind1_aux: ∀U1,U2. U1 ➡ U2 → ∀I,V1,T1. U1 = ⓑ{I} V1. T1 →
                        (∃∃V2,T2,T. V1 ➡ V2 & T1 ➡ T2 &
                                    ⋆.  ⓑ{I} V2 ⊢ T2 ▶ [0, 1] T &
                                    U2 = ⓑ{I} V2. T
                        ) ∨
                        ∃∃T. ⇧[0,1] T ≡ T1 & T ➡ U2 & I = Abbr.
#U1 #U2 * -U1 -U2
[ #J #I #V #T #H destruct
| #I1 #V1 #V2 #T1 #T2 #_ #_ #I #V #T #H destruct
| #V1 #V2 #W #T1 #T2 #_ #_ #I #V #T #H destruct
| #I1 #V1 #V2 #T1 #T2 #T #HV12 #HT12 #HT2 #I0 #V0 #T0 #H destruct /3 width=7/
| #V #V1 #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #_ #I0 #V0 #T0 #H destruct
| #V #T #T1 #T2 #HT1 #HT12 #I0 #V0 #T0 #H destruct /3 width=3/
| #V #T1 #T2 #_ #I0 #V0 #T0 #H destruct
]
qed.

lemma tpr_inv_bind1: ∀V1,T1,U2,I. ⓑ{I} V1. T1 ➡ U2 →
                     (∃∃V2,T2,T. V1 ➡ V2 & T1 ➡ T2 &
                                 ⋆.  ⓑ{I} V2 ⊢ T2 ▶ [0, 1] T &
                                 U2 = ⓑ{I} V2. T
                     ) ∨
                     ∃∃T. ⇧[0,1] T ≡ T1 & T ➡ U2 & I = Abbr.
/2 width=3/ qed-.

(* Basic_1: was pr0_gen_abbr *)
lemma tpr_inv_abbr1: ∀V1,T1,U2. ⓓV1. T1 ➡ U2 →
                     (∃∃V2,T2,T. V1 ➡ V2 & T1 ➡ T2 &
                                 ⋆.  ⓓV2 ⊢ T2 ▶ [0, 1] T &
                                 U2 = ⓓV2. T
                      ) ∨
                      ∃∃T. ⇧[0,1] T ≡ T1 & T ➡ U2.
#V1 #T1 #U2 #H
elim (tpr_inv_bind1 … H) -H * /3 width=7/
qed-.

fact tpr_inv_flat1_aux: ∀U1,U2. U1 ➡ U2 → ∀I,V1,U0. U1 = ⓕ{I} V1. U0 →
                        ∨∨ ∃∃V2,T2.            V1 ➡ V2 & U0 ➡ T2 &
                                               U2 = ⓕ{I} V2. T2
                         | ∃∃V2,W,T1,T2.       V1 ➡ V2 & T1 ➡ T2 &
                                               U0 = ⓛW. T1 &
                                               U2 = ⓓV2. T2 & I = Appl
                         | ∃∃V2,V,W1,W2,T1,T2. V1 ➡ V2 & W1 ➡ W2 & T1 ➡ T2 &
                                               ⇧[0,1] V2 ≡ V &
                                               U0 = ⓓW1. T1 &
                                               U2 = ⓓW2. ⓐV. T2 &
                                               I = Appl
                         |                     (U0 ➡ U2 ∧ I = Cast).
#U1 #U2 * -U1 -U2
[ #I #J #V #T #H destruct
| #I #V1 #V2 #T1 #T2 #HV12 #HT12 #J #V #T #H destruct /3 width=5/
| #V1 #V2 #W #T1 #T2 #HV12 #HT12 #J #V #T #H destruct /3 width=8/
| #I #V1 #V2 #T1 #T2 #T #_ #_ #_ #J #V0 #T0 #H destruct
| #V #V1 #V2 #W1 #W2 #T1 #T2 #HV12 #HV2 #HW12 #HT12 #J #V0 #T0 #H destruct /3 width=12/
| #V #T #T1 #T2 #_ #_ #J #V0 #T0 #H destruct
| #V #T1 #T2 #HT12 #J #V0 #T0 #H destruct /3 width=1/
]
qed.

lemma tpr_inv_flat1: ∀V1,U0,U2,I. ⓕ{I} V1. U0 ➡ U2 →
                     ∨∨ ∃∃V2,T2.            V1 ➡ V2 & U0 ➡ T2 &
                                            U2 = ⓕ{I} V2. T2
                      | ∃∃V2,W,T1,T2.       V1 ➡ V2 & T1 ➡ T2 &
                                            U0 = ⓛW. T1 &
                                            U2 = ⓓV2. T2 & I = Appl
                      | ∃∃V2,V,W1,W2,T1,T2. V1 ➡ V2 & W1 ➡ W2 & T1 ➡ T2 &
                                            ⇧[0,1] V2 ≡ V &
                                            U0 = ⓓW1. T1 &
                                            U2 = ⓓW2. ⓐV. T2 &
                                            I = Appl
                      |                     (U0 ➡ U2 ∧ I = Cast).
/2 width=3/ qed-.

(* Basic_1: was pr0_gen_appl *)
lemma tpr_inv_appl1: ∀V1,U0,U2. ⓐV1. U0 ➡ U2 →
                     ∨∨ ∃∃V2,T2.            V1 ➡ V2 & U0 ➡ T2 &
                                            U2 = ⓐV2. T2
                      | ∃∃V2,W,T1,T2.       V1 ➡ V2 & T1 ➡ T2 &
                                            U0 = ⓛW. T1 &
                                            U2 = ⓓV2. T2
                      | ∃∃V2,V,W1,W2,T1,T2. V1 ➡ V2 & W1 ➡ W2 & T1 ➡ T2 &
                                            ⇧[0,1] V2 ≡ V &
                                            U0 = ⓓW1. T1 &
                                            U2 = ⓓW2. ⓐV. T2.
#V1 #U0 #U2 #H
elim (tpr_inv_flat1 … H) -H * /3 width=12/ #_ #H destruct
qed-.

(* Note: the main property of simple terms *)
lemma tpr_inv_appl1_simple: ∀V1,T1,U. ⓐV1. T1 ➡ U → 𝐒⦃T1⦄ →
                            ∃∃V2,T2. V1 ➡ V2 & T1 ➡ T2 &
                                     U = ⓐV2. T2.
#V1 #T1 #U #H #HT1
elim (tpr_inv_appl1 … H) -H *
[ /2 width=5/
| #V2 #W #W1 #W2 #_ #_ #H #_ destruct
  elim (simple_inv_bind … HT1)
| #V2 #V #W1 #W2 #U1 #U2 #_ #_ #_ #_ #H #_ destruct
  elim (simple_inv_bind … HT1)
]
qed-.

(* Basic_1: was: pr0_gen_cast *)
lemma tpr_inv_cast1: ∀V1,T1,U2. ⓣV1. T1 ➡ U2 →
                       (∃∃V2,T2. V1 ➡ V2 & T1 ➡ T2 & U2 = ⓣV2. T2)
                     ∨ T1 ➡ U2.
#V1 #T1 #U2 #H
elim (tpr_inv_flat1 … H) -H * /3 width=5/
[ #V2 #W #W1 #W2 #_ #_ #_ #_ #H destruct
| #V2 #W #W1 #W2 #T2 #U1 #_ #_ #_ #_ #_ #_ #H destruct
]
qed-.

fact tpr_inv_lref2_aux: ∀T1,T2. T1 ➡ T2 → ∀i. T2 = #i →
                        ∨∨           T1 = #i
                         | ∃∃V,T,T0. ⇧[O,1] T0 ≡ T & T0 ➡ #i &
                                     T1 = ⓓV. T
                         | ∃∃V,T.    T ➡ #i & T1 = ⓣV. T.
#T1 #T2 * -T1 -T2
[ #I #i #H destruct /2 width=1/
| #I #V1 #V2 #T1 #T2 #_ #_ #i #H destruct
| #V1 #V2 #W #T1 #T2 #_ #_ #i #H destruct
| #I #V1 #V2 #T1 #T2 #T #_ #_ #_ #i #H destruct
| #V #V1 #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #_ #i #H destruct
| #V #T #T1 #T2 #HT1 #HT12 #i #H destruct /3 width=6/
| #V #T1 #T2 #HT12 #i #H destruct /3 width=4/
]
qed.

lemma tpr_inv_lref2: ∀T1,i. T1 ➡ #i →
                     ∨∨           T1 = #i
                      | ∃∃V,T,T0. ⇧[O,1] T0 ≡ T & T0 ➡ #i &
                                  T1 = ⓓV. T
                      | ∃∃V,T.    T ➡ #i & T1 = ⓣV. T.
/2 width=3/ qed-.

(* Basic_1: removed theorems 3:
            pr0_subst0_back pr0_subst0_fwd pr0_subst0
   Basic_1: removed local theorems: 1: pr0_delta_tau
*)
