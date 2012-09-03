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
| tpr_beta : ∀a,V1,V2,W,T1,T2.
             tpr V1 V2 → tpr T1 T2 → tpr (ⓐV1. ⓛ{a}W. T1) (ⓓ{a}V2. T2)
| tpr_delta: ∀a,I,V1,V2,T1,T,T2.
             tpr V1 V2 → tpr T1 T → ⋆. ⓑ{I} V2 ⊢ T ▶ [0, 1] T2 →
             tpr (ⓑ{a,I} V1. T1) (ⓑ{a,I} V2. T2)
| tpr_theta: ∀a,V,V1,V2,W1,W2,T1,T2.
             tpr V1 V2 → ⇧[0,1] V2 ≡ V → tpr W1 W2 → tpr T1 T2 →
             tpr (ⓐV1. ⓓ{a}W1. T1) (ⓓ{a}W2. ⓐV. T2)
| tpr_zeta : ∀V,T1,T,T2. tpr T1 T → ⇧[0, 1] T2 ≡ T → tpr (+ⓓV. T1) T2
| tpr_tau  : ∀V,T1,T2. tpr T1 T2 → tpr (ⓝV. T1) T2
.

interpretation
   "context-free parallel reduction (term)"
   'PRed T1 T2 = (tpr T1 T2).

(* Basic properties *********************************************************)

lemma tpr_bind: ∀a,I,V1,V2,T1,T2. V1 ➡ V2 → T1 ➡ T2 → ⓑ{a,I} V1. T1 ➡ ⓑ{a,I} V2. T2.
/2 width=3/ qed.

(* Basic_1: was by definition: pr0_refl *)
lemma tpr_refl: reflexive … tpr.
#T elim T -T //
#I elim I -I /2 width=1/
qed.

(* Basic inversion lemmas ***************************************************)

fact tpr_inv_atom1_aux: ∀U1,U2. U1 ➡ U2 → ∀I. U1 = ⓪{I} → U2 = ⓪{I}.
#U1 #U2 * -U1 -U2
[ //
| #I #V1 #V2 #T1 #T2 #_ #_ #k #H destruct
| #a #V1 #V2 #W #T1 #T2 #_ #_ #k #H destruct
| #a #I #V1 #V2 #T1 #T #T2 #_ #_ #_ #k #H destruct
| #a #V #V1 #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #_ #k #H destruct
| #V #T1 #T #T2 #_ #_ #k #H destruct
| #V #T1 #T2 #_ #k #H destruct
]
qed.

(* Basic_1: was: pr0_gen_sort pr0_gen_lref *)
lemma tpr_inv_atom1: ∀I,U2. ⓪{I} ➡ U2 → U2 = ⓪{I}.
/2 width=3/ qed-.

fact tpr_inv_bind1_aux: ∀U1,U2. U1 ➡ U2 → ∀a,I,V1,T1. U1 = ⓑ{a,I} V1. T1 →
                        (∃∃V2,T,T2. V1 ➡ V2 & T1 ➡ T &
                                    ⋆.  ⓑ{I} V2 ⊢ T ▶ [0, 1] T2 &
                                    U2 = ⓑ{a,I} V2. T2
                        ) ∨
                        ∃∃T. T1 ➡ T & ⇧[0, 1] U2 ≡ T & a = true & I = Abbr.
#U1 #U2 * -U1 -U2
[ #J #a #I #V #T #H destruct
| #I1 #V1 #V2 #T1 #T2 #_ #_ #a #I #V #T #H destruct
| #b #V1 #V2 #W #T1 #T2 #_ #_ #a #I #V #T #H destruct
| #b #I1 #V1 #V2 #T1 #T #T2 #HV12 #HT1 #HT2 #a #I0 #V0 #T0 #H destruct /3 width=7/
| #b #V #V1 #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #_ #a #I0 #V0 #T0 #H destruct
| #V #T1 #T #T2 #HT1 #HT2 #a #I0 #V0 #T0 #H destruct /3 width=3/
| #V #T1 #T2 #_ #a #I0 #V0 #T0 #H destruct
]
qed.

lemma tpr_inv_bind1: ∀V1,T1,U2,a,I. ⓑ{a,I} V1. T1 ➡ U2 →
                     (∃∃V2,T,T2. V1 ➡ V2 & T1 ➡ T &
                                 ⋆.  ⓑ{I} V2 ⊢ T ▶ [0, 1] T2 &
                                 U2 = ⓑ{a,I} V2. T2
                     ) ∨
                     ∃∃T. T1 ➡ T & ⇧[0,1] U2 ≡ T & a = true & I = Abbr.
/2 width=3/ qed-.

(* Basic_1: was pr0_gen_abbr *)
lemma tpr_inv_abbr1: ∀a,V1,T1,U2. ⓓ{a}V1. T1 ➡ U2 →
                     (∃∃V2,T,T2. V1 ➡ V2 & T1 ➡ T &
                                 ⋆.  ⓓV2 ⊢ T ▶ [0, 1] T2 &
                                 U2 = ⓓ{a}V2. T2
                      ) ∨
                      ∃∃T. T1 ➡ T & ⇧[0, 1] U2 ≡ T & a = true.
#a #V1 #T1 #U2 #H
elim (tpr_inv_bind1 … H) -H * /3 width=7/
qed-.

fact tpr_inv_flat1_aux: ∀U1,U2. U1 ➡ U2 → ∀I,V1,U0. U1 = ⓕ{I} V1. U0 →
                        ∨∨ ∃∃V2,T2.              V1 ➡ V2 & U0 ➡ T2 &
                                                 U2 = ⓕ{I} V2. T2
                         | ∃∃a,V2,W,T1,T2.       V1 ➡ V2 & T1 ➡ T2 &
                                                 U0 = ⓛ{a}W. T1 &
                                                 U2 = ⓓ{a}V2. T2 & I = Appl
                         | ∃∃a,V2,V,W1,W2,T1,T2. V1 ➡ V2 & W1 ➡ W2 & T1 ➡ T2 &
                                                 ⇧[0,1] V2 ≡ V &
                                                 U0 = ⓓ{a}W1. T1 &
                                                 U2 = ⓓ{a}W2. ⓐV. T2 &
                                                 I = Appl
                         |                       (U0 ➡ U2 ∧ I = Cast).
#U1 #U2 * -U1 -U2
[ #I #J #V #T #H destruct
| #I #V1 #V2 #T1 #T2 #HV12 #HT12 #J #V #T #H destruct /3 width=5/
| #a #V1 #V2 #W #T1 #T2 #HV12 #HT12 #J #V #T #H destruct /3 width=9/
| #a #I #V1 #V2 #T1 #T #T2 #_ #_ #_ #J #V0 #T0 #H destruct
| #a #V #V1 #V2 #W1 #W2 #T1 #T2 #HV12 #HV2 #HW12 #HT12 #J #V0 #T0 #H destruct /3 width=13/
| #V #T1 #T #T2 #_ #_ #J #V0 #T0 #H destruct
| #V #T1 #T2 #HT12 #J #V0 #T0 #H destruct /3 width=1/
]
qed.

lemma tpr_inv_flat1: ∀V1,U0,U2,I. ⓕ{I} V1. U0 ➡ U2 →
                     ∨∨ ∃∃V2,T2.              V1 ➡ V2 & U0 ➡ T2 &
                                              U2 = ⓕ{I} V2. T2
                      | ∃∃a,V2,W,T1,T2.       V1 ➡ V2 & T1 ➡ T2 &
                                              U0 = ⓛ{a}W. T1 &
                                              U2 = ⓓ{a}V2. T2 & I = Appl
                      | ∃∃a,V2,V,W1,W2,T1,T2. V1 ➡ V2 & W1 ➡ W2 & T1 ➡ T2 &
                                              ⇧[0,1] V2 ≡ V &
                                              U0 = ⓓ{a}W1. T1 &
                                              U2 = ⓓ{a}W2. ⓐV. T2 &
                                              I = Appl
                      |                       (U0 ➡ U2 ∧ I = Cast).
/2 width=3/ qed-.

(* Basic_1: was pr0_gen_appl *)
lemma tpr_inv_appl1: ∀V1,U0,U2. ⓐV1. U0 ➡ U2 →
                     ∨∨ ∃∃V2,T2.              V1 ➡ V2 & U0 ➡ T2 &
                                              U2 = ⓐV2. T2
                      | ∃∃a,V2,W,T1,T2.       V1 ➡ V2 & T1 ➡ T2 &
                                              U0 = ⓛ{a}W. T1 &
                                              U2 = ⓓ{a}V2. T2
                      | ∃∃a,V2,V,W1,W2,T1,T2. V1 ➡ V2 & W1 ➡ W2 & T1 ➡ T2 &
                                              ⇧[0,1] V2 ≡ V &
                                              U0 = ⓓ{a}W1. T1 &
                                              U2 = ⓓ{a}W2. ⓐV. T2.
#V1 #U0 #U2 #H
elim (tpr_inv_flat1 … H) -H *
/3 width=5/ /3 width=9/ /3 width=13/
#_ #H destruct
qed-.

(* Note: the main property of simple terms *)
lemma tpr_inv_appl1_simple: ∀V1,T1,U. ⓐV1. T1 ➡ U → 𝐒⦃T1⦄ →
                            ∃∃V2,T2. V1 ➡ V2 & T1 ➡ T2 &
                                     U = ⓐV2. T2.
#V1 #T1 #U #H #HT1
elim (tpr_inv_appl1 … H) -H *
[ /2 width=5/
| #a #V2 #W #W1 #W2 #_ #_ #H #_ destruct
  elim (simple_inv_bind … HT1)
| #a #V2 #V #W1 #W2 #U1 #U2 #_ #_ #_ #_ #H #_ destruct
  elim (simple_inv_bind … HT1)
]
qed-.

(* Basic_1: was: pr0_gen_cast *)
lemma tpr_inv_cast1: ∀V1,T1,U2. ⓝV1. T1 ➡ U2 →
                       (∃∃V2,T2. V1 ➡ V2 & T1 ➡ T2 & U2 = ⓝV2. T2)
                     ∨ T1 ➡ U2.
#V1 #T1 #U2 #H
elim (tpr_inv_flat1 … H) -H * /3 width=5/ #a #V2 #W #W1 #W2
[ #_ #_ #_ #_ #H destruct
| #T2 #U1 #_ #_ #_ #_ #_ #_ #H destruct
]
qed-.

fact tpr_inv_lref2_aux: ∀T1,T2. T1 ➡ T2 → ∀i. T2 = #i →
                        ∨∨        T1 = #i
                         | ∃∃V,T. T ➡ #(i+1) & T1 = +ⓓV. T
                         | ∃∃V,T. T ➡ #i & T1 = ⓝV. T.
#T1 #T2 * -T1 -T2
[ #I #i #H destruct /2 width=1/
| #I #V1 #V2 #T1 #T2 #_ #_ #i #H destruct
| #a #V1 #V2 #W #T1 #T2 #_ #_ #i #H destruct
| #a #I #V1 #V2 #T1 #T #T2 #_ #_ #_ #i #H destruct
| #a #V #V1 #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #_ #i #H destruct
| #V #T1 #T #T2 #HT1 #HT2 #i #H destruct
  lapply (lift_inv_lref1_ge … HT2 ?) -HT2 // #H destruct /3 width=4/
| #V #T1 #T2 #HT12 #i #H destruct /3 width=4/
]
qed.

lemma tpr_inv_lref2: ∀T1,i. T1 ➡ #i →
                     ∨∨        T1 = #i
                      | ∃∃V,T. T ➡ #(i+1) & T1 = +ⓓV. T
                      | ∃∃V,T. T ➡ #i & T1 = ⓝV. T.
/2 width=3/ qed-.

(* Basic forward lemmas *****************************************************)

lemma tpr_fwd_shift1: ∀L1,T1,T. L1 @@ T1 ➡ T →
                      ∃∃L2,T2. L1 𝟙 L2 & T = L2 @@ T2.
#L1 @(lenv_ind_dx … L1) -L1
[ #T1 #T #_ @ex2_2_intro [3: // |4: // |1,2: skip ] (**) (* /2 width=4/ does not work *)
| #I #L1 #V1 #IH #T1 #T >shift_append_assoc #H
  elim (tpr_inv_bind1 … H) -H *
  [ #V0 #T0 #X0 #_ #HT10 #HTX0 #H destruct
    elim (IH … HT10) -IH -T1 #L2 #V2 #HL12 #H destruct
    elim (tps_fwd_shift1 … HTX0) -V2 #L3 #X3 #HL23 #H destruct
    lapply (ltop_trans … HL12 HL23) -L2 #HL13
    @(ex2_2_intro … (⋆.ⓑ{I}V0@@L3)) /2 width=4/ /3 width=1/
  | #T0 #_ #_ #H destruct
  ]
]
qed-.

lemma tpr_fwd_shift_bind_minus: ∀L1,L2. |L1| = |L2| → ∀I1,I2,V1,V2,T1,T2.
                                L1 @@ -ⓑ{I1}V1.T1 ➡ L2 @@ -ⓑ{I2}V2.T2 →
                                L1 𝟙 L2 ∧ I1 = I2.
#L1 #L2 #HL12 #I1 #I2 #V1 #V2 #T1 #T2 #H
elim (tpr_fwd_shift1 (L1.ⓑ{I1}V1) … H) -H #Y #X #HY #HX
elim (ltop_inv_pair1 … HY) -HY #L #V #HL1 #H destruct
elim (shift_inj (L2.ⓑ{I2}V2) … HX ?) -HX
[ #H1 #_ destruct /2 width=1/
| lapply (ltop_fwd_length … HL1) -HL1 normalize // 
]
qed-.

(* Basic_1: removed theorems 3:
            pr0_subst0_back pr0_subst0_fwd pr0_subst0
   Basic_1: removed local theorems: 1: pr0_delta_tau
*)
