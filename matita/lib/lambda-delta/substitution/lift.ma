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

include "lambda-delta/language/term.ma".

(* RELOCATION ***************************************************************)

inductive lift: term → nat → nat → term → Prop ≝
   | lift_sort   : ∀k,d,e. lift (⋆k) d e (⋆k)
   | lift_lref_lt: ∀i,d,e. i < d → lift (#i) d e (#i)
   | lift_lref_ge: ∀i,d,e. d ≤ i → lift (#i) d e (#(i + e))
   | lift_con2   : ∀I,V1,V2,T1,T2,d,e.
                   lift V1 d e V2 → lift T1 (d + 1) e T2 →
                   lift (♭I V1. T1) d e (♭I V2. T2)
.

interpretation "relocation" 'RLift T1 d e T2 = (lift T1 d e T2).

(* The basic properties *****************************************************)

lemma lift_lref_ge_minus: ∀d,e,i. d + e ≤ i → ↑[d,e] #(i - e) ≡ #i.
#d #e #i #H >(plus_minus_m_m i e) in ⊢ (? ? ? ? %) /3/
qed.

(* The basic inversion lemmas ***********************************************)

lemma lift_inv_sort2_aux: ∀d,e,T1,T2. ↑[d,e] T1 ≡ T2 → ∀k. T2 = ⋆k → T1 = ⋆k.
#d #e #T1 #T2 #H elim H -H d e T1 T2 //
   [ #i #d #e #_ #k #H destruct
   | #I #V1 #V2 #T1 #T2 #d #e #_ #_ #_ #_ #k #H destruct
   ]
qed.

lemma lift_inv_sort2: ∀d,e,T1,k. ↑[d,e] T1 ≡ ⋆k → T1 = ⋆k.
#d #e #T1 #k #H lapply (lift_inv_sort2_aux … H) /2/
qed.

lemma lift_inv_lref2_aux: ∀d,e,T1,T2. ↑[d,e] T1 ≡ T2 → ∀i. T2 = #i →
                          (i < d ∧ T1 = #i) ∨ (d + e ≤ i ∧ T1 = #(i - e)).
#d #e #T1 #T2 #H elim H -H d e T1 T2
   [ #k #d #e #i #H destruct
   | #j #d #e #Hj #i #Hi destruct /3/
   | #j #d #e #Hj #i #Hi destruct <minus_plus_m_m /4/
   | #I #V1 #V2 #T1 #T2 #d #e #_ #_ #_ #_ #i #H destruct
   ]
qed.

lemma lift_inv_lref2: ∀d,e,T1,i. ↑[d,e] T1 ≡ #i →
                      (i < d ∧ T1 = #i) ∨ (d + e ≤ i ∧ T1 = #(i - e)).
#d #e #T1 #i #H lapply (lift_inv_lref2_aux … H) /2/
qed.

lemma lift_inv_con22_aux: ∀d,e,T1,T2. ↑[d,e] T1 ≡ T2 →
                          ∀I,V2,U2. T2 = ♭I V2.U2 →
                          ∃V1,U1. ↑[d,e] V1 ≡ V2 ∧ ↑[d+1,e] U1 ≡ U2 ∧
                                  T1 = ♭I V1.U1.
#d #e #T1 #T2 #H elim H -H d e T1 T2
   [ #k #d #e #I #V2 #U2 #H destruct
   | #i #d #e #_ #I #V2 #U2 #H destruct
   | #i #d #e #_ #I #V2 #U2 #H destruct
   | #J #W1 #W2 #T1 #T2 #d #e #HW #HT #_ #_ #I #V2 #U2 #H destruct /5/
qed.

lemma lift_inv_con22: ∀d,e,T1,I,V2,U2. ↑[d,e] T1 ≡  ♭I V2. U2 →
                      ∃V1,U1. ↑[d,e] V1 ≡ V2 ∧ ↑[d+1,e] U1 ≡ U2 ∧
                              T1 = ♭I V1. U1.
#d #e #T1 #I #V2 #U2 #H lapply (lift_inv_con22_aux … H) /2/
qed.

(* the main properies *******************************************************)

axiom lift_trans_rev: ∀d1,e1,T1,T. ↑[d1,e1] T1 ≡ T →
                      ∀d2,e2,T2. ↑[d2 + e1, e2] T2 ≡ T →
                      d1 ≤ d2 →
                      ∃T0. ↑[d1, e1] T0 ≡ T2 ∧ ↑[d2, e2] T0 ≡ T1.
