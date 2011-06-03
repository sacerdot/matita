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
                          ∃∃V1,U1. ↑[d,e] V1 ≡ V2 & ↑[d+1,e] U1 ≡ U2 &
                                   T1 = ♭I V1.U1.
#d #e #T1 #T2 #H elim H -H d e T1 T2
   [ #k #d #e #I #V2 #U2 #H destruct
   | #i #d #e #_ #I #V2 #U2 #H destruct
   | #i #d #e #_ #I #V2 #U2 #H destruct
   | #J #W1 #W2 #T1 #T2 #d #e #HW #HT #_ #_ #I #V2 #U2 #H destruct
     /2 width = 5/
   ]
qed.

lemma lift_inv_con22: ∀d,e,T1,I,V2,U2. ↑[d,e] T1 ≡  ♭I V2. U2 →
                      ∃∃V1,U1. ↑[d,e] V1 ≡ V2 & ↑[d+1,e] U1 ≡ U2 &
                               T1 = ♭I V1. U1.
#d #e #T1 #I #V2 #U2 #H lapply (lift_inv_con22_aux … H) /2/
qed.

(* the main properies *******************************************************)

theorem lift_trans_rev: ∀d1,e1,T1,T. ↑[d1,e1] T1 ≡ T →
                        ∀d2,e2,T2. ↑[d2 + e1, e2] T2 ≡ T →
                        d1 ≤ d2 →
                        ∃∃T0. ↑[d1, e1] T0 ≡ T2 & ↑[d2, e2] T0 ≡ T1.
#d1 #e1 #T1 #T #H elim H -H d1 e1 T1 T
   [ #k #d1 #e1 #d2 #e2 #T2 #Hk #Hd12
     lapply (lift_inv_sort2 … Hk) -Hk #Hk destruct -T2 /3/
   | #i #d1 #e1 #Hid1 #d2 #e2 #T2 #Hi #Hd12
     lapply (lift_inv_lref2 … Hi) -Hi * * #Hid2 #H destruct -T2
     [ -Hid2 /4/
     | elim (lt_false d1 ?)
       @(le_to_lt_to_lt … Hd12) -Hd12 @(le_to_lt_to_lt … Hid1) -Hid1 /2/
     ]
   | #i #d1 #e1 #Hid1 #d2 #e2 #T2 #Hi #Hd12
     lapply (lift_inv_lref2 … Hi) -Hi * * #Hid2 #H destruct -T2
     [ -Hd12; lapply (lt_plus_to_lt_l … Hid2) -Hid2 #Hid2 /3/
     | -Hid1; lapply (arith1 … Hid2) -Hid2 #Hid2
       @(ex2_1_intro … #(i - e2))
       [ >le_plus_minus_comm [ @lift_lref_ge @(transitive_le … Hd12) -Hd12 /2/ | -Hd12 /2/ ]
       | -Hd12 >(plus_minus_m_m i e2) in ⊢ (? ? ? ? %) /3/
       ]
     ]
   | #I #W1 #W #U1 #U #d1 #e1 #_ #_ #IHW #IHU #d2 #e2 #T2 #H #Hd12
     lapply (lift_inv_con22 … H) -H * #W2 #U2 #HW2 #HU2 #H destruct -T2;
     elim (IHW … HW2 ?) // -IHW HW2 #W0 #HW2 #HW1
     >plus_plus_comm_23 in HU2 #HU2 elim (IHU … HU2 ?) /3 width = 5/
   ]
qed.

theorem lift_free: ∀d1,e2,T1,T2. ↑[d1, e2] T1 ≡ T2 → ∀d2,e1.
                                 d1 ≤ d2 → d2 ≤ d1 + e1 → e1 ≤ e2 →
                                 ∃∃T. ↑[d1, e1] T1 ≡ T & ↑[d2, e2 - e1] T ≡ T2.
#d1 #e2 #T1 #T2 #H elim H -H d1 e2 T1 T2
   [ /3/
   | #i #d1 #e2 #Hid1 #d2 #e1 #Hd12 #_ #_
     lapply (lt_to_le_to_lt … Hid1 Hd12) -Hd12 #Hid2 /4/
   | #i #d1 #e2 #Hid1 #d2 #e1 #_ #Hd21 #He12
     lapply (transitive_le …(i+e1) Hd21 ?) /2/ -Hd21 #Hd21
     <(plus_plus_minus_m_m e1 e2 i) /3/
   | #I #V1 #V2 #T1 #T2 #d1 #e2 #_ #_ #IHV #IHT #d2 #e1 #Hd12 #Hd21 #He12
     elim (IHV … Hd12 Hd21 He12) -IHV #V0 #HV0a #HV0b 
     elim (IHT (d2+1) … ? ? He12) /3 width = 5/
   ]
qed.
