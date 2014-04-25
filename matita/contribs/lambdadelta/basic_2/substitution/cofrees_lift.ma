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

include "basic_2/substitution/cpys_lift.ma".
include "basic_2/substitution/cofrees.ma".

(* CONTEXT-SENSITIVE EXCLUSION FROM FREE VARIABLES **************************)

(* Advanced properties ******************************************************)

lemma cofrees_lref_skip: ∀L,d,i,j. j < i → yinj j < d → L ⊢ i ~ϵ 𝐅*[d]⦃#j⦄.
#L #d #i #j #Hji #Hjd #X #H elim (cpys_inv_lref1_Y2 … H) -H
[ #H destruct /3 width=2 by lift_lref_lt, ex_intro/
| * #I #K #W1 #W2 #Hdj elim (ylt_yle_false … Hdj) -i -I -L -K -W1 -W2 -X //
]
qed.

lemma cofrees_lref_lt: ∀L,d,i,j. i < j → L ⊢ i ~ϵ 𝐅*[d]⦃#j⦄.
#L #d #i #j #Hij #X #H elim (cpys_inv_lref1_Y2 … H) -H
[ #H destruct /3 width=2 by lift_lref_ge_minus, ex_intro/
| * #I #K #V1 #V2 #_ #_ #_ #H -I -L -K -V1 -d
  elim (lift_split … H i j) /2 width=2 by lt_to_le, ex_intro/
]
qed.

lemma cofrees_lref_gt: ∀I,L,K,W,d,i,j. j < i → ⇩[j] L ≡ K.ⓑ{I}W → 
                       K ⊢ (i-j-1) ~ϵ 𝐅*[O]⦃W⦄ → L ⊢ i ~ϵ 𝐅*[d]⦃#j⦄.
#I #L #K #W1 #d #i #j #Hji #HLK #HW1 #X #H elim (cpys_inv_lref1_Y2 … H) -H
[ #H destruct /3 width=2 by lift_lref_lt, ex_intro/
| * #I0 #K0 #W0 #W2 #Hdj #HLK0 #HW12 #HW2 lapply (ldrop_mono … HLK0 … HLK) -L
  #H destruct elim (HW1 … HW12) -I -K -W1 -d
  #V2 #HVW2 elim (lift_trans_le … HVW2 … HW2) -W2 //
  >minus_plus <plus_minus_m_m /2 width=2 by ex_intro/
]
qed.

lemma cofrees_lref_free: ∀L,d,i,j. |L| ≤ j → j < i → L ⊢ i ~ϵ 𝐅*[d]⦃#j⦄.
#L #d #i #j #Hj #Hji #X #H elim (cpys_inv_lref1_Y2 … H) -H
[ #H destruct /3 width=2 by lift_lref_lt, ex_intro/
| * #I #K #W1 #W2 #_ #HLK lapply (ldrop_fwd_length_lt2 … HLK) -I
  #H elim (lt_refl_false j) -d -i -K -W1 -W2 -X /2 width=3 by lt_to_le_to_lt/
]
qed.

(* Advanced negated inversion lemmas ****************************************)

lemma frees_inv_lref_gt: ∀L,d,i,j. j < i → (L ⊢ i ~ϵ 𝐅*[d]⦃#j⦄ → ⊥) →
                         ∃∃I,K,W. ⇩[j] L ≡ K.ⓑ{I}W & (K ⊢ (i-j-1) ~ϵ 𝐅*[0]⦃W⦄ → ⊥) & d ≤ yinj j.
#L #d #i #j #Hji #H elim (ylt_split j d) #Hjd
[ elim H -H /2 width=6 by cofrees_lref_skip/ 
| elim (lt_or_ge j (|L|)) #Hj
  [ elim (ldrop_O1_lt … Hj) -Hj /4 width=10 by cofrees_lref_gt, ex3_3_intro/
  | elim H -H /2 width=6 by cofrees_lref_free/
  ]
]
qed-.

lemma frees_inv_lref_free: ∀L,d,i,j. (L ⊢ i ~ϵ 𝐅*[d]⦃#j⦄  → ⊥) → |L| ≤ j → j = i.
#L #d #i #j #H #Hj elim (lt_or_eq_or_gt i j) //
#Hij elim H -H /2 width=6 by cofrees_lref_lt, cofrees_lref_free/
qed-.

lemma frees_inv_gen: ∀L,U,d,i. (L ⊢ i ~ϵ 𝐅*[d]⦃U⦄ → ⊥) →
                     ∃∃U0.  ⦃⋆, L⦄ ⊢ U ▶*[d, ∞] U0 & (∀T. ⇧[i, 1] T ≡ U0 → ⊥).
#L #U @(f2_ind … rfw … L U) -L -U
#n #IH #L * *
[ -IH #k #_ #d #i #H elim H -H //
| #j #Hn #d #i #H elim (lt_or_eq_or_gt i j)
  [ -n #Hij elim H -H /2 width=5 by cofrees_lref_lt/
  | -H -n #H destruct /3 width=7 by lift_inv_lref2_be, ex2_intro/
  | #Hji elim (frees_inv_lref_gt … H) // -H
    #I #K #W1 #HLK #H #Hdj elim (IH … H) /2 width=2 by ldrop_fwd_rfw/ -H -n
    #W2 #HW12 #HnW2 elim (lift_total W2 0 (j+1))
    #U2 #HWU2 @(ex2_intro … U2) /2 width=7 by cpys_subst_Y2/ -I -L -K -W1 -d
    #T2 #HTU2 elim (lift_div_le … HWU2 (i-j-1) 1 T2) /2 width=2 by/ -W2
    >minus_plus <plus_minus_m_m //
  ]
| -IH #p #_ #d #i #H elim H -H //
| #a #I #W #U #Hn #d #i #H elim (frees_inv_bind … H) -H
  #H elim (IH … H) // -H -n
  /4 width=9 by cpys_bind, nlift_bind_dx, nlift_bind_sn, ex2_intro/
| #I #W #U #Hn #d #i #H elim (frees_inv_flat … H) -H
  #H elim (IH … H) // -H -n
  /4 width=9 by cpys_flat, nlift_flat_dx, nlift_flat_sn, ex2_intro/
]
qed-.
