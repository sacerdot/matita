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

include "ground_2/ynat/ynat_plus.ma".
include "basic_2/notation/relations/freestar_4.ma".
include "basic_2/substitution/lift_neg.ma".
include "basic_2/substitution/drop.ma".

(* CONTEXT-SENSITIVE FREE VARIABLES *****************************************)

inductive frees: relation4 ynat lenv term nat ≝
| frees_eq: ∀L,U,d,i. (∀T. ⇧[i, 1] T ≡ U → ⊥) → frees d L U i
| frees_be: ∀I,L,K,U,W,d,i,j. d ≤ yinj j → j < i →
            (∀T. ⇧[j, 1] T ≡ U → ⊥) → ⇩[j]L ≡ K.ⓑ{I}W →
            frees 0 K W (i-j-1) → frees d L U i.

interpretation
   "context-sensitive free variables (term)"
   'FreeStar L i d U = (frees d L U i).

definition frees_trans: predicate (relation3 lenv term term) ≝
                        λR. ∀L,U1,U2,i. R L U1 U2 → L ⊢ i ϵ 𝐅*[0]⦃U2⦄ → L ⊢ i ϵ 𝐅*[0]⦃U1⦄.

(* Basic inversion lemmas ***************************************************)

lemma frees_inv: ∀L,U,d,i. L ⊢ i ϵ 𝐅*[d]⦃U⦄ →
                 (∀T. ⇧[i, 1] T ≡ U → ⊥) ∨
                 ∃∃I,K,W,j. d ≤ yinj j & j < i & (∀T. ⇧[j, 1] T ≡ U → ⊥) &
                            ⇩[j]L ≡ K.ⓑ{I}W & K ⊢ (i-j-1) ϵ 𝐅*[yinj 0]⦃W⦄.
#L #U #d #i * -L -U -d -i /4 width=9 by ex5_4_intro, or_intror, or_introl/
qed-.

lemma frees_inv_sort: ∀L,d,i,k. L ⊢ i ϵ 𝐅*[d]⦃⋆k⦄ → ⊥.
#L #d #i #k #H elim (frees_inv … H) -H [|*] /2 width=2 by/
qed-.

lemma frees_inv_gref: ∀L,d,i,p. L ⊢ i ϵ 𝐅*[d]⦃§p⦄ → ⊥.
#L #d #i #p #H elim (frees_inv … H) -H [|*] /2 width=2 by/
qed-.

lemma frees_inv_lref: ∀L,d,j,i. L ⊢ i ϵ 𝐅*[d]⦃#j⦄ →
                      j = i ∨
                      ∃∃I,K,W. d ≤ yinj j & j < i & ⇩[j] L ≡ K.ⓑ{I}W & K ⊢ (i-j-1) ϵ 𝐅*[yinj 0]⦃W⦄.
#L #d #x #i #H elim (frees_inv … H) -H
[ /4 width=2 by nlift_inv_lref_be_SO, or_introl/
| * #I #K #W #j #Hdj #Hji #Hnx #HLK #HW
  >(nlift_inv_lref_be_SO … Hnx) -x /3 width=5 by ex4_3_intro, or_intror/
]
qed-.

lemma frees_inv_lref_free: ∀L,d,j,i. L ⊢ i ϵ 𝐅*[d]⦃#j⦄ → |L| ≤ j → j = i.
#L #d #j #i #H #Hj elim (frees_inv_lref … H) -H //
* #I #K #W #_ #_ #HLK lapply (drop_fwd_length_lt2 … HLK) -I
#H elim (lt_refl_false j) /2 width=3 by lt_to_le_to_lt/
qed-.

lemma frees_inv_lref_skip: ∀L,d,j,i. L ⊢ i ϵ 𝐅*[d]⦃#j⦄ → yinj j < d → j = i.
#L #d #j #i #H #Hjd elim (frees_inv_lref … H) -H //
* #I #K #W #Hdj elim (ylt_yle_false … Hdj) -Hdj //
qed-. 

lemma frees_inv_lref_ge: ∀L,d,j,i. L ⊢ i ϵ 𝐅*[d]⦃#j⦄ → i ≤ j → j = i.
#L #d #j #i #H #Hij elim (frees_inv_lref … H) -H //
* #I #K #W #_ #Hji elim (lt_refl_false j) -I -L -K -W -d /2 width=3 by lt_to_le_to_lt/
qed-.

lemma frees_inv_lref_lt: ∀L,d,j,i.L ⊢ i ϵ 𝐅*[d]⦃#j⦄ → j < i →
                         ∃∃I,K,W. d ≤ yinj j & ⇩[j] L ≡ K.ⓑ{I}W & K ⊢ (i-j-1) ϵ 𝐅*[yinj 0]⦃W⦄.
#L #d #j #i #H #Hji elim (frees_inv_lref … H) -H
[ #H elim (lt_refl_false j) //
| * /2 width=5 by ex3_3_intro/
]
qed-.

lemma frees_inv_bind: ∀a,I,L,W,U,d,i. L ⊢ i ϵ 𝐅*[d]⦃ⓑ{a,I}W.U⦄ →
                      L ⊢ i ϵ 𝐅*[d]⦃W⦄ ∨ L.ⓑ{I}W ⊢ i+1 ϵ 𝐅*[⫯d]⦃U⦄ .
#a #J #L #V #U #d #i #H elim (frees_inv … H) -H
[ #HnX elim (nlift_inv_bind … HnX) -HnX
  /4 width=2 by frees_eq, or_intror, or_introl/
| * #I #K #W #j #Hdj #Hji #HnX #HLK #HW elim (nlift_inv_bind … HnX) -HnX
  [ /4 width=9 by frees_be, or_introl/
  | #HnT @or_intror @(frees_be … HnT) -HnT
    [4,5,6: /2 width=1 by drop_drop, yle_succ, lt_minus_to_plus/
    |7: >minus_plus_plus_l //
    |*: skip
    ]
  ]
]
qed-.

lemma frees_inv_flat: ∀I,L,W,U,d,i. L ⊢ i ϵ 𝐅*[d]⦃ⓕ{I}W.U⦄ →
                      L ⊢ i ϵ 𝐅*[d]⦃W⦄ ∨ L ⊢ i ϵ 𝐅*[d]⦃U⦄ .
#J #L #V #U #d #i #H elim (frees_inv … H) -H
[ #HnX elim (nlift_inv_flat … HnX) -HnX
  /4 width=2 by frees_eq, or_intror, or_introl/
| * #I #K #W #j #Hdj #Hji #HnX #HLK #HW elim (nlift_inv_flat … HnX) -HnX
  /4 width=9 by frees_be, or_intror, or_introl/
]
qed-.

(* Basic properties *********************************************************)

lemma frees_lref_eq: ∀L,d,i. L ⊢ i ϵ 𝐅*[d]⦃#i⦄.
/3 width=7 by frees_eq, lift_inv_lref2_be/ qed.

lemma frees_lref_be: ∀I,L,K,W,d,i,j. d ≤ yinj j → j < i → ⇩[j]L ≡ K.ⓑ{I}W →
                     K ⊢ i-j-1 ϵ 𝐅*[0]⦃W⦄ → L ⊢ i ϵ 𝐅*[d]⦃#j⦄.
/3 width=9 by frees_be, lift_inv_lref2_be/ qed.

lemma frees_bind_sn: ∀a,I,L,W,U,d,i. L ⊢ i ϵ 𝐅*[d]⦃W⦄ →
                     L ⊢ i ϵ 𝐅*[d]⦃ⓑ{a,I}W.U⦄.
#a #I #L #W #U #d #i #H elim (frees_inv … H) -H [|*]
/4 width=9 by frees_be, frees_eq, nlift_bind_sn/
qed.

lemma frees_bind_dx: ∀a,I,L,W,U,d,i. L.ⓑ{I}W ⊢ i+1 ϵ 𝐅*[⫯d]⦃U⦄ →
                     L ⊢ i ϵ 𝐅*[d]⦃ⓑ{a,I}W.U⦄.
#a #J #L #V #U #d #i #H elim (frees_inv … H) -H
[ /4 width=9 by frees_eq, nlift_bind_dx/
| * #I #K #W #j #Hdj #Hji #HnU #HLK #HW
  elim (yle_inv_succ1 … Hdj) -Hdj <yminus_SO2 #Hyj #H
  lapply (ylt_O … H) -H #Hj
  >(plus_minus_m_m j 1) in HnU; // <minus_le_minus_minus_comm in HW;
  /4 width=9 by frees_be, nlift_bind_dx, drop_inv_drop1_lt, lt_plus_to_minus/
]
qed.

lemma frees_flat_sn: ∀I,L,W,U,d,i. L ⊢ i ϵ 𝐅*[d]⦃W⦄ →
                     L ⊢ i ϵ 𝐅*[d]⦃ⓕ{I}W.U⦄.
#I #L #W #U #d #i #H elim (frees_inv … H) -H [|*]
/4 width=9 by frees_be, frees_eq, nlift_flat_sn/
qed.

lemma frees_flat_dx: ∀I,L,W,U,d,i. L ⊢ i ϵ 𝐅*[d]⦃U⦄ →
                     L ⊢ i ϵ 𝐅*[d]⦃ⓕ{I}W.U⦄.
#I #L #W #U #d #i #H elim (frees_inv … H) -H [|*]
/4 width=9 by frees_be, frees_eq, nlift_flat_dx/
qed.

lemma frees_weak: ∀L,U,d1,i. L ⊢ i ϵ 𝐅*[d1]⦃U⦄ →
                  ∀d2. d2 ≤ d1 → L ⊢ i ϵ 𝐅*[d2]⦃U⦄.
#L #U #d1 #i #H elim H -L -U -d1 -i
/3 width=9 by frees_be, frees_eq, yle_trans/
qed-.

(* Advanced inversion lemmas ************************************************)

lemma frees_inv_bind_O: ∀a,I,L,W,U,i. L ⊢ i ϵ 𝐅*[0]⦃ⓑ{a,I}W.U⦄ →
                        L ⊢ i ϵ 𝐅*[0]⦃W⦄ ∨ L.ⓑ{I}W ⊢ i+1 ϵ 𝐅*[0]⦃U⦄ .
#a #I #L #W #U #i #H elim (frees_inv_bind … H) -H
/3 width=3 by frees_weak, or_intror, or_introl/
qed-.
