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

include "ground_2A/ynat/ynat_plus.ma".
include "basic_2A/notation/relations/freestar_4.ma".
include "basic_2A/substitution/lift_neg.ma".
include "basic_2A/substitution/drop.ma".

(* CONTEXT-SENSITIVE FREE VARIABLES *****************************************)

inductive frees: relation4 ynat lenv term nat ≝
| frees_eq: ∀L,U,l,i. (∀T. ⬆[i, 1] T ≡ U → ⊥) → frees l L U i
| frees_be: ∀I,L,K,U,W,l,i,j. l ≤ yinj j → j < i →
            (∀T. ⬆[j, 1] T ≡ U → ⊥) → ⬇[j]L ≡ K.ⓑ{I}W →
            frees 0 K W (i-j-1) → frees l L U i.

interpretation
   "context-sensitive free variables (term)"
   'FreeStar L i l U = (frees l L U i).

definition frees_trans: predicate (relation3 lenv term term) ≝
                        λR. ∀L,U1,U2,i. R L U1 U2 → L ⊢ i ϵ 𝐅*[0]⦃U2⦄ → L ⊢ i ϵ 𝐅*[0]⦃U1⦄.

(* Basic inversion lemmas ***************************************************)

lemma frees_inv: ∀L,U,l,i. L ⊢ i ϵ 𝐅*[l]⦃U⦄ →
                 (∀T. ⬆[i, 1] T ≡ U → ⊥) ∨
                 ∃∃I,K,W,j. l ≤ yinj j & j < i & (∀T. ⬆[j, 1] T ≡ U → ⊥) &
                            ⬇[j]L ≡ K.ⓑ{I}W & K ⊢ (i-j-1) ϵ 𝐅*[yinj 0]⦃W⦄.
#L #U #l #i * -L -U -l -i /4 width=9 by ex5_4_intro, or_intror, or_introl/
qed-.

lemma frees_inv_sort: ∀L,l,i,k. L ⊢ i ϵ 𝐅*[l]⦃⋆k⦄ → ⊥.
#L #l #i #k #H elim (frees_inv … H) -H [|*] /2 width=2 by/
qed-.

lemma frees_inv_gref: ∀L,l,i,p. L ⊢ i ϵ 𝐅*[l]⦃§p⦄ → ⊥.
#L #l #i #p #H elim (frees_inv … H) -H [|*] /2 width=2 by/
qed-.

lemma frees_inv_lref: ∀L,l,j,i. L ⊢ i ϵ 𝐅*[l]⦃#j⦄ →
                      j = i ∨
                      ∃∃I,K,W. l ≤ yinj j & j < i & ⬇[j] L ≡ K.ⓑ{I}W & K ⊢ (i-j-1) ϵ 𝐅*[yinj 0]⦃W⦄.
#L #l #x #i #H elim (frees_inv … H) -H
[ /4 width=2 by nlift_inv_lref_be_SO, or_introl/
| * #I #K #W #j #Hlj #Hji #Hnx #HLK #HW
  >(nlift_inv_lref_be_SO … Hnx) -x /3 width=5 by ex4_3_intro, or_intror/
]
qed-.

lemma frees_inv_lref_free: ∀L,l,j,i. L ⊢ i ϵ 𝐅*[l]⦃#j⦄ → |L| ≤ j → j = i.
#L #l #j #i #H #Hj elim (frees_inv_lref … H) -H //
* #I #K #W #_ #_ #HLK lapply (drop_fwd_length_lt2 … HLK) -I
#H elim (lt_refl_false j) /2 width=3 by lt_to_le_to_lt/
qed-.

lemma frees_inv_lref_skip: ∀L,l,j,i. L ⊢ i ϵ 𝐅*[l]⦃#j⦄ → yinj j < l → j = i.
#L #l #j #i #H #Hjl elim (frees_inv_lref … H) -H //
* #I #K #W #Hlj elim (ylt_yle_false … Hlj) -Hlj //
qed-. 

lemma frees_inv_lref_ge: ∀L,l,j,i. L ⊢ i ϵ 𝐅*[l]⦃#j⦄ → i ≤ j → j = i.
#L #l #j #i #H #Hij elim (frees_inv_lref … H) -H //
* #I #K #W #_ #Hji elim (lt_refl_false j) -I -L -K -W -l /2 width=3 by lt_to_le_to_lt/
qed-.

lemma frees_inv_lref_lt: ∀L,l,j,i.L ⊢ i ϵ 𝐅*[l]⦃#j⦄ → j < i →
                         ∃∃I,K,W. l ≤ yinj j & ⬇[j] L ≡ K.ⓑ{I}W & K ⊢ (i-j-1) ϵ 𝐅*[yinj 0]⦃W⦄.
#L #l #j #i #H #Hji elim (frees_inv_lref … H) -H
[ #H elim (lt_refl_false j) //
| * /2 width=5 by ex3_3_intro/
]
qed-.

lemma frees_inv_bind: ∀a,I,L,W,U,l,i. L ⊢ i ϵ 𝐅*[l]⦃ⓑ{a,I}W.U⦄ →
                      L ⊢ i ϵ 𝐅*[l]⦃W⦄ ∨ L.ⓑ{I}W ⊢ i+1 ϵ 𝐅*[⫯l]⦃U⦄ .
#a #J #L #V #U #l #i #H elim (frees_inv … H) -H
[ #HnX elim (nlift_inv_bind … HnX) -HnX
  /4 width=2 by frees_eq, or_intror, or_introl/
| * #I #K #W #j #Hlj #Hji #HnX #HLK #HW elim (nlift_inv_bind … HnX) -HnX
  [ /4 width=9 by frees_be, or_introl/
  | #HnT @or_intror @(frees_be … HnT) -HnT
    [4,5,6: /2 width=1 by drop_drop, yle_succ, lt_minus_to_plus/
    |7: >minus_plus_plus_l //
    |*: skip
    ]
  ]
]
qed-.

lemma frees_inv_flat: ∀I,L,W,U,l,i. L ⊢ i ϵ 𝐅*[l]⦃ⓕ{I}W.U⦄ →
                      L ⊢ i ϵ 𝐅*[l]⦃W⦄ ∨ L ⊢ i ϵ 𝐅*[l]⦃U⦄ .
#J #L #V #U #l #i #H elim (frees_inv … H) -H
[ #HnX elim (nlift_inv_flat … HnX) -HnX
  /4 width=2 by frees_eq, or_intror, or_introl/
| * #I #K #W #j #Hlj #Hji #HnX #HLK #HW elim (nlift_inv_flat … HnX) -HnX
  /4 width=9 by frees_be, or_intror, or_introl/
]
qed-.

(* Basic properties *********************************************************)

lemma frees_lref_eq: ∀L,l,i. L ⊢ i ϵ 𝐅*[l]⦃#i⦄.
/3 width=7 by frees_eq, lift_inv_lref2_be/ qed.

lemma frees_lref_be: ∀I,L,K,W,l,i,j. l ≤ yinj j → j < i → ⬇[j]L ≡ K.ⓑ{I}W →
                     K ⊢ i-j-1 ϵ 𝐅*[0]⦃W⦄ → L ⊢ i ϵ 𝐅*[l]⦃#j⦄.
/3 width=9 by frees_be, lift_inv_lref2_be/ qed.

lemma frees_bind_sn: ∀a,I,L,W,U,l,i. L ⊢ i ϵ 𝐅*[l]⦃W⦄ →
                     L ⊢ i ϵ 𝐅*[l]⦃ⓑ{a,I}W.U⦄.
#a #I #L #W #U #l #i #H elim (frees_inv … H) -H [|*]
/4 width=9 by frees_be, frees_eq, nlift_bind_sn/
qed.

lemma frees_bind_dx: ∀a,I,L,W,U,l,i. L.ⓑ{I}W ⊢ i+1 ϵ 𝐅*[⫯l]⦃U⦄ →
                     L ⊢ i ϵ 𝐅*[l]⦃ⓑ{a,I}W.U⦄.
#a #J #L #V #U #l #i #H elim (frees_inv … H) -H
[ /4 width=9 by frees_eq, nlift_bind_dx/
| * #I #K #W #j #Hlj #Hji #HnU #HLK #HW
  elim (yle_inv_succ1 … Hlj) -Hlj <yminus_SO2 #Hyj #H
  lapply (ylt_O … H) -H #Hj
  >(plus_minus_m_m j 1) in HnU; // <minus_le_minus_minus_comm in HW;
  /4 width=9 by frees_be, nlift_bind_dx, drop_inv_drop1_lt, lt_plus_to_minus/
]
qed.

lemma frees_flat_sn: ∀I,L,W,U,l,i. L ⊢ i ϵ 𝐅*[l]⦃W⦄ →
                     L ⊢ i ϵ 𝐅*[l]⦃ⓕ{I}W.U⦄.
#I #L #W #U #l #i #H elim (frees_inv … H) -H [|*]
/4 width=9 by frees_be, frees_eq, nlift_flat_sn/
qed.

lemma frees_flat_dx: ∀I,L,W,U,l,i. L ⊢ i ϵ 𝐅*[l]⦃U⦄ →
                     L ⊢ i ϵ 𝐅*[l]⦃ⓕ{I}W.U⦄.
#I #L #W #U #l #i #H elim (frees_inv … H) -H [|*]
/4 width=9 by frees_be, frees_eq, nlift_flat_dx/
qed.

lemma frees_weak: ∀L,U,l1,i. L ⊢ i ϵ 𝐅*[l1]⦃U⦄ →
                  ∀l2. l2 ≤ l1 → L ⊢ i ϵ 𝐅*[l2]⦃U⦄.
#L #U #l1 #i #H elim H -L -U -l1 -i
/3 width=9 by frees_be, frees_eq, yle_trans/
qed-.

(* Advanced inversion lemmas ************************************************)

lemma frees_inv_bind_O: ∀a,I,L,W,U,i. L ⊢ i ϵ 𝐅*[0]⦃ⓑ{a,I}W.U⦄ →
                        L ⊢ i ϵ 𝐅*[0]⦃W⦄ ∨ L.ⓑ{I}W ⊢ i+1 ϵ 𝐅*[0]⦃U⦄ .
#a #I #L #W #U #i #H elim (frees_inv_bind … H) -H
/3 width=3 by frees_weak, or_intror, or_introl/
qed-.
