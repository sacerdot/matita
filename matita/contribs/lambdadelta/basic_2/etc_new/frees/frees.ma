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

inductive frees: relation4 ynat lenv term ynat ≝
| frees_eq: ∀L,U,l,i. (∀T. ⬆[i, 1] T ≡ U → ⊥) → frees l L U i
| frees_be: ∀I,L,K,U,W,l,i,j. l ≤ yinj j → yinj j < i →
            (∀T. ⬆[j, 1] T ≡ U → ⊥) → ⬇[j]L ≡ K.ⓑ{I}W →
            frees 0 K W (⫰(i-j)) → frees l L U i.

interpretation
   "context-sensitive free variables (term)"
   'FreeStar L i l U = (frees l L U i).

definition frees_trans: predicate (relation3 lenv term term) ≝
                        λR. ∀L,U1,U2,i. R L U1 U2 → L ⊢ i ϵ 𝐅*[0]⦃U2⦄ → L ⊢ i ϵ 𝐅*[0]⦃U1⦄.

(* Basic inversion lemmas ***************************************************)

lemma frees_inv: ∀L,U,l,i. L ⊢ i ϵ 𝐅*[l]⦃U⦄ →
                 (∀T. ⬆[i, 1] T ≡ U → ⊥) ∨
                 ∃∃I,K,W,j. l ≤ yinj j & j < i & (∀T. ⬆[j, 1] T ≡ U → ⊥) &
                            ⬇[j]L ≡ K.ⓑ{I}W & K ⊢ ⫰(i-j) ϵ 𝐅*[yinj 0]⦃W⦄.
#L #U #l #i * -L -U -l -i /4 width=9 by ex5_4_intro, or_intror, or_introl/
qed-.

lemma frees_inv_sort: ∀L,l,i,k. L ⊢ i ϵ 𝐅*[l]⦃⋆k⦄ → ⊥.
#L #l #i #k #H elim (frees_inv … H) -H [|*] /2 width=2 by/
qed-.

lemma frees_inv_gref: ∀L,l,i,p. L ⊢ i ϵ 𝐅*[l]⦃§p⦄ → ⊥.
#L #l #i #p #H elim (frees_inv … H) -H [|*] /2 width=2 by/
qed-.

lemma frees_inv_lref: ∀L,l,j,i. L ⊢ i ϵ 𝐅*[l]⦃#j⦄ →
                      yinj j = i ∨
                      ∃∃I,K,W. l ≤ yinj j & yinj j < i & ⬇[j] L ≡ K.ⓑ{I}W & K ⊢ ⫰(i-j) ϵ 𝐅*[yinj 0]⦃W⦄.
#L #l #x #i #H elim (frees_inv … H) -H
[ /4 width=2 by nlift_inv_lref_be_SO, or_introl/
| * #I #K #W #j #Hlj #Hji #Hnx #HLK #HW
  lapply (nlift_inv_lref_be_SO … Hnx) -Hnx #H
  lapply (yinj_inj … H) -H #H destruct
  /3 width=5 by ex4_3_intro, or_intror/
]
qed-.

lemma frees_inv_lref_free: ∀L,l,j,i. L ⊢ i ϵ 𝐅*[l]⦃#j⦄ → |L| ≤ j → yinj j = i.
#L #l #j #i #H #Hj elim (frees_inv_lref … H) -H //
* #I #K #W #_ #_ #HLK lapply (drop_fwd_length_lt2 … HLK) -I
#H elim (lt_refl_false j) /2 width=3 by lt_to_le_to_lt/
qed-.

lemma frees_inv_lref_skip: ∀L,l,j,i. L ⊢ i ϵ 𝐅*[l]⦃#j⦄ → yinj j < l → yinj j = i.
#L #l #j #i #H #Hjl elim (frees_inv_lref … H) -H //
* #I #K #W #Hlj elim (ylt_yle_false … Hlj) -Hlj //
qed-. 

lemma frees_inv_lref_ge: ∀L,l,j,i. L ⊢ i ϵ 𝐅*[l]⦃#j⦄ → i ≤ j → yinj j = i.
#L #l #j #i #H #Hij elim (frees_inv_lref … H) -H //
* #I #K #W #_ #Hji elim (ylt_yle_false … Hji Hij)
qed-.

lemma frees_inv_lref_lt: ∀L,l,j,i.L ⊢ i ϵ 𝐅*[l]⦃#j⦄ → j < i →
                         ∃∃I,K,W. l ≤ yinj j & ⬇[j] L ≡ K.ⓑ{I}W & K ⊢ ⫰(i-j) ϵ 𝐅*[yinj 0]⦃W⦄.
#L #l #j #i #H #Hji elim (frees_inv_lref … H) -H
[ #H elim (ylt_yle_false … Hji) //
| * /2 width=5 by ex3_3_intro/
]
qed-.

lemma frees_inv_bind: ∀a,I,L,W,U,l,i. L ⊢ i ϵ 𝐅*[l]⦃ⓑ{a,I}W.U⦄ →
                      L ⊢ i ϵ 𝐅*[l]⦃W⦄ ∨ L.ⓑ{I}W ⊢ ⫯i ϵ 𝐅*[⫯l]⦃U⦄ .
#a #J #L #V #U #l #i #H elim (frees_inv … H) -H
[ #HnX elim (nlift_inv_bind … HnX) -HnX
  /4 width=2 by frees_eq, or_intror, or_introl/
| * #I #K #W #j #Hlj #Hji #HnX #HLK #HW elim (nlift_inv_bind … HnX) -HnX
  [ /4 width=9 by frees_be, or_introl/
  | #HnT @or_intror @(frees_be … HnT) -HnT
    [4: lapply (yle_succ … Hlj) // (**)
    |5: lapply (ylt_succ … Hji) // (**)
    |6: /2 width=4 by drop_drop/
    |7: <yminus_succ in HW; // (**) 
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
/4 width=7 by frees_eq, lift_inv_lref2_be, ylt_inj/ qed.

lemma frees_lref_be: ∀I,L,K,W,l,i,j. l ≤ yinj j → j < i → ⬇[j]L ≡ K.ⓑ{I}W →
                     K ⊢ ⫰(i-j) ϵ 𝐅*[0]⦃W⦄ → L ⊢ i ϵ 𝐅*[l]⦃#j⦄.
/4 width=9 by frees_be, lift_inv_lref2_be, ylt_inj/ qed.

lemma frees_bind_sn: ∀a,I,L,W,U,l,i. L ⊢ i ϵ 𝐅*[l]⦃W⦄ →
                     L ⊢ i ϵ 𝐅*[l]⦃ⓑ{a,I}W.U⦄.
#a #I #L #W #U #l #i #H elim (frees_inv … H) -H [|*]
/4 width=9 by frees_be, frees_eq, nlift_bind_sn/
qed.

lemma frees_bind_dx: ∀a,I,L,W,U,l,i. L.ⓑ{I}W ⊢ ⫯i ϵ 𝐅*[⫯l]⦃U⦄ →
                     L ⊢ i ϵ 𝐅*[l]⦃ⓑ{a,I}W.U⦄.
#a #J #L #V #U #l #i #H elim (frees_inv … H) -H
[ /4 width=9 by frees_eq, nlift_bind_dx/
| * #I #K #W #j #Hlj elim (yle_inv_succ1 … Hlj) -Hlj #Hlj
  #Hj <Hj >yminus_succ
  lapply (ylt_O … Hj) -Hj #Hj #H
  lapply (ylt_inv_succ … H) -H #Hji #HnU #HLK #HW
  @(frees_be … Hlj Hji … HW) -HW -Hlj -Hji (**) (* explicit constructor *)
  [2: #X #H lapply (nlift_bind_dx … H) /2 width=2 by/ (**)
  |3: lapply (drop_inv_drop1_lt … HLK ?) -HLK //
  |*: skip
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
                        L ⊢ i ϵ 𝐅*[0]⦃W⦄ ∨ L.ⓑ{I}W ⊢ ⫯i ϵ 𝐅*[0]⦃U⦄ .
#a #I #L #W #U #i #H elim (frees_inv_bind … H) -H
/3 width=3 by frees_weak, or_intror, or_introl/
qed-.
