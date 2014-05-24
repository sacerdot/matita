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

include "basic_2/relocation/cpy_nlift.ma".
include "basic_2/substitution/cofrees_lift.ma".

(* CONTEXT-SENSITIVE EXCLUSION FROM FREE VARIABLES **************************)

(* Alternative definition of frees_ge ***************************************)

lemma nlift_frees: ∀L,U,d,i. (∀T. ⇧[i, 1] T ≡ U → ⊥) → (L ⊢ i ~ϵ 𝐅*[d]⦃U⦄ → ⊥).
#L #U #d #i #HnTU #H elim (cofrees_fwd_lift … H) -H /2 width=2 by/
qed-.

lemma frees_inv_ge: ∀L,U,d,i. d ≤ yinj i → (L ⊢ i ~ϵ 𝐅*[d]⦃U⦄ → ⊥) →
                    (∀T. ⇧[i, 1] T ≡ U → ⊥) ∨
                    ∃∃I,K,W,j. d ≤ yinj j & j < i & ⇩[j]L ≡ K.ⓑ{I}W &
                               (K ⊢ i-j-1 ~ϵ 𝐅*[yinj 0]⦃W⦄ → ⊥) & (∀T. ⇧[j, 1] T ≡ U → ⊥).
#L #U #d #i #Hdi #H @(frees_ind … H) -U /3 width=2 by or_introl/
#U1 #U2 #HU12 #HU2 *
[ #HnU2 elim (cpy_fwd_nlift2_ge … HU12 … HnU2) -HU12 -HnU2 /3 width=2 by or_introl/
  * /5 width=9 by nlift_frees, ex5_4_intro, or_intror/
| * #I2 #K2 #W2 #j2 #Hdj2 #Hj2i #HLK2 #HnW2 #HnU2 elim (cpy_fwd_nlift2_ge … HU12 … HnU2) -HU12 -HnU2 /4 width=9 by ex5_4_intro, or_intror/
  * #I1 #K1 #W1 #j1 #Hdj1 #Hj12 #HLK1 #HnW1 #HnU1
  lapply (ldrop_conf_ge … HLK1 … HLK2 ?) -HLK2 /2 width=1 by lt_to_le/
  #HK12 lapply (ldrop_inv_drop1_lt … HK12 ?) /2 width=1 by lt_plus_to_minus_r/ -HK12
  #HK12
  @or_intror @(ex5_4_intro … HLK1 … HnU1) -HLK1 -HnU1 /2 width=3 by transitive_lt/
  @(frees_be … HK12 … HnW1) /2 width=1 by arith_k_sn/ -HK12 -HnW1
  >minus_plus in ⊢ (??(?(?%?)?)??→?); >minus_plus in ⊢ (??(?(??%)?)??→?); >arith_b1 /2 width=1 by/
]
qed-.

lemma frees_ind_ge: ∀R:relation4 ynat nat lenv term.
                    (∀d,i,L,U. d ≤ yinj i → (∀T. ⇧[i, 1] T ≡ U → ⊥) → R d i L U) →
                    (∀d,i,j,I,L,K,W,U. d ≤ yinj j → j < i → ⇩[j]L ≡ K.ⓑ{I}W → (K ⊢ i-j-1 ~ϵ 𝐅*[0]⦃W⦄ → ⊥) → (∀T. ⇧[j, 1] T ≡ U → ⊥) → R 0 (i-j-1) K W → R d i L U) →
                    ∀d,i,L,U. d ≤ yinj i → (L ⊢ i ~ϵ 𝐅*[d]⦃U⦄ → ⊥) → R d i L U.
#R #IH1 #IH2 #d #i #L #U
generalize in match d; -d generalize in match i; -i
@(f2_ind … rfw … L U) -L -U
#n #IHn #L #U #Hn #i #d #Hdi #H elim (frees_inv_ge … H) -H /3 width=2 by/
-IH1 * #I #K #W #j #Hdj #Hji #HLK #HnW #HnU destruct /4 width=12 by ldrop_fwd_rfw/
qed-.
