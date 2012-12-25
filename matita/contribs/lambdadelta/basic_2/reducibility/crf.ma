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

include "basic_2/substitution/ldrop.ma".

(* CONTEXT-SENSITIVE REDUCIBLE TERMS ****************************************)

(* reducible binary items *)
definition ri2: item2 → Prop ≝
                λI. I = Bind2 true Abbr ∨ I = Flat2 Cast.

(* irreducible binary binders *)
definition ib2: bool → bind2 → Prop ≝
                λa,I. I = Abst ∨ Bind2 a I = Bind2 false Abbr.

(* reducible terms *)
inductive crf: lenv → predicate term ≝
| crf_delta  : ∀L,K,V,i. ⇩[0, i] L ≡ K.ⓓV → crf L (#i)
| crf_appl_sn: ∀L,V,T. crf L V → crf L (ⓐV. T)
| crf_appl_dx: ∀L,V,T. crf L T → crf L (ⓐV. T)
| crf_ri2    : ∀I,L,V,T. ri2 I → crf L (②{I}V. T)
| crf_ib2_sn : ∀a,I,L,V,T. ib2 a I → crf L V → crf L (ⓑ{a,I}V. T)
| crf_ib2_dx : ∀a,I,L,V,T. ib2 a I → crf (L.ⓑ{I}V) T → crf L (ⓑ{a,I}V. T)
| crf_beta   : ∀a,L,V,W,T. crf L (ⓐV. ⓛ{a}W. T)
| crf_theta  : ∀a,L,V,W,T. crf L (ⓐV. ⓓ{a}W. T)
.

interpretation
   "context-sensitive reducibility (term)"
   'Reducible L T = (crf L T).

(* Basic inversion lemmas ***************************************************)

fact trf_inv_atom_aux: ∀I,L,T. L ⊢ 𝐑⦃T⦄ → L = ⋆ → T = ⓪{I} → ⊥.
#I #L #T * -L -T
[ #L #K #V #i #HLK #H1 #H2 destruct
  lapply (ldrop_inv_atom1 … HLK) -HLK #H destruct
| #L #V #T #_ #_ #H destruct
| #L #V #T #_ #_ #H destruct
| #J #L #V #T #_ #_ #H destruct
| #a #J #L #V #T #_ #_ #_ #H destruct
| #a #J #L #V #T #_ #_ #_ #H destruct
| #a #L #V #W #T #_ #H destruct
| #a #L #V #W #T #_ #H destruct
]
qed.

lemma trf_inv_atom: ∀I. ⋆ ⊢ 𝐑⦃⓪{I}⦄ → ⊥.
/2 width=6/ qed-.

fact trf_inv_lref_aux: ∀L,T. L ⊢ 𝐑⦃T⦄ → ∀i. T = #i → ∃∃K,V. ⇩[0, i] L ≡ K.ⓓV.
#L #T * -L -T
[ #L #K #V #j #HLK #i #H destruct /2 width=3/
| #L #V #T #_ #i #H destruct
| #L #V #T #_ #i #H destruct
| #J #L #V #T #_ #i #H destruct
| #a #J #L #V #T #_ #_ #i #H destruct
| #a #J #L #V #T #_ #_ #i #H destruct
| #a #L #V #W #T #i #H destruct
| #a #L #V #W #T #i #H destruct
]
qed.

lemma trf_inv_lref: ∀L,i. L ⊢ 𝐑⦃#i⦄ → ∃∃K,V. ⇩[0, i] L ≡ K.ⓓV.
/2 width=3/ qed-.

fact crf_inv_ib2_aux: ∀a,I,L,W,U,T. ib2 a I → L ⊢ 𝐑⦃T⦄ → T = ⓑ{a,I}W. U →
                      L ⊢ 𝐑⦃W⦄ ∨ L.ⓑ{I}W ⊢ 𝐑⦃U⦄.
#a #I #L #W #U #T #HI * -T
[ #L #K #V #i #_ #H destruct
| #L #V #T #_ #H destruct
| #L #V #T #_ #H destruct
| #J #L #V #T #H1 #H2 destruct
  elim H1 -H1 #H destruct
  elim HI -HI #H destruct
| #b #J #L #V #T #_ #HV #H destruct /2 width=1/
| #b #J #L #V #T #_ #HT #H destruct /2 width=1/
| #b #L #V #W #T #H destruct
| #b #L #V #W #T #H destruct
]
qed.

lemma crf_inv_ib2: ∀a,I,L,W,T. ib2 a I → L ⊢ 𝐑⦃ⓑ{a,I}W.T⦄ →
                   L ⊢ 𝐑⦃W⦄ ∨ L.ⓑ{I}W ⊢ 𝐑⦃T⦄.
/2 width=5/ qed-.

fact crf_inv_appl_aux: ∀L,W,U,T. L ⊢ 𝐑⦃T⦄ → T = ⓐW. U →
                       ∨∨ L ⊢ 𝐑⦃W⦄ | L ⊢ 𝐑⦃U⦄ | (𝐒⦃U⦄ → ⊥).
#L #W #U #T * -T
[ #L #K #V #i #_ #H destruct
| #L #V #T #HV #H destruct /2 width=1/
| #L #V #T #HT #H destruct /2 width=1/
| #J #L #V #T #H1 #H2 destruct
  elim H1 -H1 #H destruct
| #a #I #L #V #T #_ #_ #H destruct
| #a #I #L #V #T #_ #_ #H destruct
| #a #L #V #W0 #T #H destruct
  @or3_intro2 #H elim (simple_inv_bind … H)
| #a #L #V #W0 #T #H destruct
  @or3_intro2 #H elim (simple_inv_bind … H)
]
qed.

lemma crf_inv_appl: ∀L,V,T. L ⊢ 𝐑⦃ⓐV.T⦄ → ∨∨ L ⊢ 𝐑⦃V⦄ | L ⊢ 𝐑⦃T⦄ | (𝐒⦃T⦄ → ⊥).
/2 width=3/ qed-.
