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

include "basic_2/notation/relations/reducible_2.ma".
include "basic_2/relocation/ldrop.ma".

(* CONTEXT-SENSITIVE REDUCIBLE TERMS ****************************************)

(* reducible binary items *)
definition ri2: predicate item2 ≝
                λI. I = Bind2 true Abbr ∨ I = Flat2 Cast.

(* irreducible binary binders *)
definition ib2: relation2 bool bind2 ≝
                λa,I. I = Abst ∨ Bind2 a I = Bind2 false Abbr.

(* reducible terms *)
inductive crr: lenv → predicate term ≝
| crr_delta  : ∀L,K,V,i. ⇩[0, i] L ≡ K.ⓓV → crr L (#i)
| crr_appl_sn: ∀L,V,T. crr L V → crr L (ⓐV.T)
| crr_appl_dx: ∀L,V,T. crr L T → crr L (ⓐV.T)
| crr_ri2    : ∀I,L,V,T. ri2 I → crr L (②{I}V.T)
| crr_ib2_sn : ∀a,I,L,V,T. ib2 a I → crr L V → crr L (ⓑ{a,I}V.T)
| crr_ib2_dx : ∀a,I,L,V,T. ib2 a I → crr (L.ⓑ{I}V) T → crr L (ⓑ{a,I}V.T)
| crr_beta   : ∀a,L,V,W,T. crr L (ⓐV. ⓛ{a}W.T)
| crr_theta  : ∀a,L,V,W,T. crr L (ⓐV. ⓓ{a}W.T)
.

interpretation
   "context-sensitive reducibility (term)"
   'Reducible L T = (crr L T).

(* Basic inversion lemmas ***************************************************)

fact crr_inv_sort_aux: ∀L,T,k. ⦃G, L⦄ ⊢ 𝐑⦃T⦄ → T = ⋆k → ⊥.
#L #T #k0 * -L -T
[ #L #K #V #i #HLK #H destruct
| #L #V #T #_ #H destruct
| #L #V #T #_ #H destruct
| #I #L #V #T #_ #H destruct
| #a #I #L #V #T #_ #_ #H destruct
| #a #I #L #V #T #_ #_ #H destruct
| #a #L #V #W #T #H destruct
| #a #L #V #W #T #H destruct
]
qed-.

lemma crr_inv_sort: ∀L,k. ⦃G, L⦄ ⊢ 𝐑⦃⋆k⦄ → ⊥.
/2 width=5 by crr_inv_sort_aux/ qed-.

fact crr_inv_lref_aux: ∀L,T,i. ⦃G, L⦄ ⊢ 𝐑⦃T⦄ → T = #i → ∃∃K,V. ⇩[0, i] L ≡ K.ⓓV.
#L #T #j * -L -T
[ #L #K #V #i #HLK #H destruct /2 width=3/
| #L #V #T #_ #H destruct
| #L #V #T #_ #H destruct
| #I #L #V #T #_ #H destruct
| #a #I #L #V #T #_ #_ #H destruct
| #a #I #L #V #T #_ #_ #H destruct
| #a #L #V #W #T #H destruct
| #a #L #V #W #T #H destruct
]
qed-.

lemma crr_inv_lref: ∀L,i. ⦃G, L⦄ ⊢ 𝐑⦃#i⦄ → ∃∃K,V. ⇩[0, i] L ≡ K.ⓓV.
/2 width=3 by crr_inv_lref_aux/ qed-.

fact crr_inv_gref_aux: ∀L,T,p. ⦃G, L⦄ ⊢ 𝐑⦃T⦄ → T = §p → ⊥.
#L #T #q * -L -T
[ #L #K #V #i #HLK #H destruct
| #L #V #T #_ #H destruct
| #L #V #T #_ #H destruct
| #I #L #V #T #_ #H destruct
| #a #I #L #V #T #_ #_ #H destruct
| #a #I #L #V #T #_ #_ #H destruct
| #a #L #V #W #T #H destruct
| #a #L #V #W #T #H destruct
]
qed-.

lemma crr_inv_gref: ∀L,p. ⦃G, L⦄ ⊢ 𝐑⦃§p⦄ → ⊥.
/2 width=5 by crr_inv_gref_aux/ qed-.

lemma trr_inv_atom: ∀I. ⋆ ⊢ 𝐑⦃⓪{I}⦄ → ⊥.
* #i #H
[ elim (crr_inv_sort … H)
| elim (crr_inv_lref … H) -H #L #V #H
  elim (ldrop_inv_atom1 … H) -H #H destruct
| elim (crr_inv_gref … H)
]
qed-.

fact crr_inv_ib2_aux: ∀a,I,L,W,U,T. ib2 a I → ⦃G, L⦄ ⊢ 𝐑⦃T⦄ → T = ⓑ{a,I}W.U →
                      ⦃G, L⦄ ⊢ 𝐑⦃W⦄ ∨ L.ⓑ{I}W ⊢ 𝐑⦃U⦄.
#b #J #L #W0 #U #T #HI * -L -T
[ #L #K #V #i #_ #H destruct
| #L #V #T #_ #H destruct
| #L #V #T #_ #H destruct
| #I #L #V #T #H1 #H2 destruct
  elim H1 -H1 #H destruct
  elim HI -HI #H destruct
| #a #I #L #V #T #_ #HV #H destruct /2 width=1/
| #a #I #L #V #T #_ #HT #H destruct /2 width=1/
| #a #L #V #W #T #H destruct
| #a #L #V #W #T #H destruct
]
qed-.

lemma crr_inv_ib2: ∀a,I,L,W,T. ib2 a I → ⦃G, L⦄ ⊢ 𝐑⦃ⓑ{a,I}W.T⦄ →
                   ⦃G, L⦄ ⊢ 𝐑⦃W⦄ ∨ L.ⓑ{I}W ⊢ 𝐑⦃T⦄.
/2 width=5 by crr_inv_ib2_aux/ qed-.

fact crr_inv_appl_aux: ∀L,W,U,T. ⦃G, L⦄ ⊢ 𝐑⦃T⦄ → T = ⓐW.U →
                       ∨∨ ⦃G, L⦄ ⊢ 𝐑⦃W⦄ | ⦃G, L⦄ ⊢ 𝐑⦃U⦄ | (𝐒⦃U⦄ → ⊥).
#L #W0 #U #T * -L -T
[ #L #K #V #i #_ #H destruct
| #L #V #T #HV #H destruct /2 width=1/
| #L #V #T #HT #H destruct /2 width=1/
| #I #L #V #T #H1 #H2 destruct
  elim H1 -H1 #H destruct
| #a #I #L #V #T #_ #_ #H destruct
| #a #I #L #V #T #_ #_ #H destruct
| #a #L #V #W #T #H destruct
  @or3_intro2 #H elim (simple_inv_bind … H)
| #a #L #V #W #T #H destruct
  @or3_intro2 #H elim (simple_inv_bind … H)
]
qed-.

lemma crr_inv_appl: ∀L,V,T. ⦃G, L⦄ ⊢ 𝐑⦃ⓐV.T⦄ → ∨∨ ⦃G, L⦄ ⊢ 𝐑⦃V⦄ | ⦃G, L⦄ ⊢ 𝐑⦃T⦄ | (𝐒⦃T⦄ → ⊥).
/2 width=3 by crr_inv_appl_aux/ qed-.
