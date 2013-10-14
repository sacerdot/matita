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

include "basic_2/notation/relations/reducible_5.ma".
include "basic_2/static/sd.ma".
include "basic_2/reduction/crr.ma".

(* CONTEXT-SENSITIVE EXTENDED REDUCIBLE TERMS *******************************)

(* activate genv *)
(* extended reducible terms *)
inductive crx (h) (g) (G:genv): relation2 lenv term ≝
| crx_sort   : ∀L,k,l. deg h g k (l+1) → crx h g G L (⋆k)
| crx_delta  : ∀I,L,K,V,i. ⇩[0, i] L ≡ K.ⓑ{I}V → crx h g G L (#i)
| crx_appl_sn: ∀L,V,T. crx h g G L V → crx h g G L (ⓐV.T)
| crx_appl_dx: ∀L,V,T. crx h g G L T → crx h g G L (ⓐV.T)
| crx_ri2    : ∀I,L,V,T. ri2 I → crx h g G L (②{I}V.T)
| crx_ib2_sn : ∀a,I,L,V,T. ib2 a I → crx h g G L V → crx h g G L (ⓑ{a,I}V.T)
| crx_ib2_dx : ∀a,I,L,V,T. ib2 a I → crx h g G (L.ⓑ{I}V) T → crx h g G L (ⓑ{a,I}V.T)
| crx_beta   : ∀a,L,V,W,T. crx h g G L (ⓐV. ⓛ{a}W.T)
| crx_theta  : ∀a,L,V,W,T. crx h g G L (ⓐV. ⓓ{a}W.T)
.

interpretation
   "context-sensitive extended reducibility (term)"
   'Reducible h g G L T = (crx h g G L T).

(* Basic properties *********************************************************)

lemma crr_crx: ∀h,g,G,L,T. ⦃G, L⦄ ⊢ 𝐑⦃T⦄ → ⦃G, L⦄ ⊢ 𝐑[h, g]⦃T⦄.
#h #g #G #L #T #H elim H -L -T // /2 width=1/ /2 width=4/
qed.

(* Basic inversion lemmas ***************************************************)

fact crx_inv_sort_aux: ∀h,g,G,L,T,k. ⦃G, L⦄ ⊢ 𝐑[h, g]⦃T⦄ → T = ⋆k →
                       ∃l. deg h g k (l+1).
#h #g #G #L #T #k0 * -L -T
[ #L #k #l #Hkl #H destruct /2 width=2/
| #I #L #K #V #i #HLK #H destruct
| #L #V #T #_ #H destruct
| #L #V #T #_ #H destruct
| #I #L #V #T #_ #H destruct
| #a #I #L #V #T #_ #_ #H destruct
| #a #I #L #V #T #_ #_ #H destruct
| #a #L #V #W #T #H destruct
| #a #L #V #W #T #H destruct
]
qed-.

lemma crx_inv_sort: ∀h,g,G,L,k. ⦃G, L⦄ ⊢ 𝐑[h, g]⦃⋆k⦄ → ∃l. deg h g k (l+1).
/2 width=5 by crx_inv_sort_aux/ qed-.

fact crx_inv_lref_aux: ∀h,g,G,L,T,i. ⦃G, L⦄ ⊢ 𝐑[h, g]⦃T⦄ → T = #i →
                       ∃∃I,K,V. ⇩[0, i] L ≡ K.ⓑ{I}V.
#h #g #G #L #T #j * -L -T
[ #L #k #l #_ #H destruct
| #I #L #K #V #i #HLK #H destruct /2 width=4/
| #L #V #T #_ #H destruct
| #L #V #T #_ #H destruct
| #I #L #V #T #_ #H destruct
| #a #I #L #V #T #_ #_ #H destruct
| #a #I #L #V #T #_ #_ #H destruct
| #a #L #V #W #T #H destruct
| #a #L #V #W #T #H destruct
]
qed-.

lemma crx_inv_lref: ∀h,g,G,L,i. ⦃G, L⦄ ⊢ 𝐑[h, g]⦃#i⦄ → ∃∃I,K,V. ⇩[0, i] L ≡ K.ⓑ{I}V.
/2 width=6 by crx_inv_lref_aux/ qed-.

fact crx_inv_gref_aux: ∀h,g,G,L,T,p. ⦃G, L⦄ ⊢ 𝐑[h, g]⦃T⦄ → T = §p → ⊥.
#h #g #G #L #T #q * -L -T
[ #L #k #l #_ #H destruct
| #I #L #K #V #i #HLK #H destruct
| #L #V #T #_ #H destruct
| #L #V #T #_ #H destruct
| #I #L #V #T #_ #H destruct
| #a #I #L #V #T #_ #_ #H destruct
| #a #I #L #V #T #_ #_ #H destruct
| #a #L #V #W #T #H destruct
| #a #L #V #W #T #H destruct
]
qed-.

lemma crx_inv_gref: ∀h,g,G,L,p. ⦃G, L⦄ ⊢ 𝐑[h, g]⦃§p⦄ → ⊥.
/2 width=8 by crx_inv_gref_aux/ qed-.

lemma trx_inv_atom: ∀h,g,I,G. ⦃G, ⋆⦄ ⊢ 𝐑[h, g]⦃⓪{I}⦄ →
                    ∃∃k,l. deg h g k (l+1) & I = Sort k.
#h #g * #i #G #H
[ elim (crx_inv_sort … H) -H /2 width=4/
| elim (crx_inv_lref … H) -H #I #L #V #H
  elim (ldrop_inv_atom1 … H) -H #H destruct
| elim (crx_inv_gref … H)
]
qed-.

fact crx_inv_ib2_aux: ∀h,g,a,I,G,L,W,U,T. ib2 a I → ⦃G, L⦄ ⊢ 𝐑[h, g]⦃T⦄ →
                      T = ⓑ{a,I}W.U → ⦃G, L⦄ ⊢ 𝐑[h, g]⦃W⦄ ∨ ⦃G, L.ⓑ{I}W⦄ ⊢ 𝐑[h, g]⦃U⦄.
#h #g #b #J #G #L #W0 #U #T #HI * -L -T
[ #L #k #l #_ #H destruct
| #I #L #K #V #i #_ #H destruct
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

lemma crx_inv_ib2: ∀h,g,a,I,G,L,W,T. ib2 a I → ⦃G, L⦄ ⊢ 𝐑[h, g]⦃ⓑ{a,I}W.T⦄ →
                   ⦃G, L⦄ ⊢ 𝐑[h, g]⦃W⦄ ∨ ⦃G, L.ⓑ{I}W⦄ ⊢ 𝐑[h, g]⦃T⦄.
/2 width=5 by crx_inv_ib2_aux/ qed-.

fact crx_inv_appl_aux: ∀h,g,G,L,W,U,T. ⦃G, L⦄ ⊢ 𝐑[h, g]⦃T⦄ → T = ⓐW.U →
                       ∨∨ ⦃G, L⦄ ⊢ 𝐑[h, g]⦃W⦄ | ⦃G, L⦄ ⊢ 𝐑[h, g]⦃U⦄ | (𝐒⦃U⦄ → ⊥).
#h #g #G #L #W0 #U #T * -L -T
[ #L #k #l #_ #H destruct
| #I #L #K #V #i #_ #H destruct
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

lemma crx_inv_appl: ∀h,g,G,L,V,T. ⦃G, L⦄ ⊢ 𝐑[h, g]⦃ⓐV.T⦄ →
                    ∨∨ ⦃G, L⦄ ⊢ 𝐑[h, g]⦃V⦄ | ⦃G, L⦄ ⊢ 𝐑[h, g]⦃T⦄ | (𝐒⦃T⦄ → ⊥).
/2 width=3 by crx_inv_appl_aux/ qed-.