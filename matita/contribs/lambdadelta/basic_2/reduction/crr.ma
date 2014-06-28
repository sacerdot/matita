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

include "basic_2/notation/relations/predreducible_3.ma".
include "basic_2/grammar/genv.ma".
include "basic_2/substitution/drop.ma".

(* REDUCIBLE TERMS FOR CONTEXT-SENSITIVE REDUCTION **************************)

(* reducible binary items *)
definition ri2: predicate item2 ≝
                λI. I = Bind2 true Abbr ∨ I = Flat2 Cast.

(* irreducible binary binders *)
definition ib2: relation2 bool bind2 ≝
                λa,I. I = Abst ∨ Bind2 a I = Bind2 false Abbr.

(* activate genv *)
(* reducible terms *)
inductive crr (G:genv): relation2 lenv term ≝
| crr_delta  : ∀L,K,V,i. ⇩[i] L ≡ K.ⓓV → crr G L (#i)
| crr_appl_sn: ∀L,V,T. crr G L V → crr G L (ⓐV.T)
| crr_appl_dx: ∀L,V,T. crr G L T → crr G L (ⓐV.T)
| crr_ri2    : ∀I,L,V,T. ri2 I → crr G L (②{I}V.T)
| crr_ib2_sn : ∀a,I,L,V,T. ib2 a I → crr G L V → crr G L (ⓑ{a,I}V.T)
| crr_ib2_dx : ∀a,I,L,V,T. ib2 a I → crr G (L.ⓑ{I}V) T → crr G L (ⓑ{a,I}V.T)
| crr_beta   : ∀a,L,V,W,T. crr G L (ⓐV.ⓛ{a}W.T)
| crr_theta  : ∀a,L,V,W,T. crr G L (ⓐV.ⓓ{a}W.T)
.

interpretation
   "reducibility for context-sensitive reduction (term)"
   'PRedReducible G L T = (crr G L T).

(* Basic inversion lemmas ***************************************************)

fact crr_inv_sort_aux: ∀G,L,T,k. ⦃G, L⦄ ⊢ ➡ 𝐑⦃T⦄ → T = ⋆k → ⊥.
#G #L #T #k0 * -L -T
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

lemma crr_inv_sort: ∀G,L,k. ⦃G, L⦄ ⊢ ➡ 𝐑⦃⋆k⦄ → ⊥.
/2 width=6 by crr_inv_sort_aux/ qed-.

fact crr_inv_lref_aux: ∀G,L,T,i. ⦃G, L⦄ ⊢ ➡ 𝐑⦃T⦄ → T = #i →
                       ∃∃K,V. ⇩[i] L ≡ K.ⓓV.
#G #L #T #j * -L -T
[ #L #K #V #i #HLK #H destruct /2 width=3 by ex1_2_intro/
| #L #V #T #_ #H destruct
| #L #V #T #_ #H destruct
| #I #L #V #T #_ #H destruct
| #a #I #L #V #T #_ #_ #H destruct
| #a #I #L #V #T #_ #_ #H destruct
| #a #L #V #W #T #H destruct
| #a #L #V #W #T #H destruct
]
qed-.

lemma crr_inv_lref: ∀G,L,i. ⦃G, L⦄ ⊢ ➡ 𝐑⦃#i⦄ → ∃∃K,V. ⇩[i] L ≡ K.ⓓV.
/2 width=4 by crr_inv_lref_aux/ qed-.

fact crr_inv_gref_aux: ∀G,L,T,p. ⦃G, L⦄ ⊢ ➡ 𝐑⦃T⦄ → T = §p → ⊥.
#G #L #T #q * -L -T
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

lemma crr_inv_gref: ∀G,L,p. ⦃G, L⦄ ⊢ ➡ 𝐑⦃§p⦄ → ⊥.
/2 width=6 by crr_inv_gref_aux/ qed-.

lemma trr_inv_atom: ∀G,I. ⦃G, ⋆⦄ ⊢ ➡ 𝐑⦃⓪{I}⦄ → ⊥.
#G * #i #H
[ elim (crr_inv_sort … H)
| elim (crr_inv_lref … H) -H #L #V #H
  elim (drop_inv_atom1 … H) -H #H destruct
| elim (crr_inv_gref … H)
]
qed-.

fact crr_inv_ib2_aux: ∀a,I,G,L,W,U,T. ib2 a I → ⦃G, L⦄ ⊢ ➡ 𝐑⦃T⦄ → T = ⓑ{a,I}W.U →
                      ⦃G, L⦄ ⊢ ➡ 𝐑⦃W⦄ ∨ ⦃G, L.ⓑ{I}W⦄ ⊢ ➡ 𝐑⦃U⦄.
#G #b #J #L #W0 #U #T #HI * -L -T
[ #L #K #V #i #_ #H destruct
| #L #V #T #_ #H destruct
| #L #V #T #_ #H destruct
| #I #L #V #T #H1 #H2 destruct
  elim H1 -H1 #H destruct
  elim HI -HI #H destruct
| #a #I #L #V #T #_ #HV #H destruct /2 width=1 by or_introl/
| #a #I #L #V #T #_ #HT #H destruct /2 width=1 by or_intror/
| #a #L #V #W #T #H destruct
| #a #L #V #W #T #H destruct
]
qed-.

lemma crr_inv_ib2: ∀a,I,G,L,W,T. ib2 a I → ⦃G, L⦄ ⊢ ➡ 𝐑⦃ⓑ{a,I}W.T⦄ →
                   ⦃G, L⦄ ⊢ ➡ 𝐑⦃W⦄ ∨ ⦃G, L.ⓑ{I}W⦄ ⊢ ➡ 𝐑⦃T⦄.
/2 width=5 by crr_inv_ib2_aux/ qed-.

fact crr_inv_appl_aux: ∀G,L,W,U,T. ⦃G, L⦄ ⊢ ➡ 𝐑⦃T⦄ → T = ⓐW.U →
                       ∨∨ ⦃G, L⦄ ⊢ ➡ 𝐑⦃W⦄ | ⦃G, L⦄ ⊢ ➡ 𝐑⦃U⦄ | (𝐒⦃U⦄ → ⊥).
#G #L #W0 #U #T * -L -T
[ #L #K #V #i #_ #H destruct
| #L #V #T #HV #H destruct /2 width=1 by or3_intro0/
| #L #V #T #HT #H destruct /2 width=1 by or3_intro1/
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

lemma crr_inv_appl: ∀G,L,V,T. ⦃G, L⦄ ⊢ ➡ 𝐑⦃ⓐV.T⦄ →
                              ∨∨ ⦃G, L⦄ ⊢ ➡ 𝐑⦃V⦄ | ⦃G, L⦄ ⊢ ➡ 𝐑⦃T⦄ | (𝐒⦃T⦄ → ⊥).
/2 width=3 by crr_inv_appl_aux/ qed-.
