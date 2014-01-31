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

include "basic_2/notation/relations/prednotreducible_3.ma".
include "basic_2/reduction/crr.ma".

(* IRREDUCIBLE TERMS FOR CONTEXT-SENSITIVE REDUCTION ************************)

definition cir: relation3 genv lenv term ≝ λG,L,T. ⦃G, L⦄ ⊢ ➡ 𝐑⦃T⦄ → ⊥.

interpretation "irreducibility for context-sensitive reduction (term)"
   'PRedNotReducible G L T = (cir G L T).

(* Basic inversion lemmas ***************************************************)

lemma cir_inv_delta: ∀G,L,K,V,i. ⇩[i] L ≡ K.ⓓV → ⦃G, L⦄ ⊢ ➡ 𝐈⦃#i⦄ → ⊥.
/3 width=3 by crr_delta/ qed-.

lemma cir_inv_ri2: ∀I,G,L,V,T. ri2 I → ⦃G, L⦄ ⊢ ➡ 𝐈⦃②{I}V.T⦄ → ⊥.
/3 width=1 by crr_ri2/ qed-.

lemma cir_inv_ib2: ∀a,I,G,L,V,T. ib2 a I → ⦃G, L⦄ ⊢ ➡ 𝐈⦃ⓑ{a,I}V.T⦄ →
                   ⦃G, L⦄ ⊢ ➡ 𝐈⦃V⦄ ∧ ⦃G, L.ⓑ{I}V⦄ ⊢ ➡ 𝐈⦃T⦄.
/4 width=1 by crr_ib2_sn, crr_ib2_dx, conj/ qed-.

lemma cir_inv_bind: ∀a,I,G,L,V,T. ⦃G, L⦄ ⊢ ➡ 𝐈⦃ⓑ{a,I}V.T⦄ →
                    ∧∧ ⦃G, L⦄ ⊢ ➡ 𝐈⦃V⦄ & ⦃G, L.ⓑ{I}V⦄ ⊢ ➡ 𝐈⦃T⦄ & ib2 a I.
#a * [ elim a -a ]
#G #L #V #T #H [ elim H -H /3 width=1 by crr_ri2, or_introl/ ]
elim (cir_inv_ib2 … H) -H /3 width=1 by and3_intro, or_introl/
qed-.

lemma cir_inv_appl: ∀G,L,V,T. ⦃G, L⦄ ⊢ ➡ 𝐈⦃ⓐV.T⦄ →
                    ∧∧ ⦃G, L⦄ ⊢ ➡ 𝐈⦃V⦄ & ⦃G, L⦄ ⊢ ➡ 𝐈⦃T⦄ & 𝐒⦃T⦄.
#G #L #V #T #HVT @and3_intro /3 width=1/
generalize in match HVT; -HVT elim T -T //
* // #a * #U #T #_ #_ #H elim H -H /2 width=1 by crr_beta, crr_theta/
qed-.

lemma cir_inv_flat: ∀I,G,L,V,T. ⦃G, L⦄ ⊢ ➡ 𝐈⦃ⓕ{I}V.T⦄ →
                    ∧∧ ⦃G, L⦄ ⊢ ➡ 𝐈⦃V⦄ & ⦃G, L⦄ ⊢ ➡ 𝐈⦃T⦄ & 𝐒⦃T⦄ & I = Appl.
* #G #L #V #T #H
[ elim (cir_inv_appl … H) -H /2 width=1 by and4_intro/
| elim (cir_inv_ri2 … H) -H //
]
qed-.

(* Basic properties *********************************************************)

lemma cir_sort: ∀G,L,k. ⦃G, L⦄ ⊢ ➡ 𝐈⦃⋆k⦄.
/2 width=4 by crr_inv_sort/ qed.

lemma cir_gref: ∀G,L,p. ⦃G, L⦄ ⊢ ➡ 𝐈⦃§p⦄.
/2 width=4 by crr_inv_gref/ qed.

lemma tir_atom: ∀G,I. ⦃G, ⋆⦄ ⊢ ➡ 𝐈⦃⓪{I}⦄.
/2 width=3 by trr_inv_atom/ qed.

lemma cir_ib2: ∀a,I,G,L,V,T.
               ib2 a I → ⦃G, L⦄ ⊢ ➡ 𝐈⦃V⦄ → ⦃G, L.ⓑ{I}V⦄ ⊢ ➡ 𝐈⦃T⦄ → ⦃G, L⦄ ⊢ ➡ 𝐈⦃ⓑ{a,I}V.T⦄.
#a #I #G #L #V #T #HI #HV #HT #H
elim (crr_inv_ib2 … HI H) -HI -H /2 width=1 by/
qed.

lemma cir_appl: ∀G,L,V,T. ⦃G, L⦄ ⊢ ➡ 𝐈⦃V⦄ → ⦃G, L⦄ ⊢ ➡ 𝐈⦃T⦄ →  𝐒⦃T⦄ → ⦃G, L⦄ ⊢ ➡ 𝐈⦃ⓐV.T⦄.
#G #L #V #T #HV #HT #H1 #H2
elim (crr_inv_appl … H2) -H2 /2 width=1 by/
qed.
