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

include "basic_2/reduction/crr.ma".

(* CONTEXT-SENSITIVE IRREDUCIBLE TERMS **************************************)

definition cir: lenv → predicate term ≝ λL,T. L ⊢ 𝐑⦃T⦄ → ⊥.

interpretation "context-sensitive irreducibility (term)"
   'NotReducible L T = (cir L T).

(* Basic inversion lemmas ***************************************************)

lemma cir_inv_delta: ∀L,K,V,i. ⇩[0, i] L ≡ K.ⓓV → L ⊢ 𝐈⦃#i⦄ → ⊥.
/3 width=3/ qed-.

lemma cir_inv_ri2: ∀I,L,V,T. ri2 I → L ⊢ 𝐈⦃②{I}V.T⦄ → ⊥.
/3 width=1/ qed-.

lemma cir_inv_ib2: ∀a,I,L,V,T. ib2 a I → L ⊢ 𝐈⦃ⓑ{a,I}V.T⦄ →
                   L ⊢ 𝐈⦃V⦄ ∧ L.ⓑ{I}V ⊢ 𝐈⦃T⦄.
/4 width=1/ qed-.

lemma cir_inv_bind: ∀a,I,L,V,T. L ⊢ 𝐈⦃ⓑ{a,I}V.T⦄ →
                    ∧∧ L ⊢ 𝐈⦃V⦄ & L.ⓑ{I}V ⊢ 𝐈⦃T⦄ & ib2 a I.
#a * [ elim a -a ]
[ #L #V #T #H elim H -H /3 width=1/
|*: #L #V #T #H elim (cir_inv_ib2 … H) -H /2 width=1/ /3 width=1/
]
qed-.

lemma cir_inv_appl: ∀L,V,T. L ⊢ 𝐈⦃ⓐV.T⦄ → ∧∧ L ⊢ 𝐈⦃V⦄ & L ⊢ 𝐈⦃T⦄ & 𝐒⦃T⦄.
#L #V #T #HVT @and3_intro /3 width=1/
generalize in match HVT; -HVT elim T -T //
* // #a * #U #T #_ #_ #H elim H -H /2 width=1/
qed-.

lemma cir_inv_flat: ∀I,L,V,T. L ⊢ 𝐈⦃ⓕ{I}V.T⦄ →
                    ∧∧ L ⊢ 𝐈⦃V⦄ & L ⊢ 𝐈⦃T⦄ & 𝐒⦃T⦄ & I = Appl.
* #L #V #T #H
[ elim (cir_inv_appl … H) -H /2 width=1/
| elim (cir_inv_ri2 … H) -H /2 width=1/
]
qed-.

(* Basic properties *********************************************************)

lemma cir_sort: ∀L,k. L ⊢ 𝐈⦃⋆k⦄.
/2 width=3 by crr_inv_sort/ qed.

lemma cir_gref: ∀L,p. L ⊢ 𝐈⦃§p⦄.
/2 width=3 by crr_inv_gref/ qed.

lemma tir_atom: ∀I. ⋆ ⊢ 𝐈⦃⓪{I}⦄.
/2 width=2 by trr_inv_atom/ qed.

lemma cir_ib2: ∀a,I,L,V,T. ib2 a I → L ⊢ 𝐈⦃V⦄ → L.ⓑ{I}V ⊢ 𝐈⦃T⦄ → L ⊢ 𝐈⦃ⓑ{a,I}V.T⦄.
#a #I #L #V #T #HI #HV #HT #H
elim (crr_inv_ib2 … HI H) -HI -H /2 width=1/
qed.

lemma cir_appl: ∀L,V,T. L ⊢ 𝐈⦃V⦄ → L ⊢ 𝐈⦃T⦄ →  𝐒⦃T⦄ → L ⊢ 𝐈⦃ⓐV.T⦄.
#L #V #T #HV #HT #H1 #H2
elim (crr_inv_appl … H2) -H2 /2 width=1/
qed.
