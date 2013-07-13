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

include "basic_2/reduction/cir.ma".
include "basic_2/reduction/crx.ma".

(* CONTEXT-SENSITIVE EXTENDED IRREDUCIBLE TERMS *****************************)

definition cix: ∀h. sd h → lenv → predicate term ≝ λh,g,L,T. ⦃h, L⦄ ⊢ 𝐑[g]⦃T⦄ → ⊥.

interpretation "context-sensitive extended irreducibility (term)"
   'NotReducible h g L T = (cix h g L T).

(* Basic inversion lemmas ***************************************************)

lemma cix_inv_sort: ∀h,g,L,k,l. deg h g k (l+1) → ⦃h, L⦄ ⊢ 𝐈[g]⦃⋆k⦄ → ⊥.
/3 width=2/ qed-.

lemma cix_inv_delta: ∀h,g,I,L,K,V,i. ⇩[0, i] L ≡ K.ⓑ{I}V → ⦃h, L⦄ ⊢ 𝐈[g]⦃#i⦄ → ⊥.
/3 width=4/ qed-.

lemma cix_inv_ri2: ∀h,g,I,L,V,T. ri2 I → ⦃h, L⦄ ⊢ 𝐈[g]⦃②{I}V.T⦄ → ⊥.
/3 width=1/ qed-.

lemma cix_inv_ib2: ∀h,g,a,I,L,V,T. ib2 a I → ⦃h, L⦄ ⊢ 𝐈[g]⦃ⓑ{a,I}V.T⦄ →
                   ⦃h, L⦄ ⊢ 𝐈[g]⦃V⦄ ∧ ⦃h, L.ⓑ{I}V⦄ ⊢ 𝐈[g]⦃T⦄.
/4 width=1/ qed-.

lemma cix_inv_bind: ∀h,g,a,I,L,V,T. ⦃h, L⦄ ⊢ 𝐈[g]⦃ⓑ{a,I}V.T⦄ →
                    ∧∧ ⦃h, L⦄ ⊢ 𝐈[g]⦃V⦄ & ⦃h, L.ⓑ{I}V⦄ ⊢ 𝐈[g]⦃T⦄ & ib2 a I.
#h #g #a * [ elim a -a ]
[ #L #V #T #H elim H -H /3 width=1/
|*: #L #V #T #H elim (cix_inv_ib2 … H) -H /2 width=1/ /3 width=1/
]
qed-.

lemma cix_inv_appl: ∀h,g,L,V,T. ⦃h, L⦄ ⊢ 𝐈[g]⦃ⓐV.T⦄ →
                    ∧∧ ⦃h, L⦄ ⊢ 𝐈[g]⦃V⦄ & ⦃h, L⦄ ⊢ 𝐈[g]⦃T⦄ & 𝐒⦃T⦄.
#h #g #L #V #T #HVT @and3_intro /3 width=1/
generalize in match HVT; -HVT elim T -T //
* // #a * #U #T #_ #_ #H elim H -H /2 width=1/
qed-.

lemma cix_inv_flat: ∀h,g,I,L,V,T. ⦃h, L⦄ ⊢ 𝐈[g]⦃ⓕ{I}V.T⦄ →
                    ∧∧ ⦃h, L⦄ ⊢ 𝐈[g]⦃V⦄ & ⦃h, L⦄ ⊢ 𝐈[g]⦃T⦄ & 𝐒⦃T⦄ & I = Appl.
#h #g * #L #V #T #H
[ elim (cix_inv_appl … H) -H /2 width=1/
| elim (cix_inv_ri2 … H) -H /2 width=1/
]
qed-.

(* Basic forward lemmas *****************************************************)

lemma cix_inv_cir: ∀h,g,L,T. ⦃h, L⦄ ⊢ 𝐈[g]⦃T⦄ → L ⊢ 𝐈⦃T⦄. 
/3 width=1/ qed-.

(* Basic properties *********************************************************)

lemma cix_sort: ∀h,g,L,k. deg h g k 0 → ⦃h, L⦄ ⊢ 𝐈[g]⦃⋆k⦄.
#h #g #L #k #Hk #H elim (crx_inv_sort … H) -L #l #Hkl
lapply (deg_mono … Hk Hkl) -h -k <plus_n_Sm #H destruct
qed.

lemma tix_lref: ∀h,g,i. ⦃h, ⋆⦄ ⊢ 𝐈[g]⦃#i⦄.
#h #g #i #H elim (trx_inv_atom … H) -H #k #l #_ #H destruct
qed.

lemma cix_gref: ∀h,g,L,p. ⦃h, L⦄ ⊢ 𝐈[g]⦃§p⦄.
#h #g #L #p #H elim (crx_inv_gref … H)
qed.

lemma cix_ib2: ∀h,g,a,I,L,V,T. ib2 a I → ⦃h, L⦄ ⊢ 𝐈[g]⦃V⦄ → ⦃h, L.ⓑ{I}V⦄ ⊢ 𝐈[g]⦃T⦄ →
                               ⦃h, L⦄ ⊢ 𝐈[g]⦃ⓑ{a,I}V.T⦄.
#h #g #a #I #L #V #T #HI #HV #HT #H
elim (crx_inv_ib2 … HI H) -HI -H /2 width=1/
qed.

lemma cix_appl: ∀h,g,L,V,T. ⦃h, L⦄ ⊢ 𝐈[g]⦃V⦄ → ⦃h, L⦄ ⊢ 𝐈[g]⦃T⦄ →  𝐒⦃T⦄ → ⦃h, L⦄ ⊢ 𝐈[g]⦃ⓐV.T⦄.
#h #g #L #V #T #HV #HT #H1 #H2
elim (crx_inv_appl … H2) -H2 /2 width=1/
qed.
