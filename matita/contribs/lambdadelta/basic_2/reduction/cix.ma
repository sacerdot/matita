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

include "basic_2/notation/relations/prednotreducible_5.ma".
include "basic_2/reduction/cir.ma".
include "basic_2/reduction/crx.ma".

(* IRREDUCIBLE TERMS FOR CONTEXT-SENSITIVE EXTENDED REDUCTION ***************)

definition cix: ∀h. sd h → relation3 genv lenv term ≝
                λh,g,G,L,T. ⦃G, L⦄ ⊢ ➡[h, g] 𝐑⦃T⦄ → ⊥.

interpretation "irreducibility for context-sensitive extended reduction (term)"
   'PRedNotReducible h g G L T = (cix h g G L T).

(* Basic inversion lemmas ***************************************************)

lemma cix_inv_sort: ∀h,g,G,L,k,l. deg h g k (l+1) → ⦃G, L⦄ ⊢ ➡[h, g] 𝐈⦃⋆k⦄ → ⊥.
/3 width=2 by crx_sort/ qed-.

lemma cix_inv_delta: ∀h,g,I,G,L,K,V,i. ⇩[i] L ≡ K.ⓑ{I}V → ⦃G, L⦄ ⊢ ➡[h, g] 𝐈⦃#i⦄ → ⊥.
/3 width=4 by crx_delta/ qed-.

lemma cix_inv_ri2: ∀h,g,I,G,L,V,T. ri2 I → ⦃G, L⦄ ⊢ ➡[h, g] 𝐈⦃②{I}V.T⦄ → ⊥.
/3 width=1 by crx_ri2/ qed-.

lemma cix_inv_ib2: ∀h,g,a,I,G,L,V,T. ib2 a I → ⦃G, L⦄ ⊢ ➡[h, g] 𝐈⦃ⓑ{a,I}V.T⦄ →
                   ⦃G, L⦄ ⊢ ➡[h, g] 𝐈⦃V⦄ ∧ ⦃G, L.ⓑ{I}V⦄ ⊢ ➡[h, g] 𝐈⦃T⦄.
/4 width=1 by crx_ib2_sn, crx_ib2_dx, conj/ qed-.

lemma cix_inv_bind: ∀h,g,a,I,G,L,V,T. ⦃G, L⦄ ⊢ ➡[h, g] 𝐈⦃ⓑ{a,I}V.T⦄ →
                    ∧∧ ⦃G, L⦄ ⊢ ➡[h, g] 𝐈⦃V⦄ & ⦃G, L.ⓑ{I}V⦄ ⊢ ➡[h, g] 𝐈⦃T⦄ & ib2 a I.
#h #g #a * [ elim a -a ]
#G #L #V #T #H [ elim H -H /3 width=1 by crx_ri2, or_introl/ ]
elim (cix_inv_ib2 … H) -H /3 width=1 by and3_intro, or_introl/
qed-.

lemma cix_inv_appl: ∀h,g,G,L,V,T. ⦃G, L⦄ ⊢ ➡[h, g] 𝐈⦃ⓐV.T⦄ →
                    ∧∧ ⦃G, L⦄ ⊢ ➡[h, g] 𝐈⦃V⦄ & ⦃G, L⦄ ⊢ ➡[h, g] 𝐈⦃T⦄ & 𝐒⦃T⦄.
#h #g #G #L #V #T #HVT @and3_intro /3 width=1 by crx_appl_sn, crx_appl_dx/
generalize in match HVT; -HVT elim T -T //
* // #a * #U #T #_ #_ #H elim H -H /2 width=1 by crx_beta, crx_theta/
qed-.

lemma cix_inv_flat: ∀h,g,I,G,L,V,T. ⦃G, L⦄ ⊢ ➡[h, g] 𝐈⦃ⓕ{I}V.T⦄ →
                    ∧∧ ⦃G, L⦄ ⊢ ➡[h, g] 𝐈⦃V⦄ & ⦃G, L⦄ ⊢ ➡[h, g] 𝐈⦃T⦄ & 𝐒⦃T⦄ & I = Appl.
#h #g * #G #L #V #T #H
[ elim (cix_inv_appl … H) -H /2 width=1 by and4_intro/
| elim (cix_inv_ri2 … H) -H //
]
qed-.

(* Basic forward lemmas *****************************************************)

lemma cix_inv_cir: ∀h,g,G,L,T. ⦃G, L⦄ ⊢ ➡[h, g] 𝐈⦃T⦄ → ⦃G, L⦄ ⊢ ➡ 𝐈⦃T⦄.
/3 width=1 by crr_crx/ qed-.

(* Basic properties *********************************************************)

lemma cix_sort: ∀h,g,G,L,k. deg h g k 0 → ⦃G, L⦄ ⊢ ➡[h, g] 𝐈⦃⋆k⦄.
#h #g #G #L #k #Hk #H elim (crx_inv_sort … H) -L #l #Hkl
lapply (deg_mono … Hk Hkl) -h -k <plus_n_Sm #H destruct
qed.

lemma tix_lref: ∀h,g,G,i. ⦃G, ⋆⦄ ⊢ ➡[h, g] 𝐈⦃#i⦄.
#h #g #G #i #H elim (trx_inv_atom … H) -H #k #l #_ #H destruct
qed.

lemma cix_gref: ∀h,g,G,L,p. ⦃G, L⦄ ⊢ ➡[h, g] 𝐈⦃§p⦄.
#h #g #G #L #p #H elim (crx_inv_gref … H)
qed.

lemma cix_ib2: ∀h,g,a,I,G,L,V,T. ib2 a I → ⦃G, L⦄ ⊢ ➡[h, g] 𝐈⦃V⦄ → ⦃G, L.ⓑ{I}V⦄ ⊢ ➡[h, g] 𝐈⦃T⦄ →
                               ⦃G, L⦄ ⊢ ➡[h, g] 𝐈⦃ⓑ{a,I}V.T⦄.
#h #g #a #I #G #L #V #T #HI #HV #HT #H
elim (crx_inv_ib2 … HI H) -HI -H /2 width=1 by/
qed.

lemma cix_appl: ∀h,g,G,L,V,T. ⦃G, L⦄ ⊢ ➡[h, g] 𝐈⦃V⦄ → ⦃G, L⦄ ⊢ ➡[h, g] 𝐈⦃T⦄ →  𝐒⦃T⦄ → ⦃G, L⦄ ⊢ ➡[h, g] 𝐈⦃ⓐV.T⦄.
#h #g #G #L #V #T #HV #HT #H1 #H2
elim (crx_inv_appl … H2) -H2 /2 width=1 by/
qed.
