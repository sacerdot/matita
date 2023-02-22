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
                λh,o,G,L,T. ⦃G, L⦄ ⊢ ➡[h, o] 𝐑⦃T⦄ → ⊥.

interpretation "irreducibility for context-sensitive extended reduction (term)"
   'PRedNotReducible h o G L T = (cix h o G L T).

(* Basic inversion lemmas ***************************************************)

lemma cix_inv_sort: ∀h,o,G,L,s,d. deg h o s (d+1) → ⦃G, L⦄ ⊢ ➡[h, o] 𝐈⦃⋆s⦄ → ⊥.
/3 width=2 by crx_sort/ qed-.

lemma cix_inv_delta: ∀h,o,I,G,L,K,V,i. ⬇[i] L ≡ K.ⓑ{I}V → ⦃G, L⦄ ⊢ ➡[h, o] 𝐈⦃#i⦄ → ⊥.
/3 width=4 by crx_delta/ qed-.

lemma cix_inv_ri2: ∀h,o,I,G,L,V,T. ri2 I → ⦃G, L⦄ ⊢ ➡[h, o] 𝐈⦃②{I}V.T⦄ → ⊥.
/3 width=1 by crx_ri2/ qed-.

lemma cix_inv_ib2: ∀h,o,a,I,G,L,V,T. ib2 a I → ⦃G, L⦄ ⊢ ➡[h, o] 𝐈⦃ⓑ{a,I}V.T⦄ →
                   ⦃G, L⦄ ⊢ ➡[h, o] 𝐈⦃V⦄ ∧ ⦃G, L.ⓑ{I}V⦄ ⊢ ➡[h, o] 𝐈⦃T⦄.
/4 width=1 by crx_ib2_sn, crx_ib2_dx, conj/ qed-.

lemma cix_inv_bind: ∀h,o,a,I,G,L,V,T. ⦃G, L⦄ ⊢ ➡[h, o] 𝐈⦃ⓑ{a,I}V.T⦄ →
                    ∧∧ ⦃G, L⦄ ⊢ ➡[h, o] 𝐈⦃V⦄ & ⦃G, L.ⓑ{I}V⦄ ⊢ ➡[h, o] 𝐈⦃T⦄ & ib2 a I.
#h #o #a * [ elim a -a ]
#G #L #V #T #H [ elim H -H /3 width=1 by crx_ri2, or_introl/ ]
elim (cix_inv_ib2 … H) -H /3 width=1 by and3_intro, or_introl/
qed-.

lemma cix_inv_appl: ∀h,o,G,L,V,T. ⦃G, L⦄ ⊢ ➡[h, o] 𝐈⦃ⓐV.T⦄ →
                    ∧∧ ⦃G, L⦄ ⊢ ➡[h, o] 𝐈⦃V⦄ & ⦃G, L⦄ ⊢ ➡[h, o] 𝐈⦃T⦄ & 𝐒⦃T⦄.
#h #o #G #L #V #T #HVT @and3_intro /3 width=1 by crx_appl_sn, crx_appl_dx/
generalize in match HVT; -HVT elim T -T //
* // #a * #U #T #_ #_ #H elim H -H /2 width=1 by crx_beta, crx_theta/
qed-.

lemma cix_inv_flat: ∀h,o,I,G,L,V,T. ⦃G, L⦄ ⊢ ➡[h, o] 𝐈⦃ⓕ{I}V.T⦄ →
                    ∧∧ ⦃G, L⦄ ⊢ ➡[h, o] 𝐈⦃V⦄ & ⦃G, L⦄ ⊢ ➡[h, o] 𝐈⦃T⦄ & 𝐒⦃T⦄ & I = Appl.
#h #o * #G #L #V #T #H
[ elim (cix_inv_appl … H) -H /2 width=1 by and4_intro/
| elim (cix_inv_ri2 … H) -H //
]
qed-.

(* Basic forward lemmas *****************************************************)

lemma cix_inv_cir: ∀h,o,G,L,T. ⦃G, L⦄ ⊢ ➡[h, o] 𝐈⦃T⦄ → ⦃G, L⦄ ⊢ ➡ 𝐈⦃T⦄.
/3 width=1 by crr_crx/ qed-.

(* Basic properties *********************************************************)

lemma cix_sort: ∀h,o,G,L,s. deg h o s 0 → ⦃G, L⦄ ⊢ ➡[h, o] 𝐈⦃⋆s⦄.
#h #o #G #L #s #Hk #H elim (crx_inv_sort … H) -L #d #Hkd
lapply (deg_mono … Hk Hkd) -h -s <plus_n_Sm #H destruct
qed.

lemma tix_lref: ∀h,o,G,i. ⦃G, ⋆⦄ ⊢ ➡[h, o] 𝐈⦃#i⦄.
#h #o #G #i #H elim (trx_inv_atom … H) -H #s #d #_ #H destruct
qed.

lemma cix_gref: ∀h,o,G,L,p. ⦃G, L⦄ ⊢ ➡[h, o] 𝐈⦃§p⦄.
#h #o #G #L #p #H elim (crx_inv_gref … H)
qed.

lemma cix_ib2: ∀h,o,a,I,G,L,V,T. ib2 a I → ⦃G, L⦄ ⊢ ➡[h, o] 𝐈⦃V⦄ → ⦃G, L.ⓑ{I}V⦄ ⊢ ➡[h, o] 𝐈⦃T⦄ →
                               ⦃G, L⦄ ⊢ ➡[h, o] 𝐈⦃ⓑ{a,I}V.T⦄.
#h #o #a #I #G #L #V #T #HI #HV #HT #H
elim (crx_inv_ib2 … HI H) -HI -H /2 width=1 by/
qed.

lemma cix_appl: ∀h,o,G,L,V,T. ⦃G, L⦄ ⊢ ➡[h, o] 𝐈⦃V⦄ → ⦃G, L⦄ ⊢ ➡[h, o] 𝐈⦃T⦄ →  𝐒⦃T⦄ → ⦃G, L⦄ ⊢ ➡[h, o] 𝐈⦃ⓐV.T⦄.
#h #o #G #L #V #T #HV #HT #H1 #H2
elim (crx_inv_appl … H2) -H2 /2 width=1 by/
qed.
