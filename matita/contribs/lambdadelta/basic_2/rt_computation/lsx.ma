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

include "basic_2/notation/relations/sn_6.ma".
include "basic_2/multiple/lleq.ma".
include "basic_2/reduction/lpx.ma".

(* SN EXTENDED STRONGLY NORMALIZING LOCAL ENVIRONMENTS **********************)

definition lsx: ∀h. sd h → relation4 ynat term genv lenv ≝
                λh,o,l,T,G. SN … (lpx h o G) (lleq l T).

interpretation
   "extended strong normalization (local environment)"
   'SN h o l T G L = (lsx h o T l G L).

(* Basic eliminators ********************************************************)

lemma lsx_ind: ∀h,o,G,T,l. ∀R:predicate lenv.
               (∀L1. G ⊢ ⬊*[h, o, T, l] L1 →
                     (∀L2. ⦃G, L1⦄ ⊢ ➡[h, o] L2 → (L1 ≡[T, l] L2 → ⊥) → R L2) →
                     R L1
               ) →
               ∀L. G ⊢ ⬊*[h, o, T, l] L → R L.
#h #o #G #T #l #R #H0 #L1 #H elim H -L1
/5 width=1 by lleq_sym, SN_intro/
qed-.

(* Basic properties *********************************************************)

lemma lsx_intro: ∀h,o,G,L1,T,l.
                 (∀L2. ⦃G, L1⦄ ⊢ ➡[h, o] L2 → (L1 ≡[T, l] L2 → ⊥) → G ⊢ ⬊*[h, o, T, l] L2) →
                 G ⊢ ⬊*[h, o, T, l] L1.
/5 width=1 by lleq_sym, SN_intro/ qed.

lemma lsx_atom: ∀h,o,G,T,l. G ⊢ ⬊*[h, o, T, l] ⋆.
#h #o #G #T #l @lsx_intro
#X #H #HT lapply (lpx_inv_atom1 … H) -H
#H destruct elim HT -HT //
qed.

lemma lsx_sort: ∀h,o,G,L,l,s. G ⊢ ⬊*[h, o, ⋆s, l] L.
#h #o #G #L1 #l #s @lsx_intro
#L2 #HL12 #H elim H -H
/3 width=4 by lpx_fwd_length, lleq_sort/
qed.

lemma lsx_gref: ∀h,o,G,L,l,p. G ⊢ ⬊*[h, o, §p, l] L.
#h #o #G #L1 #l #p @lsx_intro
#L2 #HL12 #H elim H -H
/3 width=4 by lpx_fwd_length, lleq_gref/
qed.

lemma lsx_ge_up: ∀h,o,G,L,T,U,lt,l,k. lt ≤ yinj l + yinj k →
                 ⬆[l, k] T ≡ U → G ⊢ ⬊*[h, o, U, lt] L → G ⊢ ⬊*[h, o, U, l] L.
#h #o #G #L #T #U #lt #l #k #Hltlm #HTU #H @(lsx_ind … H) -L
/5 width=7 by lsx_intro, lleq_ge_up/
qed-.

lemma lsx_ge: ∀h,o,G,L,T,l1,l2. l1 ≤ l2 →
              G ⊢ ⬊*[h, o, T, l1] L → G ⊢ ⬊*[h, o, T, l2] L.
#h #o #G #L #T #l1 #l2 #Hl12 #H @(lsx_ind … H) -L
/5 width=7 by lsx_intro, lleq_ge/
qed-.

(* Basic forward lemmas *****************************************************)

lemma lsx_fwd_bind_sn: ∀h,o,a,I,G,L,V,T,l. G ⊢ ⬊*[h, o, ⓑ{a,I}V.T, l] L →
                       G ⊢ ⬊*[h, o, V, l] L.
#h #o #a #I #G #L #V #T #l #H @(lsx_ind … H) -L
#L1 #_ #IHL1 @lsx_intro
#L2 #HL12 #HV @IHL1 /3 width=4 by lleq_fwd_bind_sn/
qed-.

lemma lsx_fwd_flat_sn: ∀h,o,I,G,L,V,T,l. G ⊢ ⬊*[h, o, ⓕ{I}V.T, l] L →
                       G ⊢ ⬊*[h, o, V, l] L.
#h #o #I #G #L #V #T #l #H @(lsx_ind … H) -L
#L1 #_ #IHL1 @lsx_intro
#L2 #HL12 #HV @IHL1 /3 width=3 by lleq_fwd_flat_sn/
qed-.

lemma lsx_fwd_flat_dx: ∀h,o,I,G,L,V,T,l. G ⊢ ⬊*[h, o, ⓕ{I}V.T, l] L →
                       G ⊢ ⬊*[h, o, T, l] L.
#h #o #I #G #L #V #T #l #H @(lsx_ind … H) -L
#L1 #_ #IHL1 @lsx_intro
#L2 #HL12 #HV @IHL1 /3 width=3 by lleq_fwd_flat_dx/
qed-.

lemma lsx_fwd_pair_sn: ∀h,o,I,G,L,V,T,l. G ⊢ ⬊*[h, o, ②{I}V.T, l] L →
                       G ⊢ ⬊*[h, o, V, l] L.
#h #o * /2 width=4 by lsx_fwd_bind_sn, lsx_fwd_flat_sn/
qed-.

(* Basic inversion lemmas ***************************************************)

lemma lsx_inv_flat: ∀h,o,I,G,L,V,T,l. G ⊢ ⬊*[h, o, ⓕ{I}V.T, l] L →
                    G ⊢ ⬊*[h, o, V, l] L ∧ G ⊢ ⬊*[h, o, T, l] L.
/3 width=3 by lsx_fwd_flat_sn, lsx_fwd_flat_dx, conj/ qed-.
