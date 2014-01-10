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

include "basic_2/notation/relations/lazysn_5.ma".
include "basic_2/substitution/lleq.ma".
include "basic_2/computation/lpxs.ma".

(* SN EXTENDED STRONGLY NORMALIZING LOCAL ENVIRONMENTS **********************)

definition lsx: ∀h. sd h → relation3 term genv lenv ≝
                λh,g,T,G. SN … (lpxs h g G) (lleq 0 T).

interpretation
   "extended strong normalization (local environment)"
   'LazySN h g T G L = (lsx h g T G L).

(* Basic eliminators ********************************************************)

lemma lsx_ind: ∀h,g,T,G. ∀R:predicate lenv.
               (∀L1. G ⊢ ⋕⬊*[h, g, T] L1 →
                     (∀L2. ⦃G, L1⦄ ⊢ ➡*[h, g] L2 → (L1 ⋕[T, 0] L2 → ⊥) → R L2) →
                     R L1
               ) →
               ∀L. G ⊢ ⋕⬊*[h, g, T] L → R L.
#h #g #T #G #R #H0 #L1 #H elim H -L1
/5 width=1 by lleq_sym, SN_intro/
qed-.

(* Basic properties *********************************************************)

lemma lsx_intro: ∀h,g,T,G,L1.
                 (∀L2. ⦃G, L1⦄ ⊢ ➡*[h, g] L2 → (L1 ⋕[T, 0] L2 → ⊥) → G ⊢ ⋕⬊*[h, g, T] L2) →
                 G ⊢ ⋕⬊*[h, g, T] L1.
/5 width=1 by lleq_sym, SN_intro/ qed.

lemma lsx_atom: ∀h,g,T,G. G ⊢ ⋕⬊*[h, g, T] ⋆.
#h #g #T #G @lsx_intro
#X #H #HT lapply (lpxs_inv_atom1 … H) -H
#H destruct elim HT -HT //
qed.

lemma lsx_sort: ∀h,g,G,L,k. G ⊢ ⋕⬊*[h, g, ⋆k] L.
#h #g #G #L1 #k @lsx_intro
#L2 #HL12 #H elim H -H
/3 width=4 by lpxs_fwd_length, lleq_sort/
qed.

lemma lsx_gref: ∀h,g,G,L,p. G ⊢ ⋕⬊*[h, g, §p] L.
#h #g #G #L1 #p @lsx_intro
#L2 #HL12 #H elim H -H
/3 width=4 by lpxs_fwd_length, lleq_gref/
qed.
