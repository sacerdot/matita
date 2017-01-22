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

include "basic_2/notation/relations/lazysn_6.ma".
include "basic_2/substitution/lleq.ma".
include "basic_2/reduction/llpx.ma".

(* LAZY SN EXTENDED STRONGLY NORMALIZING LOCAL ENVIRONMENTS *****************)

definition llsx: ∀h. sd h → relation4 ynat term genv lenv ≝
                 λh,g,d,T,G. SN … (llpx h g G d T) (lleq d T).

interpretation
   "lazy extended strong normalization (local environment)"
   'LazySN h g d T G L = (llsx h g T d G L).

(* Basic eliminators ********************************************************)

lemma llsx_ind: ∀h,g,G,T,d. ∀R:predicate lenv.
                (∀L1. G ⊢ ⋕⬊*[h, g, T, d] L1 →
                      (∀L2. ⦃G, L1⦄ ⊢ ➡[h, g, T, d] L2 → (L1 ⋕[T, d] L2 → ⊥) → R L2) →
                      R L1
                ) →
                ∀L. G ⊢ ⋕⬊*[h, g, T, d] L → R L.
#h #g #G #T #d #R #H0 #L1 #H elim H -L1
/5 width=1 by lleq_sym, SN_intro/
qed-.

(* Basic properties *********************************************************)

lemma llsx_intro: ∀h,g,G,L1,T,d.
                  (∀L2. ⦃G, L1⦄ ⊢ ➡[h, g, T, d] L2 → (L1 ⋕[T, d] L2 → ⊥) → G ⊢ ⋕⬊*[h, g, T, d] L2) →
                  G ⊢ ⋕⬊*[h, g, T, d] L1.
/5 width=1 by lleq_sym, SN_intro/ qed.

lemma llsx_sort: ∀h,g,G,L,d,k. G ⊢ ⋕⬊*[h, g, ⋆k, d] L.
#h #g #G #L1 #d #k @llsx_intro
#L2 #HL12 #H elim H -H
/3 width=6 by llpx_fwd_length, lleq_sort/
qed.

lemma llsx_gref: ∀h,g,G,L,d,p. G ⊢ ⋕⬊*[h, g, §p, d] L.
#h #g #G #L1 #d #p @llsx_intro
#L2 #HL12 #H elim H -H
/3 width=6 by llpx_fwd_length, lleq_gref/
qed.
