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

include "basic_2/notation/relations/lazysnalt_6.ma".
include "basic_2/substitution/lleq_lleq.ma".
include "basic_2/computation/llpxs_lleq.ma".
include "basic_2/computation/llsx.ma".

(* SN EXTENDED STRONGLY NORMALIZING LOCAL ENVIRONMENTS **********************)

(* alternative definition of llsx *)
definition llsxa: ∀h. sd h → relation4 ynat term genv lenv ≝
                  λh,g,d,T,G. SN … (llpxs h g G d T) (lleq d T).

interpretation
   "lazy extended strong normalization (local environment) alternative"
   'LazySNAlt h g d T G L = (llsxa h g T d G L).

(* Basic eliminators ********************************************************)

lemma llsxa_ind: ∀h,g,G,T,d. ∀R:predicate lenv.
                 (∀L1. G ⊢ ⋕⬊⬊*[h, g, T, d] L1 →
                       (∀L2. ⦃G, L1⦄ ⊢ ➡*[h, g, T, d] L2 → (L1 ⋕[T, d] L2 → ⊥) → R L2) →
                       R L1
                 ) →
                 ∀L. G ⊢ ⋕⬊⬊*[h, g, T, d] L → R L.
#h #g #G #T #d #R #H0 #L1 #H elim H -L1
/5 width=1 by lleq_sym, SN_intro/
qed-.

(* Basic properties *********************************************************)

lemma llsxa_intro: ∀h,g,G,L1,T,d.
                   (∀L2. ⦃G, L1⦄ ⊢ ➡*[h, g, T, d] L2 → (L1 ⋕[T, d] L2 → ⊥) → G ⊢ ⋕⬊⬊*[h, g, T, d] L2) →
                   G ⊢ ⋕⬊⬊*[h, g, T, d] L1.
/5 width=1 by lleq_sym, SN_intro/ qed.

fact llsxa_intro_aux: ∀h,g,G,L1,T,d.
                      (∀L,L2. ⦃G, L⦄ ⊢ ➡*[h, g, T, d] L2 → L1 ⋕[T, d] L → (L1 ⋕[T, d] L2 → ⊥) → G ⊢ ⋕⬊⬊*[h, g, T, d] L2) →
                      G ⊢ ⋕⬊⬊*[h, g, T, d] L1.
/4 width=3 by llsxa_intro/ qed-.

lemma llsxa_llpxs_trans: ∀h,g,G,L1,T,d. G ⊢ ⋕⬊⬊*[h, g, T, d] L1 →
                         ∀L2. ⦃G, L1⦄ ⊢ ➡*[h, g, T, d] L2 → G ⊢ ⋕⬊⬊*[h, g, T, d] L2.
#h #g #G #L1 #T #d #H @(llsxa_ind … H) -L1 #L1 #HL1 #IHL1 #L2 #HL12 @llsxa_intro
elim (lleq_dec T L1 L2 d) /4 width=4 by lleq_llpxs_trans, lleq_canc_sn/
qed-.

lemma llsxa_intro_llpx: ∀h,g,G,L1,T,d.
                        (∀L2. ⦃G, L1⦄ ⊢ ➡[h, g, T, d] L2 → (L1 ⋕[T, d] L2 → ⊥) → G ⊢ ⋕⬊⬊*[h, g, T, d] L2) →
                        G ⊢ ⋕⬊⬊*[h, g, T, d] L1.
#h #g #G #L1 #T #d #IH @llsxa_intro_aux
#L #L2 #H @(llpxs_ind_dx … H) -L
[ #H destruct #H elim H //
| #L0 #L elim (lleq_dec T L1 L d)
  /4 width=3 by llsxa_llpxs_trans, lleq_llpx_trans/
]
qed.

(* Main properties **********************************************************)

theorem llsx_llsxa: ∀h,g,G,L,T,d. G ⊢ ⋕⬊*[h, g, T, d] L → G ⊢ ⋕⬊⬊*[h, g, T, d] L.
#h #g #G #L #T #d #H @(llsx_ind … H) -L
/4 width=1 by llsxa_intro_llpx/
qed.

(* Main inversion lemmas ****************************************************)

theorem llsxa_inv_llsx: ∀h,g,G,L,T,d. G ⊢ ⋕⬊⬊*[h, g, T, d] L → G ⊢ ⋕⬊*[h, g, T, d] L.
#h #g #G #L #T #d #H @(llsxa_ind … H) -L
/4 width=1 by llsx_intro, llpx_llpxs/
qed-.

(* Advanced properties ******************************************************)

lemma llsx_intro_alt: ∀h,g,G,L1,T,d.
                      (∀L2. ⦃G, L1⦄ ⊢ ➡*[h, g, T, d] L2 → (L1 ⋕[T, d] L2 → ⊥) → G ⊢ ⋕⬊*[h, g, T, d] L2) →
                      G ⊢ ⋕⬊*[h, g, T, d] L1.
/6 width=1 by llsxa_inv_llsx, llsx_llsxa, llsxa_intro/ qed.

lemma llsx_llpxs_trans: ∀h,g,G,L1,T,d. G ⊢ ⋕⬊*[h, g, T, d] L1 →
                        ∀L2. ⦃G, L1⦄ ⊢ ➡*[h, g, T, d] L2 → G ⊢ ⋕⬊*[h, g, T, d] L2.
/4 width=3 by llsxa_inv_llsx, llsx_llsxa, llsxa_llpxs_trans/
qed-.

(* Advanced eliminators *****************************************************)

lemma llsx_ind_alt: ∀h,g,G,T,d. ∀R:predicate lenv.
                    (∀L1. G ⊢ ⋕⬊*[h, g, T, d] L1 →
                          (∀L2. ⦃G, L1⦄ ⊢ ➡*[h, g, T, d] L2 → (L1 ⋕[T, d] L2 → ⊥) → R L2) →
                          R L1
                    ) →
                    ∀L. G ⊢ ⋕⬊*[h, g, T, d] L → R L.
#h #g #G #T #d #R #IH #L #H @(llsxa_ind h g G T d … L)
/4 width=1 by llsxa_inv_llsx, llsx_llsxa/
qed-.
