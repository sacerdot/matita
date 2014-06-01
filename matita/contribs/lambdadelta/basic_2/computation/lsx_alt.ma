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

include "basic_2/notation/relations/snalt_6.ma".
include "basic_2/multiple/lleq_lleq.ma".
include "basic_2/computation/lpxs_lleq.ma".
include "basic_2/computation/lsx.ma".

(* SN EXTENDED STRONGLY NORMALIZING LOCAL ENVIRONMENTS **********************)

(* alternative definition of lsx *)
definition lsxa: ∀h. sd h → relation4 ynat term genv lenv ≝
                 λh,g,d,T,G. SN … (lpxs h g G) (lleq d T).

interpretation
   "extended strong normalization (local environment) alternative"
   'SNAlt h g d T G L = (lsxa h g T d G L).

(* Basic eliminators ********************************************************)

lemma lsxa_ind: ∀h,g,G,T,d. ∀R:predicate lenv.
                (∀L1. G ⊢ ⬊⬊*[h, g, T, d] L1 →
                      (∀L2. ⦃G, L1⦄ ⊢ ➡*[h, g] L2 → (L1 ≡[T, d] L2 → ⊥) → R L2) →
                      R L1
                ) →
                ∀L. G ⊢ ⬊⬊*[h, g, T, d] L → R L.
#h #g #G #T #d #R #H0 #L1 #H elim H -L1
/5 width=1 by lleq_sym, SN_intro/
qed-.

(* Basic properties *********************************************************)

lemma lsxa_intro: ∀h,g,G,L1,T,d.
                  (∀L2. ⦃G, L1⦄ ⊢ ➡*[h, g] L2 → (L1 ≡[T, d] L2 → ⊥) → G ⊢ ⬊⬊*[h, g, T, d] L2) →
                  G ⊢ ⬊⬊*[h, g, T, d] L1.
/5 width=1 by lleq_sym, SN_intro/ qed.

fact lsxa_intro_aux: ∀h,g,G,L1,T,d.
                     (∀L,L2. ⦃G, L⦄ ⊢ ➡*[h, g] L2 → L1 ≡[T, d] L → (L1 ≡[T, d] L2 → ⊥) → G ⊢ ⬊⬊*[h, g, T, d] L2) →
                     G ⊢ ⬊⬊*[h, g, T, d] L1.
/4 width=3 by lsxa_intro/ qed-.

lemma lsxa_lleq_trans: ∀h,g,T,G,L1,d. G ⊢ ⬊⬊*[h, g, T, d] L1 →
                       ∀L2. L1 ≡[T, d] L2 → G ⊢ ⬊⬊*[h, g, T, d] L2.
#h #g #T #G #L1 #d #H @(lsxa_ind … H) -L1
#L1 #_ #IHL1 #L2 #HL12 @lsxa_intro
#K2 #HLK2 #HnLK2 elim (lleq_lpxs_trans … HLK2 … HL12) -HLK2
/5 width=4 by lleq_canc_sn, lleq_trans/
qed-.

lemma lsxa_lpxs_trans: ∀h,g,T,G,L1,d. G ⊢ ⬊⬊*[h, g, T, d] L1 →
                       ∀L2. ⦃G, L1⦄ ⊢ ➡*[h, g] L2 → G ⊢ ⬊⬊*[h, g, T, d] L2.
#h #g #T #G #L1 #d #H @(lsxa_ind … H) -L1 #L1 #HL1 #IHL1 #L2 #HL12
elim (lleq_dec T L1 L2 d) /3 width=4 by lsxa_lleq_trans/
qed-.

lemma lsxa_intro_lpx: ∀h,g,G,L1,T,d.
                      (∀L2. ⦃G, L1⦄ ⊢ ➡[h, g] L2 → (L1 ≡[T, d] L2 → ⊥) → G ⊢ ⬊⬊*[h, g, T, d] L2) →
                      G ⊢ ⬊⬊*[h, g, T, d] L1.
#h #g #G #L1 #T #d #IH @lsxa_intro_aux
#L #L2 #H @(lpxs_ind_dx … H) -L
[ #H destruct #H elim H //
| #L0 #L elim (lleq_dec T L1 L d) /3 width=1 by/
  #HnT #HL0 #HL2 #_ #HT #_ elim (lleq_lpx_trans … HL0 … HT) -L0
  #L0 #HL10 #HL0 @(lsxa_lpxs_trans … HL2) -HL2
  /5 width=3 by lsxa_lleq_trans, lleq_trans/
]
qed-.

(* Main properties **********************************************************)

theorem lsx_lsxa: ∀h,g,G,L,T,d. G ⊢ ⬊*[h, g, T, d] L → G ⊢ ⬊⬊*[h, g, T, d] L.
#h #g #G #L #T #d #H @(lsx_ind … H) -L
/4 width=1 by lsxa_intro_lpx/
qed.

(* Main inversion lemmas ****************************************************)

theorem lsxa_inv_lsx: ∀h,g,G,L,T,d. G ⊢ ⬊⬊*[h, g, T, d] L → G ⊢ ⬊*[h, g, T, d] L.
#h #g #G #L #T #d #H @(lsxa_ind … H) -L
/4 width=1 by lsx_intro, lpx_lpxs/
qed-.

(* Advanced properties ******************************************************)

lemma lsx_intro_alt: ∀h,g,G,L1,T,d.
                     (∀L2. ⦃G, L1⦄ ⊢ ➡*[h, g] L2 → (L1 ≡[T, d] L2 → ⊥) → G ⊢ ⬊*[h, g, T, d] L2) →
                     G ⊢ ⬊*[h, g, T, d] L1.
/6 width=1 by lsxa_inv_lsx, lsx_lsxa, lsxa_intro/ qed.

lemma lsx_lpxs_trans: ∀h,g,G,L1,T,d. G ⊢ ⬊*[h, g, T, d] L1 →
                      ∀L2. ⦃G, L1⦄ ⊢ ➡*[h, g] L2 → G ⊢ ⬊*[h, g, T, d] L2.
/4 width=3 by lsxa_inv_lsx, lsx_lsxa, lsxa_lpxs_trans/ qed-.

(* Advanced eliminators *****************************************************)

lemma lsx_ind_alt: ∀h,g,G,T,d. ∀R:predicate lenv.
                   (∀L1. G ⊢ ⬊*[h, g, T, d] L1 →
                         (∀L2. ⦃G, L1⦄ ⊢ ➡*[h, g] L2 → (L1 ≡[T, d] L2 → ⊥) → R L2) →
                         R L1
                   ) →
                   ∀L. G ⊢ ⬊*[h, g, T, d] L → R L.
#h #g #G #T #d #R #IH #L #H @(lsxa_ind h g G T d … L)
/4 width=1 by lsxa_inv_lsx, lsx_lsxa/
qed-.
