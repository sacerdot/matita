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

include "basic_2/notation/relations/predtysnstrong_5.ma".
include "basic_2/static/lfdeq.ma".
include "basic_2/rt_transition/lfpx.ma".

(* STRONGLY NORMALIZING LOCAL ENV.S FOR UNCOUNTED PARALLEL RT-TRANSITION ****)

definition lfsx: ∀h. sd h → relation3 term genv lenv ≝
                 λh,o,T,G. SN … (lfpx h G T) (lfdeq h o T).

interpretation
   "strong normalization for uncounted context-sensitive parallel rt-transition on referred entries (local environment)"
   'PRedTySNStrong h o T G L = (lfsx h o T G L).

(* Basic eliminators ********************************************************)

(* Basic_2A1: uses: lsx_ind *)
lemma lfsx_ind: ∀h,o,G,T. ∀R:predicate lenv.
                (∀L1. G ⊢ ⬈*[h, o, T] 𝐒⦃L1⦄ →
                      (∀L2. ⦃G, L1⦄ ⊢ ⬈[h, T] L2 → (L1 ≡[h, o, T] L2 → ⊥) → R L2) →
                      R L1
                ) →
                ∀L. G ⊢ ⬈*[h, o, T] 𝐒⦃L⦄ → R L.
#h #o #G #T #R #H0 #L1 #H elim H -L1
/5 width=1 by lfdeq_sym, SN_intro/
qed-.

(* Basic properties *********************************************************)

(* Basic_2A1: uses: lsx_intro *)
lemma lfsx_intro: ∀h,o,G,L1,T.
                  (∀L2. ⦃G, L1⦄ ⊢ ⬈[h, T] L2 → (L1 ≡[h, o, T] L2 → ⊥) → G ⊢ ⬈*[h, o, T] 𝐒⦃L2⦄) →
                  G ⊢ ⬈*[h, o, T] 𝐒⦃L1⦄.
/5 width=1 by lfdeq_sym, SN_intro/ qed.

(* Basic_2A1: uses: lsx_sort *)
lemma lfsx_sort: ∀h,o,G,L,s. G ⊢ ⬈*[h, o, ⋆s] 𝐒⦃L⦄.
#h #o #G #L1 #s @lfsx_intro
#L2 #H #Hs elim Hs -Hs elim (lfpx_inv_sort … H) -H *
[ #H1 #H2 destruct //
| #I1 #I2 #K1 #K2 #HK12 #H1 #H2 destruct
  /4 width=4 by lfdeq_sort, lfxs_isid, frees_sort, frees_inv_sort/
]
qed.

(* Basic_2A1: uses: lsx_gref *)
lemma lfsx_gref: ∀h,o,G,L,p. G ⊢ ⬈*[h, o, §p] 𝐒⦃L⦄.
#h #o #G #L1 #s @lfsx_intro
#L2 #H #Hs elim Hs -Hs elim (lfpx_inv_gref … H) -H *
[ #H1 #H2 destruct //
| #I1 #I2 #K1 #K2 #HK12 #H1 #H2 destruct
  /4 width=4 by lfdeq_gref, lfxs_isid, frees_gref, frees_inv_gref/
]
qed.

(* Basic_2A1: removed theorems 9:
              lsx_ge_up lsx_ge
              lsxa_ind lsxa_intro lsxa_lleq_trans lsxa_lpxs_trans lsxa_intro_lpx lsx_lsxa lsxa_inv_lsx
*)
