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

(* STRONGLY NORMALIZING LOCAL ENV.S FOR UNBOUND PARALLEL RT-TRANSITION ******)

definition lfsx: ∀h. sd h → relation3 term genv lenv ≝
                 λh,o,T,G. SN … (lfpx h G T) (lfdeq h o T).

interpretation
   "strong normalization for unbound context-sensitive parallel rt-transition on referred entries (local environment)"
   'PRedTySNStrong h o T G L = (lfsx h o T G L).

(* Basic eliminators ********************************************************)

(* Basic_2A1: uses: lsx_ind *)
lemma lfsx_ind: ∀h,o,G,T. ∀R:predicate lenv.
                (∀L1. G ⊢ ⬈*[h, o, T] 𝐒⦃L1⦄ →
                      (∀L2. ⦃G, L1⦄ ⊢ ⬈[h, T] L2 → (L1 ≛[h, o, T] L2 → ⊥) → R L2) →
                      R L1
                ) →
                ∀L. G ⊢ ⬈*[h, o, T] 𝐒⦃L⦄ → R L.
#h #o #G #T #R #H0 #L1 #H elim H -L1
/5 width=1 by SN_intro/
qed-.

(* Basic properties *********************************************************)

(* Basic_2A1: uses: lsx_intro *)
lemma lfsx_intro: ∀h,o,G,L1,T.
                  (∀L2. ⦃G, L1⦄ ⊢ ⬈[h, T] L2 → (L1 ≛[h, o, T] L2 → ⊥) → G ⊢ ⬈*[h, o, T] 𝐒⦃L2⦄) →
                  G ⊢ ⬈*[h, o, T] 𝐒⦃L1⦄.
/5 width=1 by SN_intro/ qed.

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

lemma lfsx_unit: ∀h,o,I,G,L. G ⊢ ⬈*[h, o, #0] 𝐒⦃L.ⓤ{I}⦄.
#h #o #I #G #L1 @lfsx_intro
#Y #HY #HnY elim HnY -HnY /2 width=2 by lfxs_unit_sn/
qed.

(* Basic forward lemmas *****************************************************)

fact lfsx_fwd_pair_aux: ∀h,o,G,L. G ⊢ ⬈*[h, o, #0] 𝐒⦃L⦄ →
                        ∀I,K,V. L = K.ⓑ{I}V → G ⊢ ⬈*[h, o, V] 𝐒⦃K⦄.
#h #o #G #L #H
@(lfsx_ind … H) -L #L1 #_ #IH #I #K1 #V #H destruct
/5 width=5 by lfpx_pair, lfsx_intro, lfdeq_fwd_zero_pair/
qed-.

lemma lfsx_fwd_pair: ∀h,o,I,G,K,V.
                     G ⊢ ⬈*[h, o, #0] 𝐒⦃K.ⓑ{I}V⦄ → G ⊢ ⬈*[h, o, V] 𝐒⦃K⦄.
/2 width=4 by lfsx_fwd_pair_aux/ qed-.

(* Basic_2A1: removed theorems 9:
              lsx_ge_up lsx_ge
              lsxa_ind lsxa_intro lsxa_lleq_trans lsxa_lpxs_trans lsxa_intro_lpx lsx_lsxa lsxa_inv_lsx
*)
