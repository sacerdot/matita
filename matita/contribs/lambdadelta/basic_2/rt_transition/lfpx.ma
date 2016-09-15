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

include "basic_2/notation/relations/predtysn_5.ma".
include "basic_2/static/lfxs.ma".
include "basic_2/rt_transition/cpx.ma".

(* UNCOUNTED PARALLEL RT-TRANSITION FOR LOCAL ENV.S ON REFERRED ENTRIES *****)

definition lfpx: sh → genv → relation3 term lenv lenv ≝
                 λh,G. lfxs (cpx h G).

interpretation
   "uncounted parallel rt-transition on referred entries (local environment)"
   'PRedTySn h T G L1 L2 = (lfpx h G T L1 L2).

(* Basic properties ***********************************************************)

lemma lfpx_atom: ∀h,I,G. ⦃G, ⋆⦄ ⊢ ⬈[h, ⓪{I}] ⋆.
/2 width=1 by lfxs_atom/ qed.

lemma lfpx_sort: ∀h,I,G,L1,L2,V1,V2,s.
                 ⦃G, L1⦄ ⊢ ⬈[h, ⋆s] L2 → ⦃G, L1.ⓑ{I}V1⦄ ⊢ ⬈[h, ⋆s] L2.ⓑ{I}V2.
/2 width=1 by lfxs_sort/ qed.

lemma lfpx_zero: ∀h,I,G,L1,L2,V.
                 ⦃G, L1⦄ ⊢ ⬈[h, V] L2 → ⦃G, L1.ⓑ{I}V⦄ ⊢ ⬈[h, #0] L2.ⓑ{I}V.
/2 width=1 by lfxs_zero/ qed.

lemma lfpx_lref: ∀h,I,G,L1,L2,V1,V2,i.
                 ⦃G, L1⦄ ⊢ ⬈[h, #i] L2 → ⦃G, L1.ⓑ{I}V1⦄ ⊢ ⬈[h, #⫯i] L2.ⓑ{I}V2.
/2 width=1 by lfxs_lref/ qed.

lemma lfpx_gref: ∀h,I,G,L1,L2,V1,V2,l.
                 ⦃G, L1⦄ ⊢ ⬈[h, §l] L2 → ⦃G, L1.ⓑ{I}V1⦄ ⊢ ⬈[h, §l] L2.ⓑ{I}V2.
/2 width=1 by lfxs_gref/ qed.

lemma lfpx_pair_repl_dx: ∀h,I,G,L1,L2,T,V,V1.
                         ⦃G, L1.ⓑ{I}V⦄ ⊢ ⬈[h, T] L2.ⓑ{I}V1 →
                         ∀V2. ⦃G, L1⦄ ⊢ V ⬈[h] V2 →
                         ⦃G, L1.ⓑ{I}V⦄ ⊢ ⬈[h, T] L2.ⓑ{I}V2.
/2 width=2 by lfxs_pair_repl_dx/ qed-.

(* Basic inversion lemmas ***************************************************)

lemma lfpx_inv_atom_sn: ∀h,I,G,Y2. ⦃G, ⋆⦄ ⊢ ⬈[h, ⓪{I}] Y2 → Y2 = ⋆.
/2 width=3 by lfxs_inv_atom_sn/ qed-.

lemma lfpx_inv_atom_dx: ∀h,I,G,Y1. ⦃G, Y1⦄ ⊢ ⬈[h, ⓪{I}] ⋆ → Y1 = ⋆.
/2 width=3 by lfxs_inv_atom_dx/ qed-.

lemma lfpx_inv_zero: ∀h,G,Y1,Y2. ⦃G, Y1⦄ ⊢ ⬈[h, #0] Y2 →
                     (Y1 = ⋆ ∧ Y2 = ⋆) ∨
                     ∃∃I,L1,L2,V1,V2. ⦃G, L1⦄ ⊢ ⬈[h, V1] L2 &
                                      ⦃G, L1⦄ ⊢ V1 ⬈[h] V2 &
                                      Y1 = L1.ⓑ{I}V1 & Y2 = L2.ⓑ{I}V2.
/2 width=1 by lfxs_inv_zero/ qed-.

lemma lfpx_inv_lref: ∀h,G,Y1,Y2,i. ⦃G, Y1⦄ ⊢ ⬈[h, #⫯i] Y2 →
                     (Y1 = ⋆ ∧ Y2 = ⋆) ∨
                     ∃∃I,L1,L2,V1,V2. ⦃G, L1⦄ ⊢ ⬈[h, #i] L2 &
                                      Y1 = L1.ⓑ{I}V1 & Y2 = L2.ⓑ{I}V2.
/2 width=1 by lfxs_inv_lref/ qed-.

lemma lfpx_inv_bind: ∀h,p,I,G,L1,L2,V,T. ⦃G, L1⦄ ⊢ ⬈[h, ⓑ{p,I}V.T] L2 →
                     ⦃G, L1⦄ ⊢ ⬈[h, V] L2 ∧ ⦃G, L1.ⓑ{I}V⦄ ⊢ ⬈[h, T] L2.ⓑ{I}V.
/2 width=2 by lfxs_inv_bind/ qed-.

lemma lfpx_inv_flat: ∀h,I,G,L1,L2,V,T. ⦃G, L1⦄ ⊢ ⬈[h, ⓕ{I}V.T] L2 →
                     ⦃G, L1⦄ ⊢ ⬈[h, V] L2 ∧ ⦃G, L1⦄ ⊢ ⬈[h, T] L2.
/2 width=2 by lfxs_inv_flat/ qed-.

(* Advanced inversion lemmas ************************************************)

lemma lfpx_inv_zero_pair_sn: ∀h,I,G,Y2,L1,V1. ⦃G, L1.ⓑ{I}V1⦄ ⊢ ⬈[h, #0] Y2 →
                             ∃∃L2,V2. ⦃G, L1⦄ ⊢ ⬈[h, V1] L2 & ⦃G, L1⦄ ⊢ V1 ⬈[h] V2 &
                                      Y2 = L2.ⓑ{I}V2.
/2 width=1 by lfxs_inv_zero_pair_sn/ qed-.

lemma lfpx_inv_zero_pair_dx: ∀h,I,G,Y1,L2,V2. ⦃G, Y1⦄ ⊢ ⬈[h, #0] L2.ⓑ{I}V2 →
                             ∃∃L1,V1. ⦃G, L1⦄ ⊢ ⬈[h, V1] L2 & ⦃G, L1⦄ ⊢ V1 ⬈[h] V2 &
                                      Y1 = L1.ⓑ{I}V1.
/2 width=1 by lfxs_inv_zero_pair_dx/ qed-.

lemma lfpx_inv_lref_pair_sn: ∀h,I,G,Y2,L1,V1,i. ⦃G, L1.ⓑ{I}V1⦄ ⊢ ⬈[h, #⫯i] Y2 →
                             ∃∃L2,V2. ⦃G, L1⦄ ⊢ ⬈[h, #i] L2 & Y2 = L2.ⓑ{I}V2.
/2 width=2 by lfxs_inv_lref_pair_sn/ qed-.

lemma lfpx_inv_lref_pair_dx: ∀h,I,G,Y1,L2,V2,i. ⦃G, Y1⦄ ⊢ ⬈[h, #⫯i] L2.ⓑ{I}V2 →
                             ∃∃L1,V1. ⦃G, L1⦄ ⊢ ⬈[h, #i] L2 & Y1 = L1.ⓑ{I}V1.
/2 width=2 by lfxs_inv_lref_pair_dx/ qed-.

(* Basic forward lemmas *****************************************************)

lemma lfpx_fwd_bind_sn: ∀h,p,I,G,L1,L2,V,T.
                        ⦃G, L1⦄ ⊢ ⬈[h, ⓑ{p,I}V.T] L2 → ⦃G, L1⦄ ⊢ ⬈[h, V] L2.
/2 width=4 by lfxs_fwd_bind_sn/ qed-.

lemma lfpx_fwd_bind_dx: ∀h,p,I,G,L1,L2,V,T.
                        ⦃G, L1⦄ ⊢ ⬈[h, ⓑ{p,I}V.T] L2 → ⦃G, L1.ⓑ{I}V⦄ ⊢ ⬈[h, T] L2.ⓑ{I}V.
/2 width=2 by lfxs_fwd_bind_dx/ qed-.

lemma lfpx_fwd_flat_sn: ∀h,I,G,L1,L2,V,T.
                        ⦃G, L1⦄ ⊢ ⬈[h, ⓕ{I}V.T] L2 → ⦃G, L1⦄ ⊢ ⬈[h, V] L2.
/2 width=3 by lfxs_fwd_flat_sn/ qed-.

lemma lfpx_fwd_flat_dx: ∀h,I,G,L1,L2,V,T.
                        ⦃G, L1⦄ ⊢ ⬈[h, ⓕ{I}V.T] L2 → ⦃G, L1⦄ ⊢ ⬈[h, T] L2.
/2 width=3 by lfxs_fwd_flat_dx/ qed-.

lemma lfpx_fwd_pair_sn: ∀h,I,G,L1,L2,V,T.
                        ⦃G, L1⦄ ⊢ ⬈[h, ②{I}V.T] L2 → ⦃G, L1⦄ ⊢ ⬈[h, V] L2.
/2 width=3 by lfxs_fwd_pair_sn/ qed-.

(* Basic_2A1: removed theorems 14:
              lpx_refl lpx_pair lpx_fwd_length
              lpx_inv_atom1 lpx_inv_pair1 lpx_inv_atom2 lpx_inv_pair2 lpx_inv_pair
              lpx_drop_conf drop_lpx_trans lpx_drop_trans_O1
              lpx_cpx_frees_trans cpx_frees_trans lpx_frees_trans
*)
