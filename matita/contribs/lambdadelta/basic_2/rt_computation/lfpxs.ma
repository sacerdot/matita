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

include "basic_2/notation/relations/predtysnstar_5.ma".
include "basic_2/i_static/tc_lfxs.ma".
include "basic_2/rt_transition/lfpx.ma".

(* UNCOUNTED PARALLEL RT-COMPUTATION FOR LOCAL ENV.S ON REFERRED ENTRIES ****)

definition lfpxs: ∀h. relation4 genv term lenv lenv ≝
                  λh,G. tc_lfxs (cpx h G).

interpretation
   "uncounted parallel rt-computation on referred entries (local environment)"
   'PRedTySnStar h T G L1 L2 = (lfpxs h G T L1 L2).

(* Basic properties *********************************************************)

(* Basic_2A1: was just: lpx_lpxs *)
lemma lfpx_lfpxs: ∀h,G,T,L1,L2. ⦃G, L1⦄ ⊢ ⬈[h, T] L2 → ⦃G, L1⦄ ⊢ ⬈*[h, T] L2.
/2 width=1 by inj/ qed.

(* Basic_2A1: was just: lpxs_strap1 *)
lemma lfpxs_step_dx: ∀h,G,T,L1,L,L2. ⦃G, L1⦄ ⊢ ⬈*[h, T] L → ⦃G, L⦄ ⊢ ⬈[h, T] L2 → ⦃G, L1⦄ ⊢ ⬈*[h, T] L2.
/2 width=3 by tc_lfxs_step_dx/ qed.

(* Basic_2A1: was just: lpxs_strap2 *)
lemma lfpxs_step_sn: ∀h,G,T,L1,L,L2. ⦃G, L1⦄ ⊢ ⬈[h, T] L → ⦃G, L⦄ ⊢ ⬈*[h, T] L2 → ⦃G, L1⦄ ⊢ ⬈*[h, T] L2.
/2 width=3 by tc_lfxs_step_sn/ qed.

(* Basic inversion lemmas ***************************************************)

(* Basic_2A1: uses: lpxs_inv_atom1 *)
lemma lfpxs_inv_atom1: ∀h,I,G,L2. ⦃G, ⋆⦄ ⊢ ⬈*[h, ⓪{I}] L2 → L2 = ⋆.
/2 width=3 by tc_lfxs_inv_atom_sn/ qed-.

(* Basic_2A1: uses: lpxs_inv_atom2 *)
lemma lfpxs_inv_atom2: ∀h,I,G,L1. ⦃G, L1⦄ ⊢ ⬈*[h, ⓪{I}] ⋆ → L1 = ⋆.
/2 width=3 by tc_lfxs_inv_atom_dx/ qed-.

(* Basic forward lemmas *****************************************************)

lemma lfpxs_fwd_pair_sn: ∀h,I,G,L1,L2,V,T. ⦃G, L1⦄ ⊢ ⬈*[h, ②{I}V.T] L2 → ⦃G, L1⦄ ⊢ ⬈*[h, V] L2.
/2 width=3 by tc_lfxs_fwd_pair_sn/ qed-.

lemma lfpxs_fwd_flat_dx: ∀h,I,G,L1,L2,V,T. ⦃G, L1⦄ ⊢ ⬈*[h, ⓕ{I}V.T] L2 → ⦃G, L1⦄ ⊢ ⬈*[h, T] L2.
/2 width=3 by tc_lfxs_fwd_flat_dx/ qed-.
