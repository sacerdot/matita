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
include "basic_2/rt_transition/lfpx.ma".

(* UNCOUNTED PARALLEL RT-COMPUTATION FOR LOCAL ENV.S ON REFERRED ENTRIES ****)

definition lfpxs: ∀h. relation4 genv term lenv lenv ≝
                  λh,G,T. TC … (lfpx h G T).

interpretation
   "uncounted parallel rt-computation on referred entries (local environment)"
   'PRedTySnStar h T G L1 L2 = (lfpxs h G T L1 L2).

(* Basic properties *********************************************************)

(* Basic_2A1: was just: lpx_lpxs *)
lemma lfpx_lfpxs: ∀h,G,T,L1,L2. ⦃G, L1⦄ ⊢ ⬈[h, T] L2 → ⦃G, L1⦄ ⊢ ⬈*[h, T] L2.
/2 width=1 by inj/ qed.

(* Basic_2A1: was just: lpxs_strap1 *)
lemma lfpxs_strap1: ∀h,G,T,L1,L,L2. ⦃G, L1⦄ ⊢ ⬈*[h, T] L → ⦃G, L⦄ ⊢ ⬈[h, T] L2 → ⦃G, L1⦄ ⊢ ⬈*[h, T] L2.
/2 width=3 by step/ qed.

(* Basic_2A1: was just: lpxs_strap2 *)
lemma lfpxs_strap2: ∀h,G,T,L1,L,L2. ⦃G, L1⦄ ⊢ ⬈[h, T] L → ⦃G, L⦄ ⊢ ⬈*[h, T] L2 → ⦃G, L1⦄ ⊢ ⬈*[h, T] L2.
/2 width=3 by TC_strap/ qed.
(*
(* Basic_2A1: was just: lpxs_pair_refl *)
lemma lfpxs_pair_refl: ∀h,G,T,L1,L2. ⦃G, L1⦄ ⊢ ⬈*[h, T] L2 → ∀I,V. ⦃G, L1.ⓑ{I}V⦄ ⊢ ⬈*[h, T] L2.ⓑ{I}V.
/2 width=1 by TC_lpx_sn_pair_refl/ qed.

(* Basic inversion lemmas ***************************************************)

(* Basic_2A1: was just: lpxs_inv_atom1 *)
lemma lfpxs_inv_atom1: ∀h,G,L2.T. ⦃G, ⋆⦄ ⊢ ⬈*[h, T] L2 → L2 = ⋆.
/2 width=2 by TC_lpx_sn_inv_atom1/ qed-.

(* Basic_2A1: was just: lpxs_inv_atom2 *)
lemma lfpxs_inv_atom2: ∀h,G,L1,T. ⦃G, L1⦄ ⊢ ⬈*[h, T] ⋆ → L1 = ⋆.
/2 width=2 by TC_lpx_sn_inv_atom2/ qed-.
*)

(* Basic_2A1: removed theorems 1:
              lpxs_pair
*)
