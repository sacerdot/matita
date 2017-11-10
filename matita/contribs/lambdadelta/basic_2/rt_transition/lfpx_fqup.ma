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

include "basic_2/static/lfxs_fqup.ma".
include "basic_2/rt_transition/lfpx.ma".

(* UNCOUNTED PARALLEL RT-TRANSITION FOR LOCAL ENV.S ON REFERRED ENTRIES *****)

(* Advanced properties ******************************************************)

(* Basic_2A1: uses: lpx_refl *)
lemma lfpx_refl: ∀h,G,T. reflexive … (lfpx h G T).
/2 width=1 by lfxs_refl/ qed.

(* Basic_2A1: uses: lpx_pair *)
lemma lfpx_pair_refl: ∀h,G,L,V1,V2. ⦃G, L⦄ ⊢ V1 ⬈[h] V2 →
                      ∀I,T. ⦃G, L.ⓑ{I}V1⦄ ⊢ ⬈[h, T] L.ⓑ{I}V2.
/2 width=1 by lfxs_pair_refl/ qed.

(* Advanced inversion lemmas ************************************************)

lemma lfpx_inv_bind_void: ∀h,p,I,G,L1,L2,V,T. ⦃G, L1⦄ ⊢ ⬈[h, ⓑ{p,I}V.T] L2 →
                          ∧∧ ⦃G, L1⦄ ⊢ ⬈[h, V] L2 & ⦃G, L1.ⓧ⦄ ⊢ ⬈[h, T] L2.ⓧ.
/2 width=3 by lfxs_inv_bind_void/ qed-.

(* Advanced forward lemmas **************************************************)

lemma lfpx_fwd_bind_dx_void: ∀h,p,I,G,L1,L2,V,T.
                             ⦃G, L1⦄ ⊢ ⬈[h, ⓑ{p,I}V.T] L2 → ⦃G, L1.ⓧ⦄ ⊢ ⬈[h, T] L2.ⓧ.
/2 width=4 by lfxs_fwd_bind_dx_void/ qed-.
