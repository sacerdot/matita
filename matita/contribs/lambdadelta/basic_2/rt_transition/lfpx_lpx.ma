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

include "basic_2/static/lfxs_lex.ma".
include "basic_2/rt_transition/lfpx_fsle.ma".
include "basic_2/rt_transition/lpx.ma".

(* UNCOUNTED PARALLEL RT-TRANSITION FOR LOCAL ENV.S ON REFERRED ENTRIES *****)

(* Properties with uncounted parallel rt-transition for local environments **)

lemma lfpx_lpx: ∀h,G,L1,L2,T. ⦃G, L1⦄ ⊢ ⬈[h] L2 → ⦃G, L1⦄ ⊢ ⬈[h, T] L2.
/2 width=1 by lfxs_lex/ qed.

(* Inversion lemmas with uncounted parallel rt-transition for local envs ****)

lemma lfpx_inv_lpx_lfeq: ∀h,G,L1,L2,T. ⦃G, L1⦄ ⊢ ⬈[h, T] L2 →
                         ∃∃L. ⦃G, L1⦄ ⊢ ⬈[h] L & L ≐[T] L2.
/3 width=3 by lfpx_fsge_comp, lfxs_inv_lex_lfeq/ qed-.
