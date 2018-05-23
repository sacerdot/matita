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

include "basic_2/static/lfxs_lfxs.ma".
include "basic_2/rt_transition/lfpx.ma".

(* UNBOUND PARALLEL RT-TRANSITION FOR REFERRED LOCAL ENVIRONMENTS ***********)

(* Main properties **********************************************************)

theorem lfpx_bind: ∀h,G,L1,L2,V1. ⦃G, L1⦄ ⊢ ⬈[h, V1] L2 →
                   ∀I,V2,T. ⦃G, L1.ⓑ{I}V1⦄ ⊢ ⬈[h, T] L2.ⓑ{I}V2 →
                   ∀p. ⦃G, L1⦄ ⊢ ⬈[h, ⓑ{p,I}V1.T] L2.
/2 width=2 by lfxs_bind/ qed.

theorem lfpx_flat: ∀h,G,L1,L2,V. ⦃G, L1⦄ ⊢ ⬈[h, V] L2 →
                   ∀I,T. ⦃G, L1⦄ ⊢ ⬈[h, T] L2 → ⦃G, L1⦄ ⊢ ⬈[h, ⓕ{I}V.T] L2.
/2 width=1 by lfxs_flat/ qed.

theorem lfpx_bind_void: ∀h,G,L1,L2,V. ⦃G, L1⦄ ⊢ ⬈[h, V] L2 →
                        ∀T. ⦃G, L1.ⓧ⦄ ⊢ ⬈[h, T] L2.ⓧ →
                        ∀p,I. ⦃G, L1⦄ ⊢ ⬈[h, ⓑ{p,I}V.T] L2.
/2 width=1 by lfxs_bind_void/ qed.
