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

include "static_2/static/rex_length.ma".
include "basic_2/rt_transition/rpx.ma".

(* UNBOUND PARALLEL RT-TRANSITION FOR REFERRED LOCAL ENVIRONMENTS ***********)

(* Forward lemmas with length for local environments ************************)

lemma rpx_fwd_length: ∀h,G,L1,L2,T. ⦃G,L1⦄ ⊢ ⬈[h,T] L2 → |L1| = |L2|.
/2 width=3 by rex_fwd_length/ qed-.

(* Inversion lemmas with length for local environments **********************)

lemma rpx_inv_zero_length: ∀h,G,Y1,Y2. ⦃G,Y1⦄ ⊢ ⬈[h,#0] Y2 →
                           ∨∨ ∧∧ Y1 = ⋆ & Y2 = ⋆
                            | ∃∃I,L1,L2,V1,V2. ⦃G,L1⦄ ⊢ ⬈[h,V1] L2 &
                                               ⦃G,L1⦄ ⊢ V1 ⬈[h] V2 &
                                               Y1 = L1.ⓑ{I}V1 & Y2 = L2.ⓑ{I}V2
                            | ∃∃I,L1,L2. |L1| = |L2| & Y1 = L1.ⓤ{I} & Y2 = L2.ⓤ{I}.
/2 width=1 by rex_inv_zero_length/ qed-.
