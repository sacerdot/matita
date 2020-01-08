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

include "basic_2/rt_transition/rpx_lpx.ma".

(* UNBOUND PARALLEL RT-TRANSITION FOR FULL LOCAL ENVIRONMENTS ***************)

(* Forward lemmas with free variables inclusion for restricted closures *****)

(* Basic_2A1: uses: lpx_cpx_frees_trans *)
lemma lpx_cpx_conf_fsge (h) (G): ∀L0,T0,T1. ❪G,L0❫ ⊢ T0 ⬈[h] T1 →
                                 ∀L2. ❪G,L0❫ ⊢ ⬈[h] L2 → ❪L2,T1❫ ⊆ ❪L0,T0❫.
/3 width=4 by rpx_cpx_conf_fsge, lpx_rpx/ qed-.

(* Basic_2A1: uses: lpx_frees_trans *)
lemma lpx_fsge_comp (h) (G): ∀L0,L2,T0. ❪G,L0❫ ⊢ ⬈[h] L2 → ❪L2,T0❫ ⊆ ❪L0,T0❫.
/2 width=4 by lpx_cpx_conf_fsge/ qed-.
