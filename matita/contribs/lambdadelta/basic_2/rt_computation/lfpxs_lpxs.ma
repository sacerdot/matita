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

include "basic_2/i_static/tc_lfxs_lex.ma".
include "basic_2/rt_transition/cpx_lfeq.ma".
include "basic_2/rt_computation/cpxs_lpx.ma".
include "basic_2/rt_computation/lpxs.ma".
include "basic_2/rt_computation/lfpxs.ma".

(* UNCOUNTED PARALLEL RT-COMPUTATION FOR LOCAL ENV.S ON REFERRED ENTRIES ****)

(* Properties with uncounted parallel rt-computation for local environments *)

lemma lfpxs_lpxs: ∀h,G,L1,L2,T. ⦃G, L1⦄ ⊢ ⬈*[h] L2 → ⦃G, L1⦄ ⊢ ⬈*[h, T] L2.
/2 width=1 by tc_lfxs_lex/ qed.

lemma lfpxs_lpxs_lfeq: ∀h,G,L1,L. ⦃G, L1⦄ ⊢ ⬈*[h] L →
                       ∀L2,T. L ≐[T] L2 → ⦃G, L1⦄ ⊢ ⬈*[h, T] L2.
/2 width=3 by tc_lfxs_lex_lfeq/ qed.

(* Inversion lemmas with uncounted parallel rt-computation for local envs ***)

lemma lfpxs_inv_lpxs_lfeq: ∀h,G,L1,L2,T. ⦃G, L1⦄ ⊢ ⬈*[h, T] L2 →
                           ∃∃L. ⦃G, L1⦄ ⊢ ⬈*[h] L & L ≐[T] L2.
/3 width=5 by lfpx_fsge_comp, lpx_cpxs_trans, lfeq_cpx_trans, tc_lfxs_inv_lex_lfeq/ qed-.
