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
include "basic_2/rt_transition/lfpx_frees.ma".
include "basic_2/rt_computation/lpxs.ma".
include "basic_2/rt_computation/lfpxs.ma".

(* UNCOUNTED PARALLEL RT-COMPUTATION FOR LOCAL ENV.S ON REFERRED ENTRIES ****)

(* Properties with uncounted parallel rt-computation for local environments *)

lemma lfpxs_lpxs_lfeq: ∀h,G,L1,L. ⦃G, L1⦄ ⊢ ⬈*[h] L →
                       ∀L2,T. L ≡[T] L2 → ⦃G, L1⦄ ⊢ ⬈*[h, T] L2.
/2 width=3 by tc_lfxs_lex_lfeq/ qed.

(* Inversion lemmas with uncounted parallel rt-computation for local envs ***)

lemma lpx_cpxs_ext_trans: ∀h,G. s_rs_transitive_isid cfull (cpx_ext h G).
#H1 #H2 #H3 #H4 #H5 #H6 #H7 #H8 #H9 #H10


lemma tc_lfxs_inv_lex_lfeq: ∀h,G,L1,L2,T. ⦃G, L1⦄ ⊢ ⬈*[h, T] L2 →
                            ∃∃L. ⦃G, L1⦄ ⊢ ⬈*[h] L & L ≡[T] L2.
#h #G @tc_lfxs_inv_lex_lfeq //
[ @lfpx_frees_conf
| @lpx_cpxs_ext_trans