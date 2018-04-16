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

include "basic_2/relocation/lex_tc.ma".
include "basic_2/rt_computation/lpxs.ma".
include "basic_2/rt_computation/cpxs_lpx.ma".

(* UNCOUNTED PARALLEL RT-COMPUTATION FOR LOCAL ENVIRONMENTS *****************)

(* Properties with uncounted rt-transition for local environments ***********)

(* Basic_2A1: was: lpxs_strap1 *)
lemma lpxs_step_dx: ∀h,G,L1,L. ⦃G, L1⦄ ⊢ ⬈*[h] L →
                    ∀L2. ⦃G, L⦄ ⊢ ⬈[h] L2 → ⦃G, L1⦄ ⊢ ⬈*[h] L2.
/3 width=3 by lpx_cpxs_trans, lex_CTC_step_dx/ qed-.

(* Basic_2A1: was: lpxs_strap2 *)
lemma lpxs_step_sn: ∀h,G,L1,L. ⦃G, L1⦄ ⊢ ⬈[h] L →
                    ∀L2. ⦃G, L⦄ ⊢ ⬈*[h] L2 → ⦃G, L1⦄ ⊢ ⬈*[h] L2.
/3 width=3 by lpx_cpxs_trans, lex_CTC_step_sn/ qed-.
