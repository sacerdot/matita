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

include "basic_2/rt_computation/fpbg_fqup.ma".
include "basic_2/rt_computation/cpms_fpbs.ma".

(* T-BOUND CONTEXT-SENSITIVE PARALLEL RT-COMPUTATION FOR TERMS **************)

(* Forward lemmas with proper parallel rst-computation for closures *********)

lemma fqup_cpms_fwd_fpbg (h) (o): ∀G1,G2,L1,L2,T1,T. ⦃G1, L1, T1⦄ ⊐+ ⦃G2, L2, T⦄ →
                                  ∀n,T2. ⦃G2, L2⦄ ⊢ T ➡*[n,h] T2 → ⦃G1, L1, T1⦄ >[h,o] ⦃G2, L2, T2⦄.
/3 width=5 by cpms_fwd_fpbs, fqup_fpbg,fpbg_fpbs_trans/ qed-.
