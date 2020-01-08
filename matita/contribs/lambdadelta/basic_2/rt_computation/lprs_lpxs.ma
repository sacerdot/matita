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

include "basic_2/rt_computation/cpms_cpxs.ma".
include "basic_2/rt_computation/lpxs.ma".
include "basic_2/rt_computation/lprs.ma".

(* PARALLEL R-COMPUTATION FOR FULL LOCAL ENVIRONMENTS ***********************)

(* Forward lemmas with unbound rt-computation for full local environments ***)

(* Basic_2A1: was: lprs_lpxs *)
(* Note: original proof uses lpr_fwd_lpx and monotonic_TC *)
lemma lprs_fwd_lpxs (h) (G) : ∀L1,L2. ❪G,L1❫ ⊢ ➡*[h] L2 → ❪G,L1❫ ⊢ ⬈*[h] L2.
/3 width=3 by cpms_fwd_cpxs, lex_co/ qed-.
