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

include "basic_2/rt_computation/lfpxs_cpxs.ma".
include "basic_2/rt_computation/lfpxs_lpxs.ma".

(* UNCOUNTED PARALLEL RT-COMPUTATION FOR LOCAL ENVIRONMENTS *****************)

(* Properties with uncounted context-sensitive rt-computation for terms *****)

lemma lpxs_cpx_trans: ∀h,G. s_r_transitive … (cpx h G) (λ_.lpxs h G).
/3 width=3 by lfpxs_cpx_trans, lfpxs_lpxs/ qed-.

lemma lpxs_cpxs_trans: ∀h,G. s_rs_transitive … (cpx h G) (λ_.lpxs h G).
/3 width=3 by lfpxs_cpxs_trans, lfpxs_lpxs/ qed-.
