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

include "basic_2/rt_transition/lfpx_frees.ma".
include "basic_2/rt_transition/cpm_cpx.ma".

(* PARALLEL R-TRANSITION FOR LOCAL ENV.S ON REFERRED ENTRIES ****************)

(* Properties with context-sensitive free variables *************************)

lemma cpm_frees_conf: ∀n,h,G. R_frees_confluent (cpm n h G).
/3 width=6 by cpm_fwd_cpx, cpx_frees_conf/ qed-.

lemma lfpr_frees_conf: ∀h,G. lexs_frees_confluent (cpm 0 h G) cfull.
/4 width=9 by cpm_fwd_cpx, lfpx_frees_conf, lexs_co/ qed-.
