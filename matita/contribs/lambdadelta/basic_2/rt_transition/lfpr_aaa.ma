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

include "basic_2/rt_transition/lfpx_aaa.ma".
include "basic_2/rt_transition/lfpr_lfpx.ma".

(* PARALLEL R-TRANSITION FOR LOCAL ENV.S ON REFERRED ENTRIES ****************)

(* Properties with atomic arity assignment for terms ************************)

lemma cpr_aaa_conf: ∀h,G,L. Conf3 … (aaa G L) (cpm 0 h G L).
/3 width=5 by cpx_aaa_conf, cpm_fwd_cpx/ qed-.

(* Basic_2A1: uses: lpr_aaa_conf *)
lemma lfpr_aaa_conf: ∀h,G,T. Conf3 … (λL. aaa G L T) (lfpr h G T).
/3 width=4 by lfpx_aaa_conf, lfpr_fwd_lfpx/ qed-.
