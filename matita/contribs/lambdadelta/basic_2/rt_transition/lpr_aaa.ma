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

include "basic_2/rt_transition/lpr_lpx.ma".
include "basic_2/rt_transition/lpx_aaa.ma".

(* PARALLEL R-TRANSITION FOR FULL LOCAL ENVIRONMENTS ************************)

(* Properties with atomic arity assignment for terms ************************)

lemma lpr_aaa_conf (h): ∀G,T. Conf3 … (λL. aaa G L T) (lpr h 0 G).
/3 width=5 by lpx_aaa_conf, lpr_fwd_lpx/ qed-.
