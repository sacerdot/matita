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

include "basic_2/rt_computation/lpxs_aaa.ma".
include "basic_2/rt_computation/lprs_lpxs.ma".

(* PARALLEL R-COMPUTATION FOR FULL LOCAL ENVIRONMENTS ***********************)

(* Properties with atomic arity assignment for terms ************************)

lemma lprs_aaa_conf (h) (G) (T):
      Conf3 … (λL. aaa G L T) (lprs h 0 G).
/3 width=5 by lprs_fwd_lpxs, lpxs_aaa_conf/ qed-.
