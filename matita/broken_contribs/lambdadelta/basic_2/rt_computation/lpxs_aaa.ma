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

include "basic_2/rt_transition/lpx_aaa.ma".
include "basic_2/rt_computation/lpxs_lpx.ma".

(* EXTENDED PARALLEL RT-COMPUTATION FOR FULL LOCAL ENVIRONMENTS *************)

(* Properties with atomic arity assignment for terms ************************)

lemma lpxs_aaa_conf (G) (T):
      Conf3 … (λL. aaa G L T) (lpxs G).
#G #T #A #L1 #HT #L2 #H
lapply (lex_inv_CTC … H) -H //
@TC_Conf3 [4: // |*: /2 width=4 by lpx_aaa_conf/ ]
qed-.
