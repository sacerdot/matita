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
include "basic_2/rt_computation/cpxs.ma".

(* UNBOUND CONTEXT-SENSITIVE PARALLEL RT-COMPUTATION FOR TERMS **************)

(* Properties with atomic arity assignment on terms *************************)

lemma cpxs_aaa_conf: ∀h,G,L. Conf3 … (aaa G L) (cpxs h G L).
#h #G #L @TC_Conf3 @cpx_aaa_conf (**) (* auto fails *)
qed-.
