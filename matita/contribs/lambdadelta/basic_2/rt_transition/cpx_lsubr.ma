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

include "basic_2/rt_transition/cpg_lsubr.ma".
include "basic_2/rt_transition/cpx.ma".

(* UNCOUNTED CONTEXT-SENSITIVE PARALLEL REDUCTION FOR TERMS *****************)

lemma lsubr_cpx_trans: ∀h,G. lsub_trans … (cpx h G) lsubr.
#h #G #L1 #T1 #T2 * /3 width=4 by lsubr_cpg_trans, ex_intro/
qed-.
