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

include "basic_2/unfold/lsstas_aaa.ma".
include "basic_2/computation/cpxs_aaa.ma".
include "basic_2/computation/cpds.ma".

(* DECOMPOSED EXTENDED PARALLEL COMPUTATION ON TERMS ************************)

(* Properties on atomic arity assignment for terms **************************)

lemma aaa_cpds_conf: ∀h,g,G,L. Conf3 … (aaa G L) (cpds h g G L).
#h #g #G #L #A #T #HT #U * /3 width=6 by aaa_lsstas_conf, aaa_cprs_conf/
qed.