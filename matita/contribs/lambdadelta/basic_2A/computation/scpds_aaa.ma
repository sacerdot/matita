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

include "basic_2A/unfold/lstas_aaa.ma".
include "basic_2A/computation/cpxs_aaa.ma".
include "basic_2A/computation/scpds.ma".

(* STRATIFIED DECOMPOSED PARALLEL COMPUTATION ON TERMS **********************)

(* Properties on atomic arity assignment for terms **************************)

lemma scpds_aaa_conf: ∀h,g,G,L,d. Conf3 … (aaa G L) (scpds h g d G L).
#h #g #G #L #d #A #T #HT #U * /3 width=6 by lstas_aaa_conf, cprs_aaa_conf/
qed.
