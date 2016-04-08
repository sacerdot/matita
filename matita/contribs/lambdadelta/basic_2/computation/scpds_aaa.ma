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

include "basic_2/unfold/lstas_aaa.ma".
include "basic_2/computation/cpxs_aaa.ma".
include "basic_2/computation/scpds.ma".

(* STRATIFIED DECOMPOSED PARALLEL COMPUTATION ON TERMS **********************)

(* Properties on atomic arity assignment for terms **************************)

lemma scpds_aaa_conf: ∀h,o,G,L,d. Conf3 … (aaa G L) (scpds h o d G L).
#h #o #G #L #d #A #T #HT #U * /3 width=6 by lstas_aaa_conf, cprs_aaa_conf/
qed.
