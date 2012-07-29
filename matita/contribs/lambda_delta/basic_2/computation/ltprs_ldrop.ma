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

include "basic_2/reducibility/ltpr_ldrop.ma".
include "basic_2/computation/ltprs.ma".

(* CONTEXT-FREE PARALLEL COMPUTATION ON LOCAL ENVIRONMENTS ******************)

lemma ltprs_ldrop_conf: dropable_sn ltprs.
/2 width=3/ qed.

lemma ldrop_ltprs_trans: dedropable_sn ltprs.
/2 width=3/ qed.

lemma ltprs_ldrop_trans_O1: dropable_dx ltprs.
/2 width=3/ qed.
