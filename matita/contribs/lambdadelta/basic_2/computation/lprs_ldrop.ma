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

include "basic_2/relocation/ldrop_lsuby.ma".
include "basic_2/reduction/lpr_ldrop.ma".
include "basic_2/computation/lprs.ma".

(* SN PARALLEL COMPUTATION ON LOCAL ENVIRONMENTS ****************************)

(* Properies on local environment slicing ***********************************)

lemma lprs_ldrop_conf: ∀G. dropable_sn (lprs G).
/3 width=3 by dropable_sn_TC, lpr_ldrop_conf/ qed-.

lemma ldrop_lprs_trans: ∀G. dedropable_sn (lprs G).
/3 width=3 by dedropable_sn_TC, ldrop_lpr_trans/ qed-.

lemma lprs_ldrop_trans_O1: ∀G. dropable_dx (lprs G).
/3 width=3 by dropable_dx_TC, lpr_ldrop_trans_O1/ qed-.
