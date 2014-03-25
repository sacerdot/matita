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

include "basic_2/reduction/lpr_lpr.ma".
include "basic_2/computation/lprs.ma".

(* SN PARALLEL COMPUTATION ON LOCAL ENVIRONMENTS ****************************)

(* Advanced properties ******************************************************)

lemma lprs_strip: ∀G. confluent2 … (lprs G) (lpr G).
/3 width=3 by TC_strip1, lpr_conf/ qed-.

(* Main properties **********************************************************)

theorem lprs_conf: ∀G. confluent2 … (lprs G) (lprs G).
/3 width=3 by TC_confluent2, lpr_conf/ qed-.

theorem lprs_trans: ∀G. Transitive … (lprs G).
/2 width=3/ qed-.
