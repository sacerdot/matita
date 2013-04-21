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

include "basic_2/reduction/lpr_cpr.ma".

(* SN PARALLEL REDUCTION ON LOCAL ENVIRONMENTS ******************************)

(* Main properties **********************************************************)

theorem lpr_conf: confluent … lpr.
/3 width=6 by lpx_sn_conf, cpr_conf_lpr/
qed-.
