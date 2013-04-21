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

include "basic_2/reduction/lpr_cpss.ma".

(* SN PARALLEL REDUCTION ON LOCAL ENVIRONMENTS ******************************)

(* Properties on sn parallel substitution on local environments *************)

lemma lpr_lpss_conf: confluent2 … lpr lpss.
/3 width=6 by lpx_sn_conf, cpr_cpss_conf_lpr_lpss/
qed-.
