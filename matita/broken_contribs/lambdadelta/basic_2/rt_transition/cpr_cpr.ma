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

include "basic_2/rt_transition/lpr_lpr.ma".

(* PARALLEL R-TRANSITION FOR FULL LOCAL ENVIRONMENTS ************************)

(* Main properties **********************************************************)

(* Basic_1: includes: pr0_confluence pr2_confluence *)
theorem cpr_conf (h) (G) (L): confluent … (cpm h G L 0).
/2 width=6 by cpr_conf_lpr/ qed-.
