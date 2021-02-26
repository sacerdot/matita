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

include "ground/counters/rtc_shift.ma".
include "ground/counters/rtc_max.ma".

(* MAXIMUM FOR RT-TRANSITION COUNTERS ***************************************)

(* Constructions with rtc_shift *********************************************)

lemma rtc_max_shift (c1) (c2): ((↕*c1) ∨ (↕*c2)) = ↕*(c1∨c2).
* #ri1 #rs1 #ti1 #ts1 * #ri2 #rs2 #ti2 #ts2
<rtc_shift_rew <rtc_shift_rew <rtc_shift_rew <rtc_max_rew
<nmax_assoc <nmax_assoc <nmax_assoc <nmax_assoc //
qed.
