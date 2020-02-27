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

include "ground/steps/rtc_shift.ma".
include "ground/steps/rtc_max.ma".

(* RT-TRANSITION COUNTER ****************************************************)

(* Properties with max and shift ********************************************)

lemma max_shift: ∀c1,c2. ((↕*c1) ∨ (↕*c2)) = ↕*(c1∨c2).
* #ri1 #rs1 #ti1 #ts1 * #ri2 #rs2 #ti2 #ts2
<shift_rew <shift_rew <shift_rew <max_rew //
qed.
