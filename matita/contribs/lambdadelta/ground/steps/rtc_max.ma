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

include "ground/xoa/ex_6_8.ma".
include "ground/steps/rtc.ma".

(* RT-TRANSITION COUNTER ****************************************************)

definition max (c1:rtc) (c2:rtc): rtc ≝ match c1 with [
   mk_rtc ri1 rs1 ti1 ts1 ⇒ match c2 with [
      mk_rtc ri2 rs2 ti2 ts2 ⇒ 〈ri1∨ri2,rs1∨rs2,ti1∨ti2,ts1∨ts2〉
   ]
].

interpretation "maximum (rtc)"
   'or c1 c2 = (max c1 c2).

(* Basic properties *********************************************************)

lemma max_rew: ∀ri1,ri2,rs1,rs2,ti1,ti2,ts1,ts2.
                 〈ri1∨ri2,rs1∨rs2,ti1∨ti2,ts1∨ts2〉 =
                 (〈ri1,rs1,ti1,ts1〉 ∨ 〈ri2,rs2,ti2,ts2〉).
// qed.

lemma max_O_dx: ∀c. c = (c ∨ 𝟘𝟘).
* #ri #rs #ti #ts <max_rew //
qed.

lemma max_idem: ∀c. c = (c ∨ c).
* #ri #rs #ti #ts <max_rew //
qed.

(* Basic inversion properties ***********************************************)

lemma max_inv_dx: ∀ri,rs,ti,ts,c1,c2. 〈ri,rs,ti,ts〉 = (c1 ∨ c2) →
                  ∃∃ri1,rs1,ti1,ts1,ri2,rs2,ti2,ts2.
                  (ri1∨ri2) = ri & (rs1∨rs2) = rs & (ti1∨ti2) = ti & (ts1∨ts2) = ts &
                  〈ri1,rs1,ti1,ts1〉 = c1 & 〈ri2,rs2,ti2,ts2〉 = c2.
#ri #rs #ti #ts * #ri1 #rs1 #ti1 #ts1 * #ri2 #rs2 #ti2 #ts2
<max_rew #H destruct /2 width=14 by ex6_8_intro/
qed-.

(* Main Properties **********************************************************)

theorem max_assoc: associative … max.
* #ri1 #rs1 #ti1 #ts1 * #ri2 #rs2 #ti2 #ts2 * #ri3 #rs3 #ti3 #ts3
<max_rew <max_rew //
qed.
