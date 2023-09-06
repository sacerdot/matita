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
include "ground/arith/nat_max.ma".
include "ground/counters/rtc.ma".

(* MAXIMUM FOR RT-TRANSITION COUNTERS ***************************************)

definition rtc_max (c1:rtc) (c2:rtc): rtc ≝
match c1 with
[ mk_prod_4 ri1 rs1 ti1 ts1 ⇒
  match c2 with
  [ mk_prod_4 ri2 rs2 ti2 ts2 ⇒ 〈ri1∨ri2,rs1∨rs2,ti1∨ti2,ts1∨ts2〉
  ]
].

interpretation
  "maximum (rt-transition counters)"
  'or c1 c2 = (rtc_max c1 c2).

(* Basic constructions ******************************************************)

(*** rtc_max_rew *)
lemma rtc_max_unfold (ri1) (ri2) (rs1) (rs2) (ti1) (ti2) (ts1) (ts2):
      〈ri1∨ri2,rs1∨rs2,ti1∨ti2,ts1∨ts2〉 =
      (〈ri1,rs1,ti1,ts1〉 ∨ 〈ri2,rs2,ti2,ts2〉).
// qed.

lemma rtc_max_zz_dx (c): c = (c ∨ 𝟘𝟘).
* #ri #rs #ti #ts <rtc_max_unfold //
qed.

lemma rtc_max_idem (c): c = (c ∨ c).
* #ri #rs #ti #ts <rtc_max_unfold //
qed.

(* Basic inversions *********************************************************)

lemma rtc_max_inv_dx (ri) (rs) (ti) (ts) (c1) (c2):
      〈ri,rs,ti,ts〉 = (c1 ∨ c2) →
      ∃∃ri1,rs1,ti1,ts1,ri2,rs2,ti2,ts2.
      (ri1∨ri2) = ri & (rs1∨rs2) = rs & (ti1∨ti2) = ti & (ts1∨ts2) = ts &
      〈ri1,rs1,ti1,ts1〉 = c1 & 〈ri2,rs2,ti2,ts2〉 = c2.
#ri #rs #ti #ts * #ri1 #rs1 #ti1 #ts1 * #ri2 #rs2 #ti2 #ts2
<rtc_max_unfold #H destruct /2 width=14 by ex6_8_intro/
qed-.

(* Main constructions *******************************************************)

theorem rtc_max_assoc: associative … rtc_max.
* #ri1 #rs1 #ti1 #ts1 * #ri2 #rs2 #ti2 #ts2 * #ri3 #rs3 #ti3 #ts3
<rtc_max_unfold <rtc_max_unfold //
qed.
