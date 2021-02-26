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
include "ground/arith/nat_plus.ma".
include "ground/counters/rtc.ma".

(* ADDITION FOR RT-TRANSITION COUNTERS **************************************)

definition rtc_plus (c1:rtc) (c2:rtc): rtc ≝
match c1 with
[ mk_rtc ri1 rs1 ti1 ts1 ⇒
  match c2 with
  [ mk_rtc ri2 rs2 ti2 ts2 ⇒ 〈ri1+ri2,rs1+rs2,ti1+ti2,ts1+ts2〉
  ]
].

interpretation
  "plus (rtc)"
  'plus c1 c2 = (rtc_plus c1 c2).

(* Basic constructions ******************************************************)

lemma rtc_plus_rew (ri1) (ri2) (rs1) (rs2) (ti1) (ti2) (ts1) (ts2):
      〈ri1+ri2,rs1+rs2,ti1+ti2,ts1+ts2〉 = 〈ri1,rs1,ti1,ts1〉+〈ri2,rs2,ti2,ts2〉.
// qed.

lemma rtc_plus_zz_dx (c): c = c + 𝟘𝟘.
* #ri #rs #ti #ts <rtc_plus_rew //
qed.

(* Basic inversions *********************************************************)

lemma rtc_plus_inv_dx (ri) (rs) (ti) (ts) (c1) (c2):
      〈ri,rs,ti,ts〉 = c1 + c2 →
      ∃∃ri1,rs1,ti1,ts1,ri2,rs2,ti2,ts2.
      ri1+ri2 = ri & rs1+rs2 = rs & ti1+ti2 = ti & ts1+ts2 = ts &
      〈ri1,rs1,ti1,ts1〉 = c1 & 〈ri2,rs2,ti2,ts2〉 = c2.
#ri #rs #ti #ts * #ri1 #rs1 #ti1 #ts1 * #ri2 #rs2 #ti2 #ts2
<rtc_plus_rew #H destruct /2 width=14 by ex6_8_intro/
qed-.

(* Main constructions *******************************************************)

theorem rtc_plus_assoc: associative … rtc_plus.
* #ri1 #rs1 #ti1 #ts1 * #ri2 #rs2 #ti2 #ts2 * #ri3 #rs3 #ti3 #ts3
<rtc_plus_rew //
qed.
