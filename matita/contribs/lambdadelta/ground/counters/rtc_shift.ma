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

include "ground/xoa/ex_5_4.ma".
include "ground/notation/functions/updownarrowstar_1.ma".
include "ground/arith/nat_max.ma".
include "ground/counters/rtc.ma".

(* SHIFT FOR RT-TRANSITION COUNTERS *****************************************)

definition rtc_shift (c:rtc): rtc β
match c with
[ mk_rtc ri rs ti ts β β©ri β¨ rs, π, ti β¨ ts, πβͺ 
].

interpretation
  "shift (rt-transition counters)"
  'UpDownArrowStar c = (rtc_shift c).

(* Basic constructions ******************************************************)

(*** rtc_shift_rew *)
lemma rtc_shift_unfold (ri) (rs) (ti) (ts):
      β©ri β¨ rs, π, ti β¨ ts, πβͺ = β*β©ri,rs,ti,tsβͺ.
//
qed.

lemma rtc_shift_zz: ππ = β*ππ.
// qed.

(* Basic inversions *********************************************************)

lemma rtc_shift_inv_dx (ri) (rs) (ti) (ts) (c):
      β©ri,rs,ti,tsβͺ = β*c β
      ββri0,rs0,ti0,ts0.
      (ri0β¨rs0) = ri & π = rs & (ti0β¨ts0) = ti & π = ts & β©ri0,rs0,ti0,ts0βͺ = c.
#ri #rs #ti #ts * #ri0 #rs0 #ti0 #ts0 <rtc_shift_unfold #H destruct
/2 width=7 by ex5_4_intro/
qed-.
