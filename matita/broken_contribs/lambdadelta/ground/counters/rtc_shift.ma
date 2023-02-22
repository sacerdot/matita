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

definition rtc_shift (c:rtc): rtc ≝
match c with
[ mk_rtc ri rs ti ts ⇒ 〈ri ∨ rs, 𝟎, ti ∨ ts, 𝟎〉 
].

interpretation
  "shift (rt-transition counters)"
  'UpDownArrowStar c = (rtc_shift c).

(* Basic constructions ******************************************************)

(*** rtc_shift_rew *)
lemma rtc_shift_unfold (ri) (rs) (ti) (ts):
      〈ri ∨ rs, 𝟎, ti ∨ ts, 𝟎〉 = ↕*〈ri,rs,ti,ts〉.
//
qed.

lemma rtc_shift_zz: 𝟘𝟘 = ↕*𝟘𝟘.
// qed.

(* Basic inversions *********************************************************)

lemma rtc_shift_inv_dx (ri) (rs) (ti) (ts) (c):
      〈ri,rs,ti,ts〉 = ↕*c →
      ∃∃ri0,rs0,ti0,ts0.
      (ri0∨rs0) = ri & 𝟎 = rs & (ti0∨ts0) = ti & 𝟎 = ts & 〈ri0,rs0,ti0,ts0〉 = c.
#ri #rs #ti #ts * #ri0 #rs0 #ti0 #ts0 <rtc_shift_unfold #H destruct
/2 width=7 by ex5_4_intro/
qed-.
