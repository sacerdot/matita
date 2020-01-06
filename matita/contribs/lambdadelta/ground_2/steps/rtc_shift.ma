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

include "ground_2/xoa/ex_5_4.ma".
include "ground_2/notation/functions/updownarrowstar_1.ma".
include "ground_2/steps/rtc_isrt.ma".

(* RT-TRANSITION COUNTER ****************************************************)

definition shift (c:rtc): rtc ≝ match c with
[ mk_rtc ri rs ti ts ⇒ 〈ri∨rs,0,ti∨ts,0〉 ].

interpretation "shift (rtc)"
   'UpDownArrowStar c = (shift c).

(* Basic properties *********************************************************)

lemma shift_rew: ∀ri,rs,ti,ts. 〈ri∨rs,0,ti∨ts,0〉 = ↕*〈ri,rs,ti,ts〉.
normalize //
qed.

lemma shift_O: 𝟘𝟘 = ↕*𝟘𝟘.
// qed.

(* Basic inversion properties ***********************************************)

lemma shift_inv_dx: ∀ri,rs,ti,ts,c. 〈ri,rs,ti,ts〉 = ↕*c →
                    ∃∃ri0,rs0,ti0,ts0. (ri0∨rs0) = ri & 0 = rs & (ti0∨ts0) = ti & 0 = ts &
                                       〈ri0,rs0,ti0,ts0〉 = c.
#ri #rs #ti #ts * #ri0 #rs0 #ti0 #ts0 <shift_rew #H destruct
/2 width=7 by ex5_4_intro/
qed-.

(* Properties with test for costrained rt-transition counter ****************)

lemma isr_shift: ∀c. 𝐑𝐓⦃0,c⦄ → 𝐑𝐓⦃0,↕*c⦄.
#c * #ri #rs #H destruct /2 width=3 by ex1_2_intro/
qed.

(* Inversion properties with test for costrained rt-counter *****************)

lemma isrt_inv_shift: ∀n,c. 𝐑𝐓⦃n,↕*c⦄ → 𝐑𝐓⦃0,c⦄ ∧ 0 = n.
#n #c * #ri #rs #H
elim (shift_inv_dx … H) -H #rt0 #rs0 #ti0 #ts0 #_ #_ #H1 #H2 #H3
elim (max_inv_O3 … H1) -H1 /3 width=3 by ex1_2_intro, conj/
qed-.

lemma isr_inv_shift: ∀c. 𝐑𝐓⦃0,↕*c⦄ → 𝐑𝐓⦃0,c⦄.
#c #H elim (isrt_inv_shift … H) -H //
qed-.
