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

include "ground_2/steps/rtc.ma".

(* RT-TRANSITION COUNTER ****************************************************)

definition plus (r1:rtc) (r2:rtc): rtc ≝ match r1 with [
   mk_rtc ri1 rh1 ti1 th1 ⇒ match r2 with [
      mk_rtc ri2 rh2 ti2 th2 ⇒ 〈ri1+ri2, rh1+rh2, ti1+ti2, th1+th2〉
   ]
].

interpretation "plus (rtc)"
   'plus r1 r2 = (plus r1 r2).

(* Basic properties *********************************************************)

lemma plus_OO_r: ∀r. r = 𝟘𝟘 + r.
* normalize //
qed.

lemma plus_r_OO: ∀r. r = r + 𝟘𝟘.
* normalize //
qed.
