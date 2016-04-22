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

include "ground_2/notation/functions/drop_1.ma".
include "ground_2/steps/rtc.ma".

(* RT-TRANSITION COUNTER ****************************************************)

definition shift (r:rtc): rtc ≝ match r with
[ mk_rtc ri rh ti th ⇒ 〈ri+rh, 0, ti+th, 0〉 ].

interpretation "shift (rtc)"
   'Drop r = (shift r).

(* Basic properties *********************************************************)

lemma shift_refl: ∀ri,ti. 〈ri, 0, ti, 0〉 = ↓〈ri, 0, ti, 0〉.
normalize //
qed.
