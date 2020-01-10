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

include "ground_2/steps/rtc_isrt_shift.ma".
include "ground_2/steps/rtc_isrt_max.ma".

(* RT-TRANSITION COUNTER ****************************************************)

(* Inversion properties with test for constrained rt-transition counter *****)

lemma isrt_inv_max_shift_sn: ∀n,c1,c2. 𝐑𝐓❪n,↕*c1 ∨ c2❫ →
                             ∧∧ 𝐑𝐓❪0,c1❫ & 𝐑𝐓❪n,c2❫.
#n #c1 #c2 #H
elim (isrt_inv_max … H) -H #n1 #n2 #Hc1 #Hc2 #H destruct
elim (isrt_inv_shift … Hc1) -Hc1 #Hc1 * -n1
/2 width=1 by conj/
qed-.
