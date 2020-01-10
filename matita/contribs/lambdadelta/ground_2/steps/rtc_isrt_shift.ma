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

include "ground_2/steps/rtc_shift.ma".
include "ground_2/steps/rtc_isrt.ma".

(* RT-TRANSITION COUNTER ****************************************************)

(* Properties with test for costrained rt-transition counter ****************)

lemma isr_shift: ∀c. 𝐑𝐓❪0,c❫ → 𝐑𝐓❪0,↕*c❫.
#c * #ri #rs #H destruct /2 width=3 by ex1_2_intro/
qed.

(* Inversion properties with test for costrained rt-counter *****************)

lemma isrt_inv_shift: ∀n,c. 𝐑𝐓❪n,↕*c❫ → 𝐑𝐓❪0,c❫ ∧ 0 = n.
#n #c * #ri #rs #H
elim (shift_inv_dx … H) -H #rt0 #rs0 #ti0 #ts0 #_ #_ #H1 #H2 #H3
elim (max_inv_O3 … H1) -H1 /3 width=3 by ex1_2_intro, conj/
qed-.

lemma isr_inv_shift: ∀c. 𝐑𝐓❪0,↕*c❫ → 𝐑𝐓❪0,c❫.
#c #H elim (isrt_inv_shift … H) -H //
qed-.
