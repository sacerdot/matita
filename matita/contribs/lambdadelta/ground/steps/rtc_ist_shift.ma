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

include "ground/steps/rtc_shift.ma".
include "ground/steps/rtc_ist.ma".

(* RT-TRANSITION COUNTER ****************************************************)

(* Properties with test for t-transition counter ****************************)

lemma ist_zero_shift: ∀c. 𝐓❪0,c❫ → 𝐓❪0,↕*c❫.
#c #H destruct //
qed.

(* Inversion properties with test for t-transition counter ******************)

lemma ist_inv_shift: ∀n,c. 𝐓❪n,↕*c❫ → ∧∧ 𝐓❪0,c❫ & 0 = n.
#n #c #H
elim (shift_inv_dx … H) -H #rt0 #rs0 #ti0 #ts0 #H1 #_ #H2 #H3 #H4 destruct
elim (max_inv_O3 … H1) -H1 #H11 #H12 destruct
elim (max_inv_O3 … H2) -H2 #H21 #H22 destruct
/2 width=1 by conj/
qed-.

lemma ist_inv_zero_shift: ∀c. 𝐓❪0,↕*c❫ → 𝐓❪0,c❫.
#c #H elim (ist_inv_shift … H) -H //
qed-.
