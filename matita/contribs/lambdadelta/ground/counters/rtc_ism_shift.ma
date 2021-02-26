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

include "ground/counters/rtc_shift.ma".
include "ground/counters/rtc_ism.ma".

(* T-BOUND RT-TRANSITION COUNTERS *******************************************)

(* Constructions with rtc_shift *********************************************)

lemma rtc_isr_shift (c):  𝐌❪𝟎,c❫ → 𝐌❪𝟎,↕*c❫.
#c * #ri #rs #H destruct /2 width=3 by ex1_2_intro/
qed.

(* Inversions with rtc_shift ************************************************)

lemma rtc_ism_inv_shift (n) (c): 𝐌❪n,↕*c❫ → ∧∧ 𝐌❪𝟎,c❫ & 𝟎 = n.
#n #c * #ri #rs #H
elim (rtc_shift_inv_dx … H) -H #rt0 #rs0 #ti0 #ts0 #_ #_ #H1 #H2 #H3
elim (eq_inv_nmax_zero … H1) -H1 /3 width=3 by ex1_2_intro, conj/
qed-.

lemma rtc_isr_inv_shift (c): 𝐌❪𝟎,↕*c❫ → 𝐌❪𝟎,c❫.
#c #H elim (rtc_ism_inv_shift … H) -H //
qed-.
