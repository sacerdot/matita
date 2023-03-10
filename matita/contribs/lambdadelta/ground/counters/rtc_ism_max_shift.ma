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

include "ground/counters/rtc_ism_shift.ma".
include "ground/counters/rtc_ism_max.ma".

(* T-BOUND RT-TRANSITION COUNTERS *******************************************)

(* Inversions with rtc_max and rtc_shift ************************************)

lemma rtc_ism_inv_max_shift_sn (n) (c1) (c2): ๐โจn,โ*c1 โจ c2โฉ โ
      โงโง ๐โจ๐,c1โฉ & ๐โจn,c2โฉ.
#n #c1 #c2 #H
elim (rtc_ism_inv_max โฆ H) -H #n1 #n2 #Hc1 #Hc2 #H destruct
elim (rtc_ism_inv_shift โฆ Hc1) -Hc1 #Hc1 * -n1 <nmax_zero_sn
/2 width=1 by conj/
qed-.
