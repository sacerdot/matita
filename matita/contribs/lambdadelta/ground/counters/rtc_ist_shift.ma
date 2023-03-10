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
include "ground/counters/rtc_ist.ma".

(* T-BOUND RT-TRANSITION COUNTERS *******************************************)

(* Constructions with rtc_shift *********************************************)

lemma rtc_ist_zero_shift (c): ๐โจ๐,cโฉ โ ๐โจ๐,โ*cโฉ.
#c #H destruct //
qed.

(* Inversions with rtc_shift ************************************************)

lemma rtc_ist_inv_shift (n) (c): ๐โจn,โ*cโฉ โ โงโง ๐โจ๐,cโฉ & ๐ = n.
#n #c #H
elim (rtc_shift_inv_dx โฆ H) -H #rt0 #rs0 #ti0 #ts0 #H1 #_ #H2 #H3 #H4 destruct
elim (eq_inv_nmax_zero โฆ H1) -H1 #H11 #H12 destruct
elim (eq_inv_nmax_zero โฆ H2) -H2 #H21 #H22 destruct
/2 width=1 by conj/
qed-.

lemma rtc_ist_inv_zero_shift (c): ๐โจ๐,โ*cโฉ โ ๐โจ๐,cโฉ.
#c #H elim (rtc_ist_inv_shift โฆ H) -H //
qed-.
