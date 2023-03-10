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

include "ground/notation/relations/predicate_t_2.ma".
include "ground/counters/rtc.ma".

(* T-TRANSITION COUNTERS ****************************************************)

definition rtc_ist: relation2 nat rtc â
           Î»ts,c. â©ð,ð,ð,tsâª = c.

interpretation
  "construction (t-transition counters)"
  'PredicateT ts c = (rtc_ist ts c).

(* Basic constructions ******************************************************)

lemma rtc_ist_zz: ðâ¨ð,ððâ©.
// qed.

lemma rtc_ist_zu: ðâ¨ð,ððâ©.
// qed.

(* Basic inversions *********************************************************)

lemma rtc_ist_inv_zz (n): ðâ¨n,ððâ© â ð = n.
#n #H destruct //
qed-.

lemma rtc_ist_inv_zu (n): ðâ¨n,ððâ© â ninj (ð) = n.
#n #H destruct //
qed-.

lemma rtc_ist_inv_uz (n): ðâ¨n,ððâ© â â¥.
#h #H destruct
qed-.

(* Main inversions **********************************************************)

theorem rtc_ist_inj (n1) (n2) (c): ðâ¨n1,câ© â ðâ¨n2,câ© â n1 = n2.
#n1 #n2 #c #H1 #H2 destruct //
qed-.

theorem rtc_ist_mono (n) (c1) (c2): ðâ¨n,c1â© â ðâ¨n,c2â© â c1 = c2.
#n #c1 #c2 #H1 #H2 destruct //
qed-.
