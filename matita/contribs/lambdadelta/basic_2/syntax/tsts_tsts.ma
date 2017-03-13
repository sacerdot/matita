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

include "basic_2/syntax/tsts.ma".

(* SAME TOP TERM STRUCTURE **************************************************)

(* Main properties **********************************************************)

(* Basic_1: was: iso_trans *)
theorem tsts_trans: ∀h,o. Transitive … (tsts h o).
#h #o #T1 #T * -T1 -T
[ #s1 #s #d #Hs1 #Hs #X #H
  elim (tsts_inv_sort1_deg … H … Hs) -s /2 width=3 by tsts_sort/
| #i1 #i #H <(tsts_inv_lref1 … H) -H //
| #l1 #l #H <(tsts_inv_gref1 … H) -H //
| #I #V1 #V #T1 #T #X #H
  elim (tsts_inv_pair1 … H) -H #V2 #T2 #H destruct //
]
qed-.

theorem tsts_canc_sn: ∀h,o. left_cancellable … (tsts h o).
/3 width=3 by tsts_trans, tsts_sym/ qed-.

theorem tsts_canc_dx: ∀h,o. right_cancellable … (tsts h o).
/3 width=3 by tsts_trans, tsts_sym/ qed-.
