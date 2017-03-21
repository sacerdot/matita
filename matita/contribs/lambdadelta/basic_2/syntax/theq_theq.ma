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

include "basic_2/syntax/theq.ma".

(* HEAD EQUIVALENCE FOR TERMS ***********************************************)

(* Main properties **********************************************************)

(* Basic_1: was: iso_trans *)
(* Basic_2A1: was: tsts_trans *)
theorem theq_trans: ∀h,o. Transitive … (theq h o).
#h #o #T1 #T * -T1 -T
[ #s1 #s #d #Hs1 #Hs #X #H
  elim (theq_inv_sort1_deg … H … Hs) -s /2 width=3 by theq_sort/
| #i1 #i #H <(theq_inv_lref1 … H) -H //
| #l1 #l #H <(theq_inv_gref1 … H) -H //
| #I #V1 #V #T1 #T #X #H
  elim (theq_inv_pair1 … H) -H #V2 #T2 #H destruct //
]
qed-.

(* Basic_2A1: was: tsts_canc_sn *)
theorem theq_canc_sn: ∀h,o. left_cancellable … (theq h o).
/3 width=3 by theq_trans, theq_sym/ qed-.

(* Basic_2A1: was: tsts_canc_dx *)
theorem theq_canc_dx: ∀h,o. right_cancellable … (theq h o).
/3 width=3 by theq_trans, theq_sym/ qed-.
