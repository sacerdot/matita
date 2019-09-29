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

include "static_2/syntax/toeq.ma".

(* SORT-IRRELEVANT OUTER EQUIVALENCE FOR TERMS ******************************)

(* Main properties **********************************************************)

(* Basic_1: was: iso_trans *)
(* Basic_2A1: was: tsts_trans *)
theorem toeq_trans: Transitive … toeq.
#T1 #T * -T1 -T
[ #s1 #s #X #H
  elim (toeq_inv_sort1 … H) -s /2 width=1 by toeq_sort/
| #i1 #i #H <(toeq_inv_lref1 … H) -H //
| #l1 #l #H <(toeq_inv_gref1 … H) -H //
| #I #V1 #V #T1 #T #X #H
  elim (toeq_inv_pair1 … H) -H #V2 #T2 #H destruct //
]
qed-.

(* Basic_2A1: was: tsts_canc_sn *)
theorem toeq_canc_sn: left_cancellable … toeq.
/3 width=3 by toeq_trans, toeq_sym/ qed-.

(* Basic_2A1: was: tsts_canc_dx *)
theorem toeq_canc_dx: right_cancellable … toeq.
/3 width=3 by toeq_trans, toeq_sym/ qed-.
