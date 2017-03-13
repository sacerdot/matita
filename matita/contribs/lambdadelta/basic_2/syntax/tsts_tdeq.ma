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

include "basic_2/syntax/tdeq.ma".
include "basic_2/syntax/tsts.ma".

(* SAME TOP TERM STRUCTURE **************************************************)

(* Properties with degree-based equivalence for terms ***********************)

lemma tdeq_tsts: ∀h,o,T1,T2. T1 ≡[h, o] T2 → T1 ⩳[h, o] T2.
#h #o #T1 #T2 * -T1 -T2 /2 width=3 by tsts_sort, tsts_pair/
qed.
