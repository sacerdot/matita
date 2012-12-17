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

include "lift.ma".

(* LENGTH *******************************************************************)

(* Note: this gives the number of abstractions and applications in M *)
let rec length M on M ≝ match M with
[ VRef i   ⇒ 0
| Abst A   ⇒ length A + 1
| Appl B A ⇒ (length B) + (length A) + 1
].

interpretation "term length"
   'card M = (length M).

lemma length_lift: ∀h,M,d. |↑[d, h] M| = |M|.
#h #M elim M -M normalize //
qed.
