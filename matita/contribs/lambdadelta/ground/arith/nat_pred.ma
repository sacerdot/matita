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

include "ground/notation/functions/downarrow_1.ma".
include "ground/arith/pnat_dis.ma".
include "ground/arith/nat.ma".

(* NON-NEGATIVE INTEGERS ****************************************************)

(*** pred *)
definition npred (m): nat ≝ match m with
[ nzero  ⇒ 𝟎
| ninj p ⇒ pdis … (𝟎) ninj p
].

interpretation
  "predecessor (non-negative integers"
  'DownArrow m = (npred m).

(* Basic rewrites ***********************************************************)

lemma npred_zero: 𝟎 = ↓𝟎.
// qed.
