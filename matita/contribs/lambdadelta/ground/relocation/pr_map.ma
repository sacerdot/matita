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

include "ground/notation/functions/upspoon_1.ma".
include "ground/notation/functions/uparrow_1.ma".
include "ground/lib/stream.ma".
include "ground/lib/bool.ma".

(* PARTIAL RELOCATION MAPS **************************************************)

(*** rtmap *)
definition pr_map: Type[0] ≝ stream bool.

(*** push *)
definition pr_push (f): pr_map ≝ Ⓕ⨮f.

interpretation
  "push (partial relocation maps)"
  'UpSpoon f = (pr_push f).

(*** next *)
definition pr_next (f): pr_map ≝ Ⓣ⨮f.

interpretation
  "next (partial relocation maps)"
  'UpArrow f = (pr_next f).

(* Basic constructions (specific) *******************************************)

(*** push_rew *)
lemma pr_push_unfold (f): Ⓕ⨮f = ⫯f.
// qed.

(*** next_rew *)
lemma pr_next_unfold (f): Ⓣ⨮f = ↑f.
// qed.

(* Basic inversions *********************************************************)

(*** injective_push *)
lemma eq_inv_pr_push_bi: injective ? ? pr_push.
#f1 #f2 <pr_push_unfold <pr_push_unfold #H destruct //
qed-.

(*** discr_push_next *)
lemma eq_inv_pr_push_next (f1) (f2): ⫯f1 = ↑f2 → ⊥.
#f1 #f2 <pr_push_unfold <pr_next_unfold #H destruct
qed-.

(*** discr_next_push *)
lemma eq_inv_pr_next_push (f1) (f2): ↑f1 = ⫯f2 → ⊥.
#f1 #f2 <pr_next_unfold <pr_push_unfold #H destruct
qed-.

(*** injective_next *)
lemma eq_inv_pr_next_bi: injective ? ? pr_next.
#f1 #f2 <pr_next_unfold <pr_next_unfold #H destruct //
qed-.
