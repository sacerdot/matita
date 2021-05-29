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

(* GENERIC RELOCATION MAPS **************************************************)

(*** rtmap *)
definition gr_map: Type[0] ≝ stream bool.

(*** push *)
definition gr_push (f): gr_map ≝ Ⓕ⨮f.

interpretation
  "push (generic relocation maps)"
  'UpSpoon f = (gr_push f).

(*** next *)
definition gr_next (f): gr_map ≝ Ⓣ⨮f.

interpretation
  "next (generic relocation maps)"
  'UpArrow f = (gr_next f).

(* Basic constructions (specific) *******************************************)

(*** push_rew *)
lemma gr_push_unfold (f): Ⓕ⨮f = ⫯f.
// qed.

(*** next_rew *)
lemma gr_next_unfold (f): Ⓣ⨮f = ↑f.
// qed.

(* Basic inversions *********************************************************)

(*** injective_push *)
lemma eq_inv_gr_push_bi: injective ? ? gr_push.
#f1 #f2 <gr_push_unfold <gr_push_unfold #H destruct //
qed-.

(*** discr_push_next *)
lemma eq_inv_gr_push_next (f1) (f2): ⫯f1 = ↑f2 → ⊥.
#f1 #f2 <gr_push_unfold <gr_next_unfold #H destruct
qed-.

(*** discr_next_push *)
lemma eq_inv_gr_next_push (f1) (f2): ↑f1 = ⫯f2 → ⊥.
#f1 #f2 <gr_next_unfold <gr_push_unfold #H destruct
qed-.

(*** injective_next *)
lemma eq_inv_gr_next_bi: injective ? ? gr_next.
#f1 #f2 <gr_next_unfold <gr_next_unfold #H destruct //
qed-.
