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

include "higher_order_defs/functions.ma".

(* Semigroups *)

record PreSemiGroup : Type≝
 { carrier:> Type;
   op: carrier → carrier → carrier
 }.

interpretation "Semigroup operation" 'middot a b = (op ? a b).

record IsSemiGroup (S:PreSemiGroup) : Prop ≝
 { op_is_associative: associative ? (op S) }.

record SemiGroup : Type≝
 { pre_semi_group:> PreSemiGroup;
   is_semi_group :> IsSemiGroup pre_semi_group
 }.

definition is_left_unit ≝
 λS:PreSemiGroup. λe:S. ∀x:S. e·x = x.

definition is_right_unit ≝
 λS:PreSemiGroup. λe:S. ∀x:S. x·e = x.

theorem is_left_unit_to_is_right_unit_to_eq:
 ∀S:PreSemiGroup. ∀e,e':S.
  is_left_unit ? e → is_right_unit ? e' → e=e'.
 intros;
 rewrite < (H e');
 rewrite < (H1 e) in \vdash (? ? % ?).
 reflexivity.
qed.
