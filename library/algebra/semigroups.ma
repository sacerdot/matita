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

(* Magmas *)

record Magma : Type≝
 { carrier:> Type;
   op: carrier → carrier → carrier
 }.

notation "hvbox(a break \middot b)" 
  left associative with precedence 55
for @{ 'magma_op $a $b }.

interpretation "magma operation" 'magma_op a b =
 (cic:/matita/algebra/semigroups/op.con _ a b).

(* Semigroups *)

record isSemiGroup (M:Magma) : Prop≝
 { op_associative: associative ? (op M) }.

record SemiGroup : Type≝
 { magma:> Magma;
   semigroup_properties:> isSemiGroup magma
 }.
 
definition is_left_unit ≝
 λS:SemiGroup. λe:S. ∀x:S. e·x = x.
 
definition is_right_unit ≝
 λS:SemiGroup. λe:S. ∀x:S. x·e = x.

theorem is_left_unit_to_is_right_unit_to_eq:
 ∀S:SemiGroup. ∀e,e':S.
  is_left_unit ? e → is_right_unit ? e' → e=e'.
 intros;
 rewrite < (H e');
 rewrite < (H1 e) in \vdash (? ? % ?).
 reflexivity.
qed.
