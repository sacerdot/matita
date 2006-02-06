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

set "baseuri" "cic:/matita/algebra/groups/".

include "algebra/monoids.ma".
include "nat/le_arith.ma".
include "datatypes/bool.ma".
include "nat/compare.ma".

record PreGroup : Type ≝
 { premonoid:> PreMonoid;
   inv: premonoid -> premonoid
 }.

record isGroup (G:PreGroup) : Prop ≝
 { is_monoid: isMonoid G;
   inv_is_left_inverse: is_left_inverse (mk_Monoid ? is_monoid) (inv G);
   inv_is_right_inverse: is_right_inverse (mk_Monoid ? is_monoid) (inv G)
 }.
 
record Group : Type ≝
 { pregroup:> PreGroup;
   group_properties:> isGroup pregroup
 }.

(*notation < "G"
for @{ 'monoid $G }.

interpretation "Monoid coercion" 'monoid G =
 (cic:/matita/algebra/groups/monoid.con G).*)

notation < "G"
for @{ 'type_of_group $G }.

interpretation "Type_of_group coercion" 'type_of_group G =
 (cic:/matita/algebra/groups/Type_of_Group.con G).

notation < "G"
for @{ 'magma_of_group $G }.

interpretation "magma_of_group coercion" 'magma_of_group G =
 (cic:/matita/algebra/groups/Magma_of_Group.con G).

notation "hvbox(x \sup (-1))" with precedence 89
for @{ 'ginv $x }.

interpretation "Group inverse" 'ginv x =
 (cic:/matita/algebra/groups/inv.con _ x).

definition left_cancellable ≝
 λT:Type. λop: T -> T -> T.
  ∀x. injective ? ? (op x).
  
definition right_cancellable ≝
 λT:Type. λop: T -> T -> T.
  ∀x. injective ? ? (λz.op z x).
  
theorem eq_op_x_y_op_x_z_to_eq:
 ∀G:Group. left_cancellable G (op G).
intros;
unfold left_cancellable;
unfold injective;
intros (x y z);
rewrite < (e_is_left_unit ? (is_monoid ? G));
rewrite < (e_is_left_unit ? (is_monoid ? G) z);
rewrite < (inv_is_left_inverse ? G x);
rewrite > (associative ? (is_semi_group ? (is_monoid ? G)));
rewrite > (associative ? (is_semi_group ? (is_monoid ? G)));
apply eq_f;
assumption.
qed.


theorem eq_op_x_y_op_z_y_to_eq:
 ∀G:Group. right_cancellable G (op G).
intros;
unfold right_cancellable;
unfold injective;
simplify;fold simplify (op G); 
intros (x y z);
rewrite < (e_is_right_unit ? (is_monoid ? G));
rewrite < (e_is_right_unit ? (is_monoid ? G) z);
rewrite < (inv_is_right_inverse ? G x);
rewrite < (associative ? (is_semi_group ? (is_monoid ? G)));
rewrite < (associative ? (is_semi_group ? (is_monoid ? G)));
rewrite > H;
reflexivity.
qed.

theorem inv_inv: ∀G:Group. ∀x:G. x \sup -1 \sup -1 = x.
intros;
apply (eq_op_x_y_op_z_y_to_eq ? (x \sup -1));
rewrite > (inv_is_right_inverse ? G);
rewrite > (inv_is_left_inverse ? G);
reflexivity.
qed.

theorem eq_opxy_e_to_eq_x_invy:
 ∀G:Group. ∀x,y:G. x·y=1 → x=y \sup -1.
intros;
apply (eq_op_x_y_op_z_y_to_eq ? y);
rewrite > (inv_is_left_inverse ? G);
assumption.
qed.

theorem eq_opxy_e_to_eq_invx_y:
 ∀G:Group. ∀x,y:G. x·y=1 → x \sup -1=y.
intros;
apply (eq_op_x_y_op_x_z_to_eq ? x);
rewrite > (inv_is_right_inverse ? G);
symmetry;
assumption.
qed.

theorem eq_opxy_z_to_eq_x_opzinvy:
 ∀G:Group. ∀x,y,z:G. x·y=z → x = z·y \sup -1.
intros;
apply (eq_op_x_y_op_z_y_to_eq ? y);
rewrite > (associative ? (is_semi_group ? (is_monoid ? G)));
rewrite > (inv_is_left_inverse ? G);
rewrite > (e_is_right_unit ? (is_monoid ? G));
assumption.
qed.

theorem eq_opxy_z_to_eq_y_opinvxz:
 ∀G:Group. ∀x,y,z:G. x·y=z → y = x \sup -1·z.
intros;
apply (eq_op_x_y_op_x_z_to_eq ? x);
rewrite < (associative ? (is_semi_group ? (is_monoid ? G)));
rewrite > (inv_is_right_inverse ? G);
rewrite > (e_is_left_unit ? (is_monoid ? G));
assumption.
qed.