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

include "algebra/monoids.ma".
include "nat/le_arith.ma".
include "datatypes/bool.ma".
include "nat/compare.ma".

record PreGroup : Type ≝
 { pre_monoid:> PreMonoid;
   inv: pre_monoid -> pre_monoid
 }.

interpretation "Group inverse" 'invert x = (inv ? x).

record isGroup (G:PreGroup) : Prop ≝
 { is_monoid           :> IsMonoid G;
   inv_is_left_inverse :  is_left_inverse G (inv G);
   inv_is_right_inverse:  is_right_inverse G (inv G)
 }.

record Group : Type ≝
 { pre_group:> PreGroup;
   is_group:> isGroup pre_group
 }.

definition Monoid_of_Group: Group → Monoid ≝
 λG. mk_Monoid ? (is_group G).

coercion Monoid_of_Group nocomposites.

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
rewrite < (e_is_left_unit ? G);
rewrite < (e_is_left_unit ? G z);
rewrite < (inv_is_left_inverse ? G x);
rewrite > (op_is_associative ? G);
rewrite > (op_is_associative ? G);
apply eq_f;
assumption.
qed.

theorem eq_op_x_y_op_z_y_to_eq:
 ∀G:Group. right_cancellable G (op G).
intros;
unfold right_cancellable;
unfold injective;
intros (x y z);
rewrite < (e_is_right_unit ? G);
rewrite < (e_is_right_unit ? G z);
rewrite < (inv_is_right_inverse ? G x);
rewrite < (op_is_associative ? G);
rewrite < (op_is_associative ? G);
rewrite > H;
reflexivity.
qed.

theorem eq_inv_inv_x_x: ∀G:Group. ∀x:G. x \sup -1 \sup -1 = x.
intros;
apply (eq_op_x_y_op_z_y_to_eq ? (x \sup -1));
rewrite > (inv_is_right_inverse ? G);
rewrite > (inv_is_left_inverse ? G);
reflexivity.
qed.

theorem eq_opxy_e_to_eq_x_invy:
 ∀G:Group. ∀x,y:G. x·y=ⅇ → x=y \sup -1.
intros;
apply (eq_op_x_y_op_z_y_to_eq ? y);
rewrite > (inv_is_left_inverse ? G);
assumption.
qed.

theorem eq_opxy_e_to_eq_invx_y:
 ∀G:Group. ∀x,y:G. x·y=ⅇ → x \sup -1=y.
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
rewrite > (op_is_associative ? G);
rewrite > (inv_is_left_inverse ? G);
rewrite > (e_is_right_unit ? G);
assumption.
qed.

theorem eq_opxy_z_to_eq_y_opinvxz:
 ∀G:Group. ∀x,y,z:G. x·y=z → y = x \sup -1·z.
intros;
apply (eq_op_x_y_op_x_z_to_eq ? x);
rewrite < (op_is_associative ? G);
rewrite > (inv_is_right_inverse ? G);
rewrite > (e_is_left_unit ? G);
assumption.
qed.

theorem eq_inv_op_x_y_op_inv_y_inv_x:
 ∀G:Group. ∀x,y:G. (x·y) \sup -1 = y \sup -1 · x \sup -1.
intros;
apply (eq_op_x_y_op_z_y_to_eq ? (x·y));
rewrite > (inv_is_left_inverse ? G);
rewrite < (op_is_associative ? G);
rewrite > (op_is_associative ? G (y \sup -1));
rewrite > (inv_is_left_inverse ? G);
rewrite > (e_is_right_unit ? G);
rewrite > (inv_is_left_inverse ? G);
reflexivity.
qed.

(* Morphisms *)

record morphism (G,G':Group) : Type ≝
 { image:1> G → G';
   f_morph: ∀x,y:G.image(x·y) = image x · image y
 }.
 
theorem morphism_to_eq_f_1_1:
 ∀G,G'.∀f:morphism G G'.f ⅇ  = ⅇ.
intros;
apply (eq_op_x_y_op_z_y_to_eq ? (f ⅇ));
rewrite > (e_is_left_unit ? G');
rewrite < f_morph;
rewrite > (e_is_left_unit ? G);
reflexivity.
qed.
 
theorem eq_image_inv_inv_image:
 ∀G,G'.∀f:morphism G G'.
  ∀x.f (x \sup -1) = (f x) \sup -1.
intros;
apply (eq_op_x_y_op_z_y_to_eq ? (f x));
rewrite > (inv_is_left_inverse ? G');
rewrite < f_morph;
rewrite > (inv_is_left_inverse ? G);
apply (morphism_to_eq_f_1_1 ? ? f).
qed.

record monomorphism (G,G':Group) : Type ≝
 { morphism:> morphism G G';
   injective: injective ? ? (image ? ? morphism)
 }.

(* Subgroups *)

record subgroup (G:Group) : Type ≝
 { group:> Group;
   embed:> monomorphism group G
 }.

notation "hvbox(x \sub H)" with precedence 79
for @{ 'subgroupimage $H $x }.

interpretation "Subgroup image" 'subgroupimage H x =
 (image ?? (morphism_OF_subgroup ? H) x).

definition member_of_subgroup ≝
 λG.λH:subgroup G.λx:G.∃y.x=y \sub H.

notation "hvbox(x break \in H)" with precedence 79
for @{ 'member_of $x $H }.

notation "hvbox(x break \notin H)" with precedence 79
for @{ 'not_member_of $x $H }.

interpretation "Member of subgroup" 'member_of x H =
 (member_of_subgroup ? H x).
 
interpretation "Not member of subgroup" 'not_member_of x H =
 (Not (member_of_subgroup ? H x)).

(* Left cosets *)

record left_coset (G:Group) : Type ≝
 { element: G;
   subgrp: subgroup G
 }.

(* Here I would prefer 'magma_op, but this breaks something in the next definition *)
interpretation "Left_coset" 'times x C =
 (mk_left_coset ? x C).

definition member_of_left_coset ≝
 λG:Group.λC:left_coset G.λx:G.
  ∃y.x=(element ? C)·y \sub (subgrp ? C).

interpretation "Member of left_coset" 'member_of x C =
 (member_of_left_coset ? C x).

definition left_coset_eq ≝
 λG.λC,C':left_coset G.
  ∀x.((element ? C)·x \sub (subgrp ? C)) ∈ C'.
  
interpretation "Left cosets equality" 'eq t C C' = (left_coset_eq t C C').

definition left_coset_disjoint ≝
 λG.λC,C':left_coset G.
  ∀x.¬(((element ? C)·x \sub (subgrp ? C)) ∈ C'). 

notation "hvbox(a break \par b)"
 non associative with precedence 45
for @{ 'disjoint $a $b }.

interpretation "Left cosets disjoint" 'disjoint C C' =
 (left_coset_disjoint ? C C').

(* The following should be a one-shot alias! *)
alias symbol "member_of" (instance 0) = "Member of subgroup".
theorem member_of_subgroup_op_inv_x_y_to_left_coset_eq:
 ∀G.∀x,y.∀H:subgroup G. (x \sup -1 ·y) ∈ H → x*H = y*H.
intros;
simplify;
intro;
unfold member_of_subgroup in H1;
elim H1;
clear H1;
exists;
[ apply (a\sup-1 · x1)
| rewrite > f_morph;
  rewrite > eq_image_inv_inv_image; 
  rewrite < H2;
  rewrite > eq_inv_op_x_y_op_inv_y_inv_x;
  rewrite > eq_inv_inv_x_x;
  rewrite < (op_is_associative ? G);
  rewrite < (op_is_associative ? G);
  rewrite > (inv_is_right_inverse ? G);
  rewrite > (e_is_left_unit ? G);
  reflexivity
].
qed.

theorem Not_member_of_subgroup_to_left_coset_disjoint:
 ∀G.∀x,y.∀H:subgroup G.(x \sup -1 ·y) ∉ H → x*H ∥ y*H.
intros;
simplify;
unfold Not;
intros (x');
apply H1;
unfold member_of_subgroup;
elim H2;
apply (ex_intro ? ? (x'·a \sup -1));
rewrite > f_morph; 
apply (eq_op_x_y_op_z_y_to_eq ? (a \sub H));
rewrite > (op_is_associative ? G);
rewrite < H3;
rewrite > (op_is_associative ? G);
rewrite < f_morph;
rewrite > (inv_is_left_inverse ? H);
rewrite < (op_is_associative ? G);
rewrite > (inv_is_left_inverse ? G);
rewrite > (e_is_left_unit ? G);
rewrite < (f_morph ? ? H);
rewrite > (e_is_right_unit ? H);
reflexivity.
qed.

(*CSC: here the coercion Type_of_Group cannot be omitted. Why? *)
theorem in_x_mk_left_coset_x_H:
 ∀G.∀x:Type_OF_Group G.∀H:subgroup G.x ∈ (x*H).
intros;
simplify;
apply (ex_intro ? ? ⅇ);
rewrite > morphism_to_eq_f_1_1;
rewrite > (e_is_right_unit ? G);
reflexivity.
qed.

(* Normal Subgroups *)

record normal_subgroup (G:Group) : Type ≝
 { ns_subgroup:> subgroup G;
   normal:> ∀x:G.∀y:ns_subgroup.(x·y \sub ns_subgroup·x \sup -1) ∈ ns_subgroup
 }.

(*CSC: I have not defined yet right cosets 
theorem foo:
 ∀G.∀H:normal_subgroup G.∀x.x*H=H*x.
*)
(*
theorem member_of_left_coset_mk_left_coset_x_H_a_to_member_of_left_coset_mk_left_coset_y_H_b_to_member_of_left_coset_mk_left_coset_op_x_y_H_op_a_b:
 ∀G.∀H:normal_subgroup G.∀x,y,a,b.
  a ∈ (x*H) → b ∈ (y*H) → (a·b) ∈ ((x·y)*H).
intros;
simplify;
qed.
*)
