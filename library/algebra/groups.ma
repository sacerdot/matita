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
 { is_monoid:> isMonoid G;
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
rewrite < (e_is_left_unit ? G);
rewrite < (e_is_left_unit ? G z);
rewrite < (inv_is_left_inverse ? G x);
rewrite > (associative ? (is_semi_group ? ( G)));
rewrite > (associative ? (is_semi_group ? ( G)));
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
rewrite < (e_is_right_unit ? ( G));
rewrite < (e_is_right_unit ? ( G) z);
rewrite < (inv_is_right_inverse ? G x);
rewrite < (associative ? (is_semi_group ? ( G)));
rewrite < (associative ? (is_semi_group ? ( G)));
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
rewrite > (associative ? G);
rewrite > (inv_is_left_inverse ? G);
rewrite > (e_is_right_unit ? G);
assumption.
qed.

theorem eq_opxy_z_to_eq_y_opinvxz:
 ∀G:Group. ∀x,y,z:G. x·y=z → y = x \sup -1·z.
intros;
apply (eq_op_x_y_op_x_z_to_eq ? x);
rewrite < (associative ? G);
rewrite > (inv_is_right_inverse ? G);
rewrite > (e_is_left_unit ? (is_monoid ? G));
assumption.
qed.

theorem eq_inv_op_x_y_op_inv_y_inv_x:
 ∀G:Group. ∀x,y:G. (x·y) \sup -1 = y \sup -1 · x \sup -1.
intros;
apply (eq_op_x_y_op_z_y_to_eq ? (x·y));
rewrite > (inv_is_left_inverse ? G);
rewrite < (associative ? G);
rewrite > (associative ? G (y \sup -1));
rewrite > (inv_is_left_inverse ? G);
rewrite > (e_is_right_unit ? G);
rewrite > (inv_is_left_inverse ? G);
reflexivity.
qed.

(* Morphisms *)

record morphism (G,G':Group) : Type ≝
 { image: G → G';
   f_morph: ∀x,y:G.image(x·y) = image x · image y
 }.
 
notation "hvbox(f˜ x)" with precedence 79
for @{ 'morimage $f $x }.

interpretation "Morphism image" 'morimage f x =
 (cic:/matita/algebra/groups/image.con _ _ f x).
 
theorem morphism_to_eq_f_1_1:
 ∀G,G'.∀f:morphism G G'.f˜1 = 1.
intros;
apply (eq_op_x_y_op_z_y_to_eq G' (f˜1));
rewrite > (e_is_left_unit ? G' ?);
rewrite < (f_morph ? ? f);
rewrite > (e_is_left_unit ? G);
reflexivity.
qed.
 
theorem eq_image_inv_inv_image:
 ∀G,G'.∀f:morphism G G'.
  ∀x.f˜(x \sup -1) = (f˜x) \sup -1.
intros;
apply (eq_op_x_y_op_z_y_to_eq G' (f˜x));
rewrite > (inv_is_left_inverse ? G');
rewrite < (f_morph ? ? f);
rewrite > (inv_is_left_inverse ? G);
apply (morphism_to_eq_f_1_1 ? ? f).
qed.

record monomorphism (G,G':Group) : Type ≝
 { morphism:> morphism G G';
   injective: injective ? ? (image ? ? morphism)
 }.

(* Subgroups *)

record subgroup (G:Group) : Type ≝
 { group: Group;
   embed:> monomorphism group G
 }.
 
notation "hvbox(x \sub H)" with precedence 79
for @{ 'subgroupimage $H $x }.

interpretation "Subgroup image" 'subgroupimage H x =
 (cic:/matita/algebra/groups/image.con _ _
   (cic:/matita/algebra/groups/morphism_of_subgroup.con _ H) x).

definition member_of_subgroup ≝
 λG.λH:subgroup G.λx:G.∃y.x=y \sub H.

notation "hvbox(x break ∈ H)" with precedence 79
for @{ 'member_of $x $H }.

interpretation "Member of subgroup" 'member_of x H =
 (cic:/matita/algebra/groups/member_of_subgroup.con _ H x).

(* Left cosets *)

record left_coset (G:Group) : Type ≝
 { element: G;
   subgrp: subgroup G
 }.

(* Here I would prefer 'magma_op, but this breaks something in the next definition *)
interpretation "Left_coset" 'times x C =
 (cic:/matita/algebra/groups/left_coset.ind#xpointer(1/1/1) _ x C).

definition member_of_left_coset ≝
 λG:Group.λC:left_coset G.λx:G.
  ∃y.x=(element ? C)·y \sub (subgrp ? C).

interpretation "Member of left_coset" 'member_of x C =
 (cic:/matita/algebra/groups/member_of_left_coset.con _ C x).

definition left_coset_eq ≝
 λG.λC,C':left_coset G.
  ∀x.((element ? C)·x \sub (subgrp ? C)) ∈ C'.
  
interpretation "Left cosets equality" 'eq C C' =
 (cic:/matita/algebra/groups/left_coset_eq.con _ C C').

definition left_coset_disjoint ≝
 λG.λC,C':left_coset G.
  ∀x.¬(((element ? C)·x \sub (subgrp ? C)) ∈ C'). 

notation "hvbox(a break ∥ b)"
 non associative with precedence 45
for @{ 'disjoint $a $b }.

interpretation "Left cosets disjoint" 'disjoint C C' =
 (cic:/matita/algebra/groups/left_coset_disjoint.con _ C C').

(* The following should be a one-shot alias! *)
alias symbol "member_of" (instance 0) = "Member of subgroup".
theorem member_of_subgroup_op_inv_x_y_to_left_coset_eq:
 ∀G.∀x,y.∀H:subgroup G. (x \sup -1 ·y) ∈ H → x*H = y*H.
intros;
unfold left_coset_eq;
simplify in ⊢ (? → ? ? ? (? ? % ?));
simplify in ⊢ (? → ? ? ? (? ? ? (? ? ? (? ? %) ?)));
simplify in ⊢ (? % → ?);
intros;
unfold member_of_left_coset;
simplify in ⊢ (? ? (λy:?.? ? ? (? ? ? (? ? ? (? ? %) ?))));
simplify in ⊢ (? ? (λy:? %.?));
simplify in ⊢ (? ? (λy:?.? ? ? (? ? % ?)));
unfold member_of_subgroup in H1;
elim H1;
clear H1;
exists;
[ apply (a\sup-1 · x1)
| rewrite > (f_morph ? ? (morphism ? ? H));
  rewrite > (eq_image_inv_inv_image ? ? 
  rewrite < H2;
  rewrite > (eq_inv_op_x_y_op_inv_y_inv_x ? ? ? ? H2);
].
qed.

(*theorem foo:
 \forall G:Group. \forall x1,x2:G. \forall H:subgroup G.
  x1*x2^-1 \nin H \to x1*H does_not_overlap x2*H

theorem foo:
 \forall x:G. \forall H:subgroup G. x \in x*H

definition disjoinct
 (T: Type) (n:nat) (S: \forall x:nat. x < n -> {S:Type * (S -> T)})
:=
 \forall i,j:nat. i < n \to j < n \to ...


check
 (λG.λH,H':left_coset G.λx:Type_of_Group (group ? (subgrp ? H)). (embed ? (subgrp ? H) x)).

definition left_coset_eq ≝
 λG.λH,H':left_coset G.
  ∀x:group ? (subgrp ? H).
   ex (group ? (subgroup ? H')) (λy.
    (element ? H)·(embed ? (subgrp ? H) x) =
    (element ? H')·(embed ? (subgrp ? H') y)).
 
(*record left_coset (G:Group) : Type ≝
 { subgroup: Group;
   subgroup_is_subgroup: subgroup ≤ G;
   element: G
 }.

definition left_coset_eq ≝
 λG.λH,H':left_coset G.
  ∀x:subgroup ? H.
   ex (subgroup ? H') (λy.
    (element ? H)·(embed ? ? (subgroup_is_subgroup ? H) ˜ x) =
    (element ? H')·(embed ? ? (subgroup_is_subgroup ? H') ˜ y)).
*)
*)
