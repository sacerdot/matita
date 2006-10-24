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

set "baseuri" "cic:/matita/integration_algebras/".

include "higher_order_defs/functions.ma".
include "nat/nat.ma".
include "nat/orders.ma".

definition left_neutral \def λC,op.λe:C. ∀x:C. op e x = x.

definition right_neutral \def λC,op. λe:C. ∀x:C. op x e=x.

definition left_inverse \def λC,op.λe:C.λinv:C→C. ∀x:C. op (inv x) x = e.

definition right_inverse \def λC,op.λe:C.λ inv: C→ C. ∀x:C. op x (inv x)=e. 

definition distributive_left ≝
 λA:Type.λf:A→A→A.λg:A→A→A.
  ∀x,y,z. f x (g y z) = g (f x y) (f x z).

definition distributive_right ≝
 λA:Type.λf:A→A→A.λg:A→A→A.
  ∀x,y,z. f (g x y) z = g (f x z) (f y z).

record is_abelian_group (C:Type) (plus:C→C→C) (zero:C) (opp:C→C) : Prop \def
 { (* abelian additive semigroup properties *)
    plus_assoc_: associative ? plus;
    plus_comm_: symmetric ? plus;
    (* additive monoid properties *)
    zero_neutral_: left_neutral ? plus zero;
    (* additive group properties *)
    opp_inverse_: left_inverse ? plus zero opp
 }.

record abelian_group : Type \def
 { carrier:> Type;
   plus: carrier → carrier → carrier;
   zero: carrier;
   opp: carrier → carrier;
   ag_abelian_group_properties: is_abelian_group ? plus zero opp
 }.

notation "0" with precedence 89
for @{ 'zero }.

interpretation "Ring zero" 'zero =
 (cic:/matita/integration_algebras/zero.con _).

interpretation "Ring plus" 'plus a b =
 (cic:/matita/integration_algebras/plus.con _ a b).

interpretation "Ring opp" 'uminus a =
 (cic:/matita/integration_algebras/opp.con _ a).
 
theorem plus_assoc: ∀G:abelian_group. associative ? (plus G).
 intro;
 apply (plus_assoc_ ? ? ? ? (ag_abelian_group_properties G)).
qed.

theorem plus_comm: ∀G:abelian_group. symmetric ? (plus G).
 intro;
 apply (plus_comm_ ? ? ? ? (ag_abelian_group_properties G)).
qed.

theorem zero_neutral: ∀G:abelian_group. left_neutral ? (plus G) 0.
 intro;
 apply (zero_neutral_ ? ? ? ? (ag_abelian_group_properties G)).
qed.

theorem opp_inverse: ∀G:abelian_group. left_inverse ? (plus G) 0 (opp G).
 intro;
 apply (opp_inverse_ ? ? ? ? (ag_abelian_group_properties G)).
qed.

lemma cancellationlaw: ∀G:abelian_group.∀x,y,z:G. x+y=x+z → y=z. 
intros;
generalize in match (eq_f ? ? (λa.-x +a) ? ? H);
intros; clear H;
rewrite < plus_assoc in H1;
rewrite < plus_assoc in H1;
rewrite > opp_inverse in H1;
rewrite > zero_neutral in H1;
rewrite > zero_neutral in H1;
assumption.
qed.

(****************************** rings *********************************)

record is_ring (G:abelian_group) (mult:G→G→G) : Prop
≝
 {  (* multiplicative semigroup properties *)
    mult_assoc_: associative ? mult;
    (* ring properties *)
    mult_plus_distr_left_: distributive_left ? mult (plus G);
    mult_plus_distr_right_: distributive_right ? mult (plus G)
 }.
 
record ring : Type \def
 { r_abelian_group:> abelian_group;
   mult: r_abelian_group → r_abelian_group → r_abelian_group;
   r_ring_properties: is_ring r_abelian_group mult
 }.

theorem mult_assoc: ∀R:ring.associative ? (mult R).
 intros;
 apply (mult_assoc_ ? ? (r_ring_properties R)).
qed.

theorem mult_plus_distr_left: ∀R:ring.distributive_left ? (mult R) (plus R).
 intros;
 apply (mult_plus_distr_left_ ? ? (r_ring_properties R)).
qed.

theorem mult_plus_distr_right: ∀R:ring.distributive_right ? (mult R) (plus R).
 intros;
 apply (mult_plus_distr_right_ ? ? (r_ring_properties R)).
qed.

interpretation "Ring mult" 'times a b =
 (cic:/matita/integration_algebras/mult.con _ a b).

lemma eq_mult_zero_x_zero: ∀R:ring.∀x:R.0*x=0.
 intros;
 generalize in match (zero_neutral R 0); intro;
 generalize in match (eq_f ? ? (λy.y*x) ? ? H); intro; clear H;
 rewrite > mult_plus_distr_right in H1;
 generalize in match (eq_f ? ? (λy.-(0*x)+y) ? ? H1); intro; clear H1;
 rewrite < plus_assoc in H;
 rewrite > opp_inverse in H;
 rewrite > zero_neutral in H;
 assumption.
qed.

lemma eq_mult_x_zero_zero: ∀R:ring.∀x:R.x*0=0.
intros;
generalize in match (zero_neutral R 0);
intro;
generalize in match (eq_f ? ? (\lambda y.x*y) ? ? H); intro; clear H;
rewrite > mult_plus_distr_left in H1;
generalize in match (eq_f ? ? (\lambda y. (-(x*0)) +y) ? ? H1);intro;
clear H1;
rewrite < plus_assoc in H;
rewrite > opp_inverse in H;
rewrite > zero_neutral in H;
assumption.
qed.

record is_field (R:ring) (one:R) (inv:∀x:R.x ≠ 0 → R) : Prop
≝
 {  (* multiplicative abelian properties *)
    mult_comm_: symmetric ? (mult R);
    (* multiplicative monoid properties *)
    one_neutral_: left_neutral ? (mult R) one;
    (* multiplicative group properties *)
    inv_inverse_: ∀x.∀p: x ≠ 0. mult ? (inv x p) x = one;
    (* integral domain *)
    not_eq_zero_one_: (0 ≠ one)
 }.


lemma opp_opp: \forall R:ring. \forall x:R. (-(-x))=x.
intros; 
apply (cancellationlaw ? (-x) ? ?); 
rewrite > (opp_inverse R x); 
rewrite > plus_comm;
rewrite > opp_inverse;
reflexivity.
qed.


let rec sum (C:Type) (plus:C→C→C) (zero,one:C) (n:nat) on n  ≝
 match n with
  [ O ⇒ zero
  | (S m) ⇒ plus one (sum C plus zero one m)
  ].

record field : Type \def
 { f_ring:> ring;
   one: f_ring;
   inv: ∀x:f_ring. x ≠ 0 → f_ring;
   field_properties: is_field f_ring one inv
 }.
 
notation "1" with precedence 89
for @{ 'one }.

interpretation "Field one" 'one =
 (cic:/matita/integration_algebras/one.con _).

theorem mult_comm: ∀F:field.symmetric ? (mult F).
 intro;
 apply (mult_comm_ ? ? ? (field_properties F)).
qed.

theorem one_neutral: ∀F:field.left_neutral ? (mult F) 1.
 intro;
 apply (one_neutral_ ? ? ? (field_properties F)).
qed.

theorem inv_inverse: ∀F:field.∀x.∀p: x ≠ 0. mult ? (inv F x p) x = 1.
 intro;
 apply (inv_inverse_ ? ? ? (field_properties F)).
qed.

theorem not_eq_zero_one: ∀F:field.0 ≠ 1.
 [2:
   intro;
   apply (not_eq_zero_one_ ? ? ? (field_properties F))
 | skip
 ]
qed.

definition sum_field ≝
 λF:field. sum ? (plus F) (zero F) (one F).
 
record is_ordered_field_ch0 (F:field) (le:F→F→Prop) : Prop \def
 { of_mult_compat: ∀a,b. le 0 a → le 0 b → le 0 (a*b);
   of_plus_compat: ∀a,b,c. le a b → le (a+c) (b+c);
   of_weak_tricotomy : ∀a,b. a≠b → le a b ∨ le b a;
   (* 0 characteristics *)
   of_char0: ∀n. n > O → sum ? (plus F) 0 1 n ≠ 0
 }.
 
record ordered_field_ch0 : Type \def
 { of_field:> field;
   of_le: of_field → of_field → Prop;
   of_ordered_field_properties:> is_ordered_field_ch0 of_field of_le
 }.

interpretation "Ordered field le" 'leq a b =
 (cic:/matita/integration_algebras/of_le.con _ a b).
 
definition lt \def λF:ordered_field_ch0.λa,b:F.a ≤ b ∧ a ≠ b.

interpretation "Ordered field lt" 'lt a b =
 (cic:/matita/integration_algebras/lt.con _ a b).

(*incompleto
lemma le_zero_x_to_le_opp_x_zero: ∀F:ordered_field_ch0.∀x:F. 0 ≤ x → -x ≤ 0.
intros;
 generalize in match (of_plus_compat ? ? ? ? ? ? ? ? F ? ? (-x) H); intro;
 rewrite > (zero_neutral ? ? ? ? F) in H1;
 rewrite > (plus_comm  ? ? ?  ? F) in H1;
 rewrite > (opp_inverse ? ? ? ? F) in H1;
 
 assumption.
qed.*)

axiom le_x_zero_to_le_zero_opp_x: ∀F:ordered_field_ch0.∀x:F. x ≤ 0 → 0 ≤ -x.
(* intros;
 generalize in match (of_plus_compat ? ? ? ? ? ? ? ? F ? ? (-x) H); intro;
 rewrite > (zero_neutral ? ? ? ? F) in H1;
 rewrite > (plus_comm ? ? ? ? F) in H1;
 rewrite > (opp_inverse ? ? ? ? F) in H1;
 assumption.
qed.*)

(*
lemma eq_opp_x_times_opp_one_x: ∀F:ordered_field_ch0.∀x:F.-x = -1*x.
 intros;
 
lemma not_eq_x_zero_to_lt_zero_mult_x_x:
 ∀F:ordered_field_ch0.∀x:F. x ≠ 0 → 0 < x * x.
 intros;
 elim (of_weak_tricotomy ? ? ? ? ? ? ? ? F ? ? H);
  [ generalize in match (le_x_zero_to_le_zero_opp_x F ? H1); intro;
    generalize in match (of_mult_compat ? ? ? ? ? ? ? ?  F ? ? H2 H2); intro;
*)  

axiom not_eq_sum_field_zero: ∀F,n. n > O → sum_field F n ≠ 0.

record is_vector_space (K: field) (G:abelian_group) (emult:K→G→G) : Prop
≝
 { vs_nilpotent: ∀v. emult 0 v = 0;
   vs_neutral: ∀v. emult 1 v = v;
   vs_distributive: ∀a,b,v. emult (a + b) v = (emult a v) + (emult b v);
   vs_associative: ∀a,b,v. emult (a * b) v = emult a (emult b v)
 }.

record vector_space (K:field): Type \def
{ vs_abelian_group :> abelian_group;
  emult: K → vs_abelian_group → vs_abelian_group;
  vs_vector_space_properties :> is_vector_space K vs_abelian_group emult
}.

interpretation "Vector space external product" 'times a b =
 (cic:/matita/integration_algebras/emult.con _ _ a b).

record is_lattice (C:Type) (join,meet:C→C→C) : Prop \def
 { (* abelian semigroup properties *)
   l_comm_j: symmetric ? join;
   l_associative_j: associative ? join;
   l_comm_m: symmetric ? meet;
   l_associative_m: associative ? meet;
   (* other properties *)
   l_adsorb_j_m: ∀f,g. join f (meet f g) = f;
   l_adsorb_m_j: ∀f,g. meet f (join f g) = f
 }.

record lattice (C:Type) : Type \def
 { join: C → C → C;
   meet: C → C → C;
   l_lattice_properties: is_lattice ? join meet
 }.

definition le \def λC:Type.λL:lattice C.λf,g. meet ? L f g = f.

interpretation "Lattice le" 'leq a b =
 (cic:/matita/integration_algebras/le.con _ _ a b).

definition carrier_of_lattice ≝
 λC:Type.λL:lattice C.C.

record is_riesz_space (K:ordered_field_ch0) (V:vector_space K)
 (L:lattice (Type_OF_vector_space ? V))
: Prop
\def
 { rs_compat_le_plus: ∀f,g,h. le ? L f g → le ? L (f+h) (g+h);
   rs_compat_le_times: ∀a:K.∀f. of_le ? 0 a → le ? L 0 f → le ? L 0 (a*f)
 }.

record riesz_space : Type \def
 { rs_ordered_field_ch0: ordered_field_ch0;
   rs_vector_space:> vector_space rs_ordered_field_ch0;
   rs_lattice:> lattice rs_vector_space;
   rs_riesz_space_properties: is_riesz_space ? rs_vector_space rs_lattice
 }.

definition absolute_value \def λS:riesz_space.λf.join ? S f (-f).   

record is_archimedean_riesz_space (S:riesz_space) : Prop
\def
  { ars_archimedean: ∃u.∀n.∀a.∀p:n > O.
     le ? S
      (absolute_value S a)
      (emult ? S
        (inv ? (sum_field (rs_ordered_field_ch0 S) n) (not_eq_sum_field_zero ? n p))
        u) →
     a = 0
  }.

record archimedean_riesz_space : Type \def
 { ars_riesz_space:> riesz_space;
   ars_archimedean_property: is_archimedean_riesz_space ars_riesz_space
 }.

record is_algebra (K: field) (V:vector_space K) (mult:V→V→V) : Prop
≝
 { (* ring properties *)
   a_ring: is_ring V mult;
   (* algebra properties *)
   a_associative_left: ∀a,f,g. a * (mult f g) = mult (a * f) g;
   a_associative_right: ∀a,f,g. a * (mult f g) = mult f (a * g)
 }.

record algebra (K: field) (V:vector_space K) : Type \def
 { a_mult: V → V → V;
   a_algebra_properties: is_algebra K V a_mult
 }.

interpretation "Algebra product" 'times a b =
 (cic:/matita/integration_algebras/a_mult.con _ _ _ a b).

record is_f_algebra (S:archimedean_riesz_space)
 (A:algebra (rs_ordered_field_ch0 (ars_riesz_space S)) S) : Prop
\def 
{ compat_mult_le:
   ∀f,g:S.
    le ? S 0 f → le ? S 0 g → le ? S 0 (a_mult ? ? A f g);
  compat_mult_meet:
   ∀f,g,h:S.
    meet ? S f g = 0 → meet ? S (a_mult ? ? A h f) g = 0
}.

record f_algebra : Type \def 
{ fa_archimedean_riesz_space: archimedean_riesz_space;
  fa_algebra: algebra ? fa_archimedean_riesz_space;
  fa_f_algebra_properties: is_f_algebra fa_archimedean_riesz_space fa_algebra
}.
