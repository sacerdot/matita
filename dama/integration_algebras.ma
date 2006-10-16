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

definition left_inverse \def λC,op.λe:C.λinv:C→C. ∀x:C. op (inv x) x = e.

record is_abelian_group (C:Type) (plus:C→C→C) (zero:C) (opp:C→C) : Prop \def
 { (* abelian additive semigroup properties *)
    plus_assoc: associative ? plus;
    plus_comm: symmetric ? plus;
    (* additive monoid properties *)
    zero_neutral: left_neutral ? plus zero;
    (* additive group properties *)
    opp_inverse: left_inverse ? plus zero opp
 }.

record is_field (C:Type) (plus:C→C→C) (mult:C→C→C) (zero,one:C) (opp:C→C)
 (inv:∀x:C.x ≠ zero →C)  : Prop
≝
 {  (* abelian group properties *)
    abelian_group:> is_abelian_group ? plus zero opp;
    (* abelian multiplicative semigroup properties *)
    mult_assoc: associative ? mult;
    mult_comm: symmetric ? mult;
    (* multiplicative monoid properties *)
    one_neutral: left_neutral ? mult one;
    (* multiplicative group properties *)
    inv_inverse: ∀x.∀p: x ≠ zero. mult (inv x p) x = one;
    (* ring properties *)
    mult_plus_distr: distributive ? mult plus;
    (* integral domain *)
    not_eq_zero_one: zero ≠ one
 }.

let rec sum (C:Type) (plus:C→C→C) (zero,one:C) (n:nat) on n  ≝
 match n with
  [ O ⇒ zero
  | (S m) ⇒ plus one (sum C plus zero one m)
  ].

record field : Type \def
 { carrier:> Type;
   plus: carrier → carrier → carrier;
   mult: carrier → carrier → carrier;
   zero: carrier;
   one: carrier;
   opp: carrier → carrier;
   inv: ∀x:carrier. x ≠ zero → carrier;
   field_properties: is_field ? plus mult zero one opp inv
 }.

definition sum_field ≝
 λF:field. sum ? (plus F) (zero F) (one F).
 
notation "0" with precedence 89
for @{ 'zero }.

interpretation "Field zero" 'zero =
 (cic:/matita/integration_algebras/zero.con _).

notation "1" with precedence 89
for @{ 'one }.

interpretation "Field one" 'one =
 (cic:/matita/integration_algebras/one.con _).

interpretation "Field plus" 'plus a b =
 (cic:/matita/integration_algebras/plus.con _ a b).

interpretation "Field mult" 'times a b =
 (cic:/matita/integration_algebras/mult.con _ a b).

interpretation "Field opp" 'uminus a =
 (cic:/matita/integration_algebras/opp.con _ a).
 
record is_ordered_field_ch0 (C:Type) (plus,mult:C→C→C) (zero,one:C) (opp:C→C)
 (inv:∀x:C.x ≠ zero → C) (le:C→C→Prop) : Prop \def
 { (* field properties *)
   of_is_field:> is_field C plus mult zero one opp inv;
   of_mult_compat: ∀a,b. le zero a → le zero b → le zero (mult a b);
   of_plus_compat: ∀a,b,c. le a b → le (plus a c) (plus b c);
   of_weak_tricotomy : ∀a,b. a≠b → le a b ∨ le b a;
   (* 0 characteristics *)
   of_char0: ∀n. n > O → sum ? plus zero one n ≠ zero
 }.
 
record ordered_field_ch0 : Type \def
 { of_field:> field;
   of_le: of_field → of_field → Prop;
   of_ordered_field_properties:>
    is_ordered_field_ch0 ? (plus of_field) (mult of_field) (zero of_field)
     (one of_field) (opp of_field) (inv of_field) of_le
 }.

interpretation "Ordered field le" 'leq a b =
 (cic:/matita/integration_algebras/of_le.con _ a b).
 
definition lt \def λF:ordered_field_ch0.λa,b:F.a ≤ b ∧ a ≠ b.

interpretation "Ordered field lt" 'lt a b =
 (cic:/matita/integration_algebras/lt.con _ a b).

lemma le_zero_x_to_le_opp_x_zero: ∀F:ordered_field_ch0.∀x:F. 0 ≤ x → -x ≤ 0.
 intros;
 generalize in match (of_plus_compat ? ? ? ? ? ? ? ? F ? ? (-x) H); intro;
 rewrite > (zero_neutral ? ? ? ? F) in H1;
 rewrite > (plus_comm ? ? ? ? F) in H1;
 rewrite > (opp_inverse ? ? ? ? F) in H1;
 assumption.
qed.

lemma le_x_zero_to_le_zero_opp_x: ∀F:ordered_field_ch0.∀x:F. x ≤ 0 → 0 ≤ -x.
 intros;
 generalize in match (of_plus_compat ? ? ? ? ? ? ? ? F ? ? (-x) H); intro;
 rewrite > (zero_neutral ? ? ? ? F) in H1;
 rewrite > (plus_comm ? ? ? ? F) in H1;
 rewrite > (opp_inverse ? ? ? ? F) in H1;
 assumption.
qed.

(* To be proved for rings only *)
lemma eq_mult_zero_x_zero: ∀F:ordered_field_ch0.∀x:F.0*x=0.
 intros;
 generalize in match (zero_neutral ? ? ? ? F 0); intro;
 generalize in match (eq_f ? ? (λy.x*y) ? ? H); intro; clear H;
 rewrite > (mult_plus_distr ? ? ? ? ? ? ? F) in H1;
 generalize in match (eq_f ? ? (λy.-(x*0)+y) ? ? H1); intro; clear H1;
 rewrite < (plus_assoc ? ? ? ? F) in H;
 rewrite > (opp_inverse ? ? ? ? F) in H;
 rewrite > (zero_neutral ? ? ? ? F) in H;
 rewrite > (mult_comm ? ? ? ? ? ? ? F) in H;
 assumption.
qed.

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

record is_vector_space (K: field) (C:Type) (plus:C→C→C) (zero:C) (opp:C→C)
 (mult:K→C→C) : Prop
≝
 { (* abelian group properties *)
   vs_abelian_group: is_abelian_group ? plus zero opp;
   (* other properties *)
   vs_nilpotent: ∀v. mult 0 v = zero;
   vs_neutral: ∀v. mult 1 v = v;
   vs_distributive: ∀a,b,v. mult (a + b) v = plus (mult a v) (mult b v);
   vs_associative: ∀a,b,v. mult (a * b) v = mult a (mult b v)
 }.

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

definition le \def λC.λmeet:C→C→C.λf,g. meet f g = f.

record is_riesz_space (K:ordered_field_ch0) (C:Type) (plus:C→C→C) (zero:C)
 (opp:C→C) (mult:K→C→C) (join,meet:C→C→C) : Prop \def
 { (* vector space properties *)
   rs_vector_space: is_vector_space K C plus zero opp mult;
   (* lattice properties *)
   rs_lattice: is_lattice C join meet;
   (* other properties *)
   rs_compat_le_plus: ∀f,g,h. le ? meet f g →le ? meet (plus f h) (plus g h);
   rs_compat_le_times: ∀a,f. 0≤a → le ? meet zero f → le ? meet zero (mult a f)  
 }.

definition absolute_value \def λC:Type.λopp.λjoin:C→C→C.λf.join f (opp f).   

record is_archimedean_riesz_space (K:ordered_field_ch0) (C:Type) (plus:C→C→C)
 (zero:C) (opp:C→C) (mult:Type_OF_ordered_field_ch0 K→C→C) (join,meet:C→C→C) : Prop \def
  { ars_riesz_space: is_riesz_space ? ? plus zero opp mult join meet;
    ars_archimedean: ∃u.∀n,a.∀p:n > O.
     le C meet (absolute_value ? opp join a)
      (mult (inv K (sum_field K n) (not_eq_sum_field_zero K n p)) u) →
     a = zero
  }.