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

set "baseuri" "cic:/matita/ordered_fields_ch0/".

include "fields.ma".

record is_total_order_relation (C:Type) (le:C→C→Prop) : Type \def
 { to_cotransitive: ∀x,y,z:C. le x y → le x z ∨ le z y;
   to_antisimmetry: ∀x,y:C. le x y → le y x → x=y
 }.

theorem to_transitive:
 ∀C.∀le:C→C→Prop. is_total_order_relation ? le → transitive ? le.
 intros;
 unfold transitive;
 intros;
 elim (to_cotransitive ? ? i ? ? z H);
  [ assumption
  | rewrite < (to_antisimmetry ? ? i ? ? H1 t);
    assumption
  ].
qed.

record is_ordered_field_ch0 (F:field) (le:F→F→Prop) : Type \def
 { of_total_order_relation:> is_total_order_relation ? le;
   of_mult_compat: ∀a,b. le 0 a → le 0 b → le 0 (a*b);
   of_plus_compat: ∀a,b,c. le a b → le (a+c) (b+c);
   of_weak_tricotomy : ∀a,b. a≠b → le a b ∨ le b a;
   (* 0 characteristics *)
   of_char0: ∀n. n > O → sum ? (plus F) 0 1 n ≠ 0
 }.
 
record ordered_field_ch0 : Type \def
 { of_field:> field;
   of_le: of_field → of_field → Prop;
   of_ordered_field_properties:> is_ordered_field_ch0 ? of_le
 }.

interpretation "Ordered field le" 'leq a b =
 (cic:/matita/ordered_fields_ch0/of_le.con _ a b).
 
definition lt \def λF:ordered_field_ch0.λa,b:F.a ≤ b ∧ a ≠ b.

interpretation "Ordered field lt" 'lt a b =
 (cic:/matita/ordered_fields_ch0/lt.con _ a b).

lemma le_zero_x_to_le_opp_x_zero: ∀F:ordered_field_ch0.∀x:F. 0 ≤ x → -x ≤ 0.
intros;
 generalize in match (of_plus_compat ? ? F ? ? (-x) H); intro;
 rewrite > zero_neutral in H1;
 rewrite > plus_comm in H1;
 rewrite > opp_inverse in H1;
 assumption.
qed.

lemma le_x_zero_to_le_zero_opp_x: ∀F:ordered_field_ch0.∀x:F. x ≤ 0 → 0 ≤ -x.
 intros;
 generalize in match (of_plus_compat ? ? F ? ? (-x) H); intro;
 rewrite > zero_neutral in H1;
 rewrite > plus_comm in H1;
 rewrite > opp_inverse in H1;
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

axiom lt_zero_to_lt_inv_zero:
 ∀F:ordered_field_ch0.∀x:F.∀p:x≠0. 0 < x → 0 < inv ? x p.
 
(* The ordering is not necessary. *)
axiom not_eq_sum_field_zero: ∀F:ordered_field_ch0.∀n. O<n → sum_field F n ≠ 0.
axiom le_zero_sum_field: ∀F:ordered_field_ch0.∀n. O<n → 0 < sum_field F n.

axiom lt_zero_to_le_inv_zero:
 ∀F:ordered_field_ch0.∀n:nat.∀p:sum_field F n ≠ 0. 0 ≤ inv ? (sum_field ? n) p.

definition tends_to : ∀F:ordered_field_ch0.∀f:nat→F.∀l:F.Prop.
 apply
  (λF:ordered_field_ch0.λf:nat → F.λl:F.
    ∀n:nat.∃m:nat.∀j:nat. m≤j →
     l - (inv F (sum_field ? (S n)) ?) ≤ f j ∧
     f j ≤ l + (inv F (sum_field ? (S n)) ?));
 apply not_eq_sum_field_zero;
 unfold;
 auto new.
qed.

(*
definition is_cauchy_seq ≝
 λF:ordered_field_ch0.λf:nat→F.
  ∀eps:F. 0 < eps →
   ∃n:nat.∀M. n ≤ M →
    -eps ≤ f M - f n ∧ f M - f n ≤ eps.
*)



definition is_cauchy_seq : ∀F:ordered_field_ch0.∀f:nat→F.Prop.
 apply
  (λF:ordered_field_ch0.λf:nat→F.
    ∀m:nat.
     ∃n:nat.∀N. n ≤ N →
      -(inv ? (sum_field F (S m)) ?) ≤ f N - f n ∧
      f N - f n ≤ inv ? (sum_field F (S m)) ?);
 apply not_eq_sum_field_zero;
 unfold;
 auto.
qed.

definition is_complete ≝
 λF:ordered_field_ch0.
  ∀f:nat→F. is_cauchy_seq ? f →
   ex F (λl:F. tends_to ? f l).