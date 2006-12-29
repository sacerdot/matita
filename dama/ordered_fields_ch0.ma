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
include "ordered_sets2.ma".

(*CSC: non capisco questi alias! Una volta non servivano*)
alias id "plus" = "cic:/matita/groups/plus.con".
alias symbol "plus" = "Abelian group plus".

record pre_ordered_field_ch0: Type ≝
 { of_field:> field;
   of_cotransitively_ordered_set_: cotransitively_ordered_set;
   of_with: os_carrier of_cotransitively_ordered_set_ = carrier of_field
 }.

(*CSC: the following lemma (that is also a coercion) should be automatically
  generated *)
lemma of_cotransitively_ordered_set : pre_ordered_field_ch0 → cotransitively_ordered_set.
 intro F;
 apply mk_cotransitively_ordered_set;
 [ apply mk_ordered_set;
   [ apply (carrier F)
   | apply
      (eq_rect ? ? (λC:Type.C→C→Prop) (os_le (of_cotransitively_ordered_set_ F)) ? (of_with F))
   | apply
      (eq_rect' Type (os_carrier (of_cotransitively_ordered_set_ F))
        (λa:Type.λH:os_carrier (of_cotransitively_ordered_set_ F)=a.
          is_order_relation a (eq_rect Type (os_carrier (of_cotransitively_ordered_set_ F)) (λC:Type.C→C→Prop) (os_le (of_cotransitively_ordered_set_ F)) a H))
        ? (Type_OF_pre_ordered_field_ch0 F) (of_with F));
     simplify; 
     apply (os_order_relation_properties (of_cotransitively_ordered_set_ F))
   ]
 | simplify;
   apply
    (eq_rect' ? ?
      (λa:Type.λH:os_carrier (of_cotransitively_ordered_set_ F)=a.
        cotransitive a
         match H in eq
          return
           λa2:Type.λH1:os_carrier (of_cotransitively_ordered_set_ F)=a2.
            a2→a2→Prop
         with 
          [refl_eq ⇒ os_le (of_cotransitively_ordered_set_ F)])
      ? ? (of_with F));
   simplify;
   apply cos_cotransitive
 ].
qed.

coercion cic:/matita/ordered_fields_ch0/of_cotransitively_ordered_set.con.

record is_ordered_field_ch0 (F:pre_ordered_field_ch0) : Type \def
 { of_mult_compat: ∀a,b:F. 0≤a → 0≤b → 0≤a*b;
   of_plus_compat: ∀a,b,c:F. a≤b → a+c≤b+c;
   of_weak_tricotomy : ∀a,b:F. a≠b → a≤b ∨ b≤a;
   (* 0 characteristics *)
   of_char0: ∀n. n > O → sum ? (plus F) 0 1 n ≠ 0
 }.
 
record ordered_field_ch0 : Type \def
 { of_pre_ordered_field_ch0:> pre_ordered_field_ch0;
   of_ordered_field_properties:> is_ordered_field_ch0 of_pre_ordered_field_ch0
 }.

lemma le_zero_x_to_le_opp_x_zero: ∀F:ordered_field_ch0.∀x:F.0 ≤ x → -x ≤ 0.
 intros;
 generalize in match (of_plus_compat ? F ? ? (-x) H); intro;
 rewrite > zero_neutral in H1;
 rewrite > plus_comm in H1;
 rewrite > opp_inverse in H1;
 assumption.
qed.

lemma le_x_zero_to_le_zero_opp_x: ∀F:ordered_field_ch0.∀x:F. x ≤ 0 → 0 ≤ -x.
 intros;
 generalize in match (of_plus_compat ? F ? ? (-x) H); intro;
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
 ∀F:ordered_field_ch0.∀x:F.∀p:x≠0. lt F 0 x → lt F 0 (inv ? x p).

alias symbol "lt" = "natural 'less than'".

(* The ordering is not necessary. *)
axiom not_eq_sum_field_zero: ∀F:ordered_field_ch0.∀n. O<n → sum_field F n ≠ 0.
axiom le_zero_sum_field: ∀F:ordered_field_ch0.∀n. O<n → lt F 0 (sum_field F n).

axiom lt_zero_to_le_inv_zero:
 ∀F:ordered_field_ch0.∀n:nat.∀p:sum_field F n ≠ 0. 0 ≤ inv ? (sum_field ? n) p.

definition tends_to : ∀F:ordered_field_ch0.∀f:nat→F.∀l:F.Prop.
 apply
  (λF:ordered_field_ch0.λf:nat → F.λl:F.
    ∀n:nat.∃m:nat.∀j:nat. le m j →
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
     ∃n:nat.∀N. le n N →
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
