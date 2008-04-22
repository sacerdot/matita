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



include "attic/fields.ma".
include "ordered_group.ma".

(*CSC: non capisco questi alias! Una volta non servivano*)
alias id "plus" = "cic:/matita/group/plus.con".
alias symbol "plus" = "Abelian group plus".

record pre_ordered_field_ch0: Type ≝
 { of_field:> field;
   of_ordered_abelian_group_: ordered_abelian_group;
   of_cotransitively_ordered_set_: cotransitively_ordered_set;
   of_with1_:
    cos_ordered_set of_cotransitively_ordered_set_ =
     og_ordered_set of_ordered_abelian_group_;
   of_with2:
    og_abelian_group of_ordered_abelian_group_ = r_abelian_group of_field
 }.

lemma of_ordered_abelian_group: pre_ordered_field_ch0 → ordered_abelian_group.
 intro F;
 apply mk_ordered_abelian_group;
  [ apply mk_pre_ordered_abelian_group;
     [ apply (r_abelian_group F)
     | apply (og_ordered_set (of_ordered_abelian_group_ F))
     | apply (eq_f ? ? carrier);
       apply (of_with2 F)
     ]
  |
    apply
     (eq_rect' ? ?
      (λG:abelian_group.λH:og_abelian_group (of_ordered_abelian_group_ F)=G.
        is_ordered_abelian_group
         (mk_pre_ordered_abelian_group G (of_ordered_abelian_group_ F)
          (eq_f abelian_group Type carrier (of_ordered_abelian_group_ F) G
          H)))
      ? ? (of_with2 F));
    simplify;
    apply (og_ordered_abelian_group_properties (of_ordered_abelian_group_ F))
  ]
qed.

coercion cic:/matita/attic/ordered_fields_ch0/of_ordered_abelian_group.con.

(*CSC: I am not able to prove this since unfold is undone by coercion composition*)
axiom of_with1:
 ∀G:pre_ordered_field_ch0.
  cos_ordered_set (of_cotransitively_ordered_set_ G) =
   og_ordered_set (of_ordered_abelian_group G).

lemma of_cotransitively_ordered_set : pre_ordered_field_ch0 → cotransitively_ordered_set.
 intro F;
 apply mk_cotransitively_ordered_set;
 [ apply (og_ordered_set F)
 | apply
    (eq_rect ? ? (λa:ordered_set.cotransitive (os_carrier a) (os_le a))
      ? ? (of_with1 F));
   apply cos_cotransitive
 ]
qed.

coercion cic:/matita/attic/ordered_fields_ch0/of_cotransitively_ordered_set.con.

record is_ordered_field_ch0 (F:pre_ordered_field_ch0) : Type \def
 { of_mult_compat: ∀a,b:F. 0≤a → 0≤b → 0≤a*b;
   of_weak_tricotomy : ∀a,b:F. a≠b → a≤b ∨ b≤a;
   (* 0 characteristics *)
   of_char0: ∀n. n > O → sum ? (plus F) 0 1 n ≠ 0
 }.
 
record ordered_field_ch0 : Type \def
 { of_pre_ordered_field_ch0:> pre_ordered_field_ch0;
   of_ordered_field_properties:> is_ordered_field_ch0 of_pre_ordered_field_ch0
 }.

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
    ∀n:nat.∃m:nat.∀j:nat.m ≤ j →
     l - (inv F (sum_field ? (S n)) ?) ≤ f j ∧
     f j ≤ l + (inv F (sum_field ? (S n)) ?));
 apply not_eq_sum_field_zero;
 unfold;
 autobatch.
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
     ∃n:nat.∀N.n ≤ N →
      -(inv ? (sum_field F (S m)) ?) ≤ f N - f n ∧
      f N - f n ≤ inv ? (sum_field F (S m)) ?);
 apply not_eq_sum_field_zero;
 unfold;
 autobatch.
qed.

definition is_complete ≝
 λF:ordered_field_ch0.
  ∀f:nat→F. is_cauchy_seq ? f →
   ex F (λl:F. tends_to ? f l).
