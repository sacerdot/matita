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

set "baseuri" "cic:/matita/ordered_groups/".

include "groups.ma".
include "ordered_sets2.ma".

record pre_ordered_abelian_group : Type ≝
 { og_abelian_group:> abelian_group;
   og_ordered_set_: ordered_set;
   og_with: os_carrier og_ordered_set_ = og_abelian_group
 }.

lemma og_ordered_set: pre_ordered_abelian_group → ordered_set.
 intro G;
 apply mk_ordered_set;
  [ apply (carrier (og_abelian_group G))
  | apply (eq_rect ? ? (λC:Type.C→C→Prop) ? ? (og_with G));
    apply os_le
  | apply
     (eq_rect' ? ?
       (λa:Type.λH:os_carrier (og_ordered_set_ G) = a.
        is_order_relation a
         (eq_rect Type (og_ordered_set_ G) (λC:Type.C→C→Prop)
          (os_le (og_ordered_set_ G)) a H))
       ? ? (og_with G));
    simplify;
    apply (os_order_relation_properties (og_ordered_set_ G))
  ]
qed.

coercion cic:/matita/ordered_groups/og_ordered_set.con.

definition is_ordered_abelian_group ≝
 λG:pre_ordered_abelian_group. ∀f,g,h:G. f≤g → f+h≤g+h.

record ordered_abelian_group : Type ≝
 { og_pre_ordered_abelian_group:> pre_ordered_abelian_group;
   og_ordered_abelian_group_properties:
    is_ordered_abelian_group og_pre_ordered_abelian_group
 }.

lemma le_zero_x_to_le_opp_x_zero: ∀G:ordered_abelian_group.∀x:G.0 ≤ x → -x ≤ 0.
 intros;
 generalize in match (og_ordered_abelian_group_properties ? ? ? (-x) H); intro;
 rewrite > zero_neutral in H1;
 rewrite > plus_comm in H1;
 rewrite > opp_inverse in H1;
 assumption.
qed.

lemma le_x_zero_to_le_zero_opp_x: ∀G:ordered_abelian_group.∀x:G. x ≤ 0 → 0 ≤ -x.
 intros;
 generalize in match (og_ordered_abelian_group_properties ? ? ? (-x) H); intro;
 rewrite > zero_neutral in H1;
 rewrite > plus_comm in H1;
 rewrite > opp_inverse in H1;
 assumption.
qed.
