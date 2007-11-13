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
include "ordered_sets.ma".

record pre_ordered_abelian_group : Type ≝
 { og_abelian_group:> abelian_group;
   og_tordered_set_: tordered_set;
   og_with: exc_carr og_tordered_set_ = og_abelian_group
 }.

lemma og_tordered_set: pre_ordered_abelian_group → tordered_set.
intro G; apply mk_tordered_set;
[1: apply mk_pordered_set;
    [1: apply (mk_excedence G); 
        [1: cases G; clear G; simplify; rewrite < H; clear H;
            cases og_tordered_set_; clear og_tordered_set_; simplify;
            cases tos_poset; simplify; cases pos_carr; simplify; assumption;
        |2: cases G; simplify; cases H; simplify; clear H; 
            cases og_tordered_set_; simplify; clear og_tordered_set_;
            cases tos_poset; simplify; cases pos_carr; simplify;
            intros; apply H;
        |3: cases G; simplify; cases H; simplify; cases og_tordered_set_; simplify;
            cases tos_poset; simplify; cases pos_carr; simplify; 
            intros; apply c; assumption]
    |2: cases G; simplify;
        cases H; simplify; clear H; cases og_tordered_set_; simplify;
        cases tos_poset; simplify; assumption;]
|2: simplify; (* SLOW, senza la simplify il widget muore *)
    cases G; simplify; 
    generalize in match (tos_totality og_tordered_set_);
    unfold total_order_property;
    cases H; simplify;  cases og_tordered_set_; simplify;
    cases tos_poset; simplify; cases pos_carr; simplify;
    intros; apply f; assumption;]
qed.

coercion cic:/matita/ordered_groups/og_tordered_set.con.

definition is_ordered_abelian_group ≝
 λG:pre_ordered_abelian_group. ∀f,g,h:G. f≤g → f+h≤g+h.

record ordered_abelian_group : Type ≝
 { og_pre_ordered_abelian_group:> pre_ordered_abelian_group;
   og_ordered_abelian_group_properties:
    is_ordered_abelian_group og_pre_ordered_abelian_group
 }.

lemma le_zero_x_to_le_opp_x_zero: 
  ∀G:ordered_abelian_group.∀x:G.0 ≤ x → -x ≤ 0.
intros (G x Px);
generalize in match (og_ordered_abelian_group_properties ? ? ? (-x) Px); intro;
(* ma cazzo, qui bisogna rifare anche i gruppi con ≈ ? *)
 rewrite > zero_neutral in H;
 rewrite > plus_comm in H;
 rewrite > opp_inverse in H;
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
