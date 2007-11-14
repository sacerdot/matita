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

include "ordered_sets.ma".
include "groups.ma".

record pre_ordered_abelian_group : Type ≝
 { og_abelian_group_: abelian_group;
   og_tordered_set:> tordered_set;
   og_with: carr og_abelian_group_ = og_tordered_set
 }.

lemma og_abelian_group: pre_ordered_abelian_group → abelian_group.
intro G; apply (mk_abelian_group G); [1,2,3: rewrite < (og_with G)]
[apply (plus (og_abelian_group_ G));|apply zero;|apply opp]
unfold apartness_OF_pre_ordered_abelian_group; cases (og_with G); simplify;
[apply plus_assoc|apply plus_comm|apply zero_neutral|apply opp_inverse|apply plus_strong_ext]
qed.

coercion cic:/matita/ordered_groups/og_abelian_group.con.

definition is_ordered_abelian_group ≝
 λG:pre_ordered_abelian_group. ∀f,g,h:G. f≤g → f+h≤g+h.

record ordered_abelian_group : Type ≝
 { og_pre_ordered_abelian_group:> pre_ordered_abelian_group;
   og_ordered_abelian_group_properties:
    is_ordered_abelian_group og_pre_ordered_abelian_group
 }.

lemma le_rewl: ∀E:excedence.∀x,z,y:E. x ≈ y → x ≤ z → y ≤ z.
intros (E x z y); apply (le_transitive ???? ? H1); 
clear H1 z; unfold in H; unfold; intro H1; apply H; clear H; 
lapply ap_cotransitive;  
intros (G x z y); intro Eyz; 


lemma plus_cancr_le: 
  ∀G:ordered_abelian_group.∀x,y,z:G.x+z ≤ y + z → x ≤ y.
intros 5 (G x y z L);

 apply L; clear L; elim (exc_cotransitive ???z Exy);

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
