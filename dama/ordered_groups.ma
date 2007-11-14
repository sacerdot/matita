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

lemma le_le_eq: ∀E:excedence.∀x,y:E. x ≤ y → y ≤ x → x ≈ y.
intros 6 (E x y L1 L2 H); cases H; [apply (L1 H1)|apply (L2 H1)]
qed.

lemma unfold_apart: ∀E:excedence. ∀x,y:E. x ≰ y ∨ y ≰ x → x # y.
unfold apart_of_excedence; unfold apart; simplify; intros; assumption;
qed.

lemma le_rewl: ∀E:excedence.∀z,y,x:E. x ≈ y → x ≤ z → y ≤ z.
intros (E z y x Exy Lxz); apply (le_transitive ???? ? Lxz);
intro Xyz; apply Exy; apply unfold_apart; right; assumption;
qed.

lemma le_rewr: ∀E:excedence.∀z,y,x:E. x ≈ y → z ≤ x → z ≤ y.
intros (E z y x Exy Lxz); apply (le_transitive ???? Lxz);
intro Xyz; apply Exy; apply unfold_apart; left; assumption;
qed.

lemma plus_cancr_le: 
  ∀G:ordered_abelian_group.∀x,y,z:G.x+z ≤ y + z → x ≤ y.
intros 5 (G x y z L);
apply (le_rewl ??? (0+x) (zero_neutral ??));
apply (le_rewl ??? (x+0) (plus_comm ???));
apply (le_rewl ??? (x+(-z+z))); [apply feq_plusl;apply opp_inverse;]
apply (le_rewl ??? (x+(z+ -z))); [apply feq_plusl;apply plus_comm;]
apply (le_rewl ??? (x+z+ -z)); [apply eq_symmetric; apply plus_assoc;]
apply (le_rewr ??? (0+y) (zero_neutral ??));
apply (le_rewr ??? (y+0) (plus_comm ???));
apply (le_rewr ??? (y+(-z+z))); [apply feq_plusl;apply opp_inverse;]
apply (le_rewr ??? (y+(z+ -z))); [apply feq_plusl;apply plus_comm;]
apply (le_rewr ??? (y+z+ -z)); [apply eq_symmetric; apply plus_assoc;]
apply (og_ordered_abelian_group_properties ??? (-z));
assumption;
qed.

lemma le_zero_x_to_le_opp_x_zero: 
  ∀G:ordered_abelian_group.∀x:G.0 ≤ x → -x ≤ 0.
intros (G x Px); apply (plus_cancr_le ??? x);
apply (le_rewl ??? 0 (eq_symmetric ??? (opp_inverse ??)));
apply (le_rewr ??? x (eq_symmetric ??? (zero_neutral ??)));
assumption;
qed.

lemma le_x_zero_to_le_zero_opp_x: 
  ∀G:ordered_abelian_group.∀x:G. x ≤ 0 → 0 ≤ -x.
intros (G x Lx0); apply (plus_cancr_le ??? x);
apply (le_rewr ??? 0 (eq_symmetric ??? (opp_inverse ??)));
apply (le_rewl ??? x (eq_symmetric ??? (zero_neutral ??)));
assumption; 
qed.
