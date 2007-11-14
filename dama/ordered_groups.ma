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

record pre_ogroup : Type ≝ { 
  og_abelian_group_: abelian_group;
  og_tordered_set:> tordered_set;
  og_with: carr og_abelian_group_ = og_tordered_set
}.

lemma og_abelian_group: pre_ogroup → abelian_group.
intro G; apply (mk_abelian_group G); [1,2,3: rewrite < (og_with G)]
[apply (plus (og_abelian_group_ G));|apply zero;|apply opp]
unfold apartness_OF_pre_ogroup; cases (og_with G); simplify;
[apply plus_assoc|apply plus_comm|apply zero_neutral|apply opp_inverse|apply plus_strong_ext]
qed.

coercion cic:/matita/ordered_groups/og_abelian_group.con.


record ogroup : Type ≝ { 
  og_carr:> pre_ogroup;
  fle_plusr: ∀f,g,h:og_carr. f≤g → f+h≤g+h
}.

lemma plus_cancr_le: 
  ∀G:ogroup.∀x,y,z:G.x+z ≤ y + z → x ≤ y.
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
apply (fle_plusr ??? (-z));
assumption;
qed.

lemma fle_plusl: ∀G:ogroup. ∀f,g,h:G. f≤g → h+f≤h+g.
intros (G f g h);
apply (plus_cancr_le ??? (-h));
apply (le_rewl ??? (f+h+ -h)); [apply feq_plusr;apply plus_comm;]
apply (le_rewl ??? (f+(h+ -h)) (plus_assoc ????));
apply (le_rewl ??? (f+(-h+h))); [apply feq_plusl;apply plus_comm;]
apply (le_rewl ??? (f+0)); [apply feq_plusl; apply eq_symmetric; apply opp_inverse]
apply (le_rewl ??? (0+f) (plus_comm ???));
apply (le_rewl ??? (f) (eq_symmetric ??? (zero_neutral ??)));
apply (le_rewr ??? (g+h+ -h)); [apply feq_plusr;apply plus_comm;]
apply (le_rewr ??? (g+(h+ -h)) (plus_assoc ????));
apply (le_rewr ??? (g+(-h+h))); [apply feq_plusl;apply plus_comm;]
apply (le_rewr ??? (g+0)); [apply feq_plusl; apply eq_symmetric; apply opp_inverse]
apply (le_rewr ??? (0+g) (plus_comm ???));
apply (le_rewr ??? (g) (eq_symmetric ??? (zero_neutral ??)));
assumption;
qed.

lemma plus_cancl_le: 
  ∀G:ogroup.∀x,y,z:G.z+x ≤ z+y → x ≤ y.
intros 5 (G x y z L);
apply (le_rewl ??? (0+x) (zero_neutral ??));
apply (le_rewl ??? ((-z+z)+x)); [apply feq_plusr;apply opp_inverse;]
apply (le_rewl ??? (-z+(z+x)) (plus_assoc ????));
apply (le_rewr ??? (0+y) (zero_neutral ??));
apply (le_rewr ??? ((-z+z)+y)); [apply feq_plusr;apply opp_inverse;]
apply (le_rewr ??? (-z+(z+y)) (plus_assoc ????));
apply (fle_plusl ??? (-z));
assumption;
qed.


lemma le_zero_x_to_le_opp_x_zero: 
  ∀G:ogroup.∀x:G.0 ≤ x → -x ≤ 0.
intros (G x Px); apply (plus_cancr_le ??? x);
apply (le_rewl ??? 0 (eq_symmetric ??? (opp_inverse ??)));
apply (le_rewr ??? x (eq_symmetric ??? (zero_neutral ??)));
assumption;
qed.

lemma le_x_zero_to_le_zero_opp_x: 
  ∀G:ogroup.∀x:G. x ≤ 0 → 0 ≤ -x.
intros (G x Lx0); apply (plus_cancr_le ??? x);
apply (le_rewr ??? 0 (eq_symmetric ??? (opp_inverse ??)));
apply (le_rewl ??? x (eq_symmetric ??? (zero_neutral ??)));
assumption; 
qed.
