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

(* CSC: NO! Cosi' e' nel frammento negativo. Devi scriverlo con l'eccedenza!
   Tutto il resto del file e' da rigirare nel frammento positivo.
*)
record ogroup : Type ≝ { 
  og_carr:> pre_ogroup;
  exc_canc_plusr: ∀f,g,h:og_carr. f+h ≰ g+h → f ≰ g
}.

lemma fexc_plusr: 
  ∀G:ogroup.∀x,y,z:G. x ≰ y → x+z ≰ y + z.
intros 5 (G x y z L); apply (exc_canc_plusr ??? (-z));
apply (exc_rewl ??? (x + (z + -z)) (plus_assoc ????));
apply (exc_rewl ??? (x + (-z + z)) (plus_comm ??z));
apply (exc_rewl ??? (x+0) (opp_inverse ??));
apply (exc_rewl ??? (0+x) (plus_comm ???));
apply (exc_rewl ??? x (zero_neutral ??));
apply (exc_rewr ??? (y + (z + -z)) (plus_assoc ????));
apply (exc_rewr ??? (y + (-z + z)) (plus_comm ??z));
apply (exc_rewr ??? (y+0) (opp_inverse ??));
apply (exc_rewr ??? (0+y) (plus_comm ???));
apply (exc_rewr ??? y (zero_neutral ??) L);
qed.

coercion cic:/matita/ordered_groups/fexc_plusr.con nocomposites.

lemma exc_canc_plusl: ∀G:ogroup.∀f,g,h:G. h+f ≰ h+g → f ≰ g.
intros 5 (G x y z L); apply (exc_canc_plusr ??? z);
apply (exc_rewl ??? (z+x) (plus_comm ???));
apply (exc_rewr ??? (z+y) (plus_comm ???) L);
qed.

lemma fexc_plusl: 
  ∀G:ogroup.∀x,y,z:G. x ≰ y → z+x ≰ z+y.
intros 5 (G x y z L); apply (exc_canc_plusl ??? (-z));
apply (exc_rewl ???? (plus_assoc ??z x));
apply (exc_rewr ???? (plus_assoc ??z y));
apply (exc_rewl ??? (0+x) (opp_inverse ??));
apply (exc_rewr ??? (0+y) (opp_inverse ??));
apply (exc_rewl ???? (zero_neutral ??));
apply (exc_rewr ???? (zero_neutral ??) L);
qed.

coercion cic:/matita/ordered_groups/fexc_plusl.con nocomposites.

lemma plus_cancr_le: 
  ∀G:ogroup.∀x,y,z:G.x+z ≤ y + z → x ≤ y.
intros 5 (G x y z L);
apply (le_rewl ??? (0+x) (zero_neutral ??));
apply (le_rewl ??? (x+0) (plus_comm ???));
apply (le_rewl ??? (x+(-z+z)) (opp_inverse ??));
apply (le_rewl ??? (x+(z+ -z)) (plus_comm ??z));
apply (le_rewl ??? (x+z+ -z) (plus_assoc ????));
apply (le_rewr ??? (0+y) (zero_neutral ??));
apply (le_rewr ??? (y+0) (plus_comm ???));
apply (le_rewr ??? (y+(-z+z)) (opp_inverse ??));
apply (le_rewr ??? (y+(z+ -z)) (plus_comm ??z));
apply (le_rewr ??? (y+z+ -z) (plus_assoc ????));
intro H; apply L; clear L; apply (exc_canc_plusr ??? (-z) H);
qed.

lemma fle_plusl: ∀G:ogroup. ∀f,g,h:G. f≤g → h+f≤h+g.
intros (G f g h);
apply (plus_cancr_le ??? (-h));
apply (le_rewl ??? (f+h+ -h) (plus_comm ? f h));
apply (le_rewl ??? (f+(h+ -h)) (plus_assoc ????));
apply (le_rewl ??? (f+(-h+h)) (plus_comm ? h (-h)));
apply (le_rewl ??? (f+0) (opp_inverse ??));
apply (le_rewl ??? (0+f) (plus_comm ???));
apply (le_rewl ??? (f) (zero_neutral ??));
apply (le_rewr ??? (g+h+ -h) (plus_comm ? h ?));
apply (le_rewr ??? (g+(h+ -h)) (plus_assoc ????));
apply (le_rewr ??? (g+(-h+h)) (plus_comm ??h));
apply (le_rewr ??? (g+0) (opp_inverse ??));
apply (le_rewr ??? (0+g) (plus_comm ???));
apply (le_rewr ??? (g) (zero_neutral ??) H);
qed.

lemma plus_cancl_le: 
  ∀G:ogroup.∀x,y,z:G.z+x ≤ z+y → x ≤ y.
intros 5 (G x y z L);
apply (le_rewl ??? (0+x) (zero_neutral ??));
apply (le_rewl ??? ((-z+z)+x) (opp_inverse ??));
apply (le_rewl ??? (-z+(z+x)) (plus_assoc ????));
apply (le_rewr ??? (0+y) (zero_neutral ??));
apply (le_rewr ??? ((-z+z)+y) (opp_inverse ??));
apply (le_rewr ??? (-z+(z+y)) (plus_assoc ????));
apply (fle_plusl ??? (-z) L);
qed.

lemma exc_opp_x_zero_to_exc_zero_x: 
  ∀G:ogroup.∀x:G.-x ≰ 0 → 0 ≰ x.
intros (G x H); apply (exc_canc_plusr ??? (-x));
apply (exc_rewr ???? (plus_comm ???));
apply (exc_rewr ???? (opp_inverse ??));
apply (exc_rewl ???? (zero_neutral ??) H);
qed.
  
lemma le_zero_x_to_le_opp_x_zero: 
  ∀G:ogroup.∀x:G.0 ≤ x → -x ≤ 0.
intros (G x Px); apply (plus_cancr_le ??? x);
apply (le_rewl ??? 0 (opp_inverse ??));
apply (le_rewr ??? x (zero_neutral ??) Px);
qed.

lemma exc_zero_opp_x_to_exc_x_zero: 
  ∀G:ogroup.∀x:G. 0 ≰ -x → x ≰ 0.
intros (G x H); apply (exc_canc_plusl ??? (-x));
apply (exc_rewr ???? (plus_comm ???));
apply (exc_rewl ???? (opp_inverse ??));
apply (exc_rewr ???? (zero_neutral ??) H);
qed.

lemma le_x_zero_to_le_zero_opp_x: 
  ∀G:ogroup.∀x:G. x ≤ 0 → 0 ≤ -x.
intros (G x Lx0); apply (plus_cancr_le ??? x);
apply (le_rewr ??? 0 (opp_inverse ??));
apply (le_rewl ??? x (zero_neutral ??));
assumption; 
qed.
