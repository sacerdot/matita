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



include "group.ma".

record pogroup_ : Type ≝ { 
  og_abelian_group_: abelian_group;
  og_excess:> excess;
  og_with: carr og_abelian_group_ = apart_of_excess og_excess
}.

lemma og_abelian_group: pogroup_ → abelian_group.
intro G; apply (mk_abelian_group G); [1,2,3: rewrite < (og_with G)]
[apply (plus (og_abelian_group_ G));|apply zero;|apply opp]
unfold apartness_OF_pogroup_; cases (og_with G); simplify;
[apply plus_assoc|apply plus_comm|apply zero_neutral|apply opp_inverse|apply plus_strong_ext]
qed.

coercion cic:/matita/ordered_group/og_abelian_group.con.

record pogroup : Type ≝ { 
  og_carr:> pogroup_;
  plus_cancr_exc: ∀f,g,h:og_carr. f+h ≰ g+h → f ≰ g
}.

lemma fexc_plusr: 
  ∀G:pogroup.∀x,y,z:G. x ≰ y → x+z ≰ y + z.
intros 5 (G x y z L); apply (plus_cancr_exc ??? (-z));
apply (Ex≪  (x + (z + -z)) (plus_assoc ????));
apply (Ex≪  (x + (-z + z)) (plus_comm ??z));
apply (Ex≪  (x+0) (opp_inverse ??));
apply (Ex≪  (0+x) (plus_comm ???));
apply (Ex≪  x (zero_neutral ??));
apply (Ex≫ (y + (z + -z)) (plus_assoc ????));
apply (Ex≫  (y + (-z + z)) (plus_comm ??z));
apply (Ex≫  (y+0) (opp_inverse ??));
apply (Ex≫  (0+y) (plus_comm ???));
apply (Ex≫  y (zero_neutral ??) L);
qed.

coercion cic:/matita/ordered_group/fexc_plusr.con nocomposites.

lemma plus_cancl_exc: ∀G:pogroup.∀f,g,h:G. h+f ≰ h+g → f ≰ g.
intros 5 (G x y z L); apply (plus_cancr_exc ??? z);
apply (exc_rewl ??? (z+x) (plus_comm ???));
apply (exc_rewr ??? (z+y) (plus_comm ???) L);
qed.

lemma fexc_plusl: 
  ∀G:pogroup.∀x,y,z:G. x ≰ y → z+x ≰ z+y.
intros 5 (G x y z L); apply (plus_cancl_exc ??? (-z));
apply (exc_rewl ???? (plus_assoc ??z x));
apply (exc_rewr ???? (plus_assoc ??z y));
apply (exc_rewl ??? (0+x) (opp_inverse ??));
apply (exc_rewr ??? (0+y) (opp_inverse ??));
apply (exc_rewl ???? (zero_neutral ??));
apply (exc_rewr ???? (zero_neutral ??) L);
qed.

coercion cic:/matita/ordered_group/fexc_plusl.con nocomposites.

lemma plus_cancr_le: 
  ∀G:pogroup.∀x,y,z:G.x+z ≤ y + z → x ≤ y.
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
intro H; apply L; clear L; apply (plus_cancr_exc ??? (-z) H);
qed.

lemma fle_plusl: ∀G:pogroup. ∀f,g,h:G. f≤g → h+f≤h+g.
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

lemma fle_plusr: ∀G:pogroup. ∀f,g,h:G. f≤g → f+h≤g+h.
intros (G f g h H); apply (le_rewl ???? (plus_comm ???)); 
apply (le_rewr ???? (plus_comm ???)); apply fle_plusl; assumption;
qed.

lemma plus_cancl_le: 
  ∀G:pogroup.∀x,y,z:G.z+x ≤ z+y → x ≤ y.
intros 5 (G x y z L);
apply (le_rewl ??? (0+x) (zero_neutral ??));
apply (le_rewl ??? ((-z+z)+x) (opp_inverse ??));
apply (le_rewl ??? (-z+(z+x)) (plus_assoc ????));
apply (le_rewr ??? (0+y) (zero_neutral ??));
apply (le_rewr ??? ((-z+z)+y) (opp_inverse ??));
apply (le_rewr ??? (-z+(z+y)) (plus_assoc ????));
apply (fle_plusl ??? (-z) L);
qed.

lemma plus_cancl_lt: 
  ∀G:pogroup.∀x,y,z:G.z+x < z+y → x < y.
intros 5 (G x y z L); elim L (A LE); split; [apply plus_cancl_le; assumption]
apply (plus_cancl_ap ???? LE);
qed.

lemma plus_cancr_lt: 
  ∀G:pogroup.∀x,y,z:G.x+z < y+z → x < y.
intros 5 (G x y z L); elim L (A LE); split; [apply plus_cancr_le; assumption]
apply (plus_cancr_ap ???? LE);
qed.


lemma exc_opp_x_zero_to_exc_zero_x: 
  ∀G:pogroup.∀x:G.-x ≰ 0 → 0 ≰ x.
intros (G x H); apply (plus_cancr_exc ??? (-x));
apply (exc_rewr ???? (plus_comm ???));
apply (exc_rewr ???? (opp_inverse ??));
apply (exc_rewl ???? (zero_neutral ??) H);
qed.
  
lemma le_zero_x_to_le_opp_x_zero: 
  ∀G:pogroup.∀x:G.0 ≤ x → -x ≤ 0.
intros (G x Px); apply (plus_cancr_le ??? x);
apply (le_rewl ??? 0 (opp_inverse ??));
apply (le_rewr ??? x (zero_neutral ??) Px);
qed.

lemma lt_zero_x_to_lt_opp_x_zero: 
  ∀G:pogroup.∀x:G.0 < x → -x < 0.
intros (G x Px); apply (plus_cancr_lt ??? x);
apply (lt_rewl ??? 0 (opp_inverse ??));
apply (lt_rewr ??? x (zero_neutral ??) Px);
qed.

lemma exc_zero_opp_x_to_exc_x_zero: 
  ∀G:pogroup.∀x:G. 0 ≰ -x → x ≰ 0.
intros (G x H); apply (plus_cancl_exc ??? (-x));
apply (exc_rewr ???? (plus_comm ???));
apply (exc_rewl ???? (opp_inverse ??));
apply (exc_rewr ???? (zero_neutral ??) H);
qed.

lemma le_x_zero_to_le_zero_opp_x: 
  ∀G:pogroup.∀x:G. x ≤ 0 → 0 ≤ -x.
intros (G x Lx0); apply (plus_cancr_le ??? x);
apply (le_rewr ??? 0 (opp_inverse ??));
apply (le_rewl ??? x (zero_neutral ??));
assumption; 
qed.

lemma lt_x_zero_to_lt_zero_opp_x: 
  ∀G:pogroup.∀x:G. x < 0 → 0 < -x.
intros (G x Lx0); apply (plus_cancr_lt ??? x);
apply (lt_rewr ??? 0 (opp_inverse ??));
apply (lt_rewl ??? x (zero_neutral ??));
assumption; 
qed.

lemma lt_opp_x_zero_to_lt_zero_x: 
  ∀G:pogroup.∀x:G. -x < 0 → 0 < x.
intros (G x Lx0); apply (plus_cancr_lt ??? (-x));
apply (lt_rewl ??? (-x) (zero_neutral ??));
apply (lt_rewr ??? (-x+x) (plus_comm ???));
apply (lt_rewr ??? 0 (opp_inverse ??));
assumption; 
qed.

lemma lt0plus_orlt: 
  ∀G:pogroup. ∀x,y:G. 0 ≤ x → 0 ≤ y → 0 < x + y → 0 < x ∨ 0 < y.
intros (G x y LEx LEy LT); cases LT (H1 H2); cases (ap_cotransitive ??? y H2);
[right; split; assumption|left;split;[assumption]]
apply (plus_cancr_ap ??? y); apply (ap_rewl ???? (zero_neutral ??));
assumption;
qed.

lemma le0plus_le: 
  ∀G:pogroup.∀a,b,c:G. 0 ≤ b →  a + b ≤ c → a ≤ c.
intros (G a b c L H); apply (le_transitive ????? H);
apply (plus_cancl_le ??? (-a)); 
apply (le_rewl ??? 0 (opp_inverse ??));
apply (le_rewr ??? (-a + a + b) (plus_assoc ????));
apply (le_rewr ??? (0 + b) (opp_inverse ??));
apply (le_rewr ??? b (zero_neutral ??));
assumption;
qed.

lemma le_le0plus: 
  ∀G:pogroup.∀a,b:G. 0 ≤ a → 0 ≤ b → 0 ≤ a + b.
intros (G a b L1 L2); apply (le_transitive ???? L1);
apply (plus_cancl_le ??? (-a));
apply (le_rewl ??? 0 (opp_inverse ??));
apply (le_rewr ??? (-a + a + b) (plus_assoc ????));
apply (le_rewr ??? (0 + b) (opp_inverse ??));
apply (le_rewr ??? b (zero_neutral ??));
assumption;
qed.

lemma flt_plusl: 
  ∀G:pogroup.∀x,y,z:G.x < y → z + x < z + y.
intros (G x y z H); cases H; split; [apply fle_plusl; assumption]
apply fap_plusl; assumption;
qed.

lemma flt_plusr: 
  ∀G:pogroup.∀x,y,z:G.x < y → x + z < y + z.
intros (G x y z H); cases H; split; [apply fle_plusr; assumption]
apply fap_plusr; assumption;
qed.


lemma ltxy_ltyyxx: ∀G:pogroup.∀x,y:G. y < x → y+y < x+x.
intros; apply (lt_transitive ?? (y+x));[2: 
  apply (lt_rewl ???? (plus_comm ???));
  apply (lt_rewr ???? (plus_comm ???));]
apply flt_plusl;assumption;
qed.  

lemma lew_opp : ∀O:pogroup.∀a,b,c:O.0 ≤ b → a ≤ c → a + -b ≤ c.
intros (O a b c L0 L);
apply (le_transitive ????? L);
apply (plus_cancl_le ??? (-a));
apply (le_rewr ??? 0 (opp_inverse ??));
apply (le_rewl ??? (-a+a+-b) (plus_assoc ????));
apply (le_rewl ??? (0+-b) (opp_inverse ??));
apply (le_rewl ??? (-b) (zero_neutral ?(-b)));
apply le_zero_x_to_le_opp_x_zero;
assumption;
qed.

lemma ltw_opp : ∀O:pogroup.∀a,b,c:O.0 < b → a < c → a + -b < c.
intros (O a b c P L);
apply (lt_transitive ????? L);
apply (plus_cancl_lt ??? (-a));
apply (lt_rewr ??? 0 (opp_inverse ??));
apply (lt_rewl ??? (-a+a+-b) (plus_assoc ????));
apply (lt_rewl ??? (0+-b) (opp_inverse ??));
apply (lt_rewl ??? ? (zero_neutral ??));
apply lt_zero_x_to_lt_opp_x_zero;
assumption;
qed.

record togroup : Type ≝ {
  tog_carr:> pogroup;
  tog_total: ∀x,y:tog_carr.x≰y → y < x
}.

lemma lexxyy_lexy: ∀G:togroup. ∀x,y:G. x+x ≤ y+y → x ≤ y.
intros (G x y H); intro H1; lapply (tog_total ??? H1) as H2;
lapply (ltxy_ltyyxx ??? H2) as H3; lapply (lt_to_excess ??? H3) as H4;
cases (H H4);
qed. 

lemma eqxxyy_eqxy: ∀G:togroup.∀x,y:G. x + x ≈ y + y → x ≈ y.
intros (G x y H); cases (eq_le_le ??? H); apply le_le_eq; 
apply lexxyy_lexy; assumption;
qed.

lemma applus_orap: ∀G:abelian_group. ∀x,y:G. 0 # x + y → 0 #x ∨ 0#y.
intros; cases (ap_cotransitive ??? y a); [right; assumption]
left; apply (plus_cancr_ap ??? y); apply (ap_rewl ???y (zero_neutral ??));
assumption;
qed.

lemma ltplus: ∀G:pogroup.∀a,b,c,d:G. a < b → c < d → a+c < b + d.
intros (G a b c d H1 H2);
lapply (flt_plusr ??? c H1) as H3;
apply (lt_transitive ???? H3);
apply flt_plusl; assumption;
qed.

lemma excplus_orexc: ∀G:pogroup.∀a,b,c,d:G. a+c ≰ b + d →  a ≰ b ∨ c ≰ d.
intros (G a b c d H1 H2);
cases (exc_cotransitive ??? (a + d) H1); [
  right; apply (plus_cancl_exc ??? a); assumption]
left; apply (plus_cancr_exc ??? d); assumption;
qed.

lemma leplus: ∀G:pogroup.∀a,b,c,d:G. a ≤ b → c ≤ d → a+c ≤ b + d.
intros (G a b c d H1 H2); intro H3; cases (excplus_orexc ????? H3);
[apply H1|apply H2] assumption;
qed.  

lemma leplus_lt_le: ∀G:togroup.∀x,y:G. 0 ≤ x + y → x < 0 → 0 ≤ y.
intros; intro; apply H; lapply (lt_to_excess ??? l);
lapply (tog_total ??? e);
lapply (tog_total ??? Hletin);
lapply (ltplus ????? Hletin2 Hletin1);
apply (exc_rewl ??? (0+0)); [apply eq_sym; apply zero_neutral]
apply lt_to_excess; assumption;
qed. 

lemma ltplus_orlt: ∀G:togroup.∀a,b,c,d:G. a+c < b + d →  a < b ∨ c < d.
intros (G a b c d H1 H2); lapply (lt_to_excess ??? H1);
cases (excplus_orexc ????? Hletin); [left|right] apply tog_total; assumption;
qed.

lemma excplus: ∀G:togroup.∀a,b,c,d:G.a ≰ b → c ≰ d → a + c ≰ b + d.
intros (G a b c d L1 L2); 
lapply (fexc_plusr ??? (c) L1) as L3;
elim (exc_cotransitive ??? (b+d) L3); [assumption]
lapply (plus_cancl_exc ???? t); lapply (tog_total ??? Hletin);
cases Hletin1; cases (H L2);
qed.
