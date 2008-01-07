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



include "higher_order_defs/relations.ma".
include "nat/plus.ma".
include "constructive_higher_order_relations.ma".
include "constructive_connectives.ma".

record excess : Type ≝ {
  exc_carr:> Type;
  exc_relation: exc_carr → exc_carr → Type;
  exc_coreflexive: coreflexive ? exc_relation;
  exc_cotransitive: cotransitive ? exc_relation 
}.

interpretation "excess" 'nleq a b =
 (cic:/matita/excess/exc_relation.con _ a b). 

definition le ≝ λE:excess.λa,b:E. ¬ (a ≰ b).

interpretation "ordered sets less or equal than" 'leq a b = 
 (cic:/matita/excess/le.con _ a b).

lemma le_reflexive: ∀E.reflexive ? (le E).
intros (E); unfold; cases E; simplify; intros (x); apply (H x);
qed.

lemma le_transitive: ∀E.transitive ? (le E).
intros (E); unfold; cases E; simplify; unfold Not; intros (x y z Rxy Ryz H2); 
cases (c x z y H2) (H4 H5); clear H2; [exact (Rxy H4)|exact (Ryz H5)] 
qed.

record apartness : Type ≝ {
  ap_carr:> Type;
  ap_apart: ap_carr → ap_carr → Type;
  ap_coreflexive: coreflexive ? ap_apart;
  ap_symmetric: symmetric ? ap_apart;
  ap_cotransitive: cotransitive ? ap_apart
}.

notation "a break # b" non associative with precedence 50 for @{ 'apart $a $b}.
interpretation "apartness" 'apart x y = 
  (cic:/matita/excess/ap_apart.con _ x y).

definition strong_ext ≝ λA:apartness.λop:A→A.∀x,y. op x # op y → x # y.

definition apart ≝ λE:excess.λa,b:E. a ≰ b ∨ b ≰ a.

definition apart_of_excess: excess → apartness.
intros (E); apply (mk_apartness E (apart E));  
[1: unfold; cases E; simplify; clear E; intros (x); unfold;
    intros (H1); apply (H x); cases H1; assumption;
|2: unfold; intros(x y H); cases H; clear H; [right|left] assumption;
|3: intros (E); unfold; cases E (T f _ cTf); simplify; intros (x y z Axy);
    cases Axy (H H); lapply (cTf ? ? z H) as H1; cases H1; clear Axy H1;
    [left; left|right; left|right; right|left; right] assumption]
qed.

coercion cic:/matita/excess/apart_of_excess.con.

definition eq ≝ λA:apartness.λa,b:A. ¬ (a # b).

notation "a break ≈ b" non associative with precedence 50 for @{ 'napart $a $b}.    
interpretation "alikeness" 'napart a b =
  (cic:/matita/excess/eq.con _ a b). 

lemma eq_reflexive:∀E. reflexive ? (eq E).
intros (E); unfold; intros (x); apply ap_coreflexive; 
qed.

lemma eq_sym_:∀E.symmetric ? (eq E).
intros (E); unfold; intros (x y Exy); unfold; unfold; intros (Ayx); apply Exy;
apply ap_symmetric; assumption; 
qed.

lemma eq_sym:∀E:apartness.∀x,y:E.x ≈ y → y ≈ x ≝ eq_sym_.

coercion cic:/matita/excess/eq_sym.con.

lemma eq_trans_: ∀E.transitive ? (eq E).
(* bug. intros k deve fare whd quanto basta *)
intros 6 (E x y z Exy Eyz); intro Axy; cases (ap_cotransitive ???y Axy); 
[apply Exy|apply Eyz] assumption.
qed.

lemma eq_trans:∀E:apartness.∀x,z,y:E.x ≈ y → y ≈ z → x ≈ z ≝ 
  λE,x,y,z.eq_trans_ E x z y.

notation > "'Eq'≈" non associative with precedence 50 for
 @{'eqrewrite}.
 
interpretation "eq_rew" 'eqrewrite = 
 (cic:/matita/excess/eq_trans.con _ _ _).

(* BUG: vedere se ricapita *)
alias id "antisymmetric" = "cic:/matita/constructive_higher_order_relations/antisymmetric.con".
lemma le_antisymmetric: ∀E.antisymmetric ? (le E) (eq ?).
intros 5 (E x y Lxy Lyx); intro H;
cases H; [apply Lxy;|apply Lyx] assumption;
qed.

definition lt ≝ λE:excess.λa,b:E. a ≤ b ∧ a # b.

interpretation "ordered sets less than" 'lt a b =
 (cic:/matita/excess/lt.con _ a b).

lemma lt_coreflexive: ∀E.coreflexive ? (lt E).
intros 2 (E x); intro H; cases H (_ ABS); 
apply (ap_coreflexive ? x ABS);
qed.
 
lemma lt_transitive: ∀E.transitive ? (lt E).
intros (E); unfold; intros (x y z H1 H2); cases H1 (Lxy Axy); cases H2 (Lyz Ayz); 
split; [apply (le_transitive ???? Lxy Lyz)] clear H1 H2;
cases Axy (H1 H1); cases Ayz (H2 H2); [1:cases (Lxy H1)|3:cases (Lyz H2)]
clear Axy Ayz;lapply (exc_cotransitive E) as c; unfold cotransitive in c;
lapply (exc_coreflexive E) as r; unfold coreflexive in r;
[1: lapply (c ?? y H1) as H3; cases H3 (H4 H4); [cases (Lxy H4)|cases (r ? H4)]
|2: lapply (c ?? x H2) as H3; cases H3 (H4 H4); [right; assumption|cases (Lxy H4)]]
qed.

theorem lt_to_excess: ∀E:excess.∀a,b:E. (a < b) → (b ≰ a).
intros (E a b Lab); cases Lab (LEab Aab);
cases Aab (H H); [cases (LEab H)] fold normalize (b ≰ a); assumption; (* BUG *)  
qed.

lemma unfold_apart: ∀E:excess. ∀x,y:E. x ≰ y ∨ y ≰ x → x # y.
intros; assumption;
qed.

lemma le_rewl: ∀E:excess.∀z,y,x:E. x ≈ y → x ≤ z → y ≤ z.
intros (E z y x Exy Lxz); apply (le_transitive ???? ? Lxz);
intro Xyz; apply Exy; apply unfold_apart; right; assumption;
qed.

lemma le_rewr: ∀E:excess.∀z,y,x:E. x ≈ y → z ≤ x → z ≤ y.
intros (E z y x Exy Lxz); apply (le_transitive ???? Lxz);
intro Xyz; apply Exy; apply unfold_apart; left; assumption;
qed.

notation > "'Le'≪" non associative with precedence 50 for
 @{'lerewritel}.
 
interpretation "le_rewl" 'lerewritel = 
 (cic:/matita/excess/le_rewl.con _ _ _).

notation > "'Le'≫" non associative with precedence 50 for
 @{'lerewriter}.
 
interpretation "le_rewr" 'lerewriter = 
 (cic:/matita/excess/le_rewr.con _ _ _).

lemma ap_rewl: ∀A:apartness.∀x,z,y:A. x ≈ y → y # z → x # z.
intros (A x z y Exy Ayz); cases (ap_cotransitive ???x Ayz); [2:assumption]
cases (Exy (ap_symmetric ??? a));
qed.
  
lemma ap_rewr: ∀A:apartness.∀x,z,y:A. x ≈ y → z # y → z # x.
intros (A x z y Exy Azy); apply ap_symmetric; apply (ap_rewl ???? Exy);
apply ap_symmetric; assumption;
qed.

lemma exc_rewl: ∀A:excess.∀x,z,y:A. x ≈ y → y ≰ z → x ≰ z.
intros (A x z y Exy Ayz); elim (exc_cotransitive ???x Ayz); [2:assumption]
cases Exy; right; assumption;
qed.
  
lemma exc_rewr: ∀A:excess.∀x,z,y:A. x ≈ y → z ≰ y → z ≰ x.
intros (A x z y Exy Azy); elim (exc_cotransitive ???x Azy); [assumption]
elim (Exy); left; assumption;
qed.

notation > "'Ex'≪" non associative with precedence 50 for
 @{'excessrewritel}.
 
interpretation "exc_rewl" 'excessrewritel = 
 (cic:/matita/excess/exc_rewl.con _ _ _).

notation > "'Ex'≫" non associative with precedence 50 for
 @{'excessrewriter}.
 
interpretation "exc_rewr" 'excessrewriter = 
 (cic:/matita/excess/exc_rewr.con _ _ _).

lemma lt_rewr: ∀A:excess.∀x,z,y:A. x ≈ y → z < y → z < x.
intros (A x y z E H); split; elim H; 
[apply (le_rewr ???? (eq_sym ??? E));|apply (ap_rewr ???? E)] assumption;
qed.

lemma lt_rewl: ∀A:excess.∀x,z,y:A. x ≈ y → y < z → x < z.
intros (A x y z E H); split; elim H; 
[apply (le_rewl ???? (eq_sym ??? E));| apply (ap_rewl ???? E);] assumption;
qed.

notation > "'Lt'≪" non associative with precedence 50 for
 @{'ltrewritel}.
 
interpretation "lt_rewl" 'ltrewritel = 
 (cic:/matita/excess/lt_rewl.con _ _ _).

notation > "'Lt'≫" non associative with precedence 50 for
 @{'ltrewriter}.
 
interpretation "lt_rewr" 'ltrewriter = 
 (cic:/matita/excess/lt_rewr.con _ _ _).

lemma lt_le_transitive: ∀A:excess.∀x,y,z:A.x < y → y ≤ z → x < z.
intros (A x y z LT LE); cases LT (LEx APx); split; [apply (le_transitive ???? LEx LE)]
whd in LE LEx APx; cases APx (EXx EXx); [cases (LEx EXx)]
cases (exc_cotransitive ??? z EXx) (EXz EXz); [cases (LE EXz)]
right; assumption;
qed.

lemma le_lt_transitive: ∀A:excess.∀x,y,z:A.x ≤ y → y < z → x < z.
intros (A x y z LE LT); cases LT (LEx APx); split; [apply (le_transitive ???? LE LEx)]
whd in LE LEx APx; cases APx (EXx EXx); [cases (LEx EXx)]
cases (exc_cotransitive ??? x EXx) (EXz EXz); [right; assumption]
cases LE; assumption;
qed.
    
lemma le_le_eq: ∀E:excess.∀a,b:E. a ≤ b → b ≤ a → a ≈ b.
intros (E x y L1 L2); intro H; cases H; [apply L1|apply L2] assumption;
qed.

lemma eq_le_le: ∀E:excess.∀a,b:E. a ≈ b → a ≤ b ∧ b ≤ a.
intros (E x y H); unfold apart_of_excess in H; unfold apart in H;
simplify in H; split; intro; apply H; [left|right] assumption.
qed.

lemma ap_le_to_lt: ∀E:excess.∀a,c:E.c # a → c ≤ a → c < a.
intros; split; assumption;
qed.

definition total_order_property : ∀E:excess. Type ≝
  λE:excess. ∀a,b:E. a ≰ b → b < a.

