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

record excess_base : Type ≝ {
  exc_carr:> Type;
  exc_excess: exc_carr → exc_carr → Type;
  exc_coreflexive: coreflexive ? exc_excess;
  exc_cotransitive: cotransitive ? exc_excess 
}.

interpretation "Excess base excess" 'nleq a b = (exc_excess ? a b). 

(* E(#,≰) → E(#,sym(≰)) *)
lemma make_dual_exc: excess_base → excess_base.
intro E;
apply (mk_excess_base (exc_carr E));
  [ apply (λx,y:E.y≰x);|apply exc_coreflexive;
  | unfold cotransitive; simplify; intros (x y z H);
    cases (exc_cotransitive E ??z H);[right|left]assumption]
qed.

record excess_dual : Type ≝ {
  exc_dual_base:> excess_base;
  exc_dual_dual_ : excess_base;
  exc_with: exc_dual_dual_ = make_dual_exc exc_dual_base
}.

lemma mk_excess_dual_smart: excess_base → excess_dual.
intro; apply mk_excess_dual; [apply e| apply (make_dual_exc e)|reflexivity]
qed.

definition exc_dual_dual: excess_dual → excess_base.
intro E; apply (make_dual_exc E);
qed. 

coercion cic:/matita/excess/exc_dual_dual.con.

record apartness : Type ≝ {
  ap_carr:> Type;
  ap_apart: ap_carr → ap_carr → Type;
  ap_coreflexive: coreflexive ? ap_apart;
  ap_symmetric: symmetric ? ap_apart;
  ap_cotransitive: cotransitive ? ap_apart
}.

notation "hvbox(a break # b)" non associative with precedence 55 for @{ 'apart $a $b}.
interpretation "apartness" 'apart x y = (ap_apart ? x y).

definition apartness_of_excess_base: excess_base → apartness.
intros (E); apply (mk_apartness E (λa,b:E. a ≰ b ∨ b ≰ a));  
[1: unfold; cases E; simplify; clear E; intros (x); unfold;
    intros (H1); apply (H x); cases H1; assumption;
|2: unfold; intros(x y H); cases H; clear H; [right|left] assumption;
|3: intros (E); unfold; cases E (T f _ cTf); simplify; intros (x y z Axy);
    cases Axy (H H); lapply (cTf ? ? z H) as H1; cases H1; clear Axy H1;
    [left; left|right; left|right; right|left; right] assumption]
qed.

record excess_ : Type ≝ {
  exc_exc:> excess_dual;
  exc_ap_: apartness;
  exc_with1: ap_carr exc_ap_ = exc_carr exc_exc
}.

definition exc_ap: excess_ → apartness.
intro E; apply (mk_apartness E); unfold Type_OF_excess_; 
cases (exc_with1 E); simplify;
[apply (ap_apart (exc_ap_ E));
|apply ap_coreflexive;|apply ap_symmetric;|apply ap_cotransitive] 
qed.

coercion cic:/matita/excess/exc_ap.con.

interpretation "Excess excess_" 'nleq a b =
 (exc_excess (excess_base_OF_excess_1 _) a b).

record excess : Type ≝ {
  excess_carr:> excess_;
  ap2exc: ∀y,x:excess_carr. y # x → y ≰ x ∨ x ≰ y;
  exc2ap: ∀y,x:excess_carr.y ≰ x ∨ x ≰ y →  y # x 
}.

interpretation "Excess excess" 'nleq a b =
 (exc_excess (excess_base_OF_excess1 _) a b).
 
interpretation "Excess (dual) excess" 'ngeq a b =
 (exc_excess (excess_base_OF_excess _) a b).

definition strong_ext ≝ λA:apartness.λop:A→A.∀x,y. op x # op y → x # y.

definition le ≝ λE:excess_base.λa,b:E. ¬ (a ≰ b).

interpretation "Excess less or equal than" 'leq a b = 
 (le (excess_base_OF_excess1 _) a b).

interpretation "Excess less or equal than" 'geq a b = 
 (le (excess_base_OF_excess _) a b).

lemma le_reflexive: ∀E.reflexive ? (le E).
unfold reflexive; intros 3 (E x H); apply (exc_coreflexive ?? H);
qed.

lemma le_transitive: ∀E.transitive ? (le E).
unfold transitive; intros 7 (E x y z H1 H2 H3); cases (exc_cotransitive ??? y H3) (H4 H4);
[cases (H1 H4)|cases (H2 H4)]
qed.

definition eq ≝ λA:apartness.λa,b:A. ¬ (a # b).

notation "hvbox(a break ≈ b)" non associative with precedence 55 for @{ 'napart $a $b}.    
interpretation "Apartness alikeness" 'napart a b = (eq ? a b). 
interpretation "Excess alikeness" 'napart a b = (eq (excess_base_OF_excess1 ?) a b). 
interpretation "Excess (dual) alikeness" 'napart a b = (eq (excess_base_OF_excess ?) a b). 

lemma eq_reflexive:∀E:apartness. reflexive ? (eq E).
intros (E); unfold; intros (x); apply ap_coreflexive; 
qed.

lemma eq_sym_:∀E:apartness.symmetric ? (eq E).
unfold symmetric; intros 5 (E x y H H1); cases (H (ap_symmetric ??? H1)); 
qed.

lemma eq_sym:∀E:apartness.∀x,y:E.x ≈ y → y ≈ x ≝ eq_sym_.

(* SETOID REWRITE *)
coercion cic:/matita/excess/eq_sym.con.

lemma eq_trans_: ∀E:apartness.transitive ? (eq E).
(* bug. intros k deve fare whd quanto basta *)
intros 6 (E x y z Exy Eyz); intro Axy; cases (ap_cotransitive ???y Axy); 
[apply Exy|apply Eyz] assumption.
qed.

lemma eq_trans:∀E:apartness.∀x,z,y:E.x ≈ y → y ≈ z → x ≈ z ≝ 
  λE,x,y,z.eq_trans_ E x z y.

notation > "'Eq'≈" non associative with precedence 55 for @{'eqrewrite}.
interpretation "eq_rew" 'eqrewrite = (eq_trans ? ? ?).

alias id "antisymmetric" = "cic:/matita/constructive_higher_order_relations/antisymmetric.con".
lemma le_antisymmetric: 
  ∀E:excess.antisymmetric ? (le (excess_base_OF_excess1 E)) (eq E).
intros 5 (E x y Lxy Lyx); intro H; 
cases (ap2exc ??? H); [apply Lxy;|apply Lyx] assumption;
qed.

definition lt ≝ λE:excess.λa,b:E. a ≤ b ∧ a # b.

interpretation "ordered sets less than" 'lt a b = (lt ? a b).

lemma lt_coreflexive: ∀E.coreflexive ? (lt E).
intros 2 (E x); intro H; cases H (_ ABS); 
apply (ap_coreflexive ? x ABS);
qed.
 
lemma lt_transitive: ∀E.transitive ? (lt E).
intros (E); unfold; intros (x y z H1 H2); cases H1 (Lxy Axy); cases H2 (Lyz Ayz); 
split; [apply (le_transitive ???? Lxy Lyz)] clear H1 H2;
elim (ap2exc ??? Axy) (H1 H1); elim (ap2exc ??? Ayz) (H2 H2); [1:cases (Lxy H1)|3:cases (Lyz H2)]
clear Axy Ayz;lapply (exc_cotransitive (exc_dual_base E)) as c; unfold cotransitive in c;
lapply (exc_coreflexive (exc_dual_base E)) as r; unfold coreflexive in r;
[1: lapply (c ?? y H1) as H3; elim H3 (H4 H4); [cases (Lxy H4)|cases (r ? H4)]
|2: lapply (c ?? x H2) as H3; elim H3 (H4 H4); [apply exc2ap; right; assumption|cases (Lxy H4)]]
qed.

theorem lt_to_excess: ∀E:excess.∀a,b:E. (a < b) → (b ≰ a).
intros (E a b Lab); elim Lab (LEab Aab);
elim (ap2exc ??? Aab) (H H); [cases (LEab H)] fold normalize (b ≰ a); assumption; (* BUG *)  
qed.

lemma le_rewl: ∀E:excess.∀z,y,x:E. x ≈ y → x ≤ z → y ≤ z.
intros (E z y x Exy Lxz); apply (le_transitive ???? ? Lxz);
intro Xyz; apply Exy; apply exc2ap; right; assumption;
qed.

lemma le_rewr: ∀E:excess.∀z,y,x:E. x ≈ y → z ≤ x → z ≤ y.
intros (E z y x Exy Lxz); apply (le_transitive ???? Lxz);
intro Xyz; apply Exy; apply exc2ap; left; assumption;
qed.

notation > "'Le'≪" non associative with precedence 55 for @{'lerewritel}.
interpretation "le_rewl" 'lerewritel = (le_rewl ? ? ?).
notation > "'Le'≫" non associative with precedence 55 for @{'lerewriter}.
interpretation "le_rewr" 'lerewriter = (le_rewr ? ? ?).

lemma ap_rewl: ∀A:apartness.∀x,z,y:A. x ≈ y → y # z → x # z.
intros (A x z y Exy Ayz); cases (ap_cotransitive ???x Ayz); [2:assumption]
cases (Exy (ap_symmetric ??? a));
qed.
  
lemma ap_rewr: ∀A:apartness.∀x,z,y:A. x ≈ y → z # y → z # x.
intros (A x z y Exy Azy); apply ap_symmetric; apply (ap_rewl ???? Exy);
apply ap_symmetric; assumption;
qed.

notation > "'Ap'≪" non associative with precedence 55 for @{'aprewritel}.
interpretation "ap_rewl" 'aprewritel = (ap_rewl ? ? ?).
notation > "'Ap'≫" non associative with precedence 55 for @{'aprewriter}.
interpretation "ap_rewr" 'aprewriter = (ap_rewr ? ? ?).

alias symbol "napart" = "Apartness alikeness".
lemma exc_rewl: ∀A:excess.∀x,z,y:A. x ≈ y → y ≰ z → x ≰ z.
intros (A x z y Exy Ayz); elim (exc_cotransitive ???x Ayz); [2:assumption]
cases Exy; apply exc2ap; right; assumption;
qed.
  
lemma exc_rewr: ∀A:excess.∀x,z,y:A. x ≈ y → z ≰ y → z ≰ x.
intros (A x z y Exy Azy); elim (exc_cotransitive ???x Azy); [assumption]
elim (Exy); apply exc2ap; left; assumption;
qed.

notation > "'Ex'≪" non associative with precedence 55 for @{'excessrewritel}.
interpretation "exc_rewl" 'excessrewritel = (exc_rewl ? ? ?).
notation > "'Ex'≫" non associative with precedence 55 for @{'excessrewriter}.
interpretation "exc_rewr" 'excessrewriter = (exc_rewr ? ? ?).

lemma lt_rewr: ∀A:excess.∀x,z,y:A. x ≈ y → z < y → z < x.
intros (A x y z E H); split; elim H; 
[apply (Le≫ ? (eq_sym ??? E));|apply (Ap≫ ? E)] assumption;
qed.

lemma lt_rewl: ∀A:excess.∀x,z,y:A. x ≈ y → y < z → x < z.
intros (A x y z E H); split; elim H; 
[apply (Le≪ ? (eq_sym ??? E));| apply (Ap≪ ? E);] assumption;
qed.

notation > "'Lt'≪" non associative with precedence 55 for @{'ltrewritel}.
interpretation "lt_rewl" 'ltrewritel = (lt_rewl ? ? ?).
notation > "'Lt'≫" non associative with precedence 55 for @{'ltrewriter}.
interpretation "lt_rewr" 'ltrewriter = (lt_rewr ? ? ?).

lemma lt_le_transitive: ∀A:excess.∀x,y,z:A.x < y → y ≤ z → x < z.
intros (A x y z LT LE); cases LT (LEx APx); split; [apply (le_transitive ???? LEx LE)]
apply exc2ap; cases (ap2exc ??? APx) (EXx EXx); [cases (LEx EXx)]
cases (exc_cotransitive ??? z EXx) (EXz EXz); [cases (LE EXz)]
right; assumption;
qed.

lemma le_lt_transitive: ∀A:excess.∀x,y,z:A.x ≤ y → y < z → x < z.
intros (A x y z LE LT); cases LT (LEx APx); split; [apply (le_transitive ???? LE LEx)]
elim (ap2exc ??? APx) (EXx EXx); [cases (LEx EXx)]
elim (exc_cotransitive ??? x EXx) (EXz EXz); [apply exc2ap; right; assumption]
cases LE; assumption;
qed.
    
lemma le_le_eq: ∀E:excess.∀a,b:E. a ≤ b → b ≤ a → a ≈ b.
intros (E x y L1 L2); intro H; cases (ap2exc ??? H); [apply L1|apply L2] assumption;
qed.

lemma eq_le_le: ∀E:excess.∀a,b:E. a ≈ b → a ≤ b ∧ b ≤ a.
intros (E x y H); whd in H;
split; intro; apply H; apply exc2ap; [left|right] assumption.
qed.

lemma ap_le_to_lt: ∀E:excess.∀a,c:E.c # a → c ≤ a → c < a.
intros; split; assumption;
qed.

definition total_order_property : ∀E:excess. Type ≝ 
  λE:excess. ∀a,b:E. a ≰ b → b < a.

