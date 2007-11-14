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

set "baseuri" "cic:/matita/excedence/".

include "higher_order_defs/relations.ma".
include "nat/plus.ma".
include "constructive_connectives.ma".
include "constructive_higher_order_relations.ma".

record excedence : Type ≝ {
  exc_carr:> Type;
  exc_relation: exc_carr → exc_carr → Prop;
  exc_coreflexive: coreflexive ? exc_relation;
  exc_cotransitive: cotransitive ? exc_relation 
}.

interpretation "excedence" 'nleq a b =
 (cic:/matita/excedence/exc_relation.con _ a b). 

definition le ≝ λE:excedence.λa,b:E. ¬ (a ≰ b).

interpretation "ordered sets less or equal than" 'leq a b = 
 (cic:/matita/excedence/le.con _ a b).

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

notation "a # b" non associative with precedence 50 for @{ 'apart $a $b}.
interpretation "axiomatic apartness" 'apart x y = 
  (cic:/matita/excedence/ap_apart.con _ x y).

definition apart ≝ λE:excedence.λa,b:E. a ≰ b ∨ b ≰ a.

definition apart_of_excedence: excedence → apartness.
intros (E); apply (mk_apartness E (apart E));  
[1: unfold; cases E; simplify; clear E; intros (x); unfold;
    intros (H1); apply (H x); cases H1; assumption;
|2: unfold; intros(x y H); cases H; clear H; [right|left] assumption;
|3: intros (E); unfold; cases E (T f _ cTf); simplify; intros (x y z Axy);
    cases Axy (H); lapply (cTf ? ? z H) as H1; cases H1; clear Axy H1;
    [left; left|right; left|right; right|left; right] assumption]
qed.

coercion cic:/matita/excedence/apart_of_excedence.con.

definition eq ≝ λA:apartness.λa,b:A. ¬ (a # b).

notation "a ≈ b" non associative with precedence 50 for @{ 'napart $a $b}.    
interpretation "alikeness" 'napart a b =
  (cic:/matita/excedence/eq.con _ a b). 

lemma eq_reflexive:∀E. reflexive ? (eq E).
intros (E); unfold; intros (x); apply ap_coreflexive; 
qed.

lemma eq_symmetric:∀E.symmetric ? (eq E).
intros (E); unfold; intros (x y Exy); unfold; unfold; intros (Ayx); apply Exy;
apply ap_symmetric; assumption; 
qed.

lemma eq_transitive: ∀E.transitive ? (eq E).
(* bug. intros k deve fare whd quanto basta *)
intros 6 (E x y z Exy Eyz); intro Axy; cases (ap_cotransitive ???y Axy); 
[apply Exy|apply Eyz] assumption.
qed.
(* BUG: vedere se ricapita *)
lemma le_antisymmetric: ∀E.antisymmetric ? (le E) (eq ?).
intros 5 (E x y Lxy Lyx); intro H;
cases H; [apply Lxy;|apply Lyx] assumption;
qed.

definition lt ≝ λE:excedence.λa,b:E. a ≤ b ∧ a # b.

interpretation "ordered sets less than" 'lt a b =
 (cic:/matita/excedence/lt.con _ a b).

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

theorem lt_to_excede: ∀E:excedence.∀a,b:E. (a < b) → (b ≰ a).
intros (E a b Lab); cases Lab (LEab Aab);
cases Aab (H H); [cases (LEab H)] fold normalize (b ≰ a); assumption; (* BUG *)  
qed.

theorem le_le_to_eq: ∀E:excedence.∀x,y:E. x ≤ y → y ≤ x → x ≈ y.
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
