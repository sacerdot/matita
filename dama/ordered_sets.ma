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

set "baseuri" "cic:/matita/ordered_sets/".

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
 (cic:/matita/ordered_sets/exc_relation.con _ a b). 

definition le ≝ λE:excedence.λa,b:E. ¬ (a ≰ b).

interpretation "ordered sets less or equal than" 'leq a b = 
 (cic:/matita/ordered_sets/le.con _ a b).

lemma le_reflexive: ∀E.reflexive ? (le E).
intros (E); unfold; cases E; simplify; intros (x); apply (H x);
qed.

lemma le_transitive: ∀E.transitive ? (le E).
intros (E); unfold; cases E; simplify; unfold Not; intros (x y z Rxy Ryz H2); 
cases (c x z y H2) (H4 H5); clear H2; [exact (Rxy H4)|exact (Ryz H5)] 
qed.

definition apart ≝ λE:excedence.λa,b:E. a ≰ b ∨ b ≰ a.

notation "a # b" non associative with precedence 50 for @{ 'apart $a $b}.
interpretation "apartness" 'apart a b = (cic:/matita/ordered_sets/apart.con _ a b). 

lemma apart_coreflexive: ∀E.coreflexive ? (apart E).
intros (E); unfold; cases E; simplify; clear E; intros (x); unfold;
intros (H1); apply (H x); cases H1; assumption;
qed.

lemma apart_symmetric: ∀E.symmetric ? (apart E).
intros (E); unfold; intros(x y H); cases H; clear H; [right|left] assumption; 
qed.

lemma apart_cotrans: ∀E. cotransitive ? (apart E).
intros (E); unfold; cases E (T f _ cTf); simplify; intros (x y z Axy);
cases Axy (H); lapply (cTf ? ? z H) as H1; cases H1; clear Axy H1;
[left; left|right; left|right; right|left; right] assumption.
qed.

definition eq ≝ λE:excedence.λa,b:E. ¬ (a # b).

notation "a ≈ b" non associative with precedence 50 for @{ 'napart $a $b}.    
interpretation "alikeness" 'napart a b =
  (cic:/matita/ordered_sets/eq.con _ a b). 

lemma eq_reflexive:∀E. reflexive ? (eq E).
intros (E); unfold; cases E (T f cRf _); simplify; unfold Not; intros (x H);
apply (cRf x); cases H; assumption;
qed.

lemma eq_symmetric:∀E.symmetric ? (eq E).
intros (E); unfold; unfold eq; unfold Not;
intros (x y H1 H2); apply H1; cases H2; [right|left] assumption; 
qed.

lemma eq_transitive: ∀E.transitive ? (eq E).
intros (E); unfold; cases E (T f _ cTf); simplify; unfold Not; 
intros (x y z H1 H2 H3); cases H3 (H4 H4); clear E H3; lapply (cTf ? ? y H4) as H5;
cases H5; clear H5 H4 cTf; [1,4: apply H1|*:apply H2] clear H1 H2;
[1,3:left|*:right] assumption;
qed.

lemma le_antisymmetric: ∀E.antisymmetric ? (le E) (eq E).
intros (E); unfold; intros (x y Lxy Lyx); unfold; unfold; intros (H);
cases H; [apply Lxy;|apply Lyx] assumption;
qed.

definition lt ≝ λE:excedence.λa,b:E. a ≤ b ∧ a # b.

interpretation "ordered sets less than" 'lt a b =
 (cic:/matita/ordered_sets/lt.con _ a b).

lemma lt_coreflexive: ∀E.coreflexive ? (lt E).
intros (E); unfold; unfold Not; intros (x H); cases H (_ ABS); 
apply (apart_coreflexive ? x ABS);
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
