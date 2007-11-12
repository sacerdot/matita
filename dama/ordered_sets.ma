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

theorem mah: ∀E:excedence.∀a,b:E. (a < b) → (b ≰ a).
intros (E a b Lab); cases Lab (LEab Aab);
cases Aab (H H); [cases (LEab H)] fold normalize (b ≰ a); assumption; (* BUG *)  
qed.

-- altro file
opposto TH è assioma per ordine totale.

-- 







record is_order_relation (C:Type) (le:C→C→Prop) (eq:C→C→Prop) : Type ≝ { 
  or_reflexive: reflexive ? le;
  or_transitive: transitive ? le;
  or_antisimmetric: antisymmetric ? le eq
}.

record ordered_set: Type ≝ { 
  os_carr:> excedence;
  os_order_relation_properties:> is_order_relation ? (le os_carr) (apart os_carr)
}.

ordered_set.

E

E

theorem antisimmetric_to_cotransitive_to_transitive:
 ∀C.∀le:relation C. antisimmetric ? le → cotransitive ? le →
  transitive ? le.
 intros;
 unfold transitive;
 intros;
 elim (c ? ? z H1);
  [ assumption
  | rewrite < (H ? ? H2 t);
    assumption
  ].
qed.

definition is_increasing ≝ λO:ordered_set.λa:nat→O.∀n:nat.a n ≤ a (S n).
definition is_decreasing ≝ λO:ordered_set.λa:nat→O.∀n:nat.a (S n) ≤ a n.

definition is_upper_bound ≝ λO:ordered_set.λa:nat→O.λu:O.∀n:nat.a n ≤ u.
definition is_lower_bound ≝ λO:ordered_set.λa:nat→O.λu:O.∀n:nat.u ≤ a n.

record is_sup (O:ordered_set) (a:nat→O) (u:O) : Prop ≝
 { sup_upper_bound: is_upper_bound O a u; 
   sup_least_upper_bound: ∀v:O. is_upper_bound O a v → u≤v
 }.

record is_inf (O:ordered_set) (a:nat→O) (u:O) : Prop ≝
 { inf_lower_bound: is_lower_bound O a u; 
   inf_greatest_lower_bound: ∀v:O. is_lower_bound O a v → v≤u
 }.

record is_bounded_below (O:ordered_set) (a:nat→O) : Type ≝
 { ib_lower_bound: O;
   ib_lower_bound_is_lower_bound: is_lower_bound ? a ib_lower_bound
 }.

record is_bounded_above (O:ordered_set) (a:nat→O) : Type ≝
 { ib_upper_bound: O;
   ib_upper_bound_is_upper_bound: is_upper_bound ? a ib_upper_bound
 }.

record is_bounded (O:ordered_set) (a:nat→O) : Type ≝
 { ib_bounded_below:> is_bounded_below ? a;
   ib_bounded_above:> is_bounded_above ? a
 }.

record bounded_below_sequence (O:ordered_set) : Type ≝
 { bbs_seq:1> nat→O;
   bbs_is_bounded_below:> is_bounded_below ? bbs_seq
 }.

record bounded_above_sequence (O:ordered_set) : Type ≝
 { bas_seq:1> nat→O;
   bas_is_bounded_above:> is_bounded_above ? bas_seq
 }.

record bounded_sequence (O:ordered_set) : Type ≝
 { bs_seq:1> nat → O;
   bs_is_bounded_below: is_bounded_below ? bs_seq;
   bs_is_bounded_above: is_bounded_above ? bs_seq
 }.

definition bounded_below_sequence_of_bounded_sequence ≝
 λO:ordered_set.λb:bounded_sequence O.
  mk_bounded_below_sequence ? b (bs_is_bounded_below ? b).

coercion cic:/matita/ordered_sets/bounded_below_sequence_of_bounded_sequence.con.

definition bounded_above_sequence_of_bounded_sequence ≝
 λO:ordered_set.λb:bounded_sequence O.
  mk_bounded_above_sequence ? b (bs_is_bounded_above ? b).

coercion cic:/matita/ordered_sets/bounded_above_sequence_of_bounded_sequence.con.

definition lower_bound ≝
 λO:ordered_set.λb:bounded_below_sequence O.
  ib_lower_bound ? b (bbs_is_bounded_below ? b).

lemma lower_bound_is_lower_bound:
 ∀O:ordered_set.∀b:bounded_below_sequence O.
  is_lower_bound ? b (lower_bound ? b).
 intros;
 unfold lower_bound;
 apply ib_lower_bound_is_lower_bound.
qed.

definition upper_bound ≝
 λO:ordered_set.λb:bounded_above_sequence O.
  ib_upper_bound ? b (bas_is_bounded_above ? b).

lemma upper_bound_is_upper_bound:
 ∀O:ordered_set.∀b:bounded_above_sequence O.
  is_upper_bound ? b (upper_bound ? b).
 intros;
 unfold upper_bound;
 apply ib_upper_bound_is_upper_bound.
qed.

definition lt ≝ λO:ordered_set.λa,b:O.a ≤ b ∧ a ≠ b.

interpretation "Ordered set lt" 'lt a b =
 (cic:/matita/ordered_sets/lt.con _ a b).

definition reverse_ordered_set: ordered_set → ordered_set.
 intros;
 apply mk_ordered_set;
  [2:apply (λx,y:o.y ≤ x)
  | skip
  | apply mk_is_order_relation;
     [ simplify;
       intros;
       apply (or_reflexive ? ? o)
     | simplify;
       intros;
       apply (or_transitive ? ? o);
        [2: apply H1
        | skip
        | assumption
        ] 
     | simplify;
       intros;
       apply (or_antisimmetric ? ? o);
       assumption
     ]
  ].
qed.
 
interpretation "Ordered set ge" 'geq a b =
 (cic:/matita/ordered_sets/os_le.con _
  (cic:/matita/ordered_sets/os_pre_ordered_set.con _
   (cic:/matita/ordered_sets/reverse_ordered_set.con _ _)) a b).

lemma is_lower_bound_reverse_is_upper_bound:
 ∀O:ordered_set.∀a:nat→O.∀l:O.
  is_lower_bound O a l → is_upper_bound (reverse_ordered_set O) a l.
 intros;
 unfold;
 intro;
 unfold;
 unfold reverse_ordered_set;
 simplify;
 apply H.
qed.

lemma is_upper_bound_reverse_is_lower_bound:
 ∀O:ordered_set.∀a:nat→O.∀l:O.
  is_upper_bound O a l → is_lower_bound (reverse_ordered_set O) a l.
 intros;
 unfold;
 intro;
 unfold;
 unfold reverse_ordered_set;
 simplify;
 apply H.
qed.

lemma reverse_is_lower_bound_is_upper_bound:
 ∀O:ordered_set.∀a:nat→O.∀l:O.
  is_lower_bound (reverse_ordered_set O) a l → is_upper_bound O a l.
 intros;
 unfold in H;
 unfold reverse_ordered_set in H;
 apply H.
qed.

lemma reverse_is_upper_bound_is_lower_bound:
 ∀O:ordered_set.∀a:nat→O.∀l:O.
  is_upper_bound (reverse_ordered_set O) a l → is_lower_bound O a l.
 intros;
 unfold in H;
 unfold reverse_ordered_set in H;
 apply H.
qed.


lemma is_inf_to_reverse_is_sup:
 ∀O:ordered_set.∀a:bounded_below_sequence O.∀l:O.
  is_inf O a l → is_sup (reverse_ordered_set O) a l.
 intros;
 apply (mk_is_sup (reverse_ordered_set O));
  [ apply is_lower_bound_reverse_is_upper_bound;
    apply inf_lower_bound;
    assumption
  | intros;
    change in v with (os_carrier O);
    change with (v ≤ l);
    apply (inf_greatest_lower_bound ? ? ? H);
    apply reverse_is_upper_bound_is_lower_bound;
    assumption
  ].
qed.
 
lemma is_sup_to_reverse_is_inf:
 ∀O:ordered_set.∀a:bounded_above_sequence O.∀l:O.
  is_sup O a l → is_inf (reverse_ordered_set O) a l.
 intros;
 apply (mk_is_inf (reverse_ordered_set O));
  [ apply is_upper_bound_reverse_is_lower_bound;
    apply sup_upper_bound;
    assumption
  | intros;
    change in v with (os_carrier O);
    change with (l ≤ v);
    apply (sup_least_upper_bound ? ? ? H);
    apply reverse_is_lower_bound_is_upper_bound;
    assumption
  ].
qed.

lemma reverse_is_sup_to_is_inf:
 ∀O:ordered_set.∀a:bounded_above_sequence O.∀l:O.
  is_sup (reverse_ordered_set O) a l → is_inf O a l.
 intros;
 apply mk_is_inf;
  [ apply reverse_is_upper_bound_is_lower_bound;
    change in l with (os_carrier (reverse_ordered_set O));
    apply sup_upper_bound;
    assumption
  | intros;
    change in l with (os_carrier (reverse_ordered_set O));
    change in v with (os_carrier (reverse_ordered_set O));
    change with (os_le (reverse_ordered_set O) l v);
    apply (sup_least_upper_bound ? ? ? H);
    change in v with (os_carrier O);
    apply is_lower_bound_reverse_is_upper_bound;
    assumption
  ].
qed.

lemma reverse_is_inf_to_is_sup:
 ∀O:ordered_set.∀a:bounded_above_sequence O.∀l:O.
  is_inf (reverse_ordered_set O) a l → is_sup O a l.
 intros;
 apply mk_is_sup;
  [ apply reverse_is_lower_bound_is_upper_bound;
    change in l with (os_carrier (reverse_ordered_set O));
    apply (inf_lower_bound ? ? ? H)
  | intros;
    change in l with (os_carrier (reverse_ordered_set O));
    change in v with (os_carrier (reverse_ordered_set O));
    change with (os_le (reverse_ordered_set O) v l);
    apply (inf_greatest_lower_bound ? ? ? H);
    change in v with (os_carrier O);
    apply is_upper_bound_reverse_is_lower_bound;
    assumption
  ].
qed.

record cotransitively_ordered_set: Type :=
 { cos_ordered_set :> ordered_set;
   cos_cotransitive: cotransitive ? (os_le cos_ordered_set)
 }.
