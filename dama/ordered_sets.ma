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

include "excedence.ma".

record is_porder_relation (C:Type) (le:C→C→Prop) (eq:C→C→Prop) : Type ≝ { 
  por_reflexive: reflexive ? le;
  por_transitive: transitive ? le;
  por_antisimmetric: antisymmetric ? le eq
}.

record pordered_set: Type ≝ { 
  pos_carr:> excedence;
  pos_order_relation_properties:> is_porder_relation ? (le pos_carr) (eq pos_carr)
}.

lemma pordered_set_of_excedence: excedence → pordered_set.
intros (E); apply (mk_pordered_set E); apply (mk_is_porder_relation);
[apply le_reflexive|apply le_transitive|apply le_antisymmetric]
qed. 

definition total_order : ∀E:excedence. Type ≝
  λE:excedence. ∀a,b:E. a ≰ b → a < b.

alias id "transitive" = "cic:/matita/higher_order_defs/relations/transitive.con".
alias id "cotransitive" = "cic:/matita/higher_order_defs/relations/cotransitive.con".
alias id "antisymmetric" = "cic:/matita/higher_order_defs/relations/antisymmetric.con".
theorem antisimmetric_to_cotransitive_to_transitive:
 ∀C:Type.∀le:C→C→Prop. antisymmetric ? le → cotransitive ? le → transitive ? le.  
intros (T f Af cT); unfold transitive; intros (x y z fxy fyz);
lapply (cT ? ? fxy z) as H; cases H; [assumption] cases (Af ? ? fyz H1);
qed.

definition is_increasing ≝ λO:pordered_set.λa:nat→O.∀n:nat.a n ≤ a (S n).
definition is_decreasing ≝ λO:pordered_set.λa:nat→O.∀n:nat.a (S n) ≤ a n.

definition is_upper_bound ≝ λO:pordered_set.λa:nat→O.λu:O.∀n:nat.a n ≤ u.
definition is_lower_bound ≝ λO:pordered_set.λa:nat→O.λu:O.∀n:nat.u ≤ a n.

record is_sup (O:pordered_set) (a:nat→O) (u:O) : Prop ≝
 { sup_upper_bound: is_upper_bound O a u; 
   sup_least_upper_bound: ∀v:O. is_upper_bound O a v → u≤v
 }.

record is_inf (O:pordered_set) (a:nat→O) (u:O) : Prop ≝
 { inf_lower_bound: is_lower_bound O a u; 
   inf_greatest_lower_bound: ∀v:O. is_lower_bound O a v → v≤u
 }.

record is_bounded_below (O:pordered_set) (a:nat→O) : Type ≝
 { ib_lower_bound: O;
   ib_lower_bound_is_lower_bound: is_lower_bound ? a ib_lower_bound
 }.

record is_bounded_above (O:pordered_set) (a:nat→O) : Type ≝
 { ib_upper_bound: O;
   ib_upper_bound_is_upper_bound: is_upper_bound ? a ib_upper_bound
 }.

record is_bounded (O:pordered_set) (a:nat→O) : Type ≝
 { ib_bounded_below:> is_bounded_below ? a;
   ib_bounded_above:> is_bounded_above ? a
 }.

record bounded_below_sequence (O:pordered_set) : Type ≝
 { bbs_seq:1> nat→O;
   bbs_is_bounded_below:> is_bounded_below ? bbs_seq
 }.

record bounded_above_sequence (O:pordered_set) : Type ≝
 { bas_seq:1> nat→O;
   bas_is_bounded_above:> is_bounded_above ? bas_seq
 }.

record bounded_sequence (O:pordered_set) : Type ≝
 { bs_seq:1> nat → O;
   bs_is_bounded_below: is_bounded_below ? bs_seq;
   bs_is_bounded_above: is_bounded_above ? bs_seq
 }.

definition bounded_below_sequence_of_bounded_sequence ≝
 λO:pordered_set.λb:bounded_sequence O.
  mk_bounded_below_sequence ? b (bs_is_bounded_below ? b).

coercion cic:/matita/ordered_sets/bounded_below_sequence_of_bounded_sequence.con.

definition bounded_above_sequence_of_bounded_sequence ≝
 λO:pordered_set.λb:bounded_sequence O.
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
