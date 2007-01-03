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

definition cotransitive ≝
 λC:Type.λle:C→C→Prop.∀x,y,z:C. le x y → le x z ∨ le z y. 

definition antisimmetric ≝
 λC:Type.λle:C→C→Prop.∀x,y:C. le x y → le y x → x=y.

record is_order_relation (C:Type) (le:C→C→Prop) : Type ≝
 { or_reflexive: reflexive ? le;
   or_transitive: transitive ? le;
   or_antisimmetric: antisimmetric ? le
 }.

record ordered_set: Type ≝
 { os_carrier:> Type;
   os_le: os_carrier → os_carrier → Prop;
   os_order_relation_properties:> is_order_relation ? os_le
 }.

interpretation "Ordered Sets le" 'leq a b =
 (cic:/matita/ordered_sets/os_le.con _ a b).

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

record is_dedekind_sigma_complete (O:ordered_set) : Type ≝
 { dsc_inf: ∀a:nat→O.∀m:O. is_lower_bound ? a m → ex ? (λs:O.is_inf O a s);
   dsc_inf_proof_irrelevant:
    ∀a:nat→O.∀m,m':O.∀p:is_lower_bound ? a m.∀p':is_lower_bound ? a m'.
     (match dsc_inf a m p with [ ex_intro s _ ⇒ s ]) =
     (match dsc_inf a m' p' with [ ex_intro s' _ ⇒ s' ]); 
   dsc_sup: ∀a:nat→O.∀m:O. is_upper_bound ? a m → ex ? (λs:O.is_sup O a s);
   dsc_sup_proof_irrelevant:
    ∀a:nat→O.∀m,m':O.∀p:is_upper_bound ? a m.∀p':is_upper_bound ? a m'.
     (match dsc_sup a m p with [ ex_intro s _ ⇒ s ]) =
     (match dsc_sup a m' p' with [ ex_intro s' _ ⇒ s' ])    
 }.

record dedekind_sigma_complete_ordered_set : Type ≝
 { dscos_ordered_set:> ordered_set;
   dscos_dedekind_sigma_complete_properties:>
    is_dedekind_sigma_complete dscos_ordered_set
 }.

definition inf:
 ∀O:dedekind_sigma_complete_ordered_set.
  bounded_below_sequence O → O.
 intros;
 elim
  (dsc_inf O (dscos_dedekind_sigma_complete_properties O) b);
  [ apply a
  | apply (lower_bound ? b)
  | apply lower_bound_is_lower_bound
  ]
qed.

lemma inf_is_inf:
 ∀O:dedekind_sigma_complete_ordered_set.
  ∀a:bounded_below_sequence O.
   is_inf ? a (inf ? a).
 intros;
 unfold inf;
 simplify;
 elim (dsc_inf O (dscos_dedekind_sigma_complete_properties O) a
(lower_bound O a) (lower_bound_is_lower_bound O a));
 simplify;
 assumption.
qed.

lemma inf_proof_irrelevant:
 ∀O:dedekind_sigma_complete_ordered_set.
  ∀a,a':bounded_below_sequence O.
   bbs_seq ? a = bbs_seq ? a' →
    inf ? a = inf ? a'.
 intros 3;
 elim a 0;
 elim a';
 simplify in H;
 generalize in match i1;
 clear i1;
 rewrite > H;
 intro;
 simplify;
 rewrite < (dsc_inf_proof_irrelevant O O f (ib_lower_bound ? f i)
  (ib_lower_bound ? f i2) (ib_lower_bound_is_lower_bound ? f i)
  (ib_lower_bound_is_lower_bound ? f i2));
 reflexivity.
qed.

definition sup:
 ∀O:dedekind_sigma_complete_ordered_set.
  bounded_above_sequence O → O.
 intros;
 elim
  (dsc_sup O (dscos_dedekind_sigma_complete_properties O) b);
  [ apply a
  | apply (upper_bound ? b)
  | apply upper_bound_is_upper_bound
  ].
qed.

lemma sup_is_sup:
 ∀O:dedekind_sigma_complete_ordered_set.
  ∀a:bounded_above_sequence O.
   is_sup ? a (sup ? a).
 intros;
 unfold sup;
 simplify;
 elim (dsc_sup O (dscos_dedekind_sigma_complete_properties O) a
(upper_bound O a) (upper_bound_is_upper_bound O a));
 simplify;
 assumption.
qed.

lemma sup_proof_irrelevant:
 ∀O:dedekind_sigma_complete_ordered_set.
  ∀a,a':bounded_above_sequence O.
   bas_seq ? a = bas_seq ? a' →
    sup ? a = sup ? a'.
 intros 3;
 elim a 0;
 elim a';
 simplify in H;
 generalize in match i1;
 clear i1;
 rewrite > H;
 intro;
 simplify;
 rewrite < (dsc_sup_proof_irrelevant O O f (ib_upper_bound ? f i2)
  (ib_upper_bound ? f i) (ib_upper_bound_is_upper_bound ? f i2)
  (ib_upper_bound_is_upper_bound ? f i));
 reflexivity.
qed.

axiom daemon: False.

theorem inf_le_sup:
 ∀O:dedekind_sigma_complete_ordered_set.
  ∀a:bounded_sequence O. inf ? a ≤ sup ? a.
 intros (O');
 apply (or_transitive ? ? O' ? (a O));
  [ elim daemon (*apply (inf_lower_bound ? ? ? ? (inf_is_inf ? ? a))*)
  | elim daemon (*apply (sup_upper_bound ? ? ? ? (sup_is_sup ? ? a))*)
  ].
qed.

lemma inf_respects_le:
 ∀O:dedekind_sigma_complete_ordered_set.
  ∀a:bounded_below_sequence O.∀m:O.
   is_upper_bound ? a m → inf ? a ≤ m.
 intros (O');
 apply (or_transitive ? ? O' ? (sup ? (mk_bounded_sequence ? a ? ?)));
  [ apply (bbs_is_bounded_below ? a)
  | apply (mk_is_bounded_above ? ? m H)
  | apply inf_le_sup 
  | apply
     (sup_least_upper_bound ? ? ?
      (sup_is_sup ? (mk_bounded_sequence O' a a
        (mk_is_bounded_above O' a m H))));
    assumption
  ].
qed. 

definition is_sequentially_monotone ≝
 λO:ordered_set.λf:O→O.
  ∀a:nat→O.∀p:is_increasing ? a.
   is_increasing ? (λi.f (a i)).

record is_order_continuous
 (O:dedekind_sigma_complete_ordered_set) (f:O→O) : Prop
≝
 { ioc_is_sequentially_monotone: is_sequentially_monotone ? f;
   ioc_is_upper_bound_f_sup:
    ∀a:bounded_above_sequence O.
     is_upper_bound ? (λi.f (a i)) (f (sup ? a));
   ioc_respects_sup:
    ∀a:bounded_above_sequence O.
     is_increasing ? a →
      f (sup ? a) =
       sup ? (mk_bounded_above_sequence ? (λi.f (a i))
        (mk_is_bounded_above ? ? (f (sup ? a))
         (ioc_is_upper_bound_f_sup a)));
   ioc_is_lower_bound_f_inf:
    ∀a:bounded_below_sequence O.
     is_lower_bound ? (λi.f (a i)) (f (inf ? a));
   ioc_respects_inf:
    ∀a:bounded_below_sequence O.
     is_decreasing ? a →
      f (inf ? a) =
       inf ? (mk_bounded_below_sequence ? (λi.f (a i))
        (mk_is_bounded_below ? ? (f (inf ? a))
         (ioc_is_lower_bound_f_inf a)))   
 }.

theorem tail_inf_increasing:
 ∀O:dedekind_sigma_complete_ordered_set.
  ∀a:bounded_below_sequence O.
   let y ≝ λi.mk_bounded_below_sequence ? (λj.a (i+j)) ? in
   let x ≝ λi.inf ? (y i) in
    is_increasing ? x.
 [ apply (mk_is_bounded_below ? ? (ib_lower_bound ? a a));
   simplify;
   intro;
   apply (ib_lower_bound_is_lower_bound ? a a)
 | intros;
   unfold is_increasing;
   intro;
   unfold x in ⊢ (? ? ? %);
   apply (inf_greatest_lower_bound ? ? ? (inf_is_inf ? (y (S n))));
   change with (is_lower_bound ? (y (S n)) (inf ? (y n)));
   unfold is_lower_bound;
   intro;
   generalize in match (inf_lower_bound ? ? ? (inf_is_inf ? (y n)) (S n1));
   (*CSC: coercion per FunClass inserita a mano*)
   suppose (inf ? (y n) ≤ bbs_seq ? (y n) (S n1)) (H);
   cut (bbs_seq ? (y n) (S n1) = bbs_seq ? (y (S n)) n1);
    [ rewrite < Hcut;
      assumption
    | unfold y;
      simplify;
      auto paramodulation library
    ]
 ].
qed.

definition is_liminf:
 ∀O:dedekind_sigma_complete_ordered_set.
  bounded_below_sequence O → O → Prop.
 intros;
 apply
  (is_sup ? (λi.inf ? (mk_bounded_below_sequence ? (λj.b (i+j)) ?)) t);
 apply (mk_is_bounded_below ? ? (ib_lower_bound ? b b));
 simplify;
 intros;
 apply (ib_lower_bound_is_lower_bound ? b b).
qed.  

definition liminf:
 ∀O:dedekind_sigma_complete_ordered_set.
  bounded_sequence O → O.
 intros;
 apply
  (sup ?
   (mk_bounded_above_sequence ?
     (λi.inf ?
       (mk_bounded_below_sequence ?
         (λj.b (i+j)) ?)) ?));
  [ apply (mk_is_bounded_below ? ? (ib_lower_bound ? b b));
    simplify;
    intros;
    apply (ib_lower_bound_is_lower_bound ? b b)
  | apply (mk_is_bounded_above ? ? (ib_upper_bound ? b b));
    unfold is_upper_bound;
    intro;
    change with
     (inf O
  (mk_bounded_below_sequence O (\lambda j:nat.b (n+j))
   (mk_is_bounded_below O (\lambda j:nat.b (n+j)) (ib_lower_bound O b b)
    (\lambda j:nat.ib_lower_bound_is_lower_bound O b b (n+j))))
\leq ib_upper_bound O b b);
    apply (inf_respects_le O);
    simplify;
    intro;
    apply (ib_upper_bound_is_upper_bound ? b b)
  ].
qed.

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


definition reverse_dedekind_sigma_complete_ordered_set:
 dedekind_sigma_complete_ordered_set → dedekind_sigma_complete_ordered_set.
 intros;
 apply mk_dedekind_sigma_complete_ordered_set;
  [ apply (reverse_ordered_set d)
  | elim daemon
    (*apply mk_is_dedekind_sigma_complete;
     [ intros;
       elim (dsc_sup ? ? d a m) 0;
        [ generalize in match H; clear H;
          generalize in match m; clear m;
          elim d;
          simplify in a1;
          simplify;
          change in a1 with (Type_OF_ordered_set ? (reverse_ordered_set ? o)); 
          apply (ex_intro ? ? a1);
          simplify in H1;
          change in m with (Type_OF_ordered_set ? o);
          apply (is_sup_to_reverse_is_inf ? ? ? ? H1)
        | generalize in match H; clear H;
          generalize in match m; clear m;
          elim d;
          simplify;
          change in t with (Type_OF_ordered_set ? o);
          simplify in t;
          apply reverse_is_lower_bound_is_upper_bound;
          assumption
        ]
     | apply is_sup_reverse_is_inf;
     | apply m
     | 
     ]*)
  ].
qed.

definition reverse_bounded_sequence:
 ∀O:dedekind_sigma_complete_ordered_set.
  bounded_sequence O →
   bounded_sequence (reverse_dedekind_sigma_complete_ordered_set O).
 intros;
 apply mk_bounded_sequence;
  [ apply bs_seq;
    unfold reverse_dedekind_sigma_complete_ordered_set;
    simplify;
    elim daemon
  | elim daemon
  | elim daemon
  ].
qed.

definition limsup ≝
 λO:dedekind_sigma_complete_ordered_set.
  λa:bounded_sequence O.
   liminf (reverse_dedekind_sigma_complete_ordered_set O)
    (reverse_bounded_sequence O a).

notation "hvbox(〈a〉)"
 non associative with precedence 45
for @{ 'hide_everything_but $a }.

interpretation "mk_bounded_above_sequence" 'hide_everything_but a
= (cic:/matita/ordered_sets/bounded_above_sequence.ind#xpointer(1/1/1) _ _ a _).

interpretation "mk_bounded_below_sequence" 'hide_everything_but a
= (cic:/matita/ordered_sets/bounded_below_sequence.ind#xpointer(1/1/1) _ _ a _).

theorem eq_f_sup_sup_f:
 ∀O':dedekind_sigma_complete_ordered_set.
  ∀f:O'→O'. ∀H:is_order_continuous ? f.
   ∀a:bounded_above_sequence O'.
    ∀p:is_increasing ? a.
     f (sup ? a) = sup ? (mk_bounded_above_sequence ? (λi.f (a i)) ?).
 [ apply (mk_is_bounded_above ? ? (f (sup ? a))); 
   apply ioc_is_upper_bound_f_sup;
   assumption
 | intros;
   apply ioc_respects_sup;
   assumption
 ].
qed.

theorem eq_f_sup_sup_f':
 ∀O':dedekind_sigma_complete_ordered_set.
  ∀f:O'→O'. ∀H:is_order_continuous ? f.
   ∀a:bounded_above_sequence O'.
    ∀p:is_increasing ? a.
     ∀p':is_bounded_above ? (λi.f (a i)).
      f (sup ? a) = sup ? (mk_bounded_above_sequence ? (λi.f (a i)) p').
 intros;
 rewrite > (eq_f_sup_sup_f ? f H a H1);
 apply sup_proof_irrelevant;
 reflexivity.
qed.

theorem eq_f_liminf_sup_f_inf:
 ∀O':dedekind_sigma_complete_ordered_set.
  ∀f:O'→O'. ∀H:is_order_continuous ? f.
   ∀a:bounded_sequence O'.
   let p1 := ? in
    f (liminf ? a) =
     sup ?
      (mk_bounded_above_sequence ?
        (λi.f (inf ?
          (mk_bounded_below_sequence ?
            (λj.a (i+j))
            ?)))
        p1).
 [ apply (mk_is_bounded_below ? ? (ib_lower_bound ? a a));
   simplify;
   intro;
   apply (ib_lower_bound_is_lower_bound ? a a)
 | apply (mk_is_bounded_above ? ? (f (sup ? a)));
   unfold is_upper_bound;
   intro;
   apply (or_transitive ? ? O' ? (f (a n)));
    [ generalize in match (ioc_is_lower_bound_f_inf ? ? H);
      intro H1;
      simplify in H1;
      rewrite > (plus_n_O n) in ⊢ (? ? ? (? (? ? ? %)));
      apply (H1 (mk_bounded_below_sequence O' (\lambda j:nat.a (n+j))
(mk_is_bounded_below O' (\lambda j:nat.a (n+j)) (ib_lower_bound O' a a)
 (\lambda j:nat.ib_lower_bound_is_lower_bound O' a a (n+j)))) O);
    | elim daemon (*apply (ioc_is_upper_bound_f_sup ? ? ? H)*)
    ]
 | intros;
   unfold liminf;
   clearbody p1;
   generalize in match (\lambda n:nat
.inf_respects_le O'
 (mk_bounded_below_sequence O' (\lambda j:nat.a (plus n j))
  (mk_is_bounded_below O' (\lambda j:nat.a (plus n j))
   (ib_lower_bound O' a a)
   (\lambda j:nat.ib_lower_bound_is_lower_bound O' a a (plus n j))))
 (ib_upper_bound O' a a)
 (\lambda n1:nat.ib_upper_bound_is_upper_bound O' a a (plus n n1)));
   intro p2;
   apply (eq_f_sup_sup_f' ? f H (mk_bounded_above_sequence O'
(\lambda i:nat
 .inf O'
  (mk_bounded_below_sequence O' (\lambda j:nat.a (plus i j))
   (mk_is_bounded_below O' (\lambda j:nat.a (plus i j))
    (ib_lower_bound O' a a)
    (\lambda n:nat.ib_lower_bound_is_lower_bound O' a a (plus i n)))))
(mk_is_bounded_above O'
 (\lambda i:nat
  .inf O'
   (mk_bounded_below_sequence O' (\lambda j:nat.a (plus i j))
    (mk_is_bounded_below O' (\lambda j:nat.a (plus i j))
     (ib_lower_bound O' a a)
     (\lambda n:nat.ib_lower_bound_is_lower_bound O' a a (plus i n)))))
 (ib_upper_bound O' a a) p2)));
   unfold bas_seq;
   change with
    (is_increasing ? (\lambda i:nat
.inf O'
 (mk_bounded_below_sequence O' (\lambda j:nat.a (plus i j))
  (mk_is_bounded_below O' (\lambda j:nat.a (plus i j))
   (ib_lower_bound O' a a)
   (\lambda n:nat.ib_lower_bound_is_lower_bound O' a a (plus i n))))));
   apply tail_inf_increasing
 ].
qed.




definition lt ≝ λO:ordered_set.λa,b:O.a ≤ b ∧ a ≠ b.

interpretation "Ordered set lt" 'lt a b =
 (cic:/matita/ordered_sets/lt.con _ a b).
