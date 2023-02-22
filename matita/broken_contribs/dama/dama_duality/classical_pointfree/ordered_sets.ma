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



include "excess.ma".

record is_dedekind_sigma_complete (O:excess) : Type ≝
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
 { dscos_ordered_set:> excess;
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
 λO:excess.λf:O→O.
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
      autobatch paramodulation library
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
= (mk_bounded_above_sequence _ _ a _).

interpretation "mk_bounded_below_sequence" 'hide_everything_but a
= (mk_bounded_below_sequence _ _ a _).

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

