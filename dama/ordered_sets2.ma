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

set "baseuri" "cic:/matita/ordered_sets2".

include "ordered_sets.ma".

theorem le_f_inf_inf_f:
 ∀C.∀O':dedekind_sigma_complete_ordered_set C.
  ∀f:O'→O'. ∀H:is_order_continuous ? ? f.
   ∀a:bounded_below_sequence ? O'.
    let p := ? in
     f (inf ? ? a) ≤ inf ? ? (mk_bounded_below_sequence ? ? (λi. f (a i)) p).
 [ apply mk_is_bounded_below;
    [2: apply ioc_is_lower_bound_f_inf;
        assumption
    | skip
    ] 
 | intros;
   clearbody p;
   apply (inf_greatest_lower_bound ? ? ? ? (inf_is_inf ? ? ?));
   simplify;
   intro;
   letin b := (λi.match i with [ O ⇒ inf ? ? a | S _ ⇒ a n]);
   change with (f (b O) ≤ f (b (S O)));
   apply (ioc_is_sequentially_monotone ? ? ? H);
   simplify;
   clear b;
   intro;
   elim n1; simplify;
    [ apply (inf_lower_bound ? ? ? ? (inf_is_inf ? ? ?));
    | apply (or_reflexive ? O' (dscos_ordered_set ? O'))
    ]
 ].
qed.

theorem le_to_le_sup_sup:
 ∀C.∀O':dedekind_sigma_complete_ordered_set C.
  ∀a,b:bounded_above_sequence ? O'.
   (∀i.a i ≤ b i) → sup ? ? a ≤ sup ? ? b.
 intros;
 apply (sup_least_upper_bound ? ? ? ? (sup_is_sup ? ? a));
 unfold;
 intro;
 apply (or_transitive ? ? O');
  [2: apply H
  | skip
  | apply (sup_upper_bound ? ? ? ? (sup_is_sup ? ? b))
  ].
qed. 

interpretation "mk_bounded_sequence" 'hide_everything_but a
= (cic:/matita/ordered_sets/bounded_sequence.ind#xpointer(1/1/1) _ _ a _ _).

theorem fatou:
 ∀C.∀O':dedekind_sigma_complete_ordered_set C.
  ∀f:O'→O'. ∀H:is_order_continuous ? ? f.
   ∀a:bounded_sequence ? O'.
    let pb := ? in
    let pa := ? in
     f (liminf ? ? a) ≤ liminf ? ? (mk_bounded_sequence ? ? (λi. f (a i)) pb pa).
 [ letin bas ≝ (bounded_above_sequence_of_bounded_sequence ? ? a);
   apply mk_is_bounded_above;
    [2: apply (ioc_is_upper_bound_f_sup ? ? ? H bas)
    | skip
    ]
 | letin bbs ≝ (bounded_below_sequence_of_bounded_sequence ? ? a);
   apply mk_is_bounded_below;
    [2: apply (ioc_is_lower_bound_f_inf ? ? ? H bbs)
    | skip
    ] 
 | intros;
   rewrite > eq_f_liminf_sup_f_inf;
    [ unfold liminf;
      apply le_to_le_sup_sup;
      elim daemon (*(* f inf < inf f *)
      apply le_f_inf_inf_f*)
    | assumption
    ]
 ].
qed.
