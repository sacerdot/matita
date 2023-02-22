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



include "attic/ordered_fields_ch0.ma".

record is_real (F:ordered_field_ch0) : Type
≝
 { r_archimedean: ∀x:F. ∃n:nat. x ≤ (sum_field ? n);
   r_complete: is_complete F  
 }.

record real: Type \def
 { r_ordered_field_ch0:> ordered_field_ch0;
   r_real_properties: is_real r_ordered_field_ch0
 }.

definition lim: ∀R:real.∀f:nat→R.is_cauchy_seq ? f → R.
 intros;
 elim (r_complete ? (r_real_properties R) ? H);
 exact a.
qed.

definition max_seq: ∀R:real.∀x,y:R. nat → R.
 intros (R x y);
 elim (cos_cotransitive R 0 (inv ? (sum_field ? (S n)) ?) (x-y));
  [ apply x
  | apply not_eq_sum_field_zero ;
    unfold;
    autobatch
  | apply y
  | apply lt_zero_to_le_inv_zero 
  ].
qed.

axiom daemon: False.

theorem cauchy_max_seq: ∀R:real.∀x,y:R. is_cauchy_seq ? (max_seq ? x y).
elim daemon.
(*
 intros;
 unfold;
 intros;
 exists; [ exact m | ]; (* apply (ex_intro ? ? m); *)
 intros;
 unfold max_seq;
 elim (of_cotransitive R 0
(inv R (sum_field R (S N))
 (not_eq_sum_field_zero R (S N) (le_S_S O N (le_O_n N)))) (x-y)
(lt_zero_to_le_inv_zero R (S N)
 (not_eq_sum_field_zero R (S N) (le_S_S O N (le_O_n N)))));
  [ simplify;
    elim (of_cotransitive R  0
(inv R (1+sum R (plus R) 0 1 m)
 (not_eq_sum_field_zero R (S m) (le_S_S O m (le_O_n m)))) (x-y)
(lt_zero_to_le_inv_zero R (S m)
 (not_eq_sum_field_zero R (S m) (le_S_S O m (le_O_n m)))));
    [ simplify;
      rewrite > (plus_comm ? x (-x));
      rewrite > opp_inverse;
      split;
       [ apply (le_zero_x_to_le_opp_x_zero R ?); 
         apply lt_zero_to_le_inv_zero
       | apply lt_zero_to_le_inv_zero
       ]
    | simplify;
      split;
       [ apply (or_transitive ? ? R ? 0);
          [ apply (le_zero_x_to_le_opp_x_zero R ?)
          | assumption
          ]
       | assumption
       ]
    ]
  | simplify;
    elim (of_cotransitive R 0
(inv R (1+sum R (plus R) 0 1 m)
 (not_eq_sum_field_zero R (S m) (le_S_S O m (le_O_n m)))) (x-y)
(lt_zero_to_le_inv_zero R (S m)
 (not_eq_sum_field_zero R (S m) (le_S_S O m (le_O_n m)))));
     [ simplify;
       split;
       [ elim daemon
       | generalize in match (le_zero_x_to_le_opp_x_zero R ? t1);
         intro;
         unfold minus in H1;
         rewrite > eq_opp_plus_plus_opp_opp in H1;
         rewrite > eq_opp_opp_x_x in H1;
         rewrite > plus_comm in H1;
         apply (or_transitive ? ? R ? 0);
          [ assumption
          | apply lt_zero_to_le_inv_zero
          ]
        ]
     | simplify;
       rewrite > (plus_comm ? y (-y));
       rewrite > opp_inverse;
       split;
       [ elim daemon
       | apply lt_zero_to_le_inv_zero
       ]
     ]
  ].
  elim daemon.*)
qed.

definition max: ∀R:real.R → R → R.
 intros (R x y);
 apply (lim R (max_seq R x y));
 apply cauchy_max_seq.
qed.

definition abs \def λR:real.λx:R. max R x (-x).

lemma comparison:
 ∀R:real.∀f,g:nat→R. is_cauchy_seq ? f → is_cauchy_seq ? g →
  (∀n:nat.f n ≤ g n) → lim ? f ? ≤ lim ? g ?.
 [ assumption
 | assumption
 | intros;
   elim daemon
 ].
qed.

definition to_zero ≝
 λR:real.λn.
  -(inv R (sum_field R (S n))
   (not_eq_sum_field_zero R (S n) (le_S_S O n (le_O_n n)))).
  
axiom is_cauchy_seq_to_zero: ∀R:real. is_cauchy_seq ? (to_zero R).

lemma technical1: ∀R:real.lim R (to_zero R) (is_cauchy_seq_to_zero R) = 0.
 intros;
 unfold lim;
 elim daemon.
qed.
 
lemma abs_x_ge_O: ∀R:real.∀x:R. 0 ≤ abs ? x.
 intros;
 unfold abs;
 unfold max;
 rewrite < technical1;
 apply comparison;
 intros;
 unfold to_zero;
 unfold max_seq;
 elim
     (cos_cotransitive R 0
(inv R (sum_field R (S n))
 (not_eq_sum_field_zero R (S n) (le_S_S O n (le_O_n n)))) (x--x)
(lt_zero_to_le_inv_zero R (S n)
 (not_eq_sum_field_zero R (S n) (le_S_S O n (le_O_n n)))));
 [ simplify;
   (* facile *)
   elim daemon
 | simplify;
   (* facile *)
   elim daemon
 ].
qed.
