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

set "baseuri" "cic:/matita/reals/".

include "ordered_fields_ch0.ma".

record is_real (F:ordered_field_ch0) : Type
≝
 { r_archimedean: ∀x:F. ∃n:nat. x ≤ (sum_field F n);
   r_complete: is_complete F  
 }.

record real: Type \def
 { r_ordered_field_ch0:> ordered_field_ch0;
   r_real_properties: is_real r_ordered_field_ch0
 }.

(* serve l'esistenziale in CProp!
definition lim: ∀R:real.∀f:nat→R.is_cauchy_seq R f → R.
 intros;
 elim H;
qed.
*)

definition max_seq: ∀R:real.∀x,y:R. nat → R.
 intros (R x y);
 elim (to_cotransitive R (of_le R) R 0 (inv ? (sum_field R (S n)) ?) (x-y));
  [ apply x
  | apply not_eq_sum_field_zero ;
    unfold;
    auto new
  | apply y
  | apply lt_zero_to_le_inv_zero 
  ].
qed.

axiom daemon: False.

theorem cauchy_max_seq: ∀R:real.∀x,y. is_cauchy_seq ? (max_seq R x y).
 intros;
 unfold;
 intros;
 exists; [ exact m | ]; (* apply (ex_intro ? ? m); *)
 intros;
 unfold max_seq;
 elim (to_cotransitive R (of_le R) R 0
(inv R (sum_field R (S N))
 (not_eq_sum_field_zero R (S N) (le_S_S O N (le_O_n N)))) (x-y)
(lt_zero_to_le_inv_zero R (S N)
 (not_eq_sum_field_zero R (S N) (le_S_S O N (le_O_n N)))));
  [ simplify;
    elim (to_cotransitive R (of_le R) R 0
(inv R (1+sum R (plus R) 0 1 m)
 (not_eq_sum_field_zero R (S m) (le_S_S O m (le_O_n m)))) (x-y)
(lt_zero_to_le_inv_zero R (S m)
 (not_eq_sum_field_zero R (S m) (le_S_S O m (le_O_n m)))));
    [ simplify;
      rewrite > (plus_comm ? x (-x));
      rewrite > opp_inverse;
      split;
       [ elim daemon (* da finire *)
       | apply lt_zero_to_le_inv_zero
       ]
    | simplify;
      split;
       [ elim daemon (* da finire *)
       | assumption
       ]
    ]
  | simplify;
    elim (to_cotransitive R (of_le R) R 0
(inv R (1+sum R (plus R) 0 1 m)
 (not_eq_sum_field_zero R (S m) (le_S_S O m (le_O_n m)))) (x-y)
(lt_zero_to_le_inv_zero R (S m)
 (not_eq_sum_field_zero R (S m) (le_S_S O m (le_O_n m)))));
     [ simplify;
       split;
       [ elim daemon (* da finire *)
       | generalize in match (le_zero_x_to_le_opp_x_zero R ? t1);
         intro;
         unfold minus in H1;
         rewrite > eq_opp_plus_plus_opp_opp in H1;
         rewrite > eq_opp_opp_x_x in H1;
         rewrite > plus_comm in H1;
         apply (to_transitive ? ? (of_total_order_relation ? ? R) ? 0 ?);
          [ assumption
          | apply lt_zero_to_le_inv_zero
          ]
        ]
     | simplify;
       rewrite > (plus_comm ? y (-y));
       rewrite > opp_inverse;
       split;
       [ elim daemon (* da finire *)
       | apply lt_zero_to_le_inv_zero
       ]
     ]
  ].
qed.

definition max: ∀R:real.R → R → R.
 intros (R x y);
 elim (r_complete ? (r_real_properties R) ? ?);
  [|| apply (cauchy_max_seq R x y) ]
qed.
 
