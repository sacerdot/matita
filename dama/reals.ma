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

record is_real (F:ordered_field_ch0) : Prop
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

theorem cauchy_max_seq: ∀R:real.∀x,y. is_cauchy_seq ? (max_seq R x y).
 intros;
 unfold;
 intros;
 apply (ex_intro ? ? m);
 intros;
 split;
  [ 
  | unfold max_seq;
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
         apply lt_zero_to_le_inv_zero
       | simplify;
         assumption
       ]
     | elim (to_cotransitive R (of_le R) R 0
(inv R (1+sum R (plus R) 0 1 m)
 (not_eq_sum_field_zero R (S m) (le_S_S O m (le_O_n m)))) (x-y)
(lt_zero_to_le_inv_zero R (S m)
 (not_eq_sum_field_zero R (S m) (le_S_S O m (le_O_n m)))));
        [ simplify;
          generalize in match (le_zero_x_to_le_opp_x_zero R ? t1);
          intro;
          (* finire *)
        |simplify;
         rewrite > (plus_comm ? y (-y));
         rewrite > opp_inverse;
         apply lt_zero_to_le_inv_zero
        ]
     ]
  ].
 
 