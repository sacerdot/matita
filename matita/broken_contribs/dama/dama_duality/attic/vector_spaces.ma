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



include "attic/reals.ma".

record is_vector_space (K: field) (G:abelian_group) (emult:K→G→G) : Prop
≝
 { vs_nilpotent: ∀v. emult 0 v = 0;
   vs_neutral: ∀v. emult 1 v = v;
   vs_distributive: ∀a,b,v. emult (a + b) v = (emult a v) + (emult b v);
   vs_associative: ∀a,b,v. emult (a * b) v = emult a (emult b v)
 }.

record vector_space (K:field): Type \def
{ vs_abelian_group :> abelian_group;
  emult: K → vs_abelian_group → vs_abelian_group;
  vs_vector_space_properties :> is_vector_space ? vs_abelian_group emult
}.

interpretation "Vector space external product" 'times a b = (emult ? ? a b).

record is_semi_norm (R:real) (V: vector_space R) (semi_norm:V→R) : Prop \def
 { sn_positive: ∀x:V. zero R ≤ semi_norm x;
   sn_omogeneous: ∀a:R.∀x:V. semi_norm (a*x) = (abs ? a) * semi_norm x;
   sn_triangle_inequality: ∀x,y:V. semi_norm (x + y) ≤ semi_norm x + semi_norm y
 }.

theorem eq_semi_norm_zero_zero:
 ∀R:real.∀V:vector_space R.∀semi_norm:V→R.
  is_semi_norm ? ? semi_norm →
   semi_norm 0 = 0.
 intros;
 (* facile *)
 elim daemon.
qed.

record is_norm (R:real) (V:vector_space R) (norm:V → R) : Prop ≝
 { n_semi_norm:> is_semi_norm ? ? norm;
   n_properness: ∀x:V. norm x = 0 → x = 0
 }.

record norm (R:real) (V:vector_space R) : Type ≝
 { n_function:1> V→R;
   n_norm_properties: is_norm ? ? n_function
 }.

record is_semi_distance (R:real) (C:Type) (semi_d: C→C→R) : Prop ≝
 { sd_positive: ∀x,y:C. zero R ≤ semi_d x y;
   sd_properness: ∀x:C. semi_d x x = 0; 
   sd_triangle_inequality: ∀x,y,z:C. semi_d x z ≤ semi_d x y + semi_d z y
 }.

record is_distance (R:real) (C:Type) (d:C→C→R) : Prop ≝
 { d_semi_distance:> is_semi_distance ? ? d;
   d_properness: ∀x,y:C. d x y = 0 → x=y
 }.

record distance (R:real) (V:vector_space R) : Type ≝
 { d_function:2> V→V→R;
   d_distance_properties: is_distance ? ? d_function
 }.

definition induced_distance_fun ≝
 λR:real.λV:vector_space R.λnorm:norm ? V.
  λf,g:V.norm (f - g).

theorem induced_distance_is_distance:
 ∀R:real.∀V:vector_space R.∀norm:norm ? V.
  is_distance ? ? (induced_distance_fun ? ? norm).
elim daemon.(*
 intros;
 apply mk_is_distance;
  [ apply mk_is_semi_distance;
    [ unfold induced_distance_fun;
      intros;
      apply sn_positive;
      apply n_semi_norm;
      apply (n_norm_properties ? ? norm)
    | unfold induced_distance_fun;
      intros;
      unfold minus;
      rewrite < plus_comm;
      rewrite > opp_inverse;
      apply eq_semi_norm_zero_zero;
      apply n_semi_norm;
      apply (n_norm_properties ? ? norm)
    | unfold induced_distance_fun;
      intros;
      (* ??? *)
      elim daemon
    ]
  | unfold induced_distance_fun;
    intros;
    generalize in match (n_properness ? ? norm ? ? H);
     [ intro;
       (* facile *)
       elim daemon
     | apply (n_norm_properties ? ? norm)
     ]
  ].*)
qed.

definition induced_distance ≝
 λR:real.λV:vector_space R.λnorm:norm ? V.
  mk_distance ? ? (induced_distance_fun ? ? norm)
   (induced_distance_is_distance ? ? norm).

definition tends_to :
 ∀R:real.∀V:vector_space R.∀d:distance ? V.∀f:nat→V.∀l:V.Prop.
apply
  (λR:real.λV:vector_space R.λd:distance ? V.λf:nat→V.λl:V.
    ∀n:nat.∃m:nat.∀j:nat. m ≤ j →
     d (f j) l ≤ inv R (sum_field ? (S n)) ?);
 apply not_eq_sum_field_zero;
 unfold;
 autobatch.
qed.

definition is_cauchy_seq : ∀R:real.\forall V:vector_space R.
\forall d:distance ? V.∀f:nat→V.Prop.
 apply
  (λR:real.λV: vector_space R. \lambda d:distance ? V.
   \lambda f:nat→V.
    ∀m:nat.
     ∃n:nat.∀N. n ≤ N →
      -(inv R (sum_field ? (S m)) ?) ≤ d (f N)  (f n)  ∧
      d (f N)  (f n)≤ inv R (sum_field R (S m)) ?);
 apply not_eq_sum_field_zero;
 unfold;
 autobatch.
qed.

definition is_complete ≝
 λR:real.λV:vector_space R. 
 λd:distance ? V.
  ∀f:nat→V. is_cauchy_seq ? ? d f→
   ex V (λl:V. tends_to ? ? d f l).
