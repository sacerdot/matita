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

set "baseuri" "cic:/matita/integration_algebras/".

include "vector_spaces.ma".

record is_lattice (C:Type) (join,meet:C→C→C) : Prop \def
 { (* abelian semigroup properties *)
   l_comm_j: symmetric ? join;
   l_associative_j: associative ? join;
   l_comm_m: symmetric ? meet;
   l_associative_m: associative ? meet;
   (* other properties *)
   l_adsorb_j_m: ∀f,g. join f (meet f g) = f;
   l_adsorb_m_j: ∀f,g. meet f (join f g) = f
 }.

record lattice (C:Type) : Type \def
 { join: C → C → C;
   meet: C → C → C;
   l_lattice_properties: is_lattice ? join meet
 }.

definition le \def λC:Type.λL:lattice C.λf,g. meet ? L f g = f.

interpretation "Lattice le" 'leq a b =
 (cic:/matita/integration_algebras/le.con _ _ a b).

definition lt \def λC:Type.λL:lattice C.λf,g. le ? L f g ∧ f ≠ g.

interpretation "Lattice lt" 'lt a b =
 (cic:/matita/integration_algebras/lt.con _ _ a b).

definition carrier_of_lattice ≝
 λC:Type.λL:lattice C.C.

record is_riesz_space (K:ordered_field_ch0) (V:vector_space K)
 (L:lattice (Type_OF_vector_space ? V))
: Prop
\def
 { rs_compat_le_plus: ∀f,g,h. le ? L f g → le ? L (f+h) (g+h);
   rs_compat_le_times: ∀a:K.∀f. of_le ? 0 a → le ? L 0 f → le ? L 0 (a*f)
 }.

record riesz_space (K:ordered_field_ch0) : Type \def
 { rs_vector_space:> vector_space K;
   rs_lattice:> lattice rs_vector_space;
   rs_riesz_space_properties: is_riesz_space ? rs_vector_space rs_lattice
 }.

definition absolute_value \def λK.λS:riesz_space K.λf.join ? S f (-f).   

(*CSC: qui la notazione non fa capire!!! *)
definition is_riesz_norm ≝
 λR:real.λV:riesz_space R.λnorm:norm ? V.
  ∀f,g:V. le ? V (absolute_value ? V f) (absolute_value ? V g) →
   of_le R (norm f) (norm g).

record riesz_norm (R:real) (V:riesz_space R) : Type ≝
 { rn_norm:> norm ? V;
   rn_riesz_norm_property: is_riesz_norm ? ? rn_norm
 }.

(*CSC: non fa la chiusura delle coercion verso funclass *)
definition rn_function ≝
 λR:real.λV:riesz_space R.λnorm:riesz_norm ? V.
  n_function ? ? (rn_norm ? ? norm).

coercion cic:/matita/integration_algebras/rn_function.con 1.

(************************** L-SPACES *************************************)

record is_l_space (R:real) (V:riesz_space R) (norm:riesz_norm ? V) : Prop ≝
 { ls_banach: is_complete ? V (induced_distance ? ? norm);
   ls_linear: ∀f,g:V. le ? V 0 f → le ? V 0 g → norm (f+g) = norm f + norm g
 }.

(******************** ARCHIMEDEAN RIESZ SPACES ***************************)

record is_archimedean_riesz_space (K) (S:riesz_space K) : Prop
\def
  { ars_archimedean: ∃u.∀n.∀a.∀p:n > O.
     le ? S
      (absolute_value ? S a)
      ((inv ? (sum_field K n) (not_eq_sum_field_zero ? n p))* u) →
     a = 0
  }.

record archimedean_riesz_space (K:ordered_field_ch0) : Type \def
 { ars_riesz_space:> riesz_space K;
   ars_archimedean_property: is_archimedean_riesz_space ? ars_riesz_space
 }.

record is_integral (K) (R:archimedean_riesz_space K) (I:R→K) : Prop
\def
 { i_positive: ∀f:R. le ? R 0 f → of_le K 0 (I f);
   i_linear1: ∀f,g:R. I (f + g) = I f + I g;
   i_linear2: ∀f:R.∀k:K. I (k*f) = k*(I f)
 }.

definition is_weak_unit ≝
(* This definition is by Spitters. He cites Fremlin 353P, but:
   1. that theorem holds only in f-algebras (as in Spitters, but we are
      defining it on Riesz spaces)
   2. Fremlin proves |x|/\u=0 \to u=0. How do we remove the absolute value?
 λR:real.λV:archimedean_riesz_space R.λunit: V.
  ∀x:V. meet x unit = 0 → u = 0.
  3. Fremlin proves u > 0 implies x /\ u > 0  > 0 for Archimedean spaces
   only. We pick this definition for now.
*) λR:real.λV:archimedean_riesz_space R.λe:V.
    ∀v:V. lt ? V 0 v → lt ? V 0 (meet ? V v e).

(* Here we are avoiding a construction (the quotient space to define
   f=g iff I(|f-g|)=0 *)
record integration_riesz_space (R:real) : Type \def
 { irs_archimedean_riesz_space:> archimedean_riesz_space R;
   irs_unit: irs_archimedean_riesz_space;
   irs_weak_unit: is_weak_unit ? ? irs_unit;
   integral: irs_archimedean_riesz_space → R;
   irs_integral_properties: is_integral ? ? integral;
   irs_limit1:
    ∀f:irs_archimedean_riesz_space.
     tends_to ?
      (λn.integral (meet ? irs_archimedean_riesz_space f
       ((sum_field R n)*irs_unit)))
       (integral f);
   irs_limit2:
    ∀f:irs_archimedean_riesz_space.
     tends_to ?
      (λn.
        integral (meet ? irs_archimedean_riesz_space f
         ((inv ? (sum_field R (S n))
           (not_eq_sum_field_zero R (S n) (le_S_S O n (le_O_n n)))
         ) * irs_unit))) 0;
   irs_quotient_space1:
    ∀f,g:irs_archimedean_riesz_space.
     integral (absolute_value ? irs_archimedean_riesz_space (f - g)) = 0 → f=g
 }.

definition induced_norm_fun ≝
 λR:real.λV:integration_riesz_space R.λf:V.
  integral ? ? (absolute_value ? ? f).

lemma induced_norm_is_norm:
 ∀R:real.∀V:integration_riesz_space R.is_norm ? V (induced_norm_fun ? V).
 intros;
 apply mk_is_norm;
  [ apply mk_is_semi_norm;
     [ unfold induced_norm_fun;
       intros;
       apply i_positive;
       [ apply (irs_integral_properties ? V)
       | (* difficile *)
         elim daemon
       ]
     | intros;
       unfold induced_norm_fun;
       (* facile *)
       elim daemon
     | intros;
       unfold induced_norm_fun;
       (* difficile *)
       elim daemon
     ]
  | intros;
    unfold induced_norm_fun in H;
    apply irs_quotient_space1;
    unfold minus;
    rewrite < plus_comm;
    rewrite < eq_zero_opp_zero;
    rewrite > zero_neutral;
    assumption
  ].
qed.

definition induced_norm ≝
 λR:real.λV:integration_riesz_space R.
  mk_norm ? ? (induced_norm_fun ? V) (induced_norm_is_norm ? V).

lemma is_riesz_norm_induced_norm:
 ∀R:real.∀V:integration_riesz_space R.
  is_riesz_norm ? ? (induced_norm ? V).
 intros;
 unfold is_riesz_norm;
 intros;
 unfold induced_norm;
 simplify;
 unfold induced_norm_fun;
 (* difficile *)
 elim daemon.
qed.

definition induced_riesz_norm ≝
 λR:real.λV:integration_riesz_space R.
  mk_riesz_norm ? ? (induced_norm ? V) (is_riesz_norm_induced_norm ? V).

definition distance_induced_by_integral ≝
 λR:real.λV:integration_riesz_space R.
  induced_distance ? ? (induced_norm R V).

definition is_complete_integration_riesz_space ≝
 λR:real.λV:integration_riesz_space R.
  is_complete ? ? (distance_induced_by_integral ? V).

record complete_integration_riesz_space (R:real) : Type ≝
 { cirz_integration_riesz_space:> integration_riesz_space R;
   cirz_complete_integration_riesz_space_property:
    is_complete_integration_riesz_space ? cirz_integration_riesz_space
 }.

(* now we prove that any complete integration riesz space is an L-space *)

theorem is_l_space_l_space_induced_by_integral:
 ∀R:real.∀V:complete_integration_riesz_space R.
  is_l_space ? ? (induced_riesz_norm ? V).
 intros;
 constructor 1;
  [ apply cirz_complete_integration_riesz_space_property
  | intros;
    unfold induced_riesz_norm;
    simplify;
    unfold induced_norm;
    simplify;
    unfold induced_norm_fun;
    (* difficile *)
    elim daemon
  ].
qed.

(**************************** f-ALGEBRAS ********************************)

record is_algebra (K: field) (V:vector_space K) (mult:V→V→V) (one:V) : Prop
≝
 { (* ring properties *)
   a_ring: is_ring V mult one;
   (* algebra properties *)
   a_associative_left: ∀a,f,g. a * (mult f g) = mult (a * f) g;
   a_associative_right: ∀a,f,g. a * (mult f g) = mult f (a * g)
 }.

record algebra (K: field) (V:vector_space K) (a_one:V) : Type \def
 { a_mult: V → V → V;
   a_algebra_properties: is_algebra ? ? a_mult a_one
 }.

interpretation "Algebra product" 'times a b =
 (cic:/matita/integration_algebras/a_mult.con _ _ _ a b).

definition ring_of_algebra ≝
 λK.λV:vector_space K.λone:V.λA:algebra ? V one.
  mk_ring V (a_mult ? ? ? A) one
   (a_ring ? ? ? ? (a_algebra_properties ? ? ? A)).

coercion cic:/matita/integration_algebras/ring_of_algebra.con.

record is_f_algebra (K) (S:archimedean_riesz_space K) (one: S)
 (A:algebra ? S one) : Prop
\def 
{ compat_mult_le:
   ∀f,g:S.
    le ? S 0 f → le ? S 0 g → le ? S 0 (a_mult ? ? ? A f g);
  compat_mult_meet:
   ∀f,g,h:S.
    meet ? S f g = 0 → meet ? S (a_mult ? ? ? A h f) g = 0
}.

record f_algebra (K:ordered_field_ch0) (R:archimedean_riesz_space K) (one:R) :
Type \def 
{ fa_algebra:> algebra ? R one;
  fa_f_algebra_properties: is_f_algebra ? ? ? fa_algebra
}.

(* to be proved; see footnote 2 in the paper by Spitters *)
axiom symmetric_a_mult:
 ∀K,R,one.∀A:f_algebra K R one. symmetric ? (a_mult ? ? ? A).

record integration_f_algebra (R:real) : Type \def
 { ifa_integration_riesz_space:> integration_riesz_space R;
   ifa_f_algebra:>
    f_algebra ? ifa_integration_riesz_space
     (irs_unit ? ifa_integration_riesz_space)
 }.
