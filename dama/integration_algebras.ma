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

include "reals.ma".

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
  vs_vector_space_properties :> is_vector_space K vs_abelian_group emult
}.

interpretation "Vector space external product" 'times a b =
 (cic:/matita/integration_algebras/emult.con _ _ a b).

record is_semi_norm (R:real) (V: vector_space R)
 (semi_norm:Type_OF_vector_space ? V→R) : Prop
\def
 { sn_positive: ∀x:V. 0 ≤ semi_norm x;
   sn_omogeneous: ∀a:R.∀x:V. semi_norm (a*x) = (abs ? a) * semi_norm x;
   sn_triangle_inequality: ∀x,y:V. semi_norm (x + y) ≤ semi_norm x + semi_norm y
 }.

record is_norm (R:real) (V:vector_space R) (norm:Type_OF_vector_space ? V → R)
 : Prop \def
 { n_semi_norm:> is_semi_norm ? ? norm;
   n_properness: ∀x:V. norm x = 0 → x = 0
 }.

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

record is_archimedean_riesz_space (K) (S:riesz_space K) : Prop
\def
  { ars_archimedean: ∃u.∀n.∀a.∀p:n > O.
     le ? S
      (absolute_value ? S a)
      (emult ? S
        (inv ? (sum_field K n) (not_eq_sum_field_zero ? n p))
        u) →
     a = 0
  }.

record archimedean_riesz_space (K:ordered_field_ch0) : Type \def
 { ars_riesz_space:> riesz_space K;
   ars_archimedean_property: is_archimedean_riesz_space ? ars_riesz_space
 }.

record is_integral (K) (R:archimedean_riesz_space K) (I:Type_OF_archimedean_riesz_space ? R→K) : Prop
\def
 { i_positive: ∀f:R. le ? R 0 f → of_le K 0 (I f);
   i_linear1: ∀f,g:R. I (f + g) = I f + I g;
   i_linear2: ∀f:R.∀k:K. I (emult ? R k f) = k*(I f)
 }.

definition is_weak_unit ≝
(* This definition is by Spitters. He cites Fremlin 353P, but:
   1. that theorem holds only in f-algebras (as in Spitters, but we are
      defining it on Riesz spaces)
   2. Fremlin proves |x|/\u=0 \to u=0. How do we remove the absolute value?
 λR:real.λV:archimedean_riesz_space R.λunit: V.
  ∀x:V. meet x unit = 0 → u = 0.
*) λR:real.λV:archimedean_riesz_space R.λe:V.True.

record integration_riesz_space (R:real) : Type \def
 { irs_archimedean_riesz_space:> archimedean_riesz_space R;
   irs_unit: Type_OF_archimedean_riesz_space ? irs_archimedean_riesz_space;
   irs_weak_unit: is_weak_unit ? ? irs_unit;
   integral: Type_OF_archimedean_riesz_space ? irs_archimedean_riesz_space → R;
   irs_integral_properties: is_integral R irs_archimedean_riesz_space integral;
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
     f=g → integral (absolute_value ? irs_archimedean_riesz_space (f - g)) = 0
 }.

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
   a_algebra_properties: is_algebra K V a_mult a_one
 }.

interpretation "Algebra product" 'times a b =
 (cic:/matita/integration_algebras/a_mult.con _ _ _ a b).

definition ring_of_algebra ≝
 λK.λV:vector_space K.λone:Type_OF_vector_space ? V.λA:algebra ? V one.
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

record f_algebra (K:ordered_field_ch0) (R:archimedean_riesz_space K)
 (one:Type_OF_archimedean_riesz_space ? R) :
Type \def 
{ fa_algebra:> algebra ? R one;
  fa_f_algebra_properties: is_f_algebra ? ? ? fa_algebra
}.

(* to be proved; see footnote 2 in the paper by Spitters *)
axiom symmetric_a_mult:
 ∀K,R,one.∀A:f_algebra K R one. symmetric ? (a_mult ? ? ? A).

(* Here we are avoiding a construction (the quotient space to define
   f=g iff I(|f-g|)=0 *)
record integration_f_algebra (R:real) : Type \def
 { ifa_integration_riesz_space:> integration_riesz_space R;
   ifa_f_algebra:>
    f_algebra ? ifa_integration_riesz_space
     (irs_unit ? ifa_integration_riesz_space)
 }.