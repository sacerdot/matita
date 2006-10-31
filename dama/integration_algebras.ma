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

record is_algebra (K: field) (V:vector_space K) (mult:V→V→V) (one:V) : Prop
≝
 { (* ring properties *)
   a_ring: is_ring V mult one;
   (* algebra properties *)
   a_associative_left: ∀a,f,g. a * (mult f g) = mult (a * f) g;
   a_associative_right: ∀a,f,g. a * (mult f g) = mult f (a * g)
 }.

record algebra (K: field) (V:vector_space K) : Type \def
 { a_mult: V → V → V;
   a_one: V;
   a_algebra_properties: is_algebra K V a_mult a_one
 }.

interpretation "Algebra product" 'times a b =
 (cic:/matita/integration_algebras/a_mult.con _ _ _ a b).

interpretation "Algebra one" 'one =
 (cic:/matita/integration_algebras/a_one.con _ _ _).

definition ring_of_algebra ≝
 λK.λV:vector_space K.λA:algebra ? V.
  mk_ring V (a_mult ? ? A) (a_one ? ? A)
   (a_ring ? ? ? ? (a_algebra_properties ? ? A)).

coercion cic:/matita/integration_algebras/ring_of_algebra.con.

record is_f_algebra (K) (S:archimedean_riesz_space K) (A:algebra ? S) : Prop
\def 
{ compat_mult_le:
   ∀f,g:S.
    le ? S 0 f → le ? S 0 g → le ? S 0 (a_mult ? ? A f g);
  compat_mult_meet:
   ∀f,g,h:S.
    meet ? S f g = 0 → meet ? S (a_mult ? ? A h f) g = 0
}.

record f_algebra (K:ordered_field_ch0) : Type \def 
{ fa_archimedean_riesz_space:> archimedean_riesz_space K;
  fa_algebra:> algebra ? fa_archimedean_riesz_space;
  fa_f_algebra_properties: is_f_algebra ? fa_archimedean_riesz_space fa_algebra
}.

(* to be proved; see footnote 2 in the paper by Spitters *)
axiom symmetric_a_mult: ∀K.∀A:f_algebra K. symmetric ? (a_mult ? ? A).

record is_integral (K) (A:f_algebra K) (I:Type_OF_f_algebra ? A→K) : Prop
\def
 { i_positive: ∀f:Type_OF_f_algebra ? A. le ? (lattice_OF_f_algebra ? A) 0 f → of_le K 0 (I f);
   i_linear1: ∀f,g:Type_OF_f_algebra ? A. I (f + g) = I f + I g;
   i_linear2: ∀f:A.∀k:K. I (emult ? A k f) = k*(I f)
 }.

(* Here we are avoiding a construction (the quotient space to define
   f=g iff I(|f-g|)=0 *)
record is_integration_f_algebra (K) (A:f_algebra K) (I:Type_OF_f_algebra ? A→K) : Prop
\def
 { ifa_integral: is_integral ? ? I;
   ifa_limit1:
    ∀f:A. tends_to ? (λn.I(meet ? A f ((sum_field K n)*(a_one ? ? A)))) (I f);
   ifa_limit2:
    ∀f:A.
     tends_to ?
      (λn.
        I (meet ? A f
         ((inv ? (sum_field K (S n))
           (not_eq_sum_field_zero K (S n) (le_S_S O n (le_O_n n)))
         ) * (a_one ? ? A)))) 0;
   ifa_quotient_space1:
    ∀f,g:A. f=g → I(absolute_value ? A (f - g)) = 0
 }.
