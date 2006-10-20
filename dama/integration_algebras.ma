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

include "higher_order_defs/functions.ma".
include "nat/nat.ma".
include "nat/orders.ma".

definition left_neutral \def λC,op.λe:C. ∀x:C. op e x = x.

definition right_neutral \def λC,op. λe:C. ∀x:C. op x e=x.

definition left_inverse \def λC,op.λe:C.λinv:C→C. ∀x:C. op (inv x) x = e.

definition right_inverse \def λC,op.λe:C.λ inv: C→ C. ∀x:C. op x (inv x)=e. 

definition distributive_left ≝
 λA:Type.λf:A→A→A.λg:A→A→A.
  ∀x,y,z. f x (g y z) = g (f x y) (f x z).

definition distributive_right ≝
 λA:Type.λf:A→A→A.λg:A→A→A.
  ∀x,y,z. f (g x y) z = g (f x z) (f y z).

record is_abelian_group (C:Type) (plus:C→C→C) (zero:C) (opp:C→C) : Prop \def
 { (* abelian additive semigroup properties *)
    plus_assoc: associative ? plus;
    plus_comm: symmetric ? plus;
    (* additive monoid properties *)
    zero_neutral: left_neutral ? plus zero;
    (* additive group properties *)
    opp_inverse: left_inverse ? plus zero opp
 }.

record is_ring (C:Type) (plus:C→C→C) (mult:C→C→C) (zero:C) (opp:C→C) : Prop
≝
 { (* abelian group properties *)
    abelian_group:> is_abelian_group ? plus zero opp;
    (* multiplicative semigroup properties *)
    mult_assoc: associative ? mult;
    (* ring properties *)
    mult_plus_distr_left: distributive_left C mult plus;
    mult_plus_distr_right: distributive_right C mult plus
 }.
 
record ring : Type \def
 { r_carrier:> Type;
   r_plus: r_carrier → r_carrier → r_carrier;
   r_mult: r_carrier → r_carrier → r_carrier;
   r_zero: r_carrier;
   r_opp: r_carrier → r_carrier;
   r_ring_properties:> is_ring ? r_plus r_mult r_zero r_opp
 }.

notation "0" with precedence 89
for @{ 'zero }.

interpretation "Ring zero" 'zero =
 (cic:/matita/integration_algebras/r_zero.con _).

interpretation "Ring plus" 'plus a b =
 (cic:/matita/integration_algebras/r_plus.con _ a b).

interpretation "Ring mult" 'times a b =
 (cic:/matita/integration_algebras/r_mult.con _ a b).

interpretation "Ring opp" 'uminus a =
 (cic:/matita/integration_algebras/r_opp.con _ a).

lemma eq_mult_zero_x_zero: ∀R:ring.∀x:R.0*x=0.
 intros;
 generalize in match (zero_neutral ? ? ? ? R 0); intro;
 generalize in match (eq_f ? ? (λy.y*x) ? ? H); intro; clear H;
 rewrite > (mult_plus_distr_right ? ? ? ? ? R) in H1;
 generalize in match (eq_f ? ? (λy.-(0*x)+y) ? ? H1); intro; clear H1;
 rewrite < (plus_assoc ? ? ? ? R) in H;
 rewrite > (opp_inverse ? ? ? ? R) in H;
 rewrite > (zero_neutral ? ? ? ? R) in H;
 assumption.
qed.

lemma eq_mult_x_zero_zero: ∀R:ring.∀x:R.x*0=0.
intros;
generalize in match (zero_neutral ? ? ? ? R 0);
intro;
generalize in match (eq_f ? ? (\lambda y.x*y) ? ? H); intro; clear H;
rewrite > (mult_plus_distr_left ? ? ? ? ? R) in H1;
generalize in match (eq_f ? ? (\lambda y. (-(x*0)) +y) ? ? H1);intro;
clear H1;
rewrite < (plus_assoc ? ? ? ? R) in H;
rewrite > (opp_inverse ? ? ? ? R) in H;
rewrite > (zero_neutral ? ? ? ? R) in H;
assumption.


record is_field (C:Type) (plus:C→C→C) (mult:C→C→C) (zero,one:C) (opp:C→C)
 (inv:∀x:C.x ≠ zero →C)  : Prop
≝
 {  (* ring properties *)
    ring_properties:> is_ring ? plus mult zero opp;
    (* multiplicative abelian properties *)
    mult_comm: symmetric ? mult;
    (* multiplicative monoid properties *)
    one_neutral: left_neutral ? mult one;
    (* multiplicative group properties *)
    inv_inverse: ∀x.∀p: x ≠ zero. mult (inv x p) x = one;
    (* integral domain *)
    not_eq_zero_one: zero ≠ one
 }.

lemma cancellationlaw: \forall R:ring. \forall x,y,z:R. 
(x+y=x+z) \to (y=z). 
intros;
generalize in match (eq_f ? ? (\lambda a. (-x +a)) ? ? H);
intros; clear H;
rewrite < (plus_assoc ? ? ? ? R) in H1;
rewrite < (plus_assoc ? ? ? ? R) in H1;
rewrite > (opp_inverse ? ? ? ? R) in H1;
rewrite > (zero_neutral ? ? ? ? R) in H1;
rewrite > (zero_neutral ? ? ? ? R) in H1;
assumption.
qed.


lemma opp_opp: \forall R:ring. \forall x:R. (-(-x))=x.
intros; 
apply (cancellationlaw ? (-x) ? ?); 
rewrite  > (opp_inverse ? ? ? ? R (x)); 
rewrite > (plus_comm ? ? ? ? R);
rewrite > (opp_inverse ? ? ? ? R);
reflexivity.
qed.




let rec sum (C:Type) (plus:C→C→C) (zero,one:C) (n:nat) on n  ≝
 match n with
  [ O ⇒ zero
  | (S m) ⇒ plus one (sum C plus zero one m)
  ].

record field : Type \def
 { f_ring:> ring;
   one: f_ring;
   inv: ∀x:f_ring. x ≠ 0 → f_ring;
   field_properties:>
    is_field ? (r_plus f_ring) (r_mult f_ring) (r_zero f_ring) one
     (r_opp f_ring) inv
 }.

definition sum_field ≝
 λF:field. sum ? (r_plus F) (r_zero F) (one F).
 
notation "1" with precedence 89
for @{ 'one }.

interpretation "Field one" 'one =
 (cic:/matita/integration_algebras/one.con _).

record is_ordered_field_ch0 (C:Type) (plus,mult:C→C→C) (zero,one:C) (opp:C→C)
 (inv:∀x:C.x ≠ zero → C) (le:C→C→Prop) : Prop \def
 { (* field properties *)
   of_is_field:> is_field C plus mult zero one opp inv;
   of_mult_compat: ∀a,b. le zero a → le zero b → le zero (mult a b);
   of_plus_compat: ∀a,b,c. le a b → le (plus a c) (plus b c);
   of_weak_tricotomy : ∀a,b. a≠b → le a b ∨ le b a;
   (* 0 characteristics *)
   of_char0: ∀n. n > O → sum ? plus zero one n ≠ zero
 }.
 
record ordered_field_ch0 : Type \def
 { of_field:> field;
   of_le: of_field → of_field → Prop;
   of_ordered_field_properties:>
    is_ordered_field_ch0 ? (r_plus of_field) (r_mult of_field) (r_zero of_field)
     (one of_field) (r_opp of_field) (inv of_field) of_le
 }.

interpretation "Ordered field le" 'leq a b =
 (cic:/matita/integration_algebras/of_le.con _ a b).
 
definition lt \def λF:ordered_field_ch0.λa,b:F.a ≤ b ∧ a ≠ b.

interpretation "Ordered field lt" 'lt a b =
 (cic:/matita/integration_algebras/lt.con _ a b).

(*incompleto
lemma le_zero_x_to_le_opp_x_zero: ∀F:ordered_field_ch0.∀x:F. 0 ≤ x → -x ≤ 0.
intros;
 generalize in match (of_plus_compat ? ? ? ? ? ? ? ? F ? ? (-x) H); intro;
 rewrite > (zero_neutral ? ? ? ? F) in H1;
 rewrite > (plus_comm  ? ? ?  ? F) in H1;
 rewrite > (opp_inverse ? ? ? ? F) in H1;
 
 assumption.
qed.*)

axiom le_x_zero_to_le_zero_opp_x: ∀F:ordered_field_ch0.∀x:F. x ≤ 0 → 0 ≤ -x.
(* intros;
 generalize in match (of_plus_compat ? ? ? ? ? ? ? ? F ? ? (-x) H); intro;
 rewrite > (zero_neutral ? ? ? ? F) in H1;
 rewrite > (plus_comm ? ? ? ? F) in H1;
 rewrite > (opp_inverse ? ? ? ? F) in H1;
 assumption.
qed.*)

(*
lemma eq_opp_x_times_opp_one_x: ∀F:ordered_field_ch0.∀x:F.-x = -1*x.
 intros;
 
lemma not_eq_x_zero_to_lt_zero_mult_x_x:
 ∀F:ordered_field_ch0.∀x:F. x ≠ 0 → 0 < x * x.
 intros;
 elim (of_weak_tricotomy ? ? ? ? ? ? ? ? F ? ? H);
  [ generalize in match (le_x_zero_to_le_zero_opp_x F ? H1); intro;
    generalize in match (of_mult_compat ? ? ? ? ? ? ? ?  F ? ? H2 H2); intro;
*)  

axiom not_eq_sum_field_zero: ∀F,n. n > O → sum_field F n ≠ 0.

record is_vector_space (K: field) (C:Type) (plus:C→C→C) (zero:C) (opp:C→C)
 (emult:K→C→C) : Prop
≝
 { (* abelian group properties *)
   vs_abelian_group: is_abelian_group ? plus zero opp;
   (* other properties *)
   vs_nilpotent: ∀v. emult 0 v = zero;
   vs_neutral: ∀v. emult 1 v = v;
   vs_distributive: ∀a,b,v. emult (a + b) v = plus (emult a v) (emult b v);
   vs_associative: ∀a,b,v. emult (a * b) v = emult a (emult b v)
 }.

record vector_space : Type \def
{vs_ :


}
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

(* This should be a let-in field of the riesz_space!!! *)
definition le_ \def λC.λmeet:C→C→C.λf,g. meet f g = f.

record is_riesz_space (K:ordered_field_ch0) (C:Type) (plus:C→C→C) (zero:C)
 (opp:C→C) (emult:K→C→C) (join,meet:C→C→C) : Prop \def
 { (* vector space properties *)
   rs_vector_space: is_vector_space K C plus zero opp emult;
   (* lattice properties *)
   rs_lattice: is_lattice C join meet;
   (* other properties *)
   rs_compat_le_plus: ∀f,g,h. le_ ? meet f g → le_ ? meet (plus f h) (plus g h);
   rs_compat_le_times: ∀a,f. 0≤a → le_ ? meet zero f → le_ ? meet zero (emult a f)  
 }.
 
definition absolute_value \def λC:Type.λopp.λjoin:C→C→C.λf.join f (opp f).   

record is_archimedean_riesz_space (K:ordered_field_ch0) (C:Type) (plus:C→C→C)
 (zero:C) (opp:C→C) (emult:K→C→C) (join,meet:C→C→C)
 :Prop \def
  { ars_riesz_space: is_riesz_space ? ? plus zero opp emult join meet;
    ars_archimedean: ∃u.∀n,a.∀p:n > O.
     le_ C meet (absolute_value ? opp join a)
      (emult (inv K (sum_field K n) (not_eq_sum_field_zero K n p)) u) →
     a = zero
  }.

record is_algebra (K: field) (C:Type) (plus:C→C→C) (zero:C) (opp:C→C)
 (emult:K→C→C) (mult:C→C→C) : Prop
≝
 { (* vector space properties *)
   a_vector_space_properties: is_vector_space ? ? plus zero opp emult;
   (* ring properties *)
   a_ring: is_ring ? plus mult zero opp;
   (* algebra properties *)
   a_associative_left: ∀a,f,g. emult a (mult f g) = mult (emult a f) g;
   a_associative_right: ∀a,f,g. emult a (mult f g) = mult f (emult a g)
 }.
 
 
record is_f_algebra (K: ordered_field_ch0) (C:Type) (plus: C\to C \to C) 
(zero:C) (opp: C \to C) (emult: Type_OF_ordered_field_ch0 K\to C\to C) (mult: C\to C\to C) 
(join,meet: C\to C\to C) : Prop
\def 
{ archimedean_riesz_properties:> is_archimedean_riesz_space K C
 plus zero opp emult join meet ;          
algebra_properties:> is_algebra ? ? plus zero opp emult mult;
compat_mult_le: \forall f,g: C. le_ ? meet zero f \to le_ ? meet zero g \to
 le_ ? meet zero (mult f g);
compat_mult_meet: \forall f,g,h. meet f g = zero \to meet (mult h f) g = zero
}.

record f_algebra : Type \def 
{

}
