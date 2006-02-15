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

set "baseuri" "cic:/matita/algebra/monoids/".

include "algebra/semigroups.ma".

record PreMonoid : Type ≝
 { magma:> Magma;
   e: magma
 }.

notation < "M" for @{ 'pmmagma $M }.
interpretation "premonoid magma coercion" 'pmmagma M =
 (cic:/matita/algebra/monoids/magma.con M).

record isMonoid (M:PreMonoid) : Prop ≝
 { is_semi_group:> isSemiGroup M;
   e_is_left_unit:
    is_left_unit (mk_SemiGroup ? is_semi_group) (e M);
   e_is_right_unit:
    is_right_unit (mk_SemiGroup ? is_semi_group) (e M)
 }.
 
record Monoid : Type ≝
 { premonoid:> PreMonoid;
   monoid_properties:> isMonoid premonoid 
 }.

notation < "M" for @{ 'semigroup $M }.
interpretation "premonoid coercion" 'premonoid M =
 (cic:/matita/algebra/monoids/premonoid.con M).
 
notation < "M" for @{ 'typeofmonoid $M }.
interpretation "premonoid coercion" 'typeofmonoid M =
 (cic:/matita/algebra/monoids/Type_of_Monoid.con M).
 
notation < "M" for @{ 'magmaofmonoid $M }.
interpretation "premonoid coercion" 'magmaofmonoid M =
 (cic:/matita/algebra/monoids/Magma_of_Monoid.con M).
 
notation "1" with precedence 89
for @{ 'munit }.

interpretation "Monoid unit" 'munit =
 (cic:/matita/algebra/monoids/e.con _).
  
definition is_left_inverse ≝
 λM:Monoid.
  λopp: M → M.
   ∀x:M. (opp x)·x = 1.
   
definition is_right_inverse ≝
 λM:Monoid.
  λopp: M → M.
   ∀x:M. x·(opp x) = 1.

theorem is_left_inverse_to_is_right_inverse_to_eq:
 ∀M:Monoid. ∀l,r.
  is_left_inverse M l → is_right_inverse M r → 
   ∀x:M. l x = r x.
 intros;
 generalize in match (H x); intro;
 generalize in match (eq_f ? ? (λy.y·(r x)) ? ? H2);
 simplify; fold simplify (op M);
 intro; clear H2;
 generalize in match (associative ? (is_semi_group ? (monoid_properties M)));
 intro;
 rewrite > H2 in H3; clear H2;
 rewrite > H1 in H3;
 rewrite > (e_is_left_unit ? (monoid_properties M)) in H3;
 rewrite > (e_is_right_unit ? (monoid_properties M)) in H3;
 assumption.
qed.
