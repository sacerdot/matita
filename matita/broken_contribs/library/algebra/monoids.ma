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

include "algebra/semigroups.ma".

record PreMonoid : Type ≝
{ pre_semi_group :> PreSemiGroup;
  e              :  pre_semi_group 
}.

interpretation "Monoid unit" 'neutral = (e ?).

record IsMonoid (M:PreMonoid): Prop ≝
 { is_pre_semi_group :> IsSemiGroup M;
   e_is_left_unit    :  is_left_unit M ⅇ;
   e_is_right_unit   :  is_right_unit M ⅇ
 }.

record Monoid : Type ≝
 { pre_monoid :> PreMonoid;
   is_monoid  :> IsMonoid pre_monoid 
 }.

definition SemiGroup_of_Monoid: Monoid → SemiGroup ≝
 λM. mk_SemiGroup ? (is_monoid M).

coercion SemiGroup_of_Monoid nocomposites.

definition is_left_inverse ≝
 λM:PreMonoid.
  λopp: M → M.
   ∀x:M. (opp x)·x = ⅇ.

definition is_right_inverse ≝
 λM:PreMonoid.
  λopp: M → M.
   ∀x:M. x·(opp x) = ⅇ.

theorem is_left_inverse_to_is_right_inverse_to_eq:
 ∀M:Monoid. ∀l,r.
  is_left_inverse M l → is_right_inverse M r → 
   ∀x:M. l x = r x.
 intros;
 lapply (H x) as H2;
 lapply (eq_f ? ? (λy.y·(r x)) ? ? H2) as H3; clear H2;
 rewrite > (op_is_associative ? M) in H3.
 rewrite > H1 in H3;
 rewrite > (e_is_left_unit ? M) in H3;
 rewrite > (e_is_right_unit ? M) in H3;
 assumption.
qed.
