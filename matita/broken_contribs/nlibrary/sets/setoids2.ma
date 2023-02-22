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

include "properties/relations2.ma".
include "sets/setoids1.ma".

nrecord setoid2: Type[3] ≝
 { carr2:> Type[2];
   eq2: equivalence_relation2 carr2
 }.

ndefinition setoid2_of_setoid1: setoid1 → setoid2.
 #s; @ (carr1 s); @ (carr1 s) (eq1 ?)
  [ napply refl1
  | napply sym1
  | napply trans1]
nqed.

(*ncoercion setoid1_of_setoid : ∀s:setoid. setoid1 ≝ setoid1_of_setoid
 on _s: setoid to setoid1.*)
(*prefer coercion Type_OF_setoid.*)

interpretation "setoid2 eq" 'eq t x y = (eq_rel2 ? (eq2 t) x y).
interpretation "setoid1 eq" 'eq t x y = (eq_rel1 ? (eq1 t) x y).
interpretation "setoid eq" 'eq t x y = (eq_rel ? (eq t) x y).

(*
notation > "hvbox(a break =_12 b)" non associative with precedence 45
for @{ eq_rel2 (carr2 (setoid2_of_setoid1 ?)) (eq2 (setoid2_of_setoid1 ?)) $a $b }.
*)
notation > "hvbox(a break =_0 b)" non associative with precedence 45
for @{ eq_rel ? (eq0 ?) $a $b }.
notation > "hvbox(a break =_1 b)" non associative with precedence 45
for @{ eq_rel1 ? (eq1 ?) $a $b }.
notation > "hvbox(a break =_2 b)" non associative with precedence 45
for @{ eq_rel2 ? (eq2 ?) $a $b }.

interpretation "setoid2 symmetry" 'invert r = (sym2 ???? r).
interpretation "setoid1 symmetry" 'invert r = (sym1 ???? r).
interpretation "setoid symmetry" 'invert r = (sym ???? r).
notation ".= r" with precedence 55 for @{'trans $r}.
interpretation "trans2" 'trans r = (trans2 ????? r).
interpretation "trans1" 'trans r = (trans1 ????? r).
interpretation "trans" 'trans r = (trans ????? r).

nrecord unary_morphism2 (A,B: setoid2) : Type[2] ≝
 { fun12:1> A → B;
   prop12: ∀a,a'. eq2 ? a a' → eq2 ? (fun12 a) (fun12 a')
 }.

nrecord binary_morphism2 (A,B,C:setoid2) : Type[2] ≝
 { fun22:2> A → B → C;
   prop22: ∀a,a',b,b'. eq2 ? a a' → eq2 ? b b' → eq2 ? (fun22 a b) (fun22 a' b')
 }.

interpretation "prop12" 'prop1 c = (prop12 ????? c).
interpretation "prop22" 'prop2 l r = (prop22 ???????? l r).
interpretation "refl2" 'refl = (refl2 ???).
