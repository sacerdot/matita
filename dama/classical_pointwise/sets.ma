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



include "nat/nat.ma".
include "logic/connectives.ma".


definition set   ≝   λX:Type.X → Prop.

definition member_of : ∀X.set X → X → Prop≝ λX.λA:set X.λx.A x.

notation "hvbox(x break ∈ A)" with precedence 60
for @{ 'member_of $x $A }.

interpretation "Member of" 'member_of x A =
 (cic:/matita/classical_pointwise/sets/member_of.con _ A x).
 
notation "hvbox(x break ∉ A)" with precedence 60
for @{ 'not_member_of $x $A }.

interpretation "Not member of" 'not_member_of x A =
 (cic:/matita/logic/connectives/Not.con
  (cic:/matita/classical_pointwise/sets/member_of.con _ A x)).

definition emptyset : ∀X.set X ≝  λX:Type.λx:X.False.

notation "∅︀" with precedence 100 for @{ 'emptyset }.

interpretation "Emptyset" 'emptyset =
 (cic:/matita/classical_pointwise/sets/emptyset.con _).

definition subset: ∀X. set X → set X → Prop≝ λX.λA,B:set X.∀x. x ∈ A → x ∈ B.

notation "hvbox(A break ⊆ B)" with precedence 60
for @{ 'subset $A $B }.

interpretation "Subset" 'subset A B =
 (cic:/matita/classical_pointwise/sets/subset.con _ A B).
 
definition intersection: ∀X. set X → set X → set X ≝ 
 λX.λA,B:set X.λx. x ∈ A ∧ x ∈ B.

notation "hvbox(A break ∩ B)" with precedence 70
for @{ 'intersection $A $B }.

interpretation "Intersection" 'intersection A B =
 (cic:/matita/classical_pointwise/sets/intersection.con _ A B).
 
definition union: ∀X. set X → set X → set X ≝ λX.λA,B:set X.λx. x ∈ A ∨ x ∈ B.

notation "hvbox(A break ∪ B)" with precedence 65
for @{ 'union $A $B }.

interpretation "Union" 'union A B =
 (cic:/matita/classical_pointwise/sets/union.con _ A B).

definition seq ≝ λX:Type.nat → X.

definition nth ≝  λX.λA:seq X.λi.A i.

notation "hvbox(A \sub i)" with precedence 100
for @{ 'nth $A $i }.

interpretation "nth" 'nth A i =
 (cic:/matita/classical_pointwise/sets/nth.con _ A i).

definition countable_union: ∀X. seq (set X) → set X ≝ 
 λX.λA:seq (set X).λx.∃j.x ∈ A \sub j.

notation "∪ \sub (ident i opt (: ty)) B" with precedence 65
for @{ 'big_union ${default @{(λ${ident i}:$ty.$B)} @{(λ${ident i}.$B)}}}.

interpretation "countable_union" 'big_union η.t =
 (cic:/matita/classical_pointwise/sets/countable_union.con _ t).  

definition complement: ∀X. set X \to set X ≝ λX.λA:set X.λx. x ∉ A.

notation "A \sup 'c'" with precedence 100
for @{ 'complement $A }.

interpretation "Complement" 'complement A =
 (cic:/matita/classical_pointwise/sets/complement.con _ A).
 
definition inverse_image: ∀X,Y.∀f: X → Y.set Y → set X ≝
 λX,Y,f,B,x. f x ∈ B.

notation "hvbox(f \sup (-1))" with precedence 100
for @{ 'finverse $f }.

interpretation "Inverse image" 'finverse f =
 (cic:/matita/classical_pointwise/sets/inverse_image.con _ _ f).
