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

notation "hvbox(x break ∈ A)" with precedence 65
for @{ 'member_of $x $A }.

interpretation "Member of" 'member_of x A = (mk_member_of ? A x).
 
notation "hvbox(x break ∉ A)" with precedence 65
for @{ 'not_member_of $x $A }.

interpretation "Not member of" 'not_member_of x A = (Not (member_of ? A x)).

definition emptyset : ∀X.set X ≝  λX:Type.λx:X.False.

notation "∅︀" with precedence 100 for @{ 'emptyset }.

interpretation "Emptyset" 'emptyset = (emptyset ?).

definition subset: ∀X. set X → set X → Prop≝ λX.λA,B:set X.∀x. x ∈ A → x ∈ B.

notation "hvbox(A break ⊆ B)" with precedence 65
for @{ 'subset $A $B }.

interpretation "Subset" 'subset A B = (subset ? A B).
 
definition intersection: ∀X. set X → set X → set X ≝ 
 λX.λA,B:set X.λx. x ∈ A ∧ x ∈ B.

notation "hvbox(A break ∩ B)" with precedence 70
for @{ 'intersection $A $B }.

interpretation "Intersection" 'intersection A B = (intersection ? A B).
 
definition union: ∀X. set X → set X → set X ≝ λX.λA,B:set X.λx. x ∈ A ∨ x ∈ B.

notation "hvbox(A break ∪ B)" with precedence 66
for @{ 'union $A $B }.

interpretation "Union" 'union A B = (union ? A B).

definition seq ≝ λX:Type.nat → X.

definition nth ≝  λX.λA:seq X.λi.A i.

notation "hvbox(A \sub i)" with precedence 100
for @{ 'nth $A $i }.

interpretation "nth" 'nth A i = (nth ? A i).

definition countable_union: ∀X. seq (set X) → set X ≝ 
 λX.λA:seq (set X).λx.∃j.x ∈ A \sub j.

notation "∪ \sub (ident i opt (: ty)) B" with precedence 66
for @{ 'big_union ${default @{(λ${ident i}:$ty.$B)} @{(λ${ident i}.$B)}}}.

interpretation "countable_union" 'big_union η.t = (countable_union ? t).  

definition complement: ∀X. set X \to set X ≝ λX.λA:set X.λx. x ∉ A.

notation "A \sup 'c'" with precedence 100
for @{ 'complement $A }.

interpretation "Complement" 'complement A = (complement ? A).
 
definition inverse_image: ∀X,Y.∀f: X → Y.set Y → set X ≝
 λX,Y,f,B,x. f x ∈ B.

notation "hvbox(f \sup (-1))" with precedence 100
for @{ 'finverse $f }.

interpretation "Inverse image" 'finverse f = (inverse_image ? ? f).
