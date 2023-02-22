(**************************************************************************)
(*       ___	                                                            *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||       A.Asperti, C.Sacerdoti Coen,                          *)
(*      ||A||       E.Tassi, S.Zacchiroli                                 *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU Lesser General Public License Version 2.1         *)
(*                                                                        *)
(**************************************************************************)

include "Plogic/connectives.ma".

ndefinition relation : Type \to Type
≝ λA:Type.A→A→Prop. 

nrecord relation (A:Type) : Type ≝
{fun:2> A→A→Prop}.

ndefinition reflexive: ∀A:Type.∀R :relation A.Prop
≝ λA.λR.∀x:A.R x x.

ndefinition symmetric: ∀A:Type.∀R: relation A.Prop
≝ λA.λR.∀x,y:A.R x y → R y x.

ndefinition transitive: ∀A:Type.∀R:relation A.Prop
≝ λA.λR.∀x,y,z:A.R x y → R y z → R x z.

ndefinition irreflexive: ∀A:Type.∀R:relation A.Prop
≝ λA.λR.∀x:A.¬(R x x).

ndefinition cotransitive: ∀A:Type.∀R:relation A.Prop
≝ λA.λR.∀x,y:A.R x y → ∀z:A. R x z ∨ R z y.

ndefinition tight_apart: ∀A:Type.∀eq,ap:relation A.Prop
≝ λA.λeq,ap.∀x,y:A. (¬(ap x y) → eq x y) ∧
(eq x y → ¬(ap x y)).

ndefinition antisymmetric: ∀A:Type.∀R:relation A.Prop
≝ λA.λR.∀x,y:A. R x y → ¬(R y x).


