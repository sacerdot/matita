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

include "ng_pts.ma".
ndefinition hint_declaration_Type0  ≝  λA:Type[0] .λa,b:A.a.
ndefinition hint_declaration_Type1  ≝  λA:Type[1].λa,b:A.a.
ndefinition hint_declaration_Type2  ≝  λa,b:Type[1].a.
ndefinition hint_declaration_CProp0 ≝  λA:CProp[0].λa,b:A.a.
ndefinition hint_declaration_CProp1 ≝  λA:CProp[1].λa,b:A.a.
ndefinition hint_declaration_CProp2 ≝  λa,b:CProp[1].a.
  
notation > "≔ (list0 (ident x : T )sep ,) ⊢ term 19 Px ≡ term 19 Py"
  with precedence 90
  for @{ ${ fold right @{'hint_decl $Px $Py} rec acc @{ ∀${ident x}:$T.$acc } } }.      

interpretation "hint_decl_Type2"  'hint_decl a b = (hint_declaration_Type2 a b).
interpretation "hint_decl_CProp2" 'hint_decl a b = (hint_declaration_CProp2 a b).
interpretation "hint_decl_Type1"  'hint_decl a b = (hint_declaration_Type1 ? a b).
interpretation "hint_decl_CProp1" 'hint_decl a b = (hint_declaration_CProp1 ? a b).
interpretation "hint_decl_CProp0" 'hint_decl a b = (hint_declaration_CProp0 ? a b).
interpretation "hint_decl_Type0"  'hint_decl a b = (hint_declaration_Type0 ? a b).

naxiom A : Type[0].
naxiom B : Type[0].

ndefinition C ≝ B.
ndefinition D ≝ A.

naxiom f : B → A.

ncoercion pippo : ∀a:B. A ≝ f on _a : B to A.

alias symbol "hint_decl" = "hint_decl_Type1".
unification hint 0 ≔ ⊢ C ≡ B.
unification hint 0 ≔ ⊢ A ≡ D.

naxiom pippo : D → Prop.

nlemma foo : ∀c:C. pippo c. 


