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

(* ********************************************************************** *)
(*                          Progetto FreeScale                            *)
(*                                                                        *)
(*   Sviluppato da: Ing. Cosimo Oliboni, oliboni@cs.unibo.it              *)
(*   Sviluppo: 2008-2010                                                  *)
(*                                                                        *)
(* ********************************************************************** *)

include "common/pts.ma".

(* 

Notation for hint declaration
==============================

The idea is to write a context, with abstraction first, then
recursive calls (let-in) and finally the two equivalent terms.
The context can be empty. Note the ; to begin the second part of
the context (necessary even if the first part is empty). 

 unification hint PREC \coloneq
   ID : TY, ..., ID : TY
   ; ID \equest T, ..., ID \equest T
   \vdash T1 \equiv T2       

With unidoce and some ASCII art it looks like the following:

 unification hint PREC ≔ ID : TY, ..., ID : TY;
    ID ≟ T, ..., ID ≟ T
 (*---------------------*) ⊢
         T1 ≡ T2       

*)
   
(* it seems unbelivable, but it works! *)
notation > "≔ (list0 ( (list1 (ident x) sep , ) opt (: T) ) sep ,) opt (; (list1 (ident U ≟ term 90 V ) sep ,)) ⊢ term 19 Px ≡ term 19 Py"
  with precedence 90
  for @{ ${ fold right 
               @{ ${ default 
                    @{ ${ fold right 
                        @{ 'hint_decl $Px $Py } 
                        rec acc1 @{ let ( ${ident U} : ?) ≝ $V in $acc1} } }
                    @{ 'hint_decl $Px $Py } 
                 }
               } 
               rec acc @{ 
                 ${ fold right @{ $acc } rec acc2 
                      @{ ∀${ident x}:${ default @{ $T } @{ ? } }.$acc2 } } 
               }
       }}.

ndefinition hint_declaration_Type0  ≝  λA:Type[0].λa,b:A.Prop.
ndefinition hint_declaration_Type1  ≝  λA:Type[1].λa,b:A.Prop.
ndefinition hint_declaration_Type2  ≝  λa,b:Type[2].Prop.
ndefinition hint_declaration_CProp0 ≝  λA:CProp[0].λa,b:A.Prop.
ndefinition hint_declaration_CProp1 ≝  λA:CProp[1].λa,b:A.Prop.
ndefinition hint_declaration_CProp2 ≝  λa,b:CProp[2].Prop.
  
interpretation "hint_decl_Type2"  'hint_decl a b = (hint_declaration_Type2 a b).
interpretation "hint_decl_CProp2" 'hint_decl a b = (hint_declaration_CProp2 a b).
interpretation "hint_decl_Type1"  'hint_decl a b = (hint_declaration_Type1 ? a b).
interpretation "hint_decl_CProp1" 'hint_decl a b = (hint_declaration_CProp1 ? a b).
interpretation "hint_decl_CProp0" 'hint_decl a b = (hint_declaration_CProp0 ? a b).
interpretation "hint_decl_Type0"  'hint_decl a b = (hint_declaration_Type0 ? a b).
