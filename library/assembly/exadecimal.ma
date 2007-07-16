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

set "baseuri" "cic:/matita/assembly/exadecimal/".

include "extra.ma".

inductive exadecimal : Type ≝
   x0: exadecimal
 | x1: exadecimal
 | x2: exadecimal
 | x3: exadecimal
 | x4: exadecimal
 | x5: exadecimal
 | x6: exadecimal
 | x7: exadecimal
 | x8: exadecimal
 | x9: exadecimal
 | xA: exadecimal
 | xB: exadecimal
 | xC: exadecimal
 | xD: exadecimal
 | xE: exadecimal
 | xF: exadecimal.

definition eqex ≝
 λb1,b2.
  match b1 with
   [ x0 ⇒
       match b2 with
        [ x0 ⇒ true  | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false
        | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
        | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false
        | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ] 
   | x1 ⇒
       match b2 with
        [ x0 ⇒ false | x1 ⇒ true  | x2 ⇒ false | x3 ⇒ false
        | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
        | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false
        | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ] 
   | x2 ⇒
       match b2 with
        [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ true  | x3 ⇒ false
        | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
        | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false
        | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ] 
   | x3 ⇒
       match b2 with
        [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ true 
        | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
        | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false
        | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ] 
   | x4 ⇒
       match b2 with
        [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false
        | x4 ⇒ true  | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
        | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false
        | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ] 
   | x5 ⇒
       match b2 with
        [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false
        | x4 ⇒ false | x5 ⇒ true  | x6 ⇒ false | x7 ⇒ false
        | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false
        | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ] 
   | x6 ⇒
       match b2 with
        [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false
        | x4 ⇒ false | x5 ⇒ false | x6 ⇒ true  | x7 ⇒ false
        | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false
        | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ] 
   | x7 ⇒
       match b2 with
        [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false
        | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ true 
        | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false
        | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ] 
   | x8 ⇒
       match b2 with
        [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false
        | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
        | x8 ⇒ true  | x9 ⇒ false | xA ⇒ false | xB ⇒ false
        | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ] 
   | x9 ⇒
       match b2 with
        [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false
        | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
        | x8 ⇒ false | x9 ⇒ true  | xA ⇒ false | xB ⇒ false
        | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ] 
   | xA ⇒
       match b2 with
        [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false
        | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
        | x8 ⇒ false | x9 ⇒ false | xA ⇒ true  | xB ⇒ false
        | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ] 
   | xB ⇒
       match b2 with
        [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false
        | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
        | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ true 
        | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ] 
   | xC ⇒
       match b2 with
        [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false
        | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
        | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false
        | xC ⇒ true  | xD ⇒ false | xE ⇒ false | xF ⇒ false ] 
   | xD ⇒
       match b2 with
        [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false
        | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
        | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false
        | xC ⇒ false | xD ⇒ true  | xE ⇒ false | xF ⇒ false ] 
   | xE ⇒
       match b2 with
        [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false
        | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
        | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false
        | xC ⇒ false | xD ⇒ false | xE ⇒ true  | xF ⇒ false ] 
   | xF ⇒
       match b2 with
        [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false
        | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
        | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false
        | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ true  ]]. 

definition plusex ≝
 λb1,b2,c.
  match c with
   [ true ⇒
      match b1 with
       [ x0 ⇒
           match b2 with
            [ x0 ⇒ couple exadecimal bool x1 false
            | x1 ⇒ couple exadecimal bool x2 false
            | x2 ⇒ couple exadecimal bool x3 false
            | x3 ⇒ couple exadecimal bool x4 false
            | x4 ⇒ couple exadecimal bool x5 false
            | x5 ⇒ couple exadecimal bool x6 false
            | x6 ⇒ couple exadecimal bool x7 false
            | x7 ⇒ couple exadecimal bool x8 false
            | x8 ⇒ couple exadecimal bool x9 false
            | x9 ⇒ couple exadecimal bool xA false
            | xA ⇒ couple exadecimal bool xB false
            | xB ⇒ couple exadecimal bool xC false
            | xC ⇒ couple exadecimal bool xD false
            | xD ⇒ couple exadecimal bool xE false
            | xE ⇒ couple exadecimal bool xF false
            | xF ⇒ couple exadecimal bool x0 true ] 
       | x1 ⇒
           match b2 with
            [ x0 ⇒ couple exadecimal bool x2 false
            | x1 ⇒ couple exadecimal bool x3 false
            | x2 ⇒ couple exadecimal bool x4 false
            | x3 ⇒ couple exadecimal bool x5 false
            | x4 ⇒ couple exadecimal bool x6 false
            | x5 ⇒ couple exadecimal bool x7 false
            | x6 ⇒ couple exadecimal bool x8 false
            | x7 ⇒ couple exadecimal bool x9 false
            | x8 ⇒ couple exadecimal bool xA false
            | x9 ⇒ couple exadecimal bool xB false
            | xA ⇒ couple exadecimal bool xC false
            | xB ⇒ couple exadecimal bool xD false
            | xC ⇒ couple exadecimal bool xE false
            | xD ⇒ couple exadecimal bool xF false
            | xE ⇒ couple exadecimal bool x0 true
            | xF ⇒ couple exadecimal bool x1 true ] 
       | x2 ⇒
           match b2 with
            [ x0 ⇒ couple exadecimal bool x3 false
            | x1 ⇒ couple exadecimal bool x4 false
            | x2 ⇒ couple exadecimal bool x5 false
            | x3 ⇒ couple exadecimal bool x6 false
            | x4 ⇒ couple exadecimal bool x7 false
            | x5 ⇒ couple exadecimal bool x8 false
            | x6 ⇒ couple exadecimal bool x9 false
            | x7 ⇒ couple exadecimal bool xA false
            | x8 ⇒ couple exadecimal bool xB false
            | x9 ⇒ couple exadecimal bool xC false
            | xA ⇒ couple exadecimal bool xD false
            | xB ⇒ couple exadecimal bool xE false
            | xC ⇒ couple exadecimal bool xF false
            | xD ⇒ couple exadecimal bool x0 true
            | xE ⇒ couple exadecimal bool x1 true
            | xF ⇒ couple exadecimal bool x2 true ] 
       | x3 ⇒
           match b2 with
            [ x0 ⇒ couple exadecimal bool x4 false
            | x1 ⇒ couple exadecimal bool x5 false
            | x2 ⇒ couple exadecimal bool x6 false
            | x3 ⇒ couple exadecimal bool x7 false
            | x4 ⇒ couple exadecimal bool x8 false
            | x5 ⇒ couple exadecimal bool x9 false
            | x6 ⇒ couple exadecimal bool xA false
            | x7 ⇒ couple exadecimal bool xB false
            | x8 ⇒ couple exadecimal bool xC false
            | x9 ⇒ couple exadecimal bool xD false
            | xA ⇒ couple exadecimal bool xE false
            | xB ⇒ couple exadecimal bool xF false
            | xC ⇒ couple exadecimal bool x0 true
            | xD ⇒ couple exadecimal bool x1 true
            | xE ⇒ couple exadecimal bool x2 true
            | xF ⇒ couple exadecimal bool x3 true ] 
       | x4 ⇒
           match b2 with
            [ x0 ⇒ couple exadecimal bool x5 false
            | x1 ⇒ couple exadecimal bool x6 false
            | x2 ⇒ couple exadecimal bool x7 false
            | x3 ⇒ couple exadecimal bool x8 false
            | x4 ⇒ couple exadecimal bool x9 false
            | x5 ⇒ couple exadecimal bool xA false
            | x6 ⇒ couple exadecimal bool xB false
            | x7 ⇒ couple exadecimal bool xC false
            | x8 ⇒ couple exadecimal bool xD false
            | x9 ⇒ couple exadecimal bool xE false
            | xA ⇒ couple exadecimal bool xF false
            | xB ⇒ couple exadecimal bool x0 true
            | xC ⇒ couple exadecimal bool x1 true
            | xD ⇒ couple exadecimal bool x2 true
            | xE ⇒ couple exadecimal bool x3 true
            | xF ⇒ couple exadecimal bool x4 true ] 
       | x5 ⇒
           match b2 with
            [ x0 ⇒ couple exadecimal bool x6 false
            | x1 ⇒ couple exadecimal bool x7 false
            | x2 ⇒ couple exadecimal bool x8 false
            | x3 ⇒ couple exadecimal bool x9 false
            | x4 ⇒ couple exadecimal bool xA false
            | x5 ⇒ couple exadecimal bool xB false
            | x6 ⇒ couple exadecimal bool xC false
            | x7 ⇒ couple exadecimal bool xD false
            | x8 ⇒ couple exadecimal bool xE false
            | x9 ⇒ couple exadecimal bool xF false
            | xA ⇒ couple exadecimal bool x0 true
            | xB ⇒ couple exadecimal bool x1 true
            | xC ⇒ couple exadecimal bool x2 true
            | xD ⇒ couple exadecimal bool x3 true
            | xE ⇒ couple exadecimal bool x4 true
            | xF ⇒ couple exadecimal bool x5 true ] 
       | x6 ⇒
           match b2 with
            [ x0 ⇒ couple exadecimal bool x7 false
            | x1 ⇒ couple exadecimal bool x8 false
            | x2 ⇒ couple exadecimal bool x9 false
            | x3 ⇒ couple exadecimal bool xA false
            | x4 ⇒ couple exadecimal bool xB false
            | x5 ⇒ couple exadecimal bool xC false
            | x6 ⇒ couple exadecimal bool xD false
            | x7 ⇒ couple exadecimal bool xE false
            | x8 ⇒ couple exadecimal bool xF false
            | x9 ⇒ couple exadecimal bool x0 true
            | xA ⇒ couple exadecimal bool x1 true
            | xB ⇒ couple exadecimal bool x2 true
            | xC ⇒ couple exadecimal bool x3 true
            | xD ⇒ couple exadecimal bool x4 true
            | xE ⇒ couple exadecimal bool x5 true
            | xF ⇒ couple exadecimal bool x6 true ] 
       | x7 ⇒
           match b2 with
            [ x0 ⇒ couple exadecimal bool x8 false
            | x1 ⇒ couple exadecimal bool x9 false
            | x2 ⇒ couple exadecimal bool xA false
            | x3 ⇒ couple exadecimal bool xB false
            | x4 ⇒ couple exadecimal bool xC false
            | x5 ⇒ couple exadecimal bool xD false
            | x6 ⇒ couple exadecimal bool xE false
            | x7 ⇒ couple exadecimal bool xF false
            | x8 ⇒ couple exadecimal bool x0 true
            | x9 ⇒ couple exadecimal bool x1 true
            | xA ⇒ couple exadecimal bool x2 true
            | xB ⇒ couple exadecimal bool x3 true
            | xC ⇒ couple exadecimal bool x4 true
            | xD ⇒ couple exadecimal bool x5 true
            | xE ⇒ couple exadecimal bool x6 true
            | xF ⇒ couple exadecimal bool x7 true ] 
       | x8 ⇒
           match b2 with
            [ x0 ⇒ couple exadecimal bool x9 false
            | x1 ⇒ couple exadecimal bool xA false
            | x2 ⇒ couple exadecimal bool xB false
            | x3 ⇒ couple exadecimal bool xC false
            | x4 ⇒ couple exadecimal bool xD false
            | x5 ⇒ couple exadecimal bool xE false
            | x6 ⇒ couple exadecimal bool xF false
            | x7 ⇒ couple exadecimal bool x0 true
            | x8 ⇒ couple exadecimal bool x1 true
            | x9 ⇒ couple exadecimal bool x2 true
            | xA ⇒ couple exadecimal bool x3 true
            | xB ⇒ couple exadecimal bool x4 true
            | xC ⇒ couple exadecimal bool x5 true
            | xD ⇒ couple exadecimal bool x6 true
            | xE ⇒ couple exadecimal bool x7 true
            | xF ⇒ couple exadecimal bool x8 true ] 
       | x9 ⇒
           match b2 with
            [ x0 ⇒ couple exadecimal bool xA false
            | x1 ⇒ couple exadecimal bool xB false
            | x2 ⇒ couple exadecimal bool xC false
            | x3 ⇒ couple exadecimal bool xD false
            | x4 ⇒ couple exadecimal bool xE false
            | x5 ⇒ couple exadecimal bool xF false
            | x6 ⇒ couple exadecimal bool x0 true
            | x7 ⇒ couple exadecimal bool x1 true
            | x8 ⇒ couple exadecimal bool x2 true
            | x9 ⇒ couple exadecimal bool x3 true
            | xA ⇒ couple exadecimal bool x4 true
            | xB ⇒ couple exadecimal bool x5 true
            | xC ⇒ couple exadecimal bool x6 true
            | xD ⇒ couple exadecimal bool x7 true
            | xE ⇒ couple exadecimal bool x8 true
            | xF ⇒ couple exadecimal bool x9 true ] 
       | xA ⇒
           match b2 with
            [ x0 ⇒ couple exadecimal bool xB false
            | x1 ⇒ couple exadecimal bool xC false
            | x2 ⇒ couple exadecimal bool xD false
            | x3 ⇒ couple exadecimal bool xE false
            | x4 ⇒ couple exadecimal bool xF false
            | x5 ⇒ couple exadecimal bool x0 true
            | x6 ⇒ couple exadecimal bool x1 true
            | x7 ⇒ couple exadecimal bool x2 true
            | x8 ⇒ couple exadecimal bool x3 true
            | x9 ⇒ couple exadecimal bool x4 true
            | xA ⇒ couple exadecimal bool x5 true
            | xB ⇒ couple exadecimal bool x6 true
            | xC ⇒ couple exadecimal bool x7 true
            | xD ⇒ couple exadecimal bool x8 true
            | xE ⇒ couple exadecimal bool x9 true
            | xF ⇒ couple exadecimal bool xA true ] 
       | xB ⇒
           match b2 with
            [ x0 ⇒ couple exadecimal bool xC false
            | x1 ⇒ couple exadecimal bool xD false
            | x2 ⇒ couple exadecimal bool xE false
            | x3 ⇒ couple exadecimal bool xF false
            | x4 ⇒ couple exadecimal bool x0 true
            | x5 ⇒ couple exadecimal bool x1 true
            | x6 ⇒ couple exadecimal bool x2 true
            | x7 ⇒ couple exadecimal bool x3 true
            | x8 ⇒ couple exadecimal bool x4 true
            | x9 ⇒ couple exadecimal bool x5 true
            | xA ⇒ couple exadecimal bool x6 true
            | xB ⇒ couple exadecimal bool x7 true
            | xC ⇒ couple exadecimal bool x8 true
            | xD ⇒ couple exadecimal bool x9 true
            | xE ⇒ couple exadecimal bool xA true
            | xF ⇒ couple exadecimal bool xB true ] 
       | xC ⇒
           match b2 with
            [ x0 ⇒ couple exadecimal bool xD false
            | x1 ⇒ couple exadecimal bool xE false
            | x2 ⇒ couple exadecimal bool xF false
            | x3 ⇒ couple exadecimal bool x0 true
            | x4 ⇒ couple exadecimal bool x1 true
            | x5 ⇒ couple exadecimal bool x2 true
            | x6 ⇒ couple exadecimal bool x3 true
            | x7 ⇒ couple exadecimal bool x4 true
            | x8 ⇒ couple exadecimal bool x5 true
            | x9 ⇒ couple exadecimal bool x6 true
            | xA ⇒ couple exadecimal bool x7 true
            | xB ⇒ couple exadecimal bool x8 true
            | xC ⇒ couple exadecimal bool x9 true
            | xD ⇒ couple exadecimal bool xA true
            | xE ⇒ couple exadecimal bool xB true
            | xF ⇒ couple exadecimal bool xC true ] 
       | xD ⇒
           match b2 with
            [ x0 ⇒ couple exadecimal bool xE false
            | x1 ⇒ couple exadecimal bool xF false
            | x2 ⇒ couple exadecimal bool x0 true
            | x3 ⇒ couple exadecimal bool x1 true
            | x4 ⇒ couple exadecimal bool x2 true
            | x5 ⇒ couple exadecimal bool x3 true
            | x6 ⇒ couple exadecimal bool x4 true
            | x7 ⇒ couple exadecimal bool x5 true
            | x8 ⇒ couple exadecimal bool x6 true
            | x9 ⇒ couple exadecimal bool x7 true
            | xA ⇒ couple exadecimal bool x8 true
            | xB ⇒ couple exadecimal bool x9 true
            | xC ⇒ couple exadecimal bool xA true
            | xD ⇒ couple exadecimal bool xB true
            | xE ⇒ couple exadecimal bool xC true
            | xF ⇒ couple exadecimal bool xD true ] 
       | xE ⇒
           match b2 with
            [ x0 ⇒ couple exadecimal bool xF false
            | x1 ⇒ couple exadecimal bool x0 true
            | x2 ⇒ couple exadecimal bool x1 true
            | x3 ⇒ couple exadecimal bool x2 true
            | x4 ⇒ couple exadecimal bool x3 true
            | x5 ⇒ couple exadecimal bool x4 true
            | x6 ⇒ couple exadecimal bool x5 true
            | x7 ⇒ couple exadecimal bool x6 true
            | x8 ⇒ couple exadecimal bool x7 true
            | x9 ⇒ couple exadecimal bool x8 true
            | xA ⇒ couple exadecimal bool x9 true
            | xB ⇒ couple exadecimal bool xA true
            | xC ⇒ couple exadecimal bool xB true
            | xD ⇒ couple exadecimal bool xC true
            | xE ⇒ couple exadecimal bool xD true
            | xF ⇒ couple exadecimal bool xE true ]
       | xF ⇒
           match b2 with
            [ x0 ⇒ couple exadecimal bool x0 true
            | x1 ⇒ couple exadecimal bool x1 true
            | x2 ⇒ couple exadecimal bool x2 true
            | x3 ⇒ couple exadecimal bool x3 true
            | x4 ⇒ couple exadecimal bool x4 true
            | x5 ⇒ couple exadecimal bool x5 true
            | x6 ⇒ couple exadecimal bool x6 true
            | x7 ⇒ couple exadecimal bool x7 true
            | x8 ⇒ couple exadecimal bool x8 true
            | x9 ⇒ couple exadecimal bool x9 true
            | xA ⇒ couple exadecimal bool xA true
            | xB ⇒ couple exadecimal bool xB true
            | xC ⇒ couple exadecimal bool xC true
            | xD ⇒ couple exadecimal bool xD true
            | xE ⇒ couple exadecimal bool xE true
            | xF ⇒ couple exadecimal bool xF true ] 
       ]
   | false ⇒
      match b1 with
       [ x0 ⇒
           match b2 with
            [ x0 ⇒ couple exadecimal bool x0 false
            | x1 ⇒ couple exadecimal bool x1 false
            | x2 ⇒ couple exadecimal bool x2 false
            | x3 ⇒ couple exadecimal bool x3 false
            | x4 ⇒ couple exadecimal bool x4 false
            | x5 ⇒ couple exadecimal bool x5 false
            | x6 ⇒ couple exadecimal bool x6 false
            | x7 ⇒ couple exadecimal bool x7 false
            | x8 ⇒ couple exadecimal bool x8 false
            | x9 ⇒ couple exadecimal bool x9 false
            | xA ⇒ couple exadecimal bool xA false
            | xB ⇒ couple exadecimal bool xB false
            | xC ⇒ couple exadecimal bool xC false
            | xD ⇒ couple exadecimal bool xD false
            | xE ⇒ couple exadecimal bool xE false
            | xF ⇒ couple exadecimal bool xF false ] 
       | x1 ⇒
           match b2 with
            [ x0 ⇒ couple exadecimal bool x1 false
            | x1 ⇒ couple exadecimal bool x2 false
            | x2 ⇒ couple exadecimal bool x3 false
            | x3 ⇒ couple exadecimal bool x4 false
            | x4 ⇒ couple exadecimal bool x5 false
            | x5 ⇒ couple exadecimal bool x6 false
            | x6 ⇒ couple exadecimal bool x7 false
            | x7 ⇒ couple exadecimal bool x8 false
            | x8 ⇒ couple exadecimal bool x9 false
            | x9 ⇒ couple exadecimal bool xA false
            | xA ⇒ couple exadecimal bool xB false
            | xB ⇒ couple exadecimal bool xC false
            | xC ⇒ couple exadecimal bool xD false
            | xD ⇒ couple exadecimal bool xE false
            | xE ⇒ couple exadecimal bool xF false
            | xF ⇒ couple exadecimal bool x0 true ] 
       | x2 ⇒
           match b2 with
            [ x0 ⇒ couple exadecimal bool x2 false
            | x1 ⇒ couple exadecimal bool x3 false
            | x2 ⇒ couple exadecimal bool x4 false
            | x3 ⇒ couple exadecimal bool x5 false
            | x4 ⇒ couple exadecimal bool x6 false
            | x5 ⇒ couple exadecimal bool x7 false
            | x6 ⇒ couple exadecimal bool x8 false
            | x7 ⇒ couple exadecimal bool x9 false
            | x8 ⇒ couple exadecimal bool xA false
            | x9 ⇒ couple exadecimal bool xB false
            | xA ⇒ couple exadecimal bool xC false
            | xB ⇒ couple exadecimal bool xD false
            | xC ⇒ couple exadecimal bool xE false
            | xD ⇒ couple exadecimal bool xF false
            | xE ⇒ couple exadecimal bool x0 true
            | xF ⇒ couple exadecimal bool x1 true ] 
       | x3 ⇒
           match b2 with
            [ x0 ⇒ couple exadecimal bool x3 false
            | x1 ⇒ couple exadecimal bool x4 false
            | x2 ⇒ couple exadecimal bool x5 false
            | x3 ⇒ couple exadecimal bool x6 false
            | x4 ⇒ couple exadecimal bool x7 false
            | x5 ⇒ couple exadecimal bool x8 false
            | x6 ⇒ couple exadecimal bool x9 false
            | x7 ⇒ couple exadecimal bool xA false
            | x8 ⇒ couple exadecimal bool xB false
            | x9 ⇒ couple exadecimal bool xC false
            | xA ⇒ couple exadecimal bool xD false
            | xB ⇒ couple exadecimal bool xE false
            | xC ⇒ couple exadecimal bool xF false
            | xD ⇒ couple exadecimal bool x0 true
            | xE ⇒ couple exadecimal bool x1 true
            | xF ⇒ couple exadecimal bool x2 true ] 
       | x4 ⇒
           match b2 with
            [ x0 ⇒ couple exadecimal bool x4 false
            | x1 ⇒ couple exadecimal bool x5 false
            | x2 ⇒ couple exadecimal bool x6 false
            | x3 ⇒ couple exadecimal bool x7 false
            | x4 ⇒ couple exadecimal bool x8 false
            | x5 ⇒ couple exadecimal bool x9 false
            | x6 ⇒ couple exadecimal bool xA false
            | x7 ⇒ couple exadecimal bool xB false
            | x8 ⇒ couple exadecimal bool xC false
            | x9 ⇒ couple exadecimal bool xD false
            | xA ⇒ couple exadecimal bool xE false
            | xB ⇒ couple exadecimal bool xF false
            | xC ⇒ couple exadecimal bool x0 true
            | xD ⇒ couple exadecimal bool x1 true
            | xE ⇒ couple exadecimal bool x2 true
            | xF ⇒ couple exadecimal bool x3 true ] 
       | x5 ⇒
           match b2 with
            [ x0 ⇒ couple exadecimal bool x5 false
            | x1 ⇒ couple exadecimal bool x6 false
            | x2 ⇒ couple exadecimal bool x7 false
            | x3 ⇒ couple exadecimal bool x8 false
            | x4 ⇒ couple exadecimal bool x9 false
            | x5 ⇒ couple exadecimal bool xA false
            | x6 ⇒ couple exadecimal bool xB false
            | x7 ⇒ couple exadecimal bool xC false
            | x8 ⇒ couple exadecimal bool xD false
            | x9 ⇒ couple exadecimal bool xE false
            | xA ⇒ couple exadecimal bool xF false
            | xB ⇒ couple exadecimal bool x0 true
            | xC ⇒ couple exadecimal bool x1 true
            | xD ⇒ couple exadecimal bool x2 true
            | xE ⇒ couple exadecimal bool x3 true
            | xF ⇒ couple exadecimal bool x4 true ] 
       | x6 ⇒
           match b2 with
            [ x0 ⇒ couple exadecimal bool x6 false
            | x1 ⇒ couple exadecimal bool x7 false
            | x2 ⇒ couple exadecimal bool x8 false
            | x3 ⇒ couple exadecimal bool x9 false
            | x4 ⇒ couple exadecimal bool xA false
            | x5 ⇒ couple exadecimal bool xB false
            | x6 ⇒ couple exadecimal bool xC false
            | x7 ⇒ couple exadecimal bool xD false
            | x8 ⇒ couple exadecimal bool xE false
            | x9 ⇒ couple exadecimal bool xF false
            | xA ⇒ couple exadecimal bool x0 true
            | xB ⇒ couple exadecimal bool x1 true
            | xC ⇒ couple exadecimal bool x2 true
            | xD ⇒ couple exadecimal bool x3 true
            | xE ⇒ couple exadecimal bool x4 true
            | xF ⇒ couple exadecimal bool x5 true ] 
       | x7 ⇒
           match b2 with
            [ x0 ⇒ couple exadecimal bool x7 false
            | x1 ⇒ couple exadecimal bool x8 false
            | x2 ⇒ couple exadecimal bool x9 false
            | x3 ⇒ couple exadecimal bool xA false
            | x4 ⇒ couple exadecimal bool xB false
            | x5 ⇒ couple exadecimal bool xC false
            | x6 ⇒ couple exadecimal bool xD false
            | x7 ⇒ couple exadecimal bool xE false
            | x8 ⇒ couple exadecimal bool xF false
            | x9 ⇒ couple exadecimal bool x0 true
            | xA ⇒ couple exadecimal bool x1 true
            | xB ⇒ couple exadecimal bool x2 true
            | xC ⇒ couple exadecimal bool x3 true
            | xD ⇒ couple exadecimal bool x4 true
            | xE ⇒ couple exadecimal bool x5 true
            | xF ⇒ couple exadecimal bool x6 true ] 
       | x8 ⇒
           match b2 with
            [ x0 ⇒ couple exadecimal bool x8 false
            | x1 ⇒ couple exadecimal bool x9 false
            | x2 ⇒ couple exadecimal bool xA false
            | x3 ⇒ couple exadecimal bool xB false
            | x4 ⇒ couple exadecimal bool xC false
            | x5 ⇒ couple exadecimal bool xD false
            | x6 ⇒ couple exadecimal bool xE false
            | x7 ⇒ couple exadecimal bool xF false
            | x8 ⇒ couple exadecimal bool x0 true
            | x9 ⇒ couple exadecimal bool x1 true
            | xA ⇒ couple exadecimal bool x2 true
            | xB ⇒ couple exadecimal bool x3 true
            | xC ⇒ couple exadecimal bool x4 true
            | xD ⇒ couple exadecimal bool x5 true
            | xE ⇒ couple exadecimal bool x6 true
            | xF ⇒ couple exadecimal bool x7 true ] 
       | x9 ⇒
           match b2 with
            [ x0 ⇒ couple exadecimal bool x9 false
            | x1 ⇒ couple exadecimal bool xA false
            | x2 ⇒ couple exadecimal bool xB false
            | x3 ⇒ couple exadecimal bool xC false
            | x4 ⇒ couple exadecimal bool xD false
            | x5 ⇒ couple exadecimal bool xE false
            | x6 ⇒ couple exadecimal bool xF false
            | x7 ⇒ couple exadecimal bool x0 true
            | x8 ⇒ couple exadecimal bool x1 true
            | x9 ⇒ couple exadecimal bool x2 true
            | xA ⇒ couple exadecimal bool x3 true
            | xB ⇒ couple exadecimal bool x4 true
            | xC ⇒ couple exadecimal bool x5 true
            | xD ⇒ couple exadecimal bool x6 true
            | xE ⇒ couple exadecimal bool x7 true
            | xF ⇒ couple exadecimal bool x8 true ] 
       | xA ⇒
           match b2 with
            [ x0 ⇒ couple exadecimal bool xA false
            | x1 ⇒ couple exadecimal bool xB false
            | x2 ⇒ couple exadecimal bool xC false
            | x3 ⇒ couple exadecimal bool xD false
            | x4 ⇒ couple exadecimal bool xE false
            | x5 ⇒ couple exadecimal bool xF false
            | x6 ⇒ couple exadecimal bool x0 true
            | x7 ⇒ couple exadecimal bool x1 true
            | x8 ⇒ couple exadecimal bool x2 true
            | x9 ⇒ couple exadecimal bool x3 true
            | xA ⇒ couple exadecimal bool x4 true
            | xB ⇒ couple exadecimal bool x5 true
            | xC ⇒ couple exadecimal bool x6 true
            | xD ⇒ couple exadecimal bool x7 true
            | xE ⇒ couple exadecimal bool x8 true
            | xF ⇒ couple exadecimal bool x9 true ] 
       | xB ⇒
           match b2 with
            [ x0 ⇒ couple exadecimal bool xB false
            | x1 ⇒ couple exadecimal bool xC false
            | x2 ⇒ couple exadecimal bool xD false
            | x3 ⇒ couple exadecimal bool xE false
            | x4 ⇒ couple exadecimal bool xF false
            | x5 ⇒ couple exadecimal bool x0 true
            | x6 ⇒ couple exadecimal bool x1 true
            | x7 ⇒ couple exadecimal bool x2 true
            | x8 ⇒ couple exadecimal bool x3 true
            | x9 ⇒ couple exadecimal bool x4 true
            | xA ⇒ couple exadecimal bool x5 true
            | xB ⇒ couple exadecimal bool x6 true
            | xC ⇒ couple exadecimal bool x7 true
            | xD ⇒ couple exadecimal bool x8 true
            | xE ⇒ couple exadecimal bool x9 true
            | xF ⇒ couple exadecimal bool xA true ] 
       | xC ⇒
           match b2 with
            [ x0 ⇒ couple exadecimal bool xC false
            | x1 ⇒ couple exadecimal bool xD false
            | x2 ⇒ couple exadecimal bool xE false
            | x3 ⇒ couple exadecimal bool xF false
            | x4 ⇒ couple exadecimal bool x0 true
            | x5 ⇒ couple exadecimal bool x1 true
            | x6 ⇒ couple exadecimal bool x2 true
            | x7 ⇒ couple exadecimal bool x3 true
            | x8 ⇒ couple exadecimal bool x4 true
            | x9 ⇒ couple exadecimal bool x5 true
            | xA ⇒ couple exadecimal bool x6 true
            | xB ⇒ couple exadecimal bool x7 true
            | xC ⇒ couple exadecimal bool x8 true
            | xD ⇒ couple exadecimal bool x9 true
            | xE ⇒ couple exadecimal bool xA true
            | xF ⇒ couple exadecimal bool xB true ] 
       | xD ⇒
           match b2 with
            [ x0 ⇒ couple exadecimal bool xD false
            | x1 ⇒ couple exadecimal bool xE false
            | x2 ⇒ couple exadecimal bool xF false
            | x3 ⇒ couple exadecimal bool x0 true
            | x4 ⇒ couple exadecimal bool x1 true
            | x5 ⇒ couple exadecimal bool x2 true
            | x6 ⇒ couple exadecimal bool x3 true
            | x7 ⇒ couple exadecimal bool x4 true
            | x8 ⇒ couple exadecimal bool x5 true
            | x9 ⇒ couple exadecimal bool x6 true
            | xA ⇒ couple exadecimal bool x7 true
            | xB ⇒ couple exadecimal bool x8 true
            | xC ⇒ couple exadecimal bool x9 true
            | xD ⇒ couple exadecimal bool xA true
            | xE ⇒ couple exadecimal bool xB true
            | xF ⇒ couple exadecimal bool xC true ] 
       | xE ⇒
           match b2 with
            [ x0 ⇒ couple exadecimal bool xE false
            | x1 ⇒ couple exadecimal bool xF false
            | x2 ⇒ couple exadecimal bool x0 true
            | x3 ⇒ couple exadecimal bool x1 true
            | x4 ⇒ couple exadecimal bool x2 true
            | x5 ⇒ couple exadecimal bool x3 true
            | x6 ⇒ couple exadecimal bool x4 true
            | x7 ⇒ couple exadecimal bool x5 true
            | x8 ⇒ couple exadecimal bool x6 true
            | x9 ⇒ couple exadecimal bool x7 true
            | xA ⇒ couple exadecimal bool x8 true
            | xB ⇒ couple exadecimal bool x9 true
            | xC ⇒ couple exadecimal bool xA true
            | xD ⇒ couple exadecimal bool xB true
            | xE ⇒ couple exadecimal bool xC true
            | xF ⇒ couple exadecimal bool xD true ] 
       | xF ⇒
           match b2 with
            [ x0 ⇒ couple exadecimal bool xF false
            | x1 ⇒ couple exadecimal bool x0 true
            | x2 ⇒ couple exadecimal bool x1 true
            | x3 ⇒ couple exadecimal bool x2 true
            | x4 ⇒ couple exadecimal bool x3 true
            | x5 ⇒ couple exadecimal bool x4 true
            | x6 ⇒ couple exadecimal bool x5 true
            | x7 ⇒ couple exadecimal bool x6 true
            | x8 ⇒ couple exadecimal bool x7 true
            | x9 ⇒ couple exadecimal bool x8 true
            | xA ⇒ couple exadecimal bool x9 true
            | xB ⇒ couple exadecimal bool xA true
            | xC ⇒ couple exadecimal bool xB true
            | xD ⇒ couple exadecimal bool xC true
            | xE ⇒ couple exadecimal bool xD true
            | xF ⇒ couple exadecimal bool xE true ]
       ]
   ]
.

definition nat_of_exadecimal ≝
 λb.
  match b with
   [ x0 ⇒ 0
   | x1 ⇒ 1
   | x2 ⇒ 2
   | x3 ⇒ 3
   | x4 ⇒ 4
   | x5 ⇒ 5
   | x6 ⇒ 6
   | x7 ⇒ 7
   | x8 ⇒ 8
   | x9 ⇒ 9
   | xA ⇒ 10
   | xB ⇒ 11
   | xC ⇒ 12
   | xD ⇒ 13
   | xE ⇒ 14
   | xF ⇒ 15
   ].

coercion cic:/matita/assembly/exadecimal/nat_of_exadecimal.con.

let rec exadecimal_of_nat b ≝
  match b with [ O ⇒ x0 | S b ⇒
  match b with [ O ⇒ x1 | S b ⇒
  match b with [ O ⇒ x2 | S b ⇒ 
  match b with [ O ⇒ x3 | S b ⇒ 
  match b with [ O ⇒ x4 | S b ⇒ 
  match b with [ O ⇒ x5 | S b ⇒ 
  match b with [ O ⇒ x6 | S b ⇒ 
  match b with [ O ⇒ x7 | S b ⇒ 
  match b with [ O ⇒ x8 | S b ⇒ 
  match b with [ O ⇒ x9 | S b ⇒ 
  match b with [ O ⇒ xA | S b ⇒ 
  match b with [ O ⇒ xB | S b ⇒ 
  match b with [ O ⇒ xC | S b ⇒ 
  match b with [ O ⇒ xD | S b ⇒ 
  match b with [ O ⇒ xE | S b ⇒ 
  match b with [ O ⇒ xF | S b ⇒ exadecimal_of_nat b ]]]]]]]]]]]]]]]]. 

lemma lt_nat_of_exadecimal_16: ∀b. nat_of_exadecimal b < 16.
 intro;
 elim b;
 simplify;
 [
 |*: alias id "lt_S_S" = "cic:/matita/algebra/finite_groups/lt_S_S.con".
   repeat (apply lt_S_S)
 ];
 autobatch.
qed.

lemma exadecimal_of_nat_mod:
 ∀n.exadecimal_of_nat n = exadecimal_of_nat (n \mod 16).
 intros;
 apply (nat_elim1 n); intro;
 cases m; [ intro; reflexivity | ];
 cases n1; [ intro; reflexivity | ];
 cases n2; [ intro; reflexivity | ];
 cases n3; [ intro; reflexivity | ];
 cases n4; [ intro; reflexivity | ];
 cases n5; [ intro; reflexivity | ];
 cases n6; [ intro; reflexivity | ];
 cases n7; [ intro; reflexivity | ];
 cases n8; [ intro; reflexivity | ];
 cases n9; [ intro; reflexivity | ];
 cases n10; [ intro; reflexivity | ];
 cases n11; [ intro; reflexivity | ];
 cases n12; [ intro; reflexivity | ];
 cases n13; [ intro; reflexivity | ];
 cases n14; [ intro; reflexivity | ];
 cases n15; [ intro; reflexivity | ];
 intros;
 change in ⊢ (? ? % ?) with (exadecimal_of_nat n16);
 change in ⊢ (? ? ? (? (? % ?))) with (16 + n16);
 rewrite > mod_plus;
 change in ⊢ (? ? ? (? (? % ?))) with (n16 \mod 16);
 rewrite < mod_mod;
  [ apply H;
    autobatch
  | autobatch
  ]
qed.

lemma nat_of_exadecimal_exadecimal_of_nat:
 ∀n. nat_of_exadecimal (exadecimal_of_nat n) = n \mod 16.
 intro;
 rewrite > exadecimal_of_nat_mod;
 generalize in match (lt_mod_m_m n 16 ?); [2: autobatch | ]
 generalize in match (n \mod 16); intro;
 cases n1; [ intro; reflexivity | ];
 cases n2; [ intro; reflexivity | ];
 cases n3; [ intro; reflexivity | ];
 cases n4; [ intro; reflexivity | ];
 cases n5; [ intro; reflexivity | ]; 
 cases n6; [ intro; reflexivity | ]; 
 cases n7; [ intro; reflexivity | ];
 cases n8; [ intro; reflexivity | ];
 cases n9; [ intro; reflexivity | ];
 cases n10; [ intro; reflexivity | ];
 cases n11 [ intro; reflexivity | ];
 cases n12; [ intro; reflexivity | ];
 cases n13; [ intro; reflexivity | ];
 cases n14; [ intro; reflexivity | ];
 cases n15; [ intro; reflexivity | ];
 cases n16; [ intro; reflexivity | ];
 intro;
 unfold lt in H;
 cut False;
  [ elim Hcut
  | autobatch
  ]
qed.

lemma plusex_ok:
 ∀b1,b2,c.
  match plusex b1 b2 c with
   [ couple r c' ⇒ b1 + b2 + nat_of_bool c = nat_of_exadecimal r + nat_of_bool c' * 16 ].
 intros;
 elim c;
 elim b1;
 elim b2;
 normalize;
 reflexivity.
qed.

definition xpred ≝
 λb.
  match b with
   [ x0 ⇒ xF
   | x1 ⇒ x0
   | x2 ⇒ x1
   | x3 ⇒ x2
   | x4 ⇒ x3
   | x5 ⇒ x4
   | x6 ⇒ x5
   | x7 ⇒ x6
   | x8 ⇒ x7
   | x9 ⇒ x8
   | xA ⇒ x9
   | xB ⇒ xA
   | xC ⇒ xB
   | xD ⇒ xC
   | xE ⇒ xD
   | xF ⇒ xE ].

lemma eq_eqex_S_x0_false:
 ∀n. n < 15 → eqex x0 (exadecimal_of_nat (S n)) = false.
 intro;
 cases n 0; [ intro; simplify; reflexivity | clear n];
 cases n1 0; [ intro; simplify; reflexivity | clear n1];
 cases n 0; [ intro; simplify; reflexivity | clear n];
 cases n1 0; [ intro; simplify; reflexivity | clear n1];
 cases n 0; [ intro; simplify; reflexivity | clear n];
 cases n1 0; [ intro; simplify; reflexivity | clear n1];
 cases n 0; [ intro; simplify; reflexivity | clear n];
 cases n1 0; [ intro; simplify; reflexivity | clear n1];
 cases n 0; [ intro; simplify; reflexivity | clear n];
 cases n1 0; [ intro; simplify; reflexivity | clear n1];
 cases n 0; [ intro; simplify; reflexivity | clear n];
 cases n1 0; [ intro; simplify; reflexivity | clear n1];
 cases n 0; [ intro; simplify; reflexivity | clear n];
 cases n1 0; [ intro; simplify; reflexivity | clear n1];
 cases n 0; [ intro; simplify; reflexivity | clear n];
 intro;
 unfold lt in H;
 cut (S n1 ≤ 0);
  [ elim (not_le_Sn_O ? Hcut)
  | do 15 (apply le_S_S_to_le);
    assumption
  ]
qed.

lemma eqex_true_to_eq: ∀b,b'. eqex b b' = true → b=b'.
 intros 2;
 elim b 0;
 elim b' 0;
 simplify;
 intro;
 first [ reflexivity | destruct H ].
qed.
 
(*
lemma xpred_S: ∀b. xpred (exadecimal_of_nat (S b)) = exadecimal_of_nat b.
 intros;
 rewrite > exadecimal_of_nat_mod;
 rewrite > exadecimal_of_nat_mod in ⊢ (? ? ? %);
*)