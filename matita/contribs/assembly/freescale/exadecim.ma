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
(*                           Progetto FreeScale                           *)
(*                                                                        *)
(* Sviluppato da:                                                         *)
(*   Cosimo Oliboni, oliboni@cs.unibo.it                                  *)
(*                                                                        *)
(* Questo materiale fa parte della tesi:                                  *)
(*   "Formalizzazione Interattiva dei Microcontroller a 8bit FreeScale"   *)
(*                                                                        *)
(*                    data ultima modifica 15/11/2007                     *)
(* ********************************************************************** *)

include "freescale/extra.ma".

(* ***************************** *)
(* DEFINIZIONE DEGLI ESADECIMALI *)
(* ***************************** *)

inductive exadecim : Type ≝
  x0: exadecim
| x1: exadecim
| x2: exadecim
| x3: exadecim
| x4: exadecim
| x5: exadecim
| x6: exadecim
| x7: exadecim
| x8: exadecim
| x9: exadecim
| xA: exadecim
| xB: exadecim
| xC: exadecim
| xD: exadecim
| xE: exadecim
| xF: exadecim.

(* operatore = *)
definition eq_ex ≝
λe1,e2:exadecim.
 match e1 with
  [ x0 ⇒ match e2 with
   [ x0 ⇒ true  | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false
   | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
   | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false
   | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ] 
  | x1 ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ true  | x2 ⇒ false | x3 ⇒ false
   | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
   | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false
   | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ] 
  | x2 ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ true  | x3 ⇒ false
   | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
   | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false
   | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ] 
  | x3 ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ true
   | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
   | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false
   | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ] 
  | x4 ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false
   | x4 ⇒ true  | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
   | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false
   | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ] 
  | x5 ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false
   | x4 ⇒ false | x5 ⇒ true  | x6 ⇒ false | x7 ⇒ false
   | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false
   | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ] 
  | x6 ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false
   | x4 ⇒ false | x5 ⇒ false | x6 ⇒ true  | x7 ⇒ false
   | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false
   | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ] 
  | x7 ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false
   | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ true 
   | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false
   | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ] 
  | x8 ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false
   | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
   | x8 ⇒ true  | x9 ⇒ false | xA ⇒ false | xB ⇒ false
   | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ] 
  | x9 ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false
   | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
   | x8 ⇒ false | x9 ⇒ true  | xA ⇒ false | xB ⇒ false
   | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ] 
  | xA ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false
   | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
   | x8 ⇒ false | x9 ⇒ false | xA ⇒ true  | xB ⇒ false
   | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ] 
  | xB ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false
   | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
   | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ true 
   | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ] 
  | xC ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false
   | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
   | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false
   | xC ⇒ true  | xD ⇒ false | xE ⇒ false | xF ⇒ false ] 
  | xD ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false
   | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
   | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false
   | xC ⇒ false | xD ⇒ true  | xE ⇒ false | xF ⇒ false ] 
  | xE ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false
   | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
   | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false
   | xC ⇒ false | xD ⇒ false | xE ⇒ true  | xF ⇒ false ] 
  | xF ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false
   | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
   | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false
   | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ true ]
  ].

(* operatore < *)
definition lt_ex ≝
λe1,e2:exadecim.
 match e1 with
  [ x0 ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ true | x2 ⇒ true | x3 ⇒ true
   | x4 ⇒ true  | x5 ⇒ true | x6 ⇒ true | x7 ⇒ true
   | x8 ⇒ true  | x9 ⇒ true | xA ⇒ true | xB ⇒ true
   | xC ⇒ true  | xD ⇒ true | xE ⇒ true | xF ⇒ true ] 
  | x1 ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ true | x3 ⇒ true
   | x4 ⇒ true  | x5 ⇒ true  | x6 ⇒ true | x7 ⇒ true
   | x8 ⇒ true  | x9 ⇒ true  | xA ⇒ true | xB ⇒ true
   | xC ⇒ true  | xD ⇒ true  | xE ⇒ true | xF ⇒ true ] 
  | x2 ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ true
   | x4 ⇒ true  | x5 ⇒ true  | x6 ⇒ true  | x7 ⇒ true
   | x8 ⇒ true  | x9 ⇒ true  | xA ⇒ true  | xB ⇒ true
   | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true ] 
  | x3 ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false
   | x4 ⇒ true  | x5 ⇒ true  | x6 ⇒ true  | x7 ⇒ true
   | x8 ⇒ true  | x9 ⇒ true  | xA ⇒ true  | xB ⇒ true
   | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true ] 
  | x4 ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false
   | x4 ⇒ false | x5 ⇒ true  | x6 ⇒ true  | x7 ⇒ true
   | x8 ⇒ true  | x9 ⇒ true  | xA ⇒ true  | xB ⇒ true
   | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true ] 
  | x5 ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false
   | x4 ⇒ false | x5 ⇒ false | x6 ⇒ true  | x7 ⇒ true
   | x8 ⇒ true  | x9 ⇒ true  | xA ⇒ true  | xB ⇒ true 
   | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true ] 
  | x6 ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false
   | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ true
   | x8 ⇒ true  | x9 ⇒ true  | xA ⇒ true  | xB ⇒ true 
   | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true ] 
  | x7 ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false
   | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false 
   | x8 ⇒ true  | x9 ⇒ true  | xA ⇒ true  | xB ⇒ true
   | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true ] 
  | x8 ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false
   | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
   | x8 ⇒ false | x9 ⇒ true  | xA ⇒ true  | xB ⇒ true 
   | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true ] 
  | x9 ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false 
   | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
   | x8 ⇒ false | x9 ⇒ false | xA ⇒ true  | xB ⇒ true 
   | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true ] 
  | xA ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false
   | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
   | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ true
   | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true ] 
  | xB ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false 
   | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
   | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false 
   | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true ] 
  | xC ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false 
   | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
   | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false 
   | xC ⇒ false | xD ⇒ true  | xE ⇒ true  | xF ⇒ true ] 
  | xD ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false 
   | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
   | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false 
   | xC ⇒ false | xD ⇒ false | xE ⇒ true  | xF ⇒ true ] 
  | xE ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false 
   | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
   | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false 
   | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ true ] 
  | xF ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false 
   | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
   | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false 
   | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ]
  ].

(* operatore ≤ *)
definition le_ex ≝
λe1,e2:exadecim.
 match e1 with
  [ x0 ⇒ match e2 with
   [ x0 ⇒ true | x1 ⇒ true | x2 ⇒ true | x3 ⇒ true 
   | x4 ⇒ true | x5 ⇒ true | x6 ⇒ true | x7 ⇒ true
   | x8 ⇒ true | x9 ⇒ true | xA ⇒ true | xB ⇒ true 
   | xC ⇒ true | xD ⇒ true | xE ⇒ true | xF ⇒ true ] 
  | x1 ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ true | x2 ⇒ true | x3 ⇒ true 
   | x4 ⇒ true  | x5 ⇒ true | x6 ⇒ true | x7 ⇒ true
   | x8 ⇒ true  | x9 ⇒ true | xA ⇒ true | xB ⇒ true 
   | xC ⇒ true  | xD ⇒ true | xE ⇒ true | xF ⇒ true ] 
  | x2 ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ true | x3 ⇒ true 
   | x4 ⇒ true  | x5 ⇒ true  | x6 ⇒ true | x7 ⇒ true
   | x8 ⇒ true  | x9 ⇒ true  | xA ⇒ true | xB ⇒ true 
   | xC ⇒ true  | xD ⇒ true  | xE ⇒ true | xF ⇒ true ] 
  | x3 ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ true 
   | x4 ⇒ true  | x5 ⇒ true  | x6 ⇒ true  | x7 ⇒ true
   | x8 ⇒ true  | x9 ⇒ true  | xA ⇒ true  | xB ⇒ true 
   | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true ] 
  | x4 ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false 
   | x4 ⇒ true  | x5 ⇒ true  | x6 ⇒ true  | x7 ⇒ true
   | x8 ⇒ true  | x9 ⇒ true  | xA ⇒ true  | xB ⇒ true 
   | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true ] 
  | x5 ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false 
   | x4 ⇒ false | x5 ⇒ true  | x6 ⇒ true  | x7 ⇒ true
   | x8 ⇒ true  | x9 ⇒ true  | xA ⇒ true  | xB ⇒ true 
   | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true ] 
  | x6 ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false 
   | x4 ⇒ false | x5 ⇒ false | x6 ⇒ true  | x7 ⇒ true
   | x8 ⇒ true  | x9 ⇒ true  | xA ⇒ true  | xB ⇒ true 
   | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true ] 
  | x7 ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false 
   | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ true 
   | x8 ⇒ true  | x9 ⇒ true  | xA ⇒ true  | xB ⇒ true 
   | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true ] 
  | x8 ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false 
   | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
   | x8 ⇒ true  | x9 ⇒ true  | xA ⇒ true  | xB ⇒ true 
   | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true ] 
  | x9 ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false 
   | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
   | x8 ⇒ false | x9 ⇒ true  | xA ⇒ true  | xB ⇒ true 
   | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true ] 
  | xA ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false 
   | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
   | x8 ⇒ false | x9 ⇒ false | xA ⇒ true  | xB ⇒ true 
   | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true ] 
  | xB ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false 
   | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
   | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ true 
   | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true ] 
  | xC ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false 
   | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
   | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false 
   | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true ] 
  | xD ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false 
   | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
   | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false 
   | xC ⇒ false | xD ⇒ true  | xE ⇒ true  | xF ⇒ true ] 
  | xE ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false 
   | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
   | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false 
   | xC ⇒ false | xD ⇒ false | xE ⇒ true  | xF ⇒ true ] 
  | xF ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false 
   | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
   | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false 
   | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ true ]
  ].

(* operatore > *)
definition gt_ex ≝
λe1,e2:exadecim.
 match e1 with
  [ x0 ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false 
   | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
   | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false 
   | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ] 
  | x1 ⇒ match e2 with
   [ x0 ⇒ true  | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false 
   | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
   | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false 
   | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ] 
  | x2 ⇒ match e2 with
   [ x0 ⇒ true  | x1 ⇒ true  | x2 ⇒ false | x3 ⇒ false 
   | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
   | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false 
   | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ] 
  | x3 ⇒ match e2 with
   [ x0 ⇒ true  | x1 ⇒ true  | x2 ⇒ true  | x3 ⇒ false 
   | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
   | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false 
   | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ] 
  | x4 ⇒ match e2 with
   [ x0 ⇒ true  | x1 ⇒ true  | x2 ⇒ true  | x3 ⇒ true 
   | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
   | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false 
   | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ] 
  | x5 ⇒ match e2 with
   [ x0 ⇒ true  | x1 ⇒ true  | x2 ⇒ true  | x3 ⇒ true 
   | x4 ⇒ true  | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
   | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false 
   | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ] 
  | x6 ⇒ match e2 with
   [ x0 ⇒ true  | x1 ⇒ true  | x2 ⇒ true  | x3 ⇒ true 
   | x4 ⇒ true  | x5 ⇒ true  | x6 ⇒ false | x7 ⇒ false
   | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false 
   | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ] 
  | x7 ⇒ match e2 with
   [ x0 ⇒ true  | x1 ⇒ true  | x2 ⇒ true  | x3 ⇒ true 
   | x4 ⇒ true  | x5 ⇒ true  | x6 ⇒ true  | x7 ⇒ false
   | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false 
   | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ]
  | x8 ⇒ match e2 with
   [ x0 ⇒ true  | x1 ⇒ true  | x2 ⇒ true  | x3 ⇒ true 
   | x4 ⇒ true  | x5 ⇒ true  | x6 ⇒ true  | x7 ⇒ true
   | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false 
   | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ]
  | x9 ⇒ match e2 with
   [ x0 ⇒ true  | x1 ⇒ true  | x2 ⇒ true  | x3 ⇒ true 
   | x4 ⇒ true  | x5 ⇒ true  | x6 ⇒ true  | x7 ⇒ true
   | x8 ⇒ true  | x9 ⇒ false | xA ⇒ false | xB ⇒ false 
   | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ]
  | xA ⇒ match e2 with
   [ x0 ⇒ true  | x1 ⇒ true  | x2 ⇒ true  | x3 ⇒ true 
   | x4 ⇒ true  | x5 ⇒ true  | x6 ⇒ true  | x7 ⇒ true
   | x8 ⇒ true  | x9 ⇒ true  | xA ⇒ false | xB ⇒ false 
   | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ]
  | xB ⇒ match e2 with
   [ x0 ⇒ true  | x1 ⇒ true  | x2 ⇒ true  | x3 ⇒ true 
   | x4 ⇒ true  | x5 ⇒ true  | x6 ⇒ true  | x7 ⇒ true
   | x8 ⇒ true  | x9 ⇒ true  | xA ⇒ true  | xB ⇒ false 
   | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ]
  | xC ⇒ match e2 with
   [ x0 ⇒ true  | x1 ⇒ true  | x2 ⇒ true  | x3 ⇒ true 
   | x4 ⇒ true  | x5 ⇒ true  | x6 ⇒ true  | x7 ⇒ true
   | x8 ⇒ true  | x9 ⇒ true  | xA ⇒ true  | xB ⇒ true 
   | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ]
  | xD ⇒ match e2 with
   [ x0 ⇒ true  | x1 ⇒ true  | x2 ⇒ true  | x3 ⇒ true 
   | x4 ⇒ true  | x5 ⇒ true  | x6 ⇒ true  | x7 ⇒ true
   | x8 ⇒ true  | x9 ⇒ true  | xA ⇒ true  | xB ⇒ true 
   | xC ⇒ true  | xD ⇒ false | xE ⇒ false | xF ⇒ false ]
  | xE ⇒ match e2 with
   [ x0 ⇒ true  | x1 ⇒ true  | x2 ⇒ true  | x3 ⇒ true 
   | x4 ⇒ true  | x5 ⇒ true  | x6 ⇒ true  | x7 ⇒ true
   | x8 ⇒ true  | x9 ⇒ true  | xA ⇒ true  | xB ⇒ true 
   | xC ⇒ true  | xD ⇒ true  | xE ⇒ false | xF ⇒ false ]
  | xF ⇒ match e2 with
   [ x0 ⇒ true  | x1 ⇒ true  | x2 ⇒ true  | x3 ⇒ true 
   | x4 ⇒ true  | x5 ⇒ true  | x6 ⇒ true  | x7 ⇒ true
   | x8 ⇒ true  | x9 ⇒ true  | xA ⇒ true  | xB ⇒ true 
   | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ false ]
  ].

(* operatore ≥ *)
definition ge_ex ≝
λe1,e2:exadecim.
 match e1 with
  [ x0 ⇒ match e2 with
   [ x0 ⇒ true  | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false 
   | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
   | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false 
   | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ] 
  | x1 ⇒ match e2 with
   [ x0 ⇒ true  | x1 ⇒ true  | x2 ⇒ false | x3 ⇒ false 
   | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
   | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false 
   | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ] 
  | x2 ⇒ match e2 with
   [ x0 ⇒ true  | x1 ⇒ true  | x2 ⇒ true  | x3 ⇒ false 
   | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
   | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false 
   | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ] 
  | x3 ⇒ match e2 with
   [ x0 ⇒ true  | x1 ⇒ true  | x2 ⇒ true  | x3 ⇒ true 
   | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
   | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false 
   | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ] 
  | x4 ⇒ match e2 with
   [ x0 ⇒ true  | x1 ⇒ true  | x2 ⇒ true  | x3 ⇒ true 
   | x4 ⇒ true  | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
   | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false 
   | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ] 
  | x5 ⇒ match e2 with
   [ x0 ⇒ true  | x1 ⇒ true  | x2 ⇒ true  | x3 ⇒ true 
   | x4 ⇒ true  | x5 ⇒ true  | x6 ⇒ false | x7 ⇒ false
   | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false 
   | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ] 
  | x6 ⇒ match e2 with
   [ x0 ⇒ true  | x1 ⇒ true  | x2 ⇒ true  | x3 ⇒ true 
   | x4 ⇒ true  | x5 ⇒ true  | x6 ⇒ true  | x7 ⇒ false
   | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false 
   | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ] 
  | x7 ⇒ match e2 with
   [ x0 ⇒ true  | x1 ⇒ true  | x2 ⇒ true  | x3 ⇒ true 
   | x4 ⇒ true  | x5 ⇒ true  | x6 ⇒ true  | x7 ⇒ true
   | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false 
   | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ]
  | x8 ⇒ match e2 with
   [ x0 ⇒ true  | x1 ⇒ true  | x2 ⇒ true  | x3 ⇒ true 
   | x4 ⇒ true  | x5 ⇒ true  | x6 ⇒ true  | x7 ⇒ true
   | x8 ⇒ true  | x9 ⇒ false | xA ⇒ false | xB ⇒ false 
   | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ]
  | x9 ⇒ match e2 with
   [ x0 ⇒ true  | x1 ⇒ true  | x2 ⇒ true  | x3 ⇒ true 
   | x4 ⇒ true  | x5 ⇒ true  | x6 ⇒ true  | x7 ⇒ true
   | x8 ⇒ true  | x9 ⇒ true  | xA ⇒ false | xB ⇒ false 
   | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ]
  | xA ⇒ match e2 with
   [ x0 ⇒ true  | x1 ⇒ true  | x2 ⇒ true  | x3 ⇒ true 
   | x4 ⇒ true  | x5 ⇒ true  | x6 ⇒ true  | x7 ⇒ true
   | x8 ⇒ true  | x9 ⇒ true  | xA ⇒ true  | xB ⇒ false 
   | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ]
  | xB ⇒ match e2 with
   [ x0 ⇒ true  | x1 ⇒ true  | x2 ⇒ true  | x3 ⇒ true 
   | x4 ⇒ true  | x5 ⇒ true  | x6 ⇒ true  | x7 ⇒ true
   | x8 ⇒ true  | x9 ⇒ true  | xA ⇒ true  | xB ⇒ true 
   | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ]
  | xC ⇒ match e2 with
   [ x0 ⇒ true  | x1 ⇒ true  | x2 ⇒ true  | x3 ⇒ true 
   | x4 ⇒ true  | x5 ⇒ true  | x6 ⇒ true  | x7 ⇒ true
   | x8 ⇒ true  | x9 ⇒ true  | xA ⇒ true  | xB ⇒ true 
   | xC ⇒ true  | xD ⇒ false | xE ⇒ false | xF ⇒ false ]
  | xD ⇒ match e2 with
   [ x0 ⇒ true  | x1 ⇒ true  | x2 ⇒ true  | x3 ⇒ true 
   | x4 ⇒ true  | x5 ⇒ true  | x6 ⇒ true  | x7 ⇒ true
   | x8 ⇒ true  | x9 ⇒ true  | xA ⇒ true  | xB ⇒ true 
   | xC ⇒ true  | xD ⇒ true  | xE ⇒ false | xF ⇒ false ]
  | xE ⇒ match e2 with
   [ x0 ⇒ true  | x1 ⇒ true  | x2 ⇒ true  | x3 ⇒ true 
   | x4 ⇒ true  | x5 ⇒ true  | x6 ⇒ true  | x7 ⇒ true
   | x8 ⇒ true  | x9 ⇒ true  | xA ⇒ true  | xB ⇒ true 
   | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ false ]
  | xF ⇒ match e2 with
   [ x0 ⇒ true  | x1 ⇒ true  | x2 ⇒ true  | x3 ⇒ true 
   | x4 ⇒ true  | x5 ⇒ true  | x6 ⇒ true  | x7 ⇒ true
   | x8 ⇒ true  | x9 ⇒ true  | xA ⇒ true  | xB ⇒ true 
   | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true ]
  ].

(* operatore and *)
definition and_ex ≝
λe1,e2:exadecim.match e1 with
 [ x0 ⇒ match e2 with
  [ x0 ⇒ x0 | x1 ⇒ x0 | x2 ⇒ x0 | x3 ⇒ x0 
  | x4 ⇒ x0 | x5 ⇒ x0 | x6 ⇒ x0 | x7 ⇒ x0
  | x8 ⇒ x0 | x9 ⇒ x0 | xA ⇒ x0 | xB ⇒ x0 
  | xC ⇒ x0 | xD ⇒ x0 | xE ⇒ x0 | xF ⇒ x0 ]
 | x1 ⇒ match e2 with
  [ x0 ⇒ x0 | x1 ⇒ x1 | x2 ⇒ x0 | x3 ⇒ x1 
  | x4 ⇒ x0 | x5 ⇒ x1 | x6 ⇒ x0 | x7 ⇒ x1
  | x8 ⇒ x0 | x9 ⇒ x1 | xA ⇒ x0 | xB ⇒ x1 
  | xC ⇒ x0 | xD ⇒ x1 | xE ⇒ x0 | xF ⇒ x1 ]
 | x2 ⇒ match e2 with
  [ x0 ⇒ x0 | x1 ⇒ x0 | x2 ⇒ x2 | x3 ⇒ x2 
  | x4 ⇒ x0 | x5 ⇒ x0 | x6 ⇒ x2 | x7 ⇒ x2
  | x8 ⇒ x0 | x9 ⇒ x0 | xA ⇒ x2 | xB ⇒ x2 
  | xC ⇒ x0 | xD ⇒ x0 | xE ⇒ x2 | xF ⇒ x2 ]
 | x3 ⇒ match e2 with
  [ x0 ⇒ x0 | x1 ⇒ x1 | x2 ⇒ x2 | x3 ⇒ x3 
  | x4 ⇒ x0 | x5 ⇒ x1 | x6 ⇒ x2 | x7 ⇒ x3
  | x8 ⇒ x0 | x9 ⇒ x1 | xA ⇒ x2 | xB ⇒ x3 
  | xC ⇒ x0 | xD ⇒ x1 | xE ⇒ x2 | xF ⇒ x3 ]
 | x4 ⇒ match e2 with
  [ x0 ⇒ x0 | x1 ⇒ x0 | x2 ⇒ x0 | x3 ⇒ x0 
  | x4 ⇒ x4 | x5 ⇒ x4 | x6 ⇒ x4 | x7 ⇒ x4
  | x8 ⇒ x0 | x9 ⇒ x0 | xA ⇒ x0 | xB ⇒ x0 
  | xC ⇒ x4 | xD ⇒ x4 | xE ⇒ x4 | xF ⇒ x4 ]
 | x5 ⇒ match e2 with
  [ x0 ⇒ x0 | x1 ⇒ x1 | x2 ⇒ x0 | x3 ⇒ x1 
  | x4 ⇒ x4 | x5 ⇒ x5 | x6 ⇒ x4 | x7 ⇒ x5
  | x8 ⇒ x0 | x9 ⇒ x1 | xA ⇒ x0 | xB ⇒ x1 
  | xC ⇒ x4 | xD ⇒ x5 | xE ⇒ x4 | xF ⇒ x5 ]
 | x6 ⇒ match e2 with
  [ x0 ⇒ x0 | x1 ⇒ x0 | x2 ⇒ x2 | x3 ⇒ x2 
  | x4 ⇒ x4 | x5 ⇒ x4 | x6 ⇒ x6 | x7 ⇒ x6
  | x8 ⇒ x0 | x9 ⇒ x0 | xA ⇒ x2 | xB ⇒ x2 
  | xC ⇒ x4 | xD ⇒ x4 | xE ⇒ x6 | xF ⇒ x6 ]
 | x7 ⇒ match e2 with
  [ x0 ⇒ x0 | x1 ⇒ x1 | x2 ⇒ x2 | x3 ⇒ x3 
  | x4 ⇒ x4 | x5 ⇒ x5 | x6 ⇒ x6 | x7 ⇒ x7
  | x8 ⇒ x0 | x9 ⇒ x1 | xA ⇒ x2 | xB ⇒ x3 
  | xC ⇒ x4 | xD ⇒ x5 | xE ⇒ x6 | xF ⇒ x7 ]
 | x8 ⇒ match e2 with
  [ x0 ⇒ x0 | x1 ⇒ x0 | x2 ⇒ x0 | x3 ⇒ x0 
  | x4 ⇒ x0 | x5 ⇒ x0 | x6 ⇒ x0 | x7 ⇒ x0
  | x8 ⇒ x8 | x9 ⇒ x8 | xA ⇒ x8 | xB ⇒ x8 
  | xC ⇒ x8 | xD ⇒ x8 | xE ⇒ x8 | xF ⇒ x8 ]
 | x9 ⇒ match e2 with
  [ x0 ⇒ x0 | x1 ⇒ x1 | x2 ⇒ x0 | x3 ⇒ x1 
  | x4 ⇒ x0 | x5 ⇒ x1 | x6 ⇒ x0 | x7 ⇒ x1
  | x8 ⇒ x8 | x9 ⇒ x9 | xA ⇒ x8 | xB ⇒ x9 
  | xC ⇒ x8 | xD ⇒ x9 | xE ⇒ x8 | xF ⇒ x9 ]
 | xA ⇒ match e2 with
  [ x0 ⇒ x0 | x1 ⇒ x0 | x2 ⇒ x2 | x3 ⇒ x2 
  | x4 ⇒ x0 | x5 ⇒ x0 | x6 ⇒ x2 | x7 ⇒ x2
  | x8 ⇒ x8 | x9 ⇒ x8 | xA ⇒ xA | xB ⇒ xA 
  | xC ⇒ x8 | xD ⇒ x8 | xE ⇒ xA | xF ⇒ xA ]
 | xB ⇒ match e2 with
  [ x0 ⇒ x0 | x1 ⇒ x1 | x2 ⇒ x2 | x3 ⇒ x3 
  | x4 ⇒ x0 | x5 ⇒ x1 | x6 ⇒ x2 | x7 ⇒ x3
  | x8 ⇒ x8 | x9 ⇒ x9 | xA ⇒ xA | xB ⇒ xB 
  | xC ⇒ x8 | xD ⇒ x9 | xE ⇒ xA | xF ⇒ xB ]
 | xC ⇒ match e2 with
  [ x0 ⇒ x0 | x1 ⇒ x0 | x2 ⇒ x0 | x3 ⇒ x0 
  | x4 ⇒ x4 | x5 ⇒ x4 | x6 ⇒ x4 | x7 ⇒ x4
  | x8 ⇒ x8 | x9 ⇒ x8 | xA ⇒ x8 | xB ⇒ x8 
  | xC ⇒ xC | xD ⇒ xC | xE ⇒ xC | xF ⇒ xC ] 
 | xD ⇒ match e2 with
  [ x0 ⇒ x0 | x1 ⇒ x1 | x2 ⇒ x0 | x3 ⇒ x1 
  | x4 ⇒ x4 | x5 ⇒ x5 | x6 ⇒ x4 | x7 ⇒ x5
  | x8 ⇒ x8 | x9 ⇒ x9 | xA ⇒ x8 | xB ⇒ x9 
  | xC ⇒ xC | xD ⇒ xD | xE ⇒ xC | xF ⇒ xD ] 
 | xE ⇒ match e2 with
  [ x0 ⇒ x0 | x1 ⇒ x0 | x2 ⇒ x2 | x3 ⇒ x2 
  | x4 ⇒ x4 | x5 ⇒ x4 | x6 ⇒ x6 | x7 ⇒ x6
  | x8 ⇒ x8 | x9 ⇒ x8 | xA ⇒ xA | xB ⇒ xA 
  | xC ⇒ xC | xD ⇒ xC | xE ⇒ xE | xF ⇒ xE ] 
 | xF ⇒ match e2 with
  [ x0 ⇒ x0 | x1 ⇒ x1 | x2 ⇒ x2 | x3 ⇒ x3 
  | x4 ⇒ x4 | x5 ⇒ x5 | x6 ⇒ x6 | x7 ⇒ x7
  | x8 ⇒ x8 | x9 ⇒ x9 | xA ⇒ xA | xB ⇒ xB 
  | xC ⇒ xC | xD ⇒ xD | xE ⇒ xE | xF ⇒ xF ]
 ]. 

(* operatore or *)
definition or_ex ≝
λe1,e2:exadecim.match e1 with
 [ x0 ⇒ match e2 with
  [ x0 ⇒ x0 | x1 ⇒ x1 | x2 ⇒ x2 | x3 ⇒ x3 
  | x4 ⇒ x4 | x5 ⇒ x5 | x6 ⇒ x6 | x7 ⇒ x7
  | x8 ⇒ x8 | x9 ⇒ x9 | xA ⇒ xA | xB ⇒ xB 
  | xC ⇒ xC | xD ⇒ xD | xE ⇒ xE | xF ⇒ xF ]
 | x1 ⇒ match e2 with
  [ x0 ⇒ x1 | x1 ⇒ x1 | x2 ⇒ x3 | x3 ⇒ x3 
  | x4 ⇒ x5 | x5 ⇒ x5 | x6 ⇒ x7 | x7 ⇒ x7
  | x8 ⇒ x9 | x9 ⇒ x9 | xA ⇒ xB | xB ⇒ xB 
  | xC ⇒ xD | xD ⇒ xD | xE ⇒ xF | xF ⇒ xF ]
 | x2 ⇒ match e2 with
  [ x0 ⇒ x2 | x1 ⇒ x3 | x2 ⇒ x2 | x3 ⇒ x3 
  | x4 ⇒ x6 | x5 ⇒ x7 | x6 ⇒ x6 | x7 ⇒ x7
  | x8 ⇒ xA | x9 ⇒ xB | xA ⇒ xA | xB ⇒ xB 
  | xC ⇒ xE | xD ⇒ xF | xE ⇒ xE | xF ⇒ xF ]
 | x3 ⇒ match e2 with
  [ x0 ⇒ x3 | x1 ⇒ x3 | x2 ⇒ x3 | x3 ⇒ x3 
  | x4 ⇒ x7 | x5 ⇒ x7 | x6 ⇒ x7 | x7 ⇒ x7
  | x8 ⇒ xB | x9 ⇒ xB | xA ⇒ xB | xB ⇒ xB 
  | xC ⇒ xF | xD ⇒ xF | xE ⇒ xF | xF ⇒ xF ]
 | x4 ⇒ match e2 with
  [ x0 ⇒ x4 | x1 ⇒ x5 | x2 ⇒ x6 | x3 ⇒ x7 
  | x4 ⇒ x4 | x5 ⇒ x5 | x6 ⇒ x6 | x7 ⇒ x7
  | x8 ⇒ xC | x9 ⇒ xD | xA ⇒ xE | xB ⇒ xF 
  | xC ⇒ xC | xD ⇒ xD | xE ⇒ xE | xF ⇒ xF ]
 | x5 ⇒ match e2 with
  [ x0 ⇒ x5 | x1 ⇒ x5 | x2 ⇒ x7 | x3 ⇒ x7 
  | x4 ⇒ x5 | x5 ⇒ x5 | x6 ⇒ x7 | x7 ⇒ x7
  | x8 ⇒ xD | x9 ⇒ xD | xA ⇒ xF | xB ⇒ xF 
  | xC ⇒ xD | xD ⇒ xD | xE ⇒ xF | xF ⇒ xF ]
 | x6 ⇒ match e2 with
  [ x0 ⇒ x6 | x1 ⇒ x7 | x2 ⇒ x6 | x3 ⇒ x7 
  | x4 ⇒ x6 | x5 ⇒ x7 | x6 ⇒ x6 | x7 ⇒ x7
  | x8 ⇒ xE | x9 ⇒ xF | xA ⇒ xE | xB ⇒ xF 
  | xC ⇒ xE | xD ⇒ xF | xE ⇒ xE | xF ⇒ xF ]
 | x7 ⇒ match e2 with
  [ x0 ⇒ x7 | x1 ⇒ x7 | x2 ⇒ x7 | x3 ⇒ x7 
  | x4 ⇒ x7 | x5 ⇒ x7 | x6 ⇒ x7 | x7 ⇒ x7
  | x8 ⇒ xF | x9 ⇒ xF | xA ⇒ xF | xB ⇒ xF 
  | xC ⇒ xF | xD ⇒ xF | xE ⇒ xF | xF ⇒ xF ]
 | x8 ⇒ match e2 with
  [ x0 ⇒ x8 | x1 ⇒ x9 | x2 ⇒ xA | x3 ⇒ xB 
  | x4 ⇒ xC | x5 ⇒ xD | x6 ⇒ xE | x7 ⇒ xF
  | x8 ⇒ x8 | x9 ⇒ x9 | xA ⇒ xA | xB ⇒ xB 
  | xC ⇒ xC | xD ⇒ xD | xE ⇒ xE | xF ⇒ xF ]
 | x9 ⇒ match e2 with
  [ x0 ⇒ x9 | x1 ⇒ x9 | x2 ⇒ xB | x3 ⇒ xB 
  | x4 ⇒ xD | x5 ⇒ xD | x6 ⇒ xF | x7 ⇒ xF
  | x8 ⇒ x9 | x9 ⇒ x9 | xA ⇒ xB | xB ⇒ xB 
  | xC ⇒ xD | xD ⇒ xD | xE ⇒ xF | xF ⇒ xF ]
 | xA ⇒ match e2 with
  [ x0 ⇒ xA | x1 ⇒ xB | x2 ⇒ xA | x3 ⇒ xB 
  | x4 ⇒ xE | x5 ⇒ xF | x6 ⇒ xE | x7 ⇒ xF
  | x8 ⇒ xA | x9 ⇒ xB | xA ⇒ xA | xB ⇒ xB 
  | xC ⇒ xE | xD ⇒ xF | xE ⇒ xE | xF ⇒ xF ]
 | xB ⇒ match e2 with
  [ x0 ⇒ xB | x1 ⇒ xB | x2 ⇒ xB | x3 ⇒ xB 
  | x4 ⇒ xF | x5 ⇒ xF | x6 ⇒ xF | x7 ⇒ xF
  | x8 ⇒ xB | x9 ⇒ xB | xA ⇒ xB | xB ⇒ xB 
  | xC ⇒ xF | xD ⇒ xF | xE ⇒ xF | xF ⇒ xF ]
 | xC ⇒ match e2 with
  [ x0 ⇒ xC | x1 ⇒ xD | x2 ⇒ xE | x3 ⇒ xF 
  | x4 ⇒ xC | x5 ⇒ xD | x6 ⇒ xE | x7 ⇒ xF
  | x8 ⇒ xC | x9 ⇒ xD | xA ⇒ xE | xB ⇒ xF 
  | xC ⇒ xC | xD ⇒ xD | xE ⇒ xE | xF ⇒ xF ]
 | xD ⇒ match e2 with
  [ x0 ⇒ xD | x1 ⇒ xD | x2 ⇒ xF | x3 ⇒ xF 
  | x4 ⇒ xD | x5 ⇒ xD | x6 ⇒ xF | x7 ⇒ xF
  | x8 ⇒ xD | x9 ⇒ xD | xA ⇒ xF | xB ⇒ xF 
  | xC ⇒ xD | xD ⇒ xD | xE ⇒ xF | xF ⇒ xF ]
 | xE ⇒ match e2 with
  [ x0 ⇒ xE | x1 ⇒ xF | x2 ⇒ xE | x3 ⇒ xF 
  | x4 ⇒ xE | x5 ⇒ xF | x6 ⇒ xE | x7 ⇒ xF
  | x8 ⇒ xE | x9 ⇒ xF | xA ⇒ xE | xB ⇒ xF 
  | xC ⇒ xE | xD ⇒ xF | xE ⇒ xE | xF ⇒ xF ]
 | xF ⇒ match e2 with
  [ x0 ⇒ xF | x1 ⇒ xF | x2 ⇒ xF | x3 ⇒ xF 
  | x4 ⇒ xF | x5 ⇒ xF | x6 ⇒ xF | x7 ⇒ xF
  | x8 ⇒ xF | x9 ⇒ xF | xA ⇒ xF | xB ⇒ xF 
  | xC ⇒ xF | xD ⇒ xF | xE ⇒ xF | xF ⇒ xF ]
 ].

(* operatore xor *)
definition xor_ex ≝
λe1,e2:exadecim.match e1 with
 [ x0 ⇒ match e2 with
  [ x0 ⇒ x0 | x1 ⇒ x1 | x2 ⇒ x2 | x3 ⇒ x3 
  | x4 ⇒ x4 | x5 ⇒ x5 | x6 ⇒ x6 | x7 ⇒ x7
  | x8 ⇒ x8 | x9 ⇒ x9 | xA ⇒ xA | xB ⇒ xB 
  | xC ⇒ xC | xD ⇒ xD | xE ⇒ xE | xF ⇒ xF ] 
 | x1 ⇒ match e2 with
  [ x0 ⇒ x1 | x1 ⇒ x0 | x2 ⇒ x3 | x3 ⇒ x2 
  | x4 ⇒ x5 | x5 ⇒ x4 | x6 ⇒ x7 | x7 ⇒ x6
  | x8 ⇒ x9 | x9 ⇒ x8 | xA ⇒ xB | xB ⇒ xA 
  | xC ⇒ xD | xD ⇒ xC | xE ⇒ xF | xF ⇒ xE ] 
 | x2 ⇒ match e2 with
  [ x0 ⇒ x2 | x1 ⇒ x3 | x2 ⇒ x0 | x3 ⇒ x1 
  | x4 ⇒ x6 | x5 ⇒ x7 | x6 ⇒ x4 | x7 ⇒ x5
  | x8 ⇒ xA | x9 ⇒ xB | xA ⇒ x8 | xB ⇒ x9 
  | xC ⇒ xE | xD ⇒ xF | xE ⇒ xC | xF ⇒ xD ] 
 | x3 ⇒ match e2 with
  [ x0 ⇒ x3 | x1 ⇒ x2 | x2 ⇒ x1 | x3 ⇒ x0 
  | x4 ⇒ x7 | x5 ⇒ x6 | x6 ⇒ x5 | x7 ⇒ x4
  | x8 ⇒ xB | x9 ⇒ xA | xA ⇒ x9 | xB ⇒ x8 
  | xC ⇒ xF | xD ⇒ xE | xE ⇒ xD | xF ⇒ xC ] 
 | x4 ⇒ match e2 with
  [ x0 ⇒ x4 | x1 ⇒ x5 | x2 ⇒ x6 | x3 ⇒ x7 
  | x4 ⇒ x0 | x5 ⇒ x1 | x6 ⇒ x2 | x7 ⇒ x3
  | x8 ⇒ xC | x9 ⇒ xD | xA ⇒ xE | xB ⇒ xF 
  | xC ⇒ x8 | xD ⇒ x9 | xE ⇒ xA | xF ⇒ xB ] 
 | x5 ⇒ match e2 with
  [ x0 ⇒ x5 | x1 ⇒ x4 | x2 ⇒ x7 | x3 ⇒ x6 
  | x4 ⇒ x1 | x5 ⇒ x0 | x6 ⇒ x3 | x7 ⇒ x2
  | x8 ⇒ xD | x9 ⇒ xC | xA ⇒ xF | xB ⇒ xE 
  | xC ⇒ x9 | xD ⇒ x8 | xE ⇒ xB | xF ⇒ xA ] 
 | x6 ⇒ match e2 with
  [ x0 ⇒ x6 | x1 ⇒ x7 | x2 ⇒ x4 | x3 ⇒ x5 
  | x4 ⇒ x2 | x5 ⇒ x3 | x6 ⇒ x0 | x7 ⇒ x1
  | x8 ⇒ xE | x9 ⇒ xF | xA ⇒ xC | xB ⇒ xD 
  | xC ⇒ xA | xD ⇒ xB | xE ⇒ x8 | xF ⇒ x9 ] 
 | x7 ⇒ match e2 with
  [ x0 ⇒ x7 | x1 ⇒ x6 | x2 ⇒ x5 | x3 ⇒ x4 
  | x4 ⇒ x3 | x5 ⇒ x2 | x6 ⇒ x1 | x7 ⇒ x0
  | x8 ⇒ xF | x9 ⇒ xE | xA ⇒ xD | xB ⇒ xC 
  | xC ⇒ xB | xD ⇒ xA | xE ⇒ x9 | xF ⇒ x8 ] 
 | x8 ⇒ match e2 with
  [ x0 ⇒ x8 | x1 ⇒ x9 | x2 ⇒ xA | x3 ⇒ xB 
  | x4 ⇒ xC | x5 ⇒ xD | x6 ⇒ xE | x7 ⇒ xF
  | x8 ⇒ x0 | x9 ⇒ x1 | xA ⇒ x2 | xB ⇒ x3 
  | xC ⇒ x4 | xD ⇒ x5 | xE ⇒ x6 | xF ⇒ x7 ] 
 | x9 ⇒ match e2 with
  [ x0 ⇒ x9 | x1 ⇒ x8 | x2 ⇒ xB | x3 ⇒ xA 
  | x4 ⇒ xD | x5 ⇒ xC | x6 ⇒ xF | x7 ⇒ xE
  | x8 ⇒ x1 | x9 ⇒ x0 | xA ⇒ x3 | xB ⇒ x2 
  | xC ⇒ x5 | xD ⇒ x4 | xE ⇒ x7 | xF ⇒ x6 ] 
 | xA ⇒ match e2 with
  [ x0 ⇒ xA | x1 ⇒ xB | x2 ⇒ x8 | x3 ⇒ x9 
  | x4 ⇒ xE | x5 ⇒ xF | x6 ⇒ xC | x7 ⇒ xD
  | x8 ⇒ x2 | x9 ⇒ x3 | xA ⇒ x0 | xB ⇒ x1 
  | xC ⇒ x6 | xD ⇒ x7 | xE ⇒ x4 | xF ⇒ x5 ] 
 | xB ⇒ match e2 with
  [ x0 ⇒ xB | x1 ⇒ xA | x2 ⇒ x9 | x3 ⇒ x8 
  | x4 ⇒ xF | x5 ⇒ xE | x6 ⇒ xD | x7 ⇒ xC
  | x8 ⇒ x3 | x9 ⇒ x2 | xA ⇒ x1 | xB ⇒ x0 
  | xC ⇒ x7 | xD ⇒ x6 | xE ⇒ x5 | xF ⇒ x4 ]
 | xC ⇒ match e2 with
  [ x0 ⇒ xC | x1 ⇒ xD | x2 ⇒ xE | x3 ⇒ xF 
  | x4 ⇒ x8 | x5 ⇒ x9 | x6 ⇒ xA | x7 ⇒ xB
  | x8 ⇒ x4 | x9 ⇒ x5 | xA ⇒ x6 | xB ⇒ x7 
  | xC ⇒ x0 | xD ⇒ x1 | xE ⇒ x2 | xF ⇒ x3 ] 
 | xD ⇒ match e2 with
  [ x0 ⇒ xD | x1 ⇒ xC | x2 ⇒ xF | x3 ⇒ xE 
  | x4 ⇒ x9 | x5 ⇒ x8 | x6 ⇒ xB | x7 ⇒ xA
  | x8 ⇒ x5 | x9 ⇒ x4 | xA ⇒ x7 | xB ⇒ x6 
  | xC ⇒ x1 | xD ⇒ x0 | xE ⇒ x3 | xF ⇒ x2 ]
 | xE ⇒ match e2 with
  [ x0 ⇒ xE | x1 ⇒ xF | x2 ⇒ xC | x3 ⇒ xD 
  | x4 ⇒ xA | x5 ⇒ xB | x6 ⇒ x8 | x7 ⇒ x9
  | x8 ⇒ x6 | x9 ⇒ x7 | xA ⇒ x4 | xB ⇒ x5 
  | xC ⇒ x2 | xD ⇒ x3 | xE ⇒ x0 | xF ⇒ x1 ] 
 | xF ⇒ match e2 with
  [ x0 ⇒ xF | x1 ⇒ xE | x2 ⇒ xD | x3 ⇒ xC 
  | x4 ⇒ xB | x5 ⇒ xA | x6 ⇒ x9 | x7 ⇒ x8
  | x8 ⇒ x7 | x9 ⇒ x6 | xA ⇒ x5 | xB ⇒ x4 
  | xC ⇒ x3 | xD ⇒ x2 | xE ⇒ x1 | xF ⇒ x0 ] 
 ].

(* operatore rotazione destra con carry *)
definition rcr_ex ≝
λe:exadecim.λc:bool.match c with
 [ true ⇒ match e with
  [ x0 ⇒ pair exadecim bool x8 false | x1 ⇒ pair exadecim bool x8 true
  | x2 ⇒ pair exadecim bool x9 false | x3 ⇒ pair exadecim bool x9 true
  | x4 ⇒ pair exadecim bool xA false | x5 ⇒ pair exadecim bool xA true
  | x6 ⇒ pair exadecim bool xB false | x7 ⇒ pair exadecim bool xB true
  | x8 ⇒ pair exadecim bool xC false | x9 ⇒ pair exadecim bool xC true
  | xA ⇒ pair exadecim bool xD false | xB ⇒ pair exadecim bool xD true
  | xC ⇒ pair exadecim bool xE false | xD ⇒ pair exadecim bool xE true
  | xE ⇒ pair exadecim bool xF false | xF ⇒ pair exadecim bool xF true ]
 | false ⇒ match e with 
  [ x0 ⇒ pair exadecim bool x0 false | x1 ⇒ pair exadecim bool x0 true
  | x2 ⇒ pair exadecim bool x1 false | x3 ⇒ pair exadecim bool x1 true
  | x4 ⇒ pair exadecim bool x2 false | x5 ⇒ pair exadecim bool x2 true
  | x6 ⇒ pair exadecim bool x3 false | x7 ⇒ pair exadecim bool x3 true
  | x8 ⇒ pair exadecim bool x4 false | x9 ⇒ pair exadecim bool x4 true
  | xA ⇒ pair exadecim bool x5 false | xB ⇒ pair exadecim bool x5 true
  | xC ⇒ pair exadecim bool x6 false | xD ⇒ pair exadecim bool x6 true
  | xE ⇒ pair exadecim bool x7 false | xF ⇒ pair exadecim bool x7 true ]
 ].

(* operatore shift destro *)
definition shr_ex ≝
λe:exadecim.match e with 
 [ x0 ⇒ pair exadecim bool x0 false | x1 ⇒ pair exadecim bool x0 true
 | x2 ⇒ pair exadecim bool x1 false | x3 ⇒ pair exadecim bool x1 true
 | x4 ⇒ pair exadecim bool x2 false | x5 ⇒ pair exadecim bool x2 true
 | x6 ⇒ pair exadecim bool x3 false | x7 ⇒ pair exadecim bool x3 true
 | x8 ⇒ pair exadecim bool x4 false | x9 ⇒ pair exadecim bool x4 true
 | xA ⇒ pair exadecim bool x5 false | xB ⇒ pair exadecim bool x5 true
 | xC ⇒ pair exadecim bool x6 false | xD ⇒ pair exadecim bool x6 true
 | xE ⇒ pair exadecim bool x7 false | xF ⇒ pair exadecim bool x7 true ].

(* operatore rotazione destra *)
definition ror_ex ≝
λe:exadecim.match e with 
 [ x0 ⇒ x0 | x1 ⇒ x8 | x2 ⇒ x1 | x3 ⇒ x9
 | x4 ⇒ x2 | x5 ⇒ xA | x6 ⇒ x3 | x7 ⇒ xB 
 | x8 ⇒ x4 | x9 ⇒ xC | xA ⇒ x5 | xB ⇒ xD 
 | xC ⇒ x6 | xD ⇒ xE | xE ⇒ x7 | xF ⇒ xF ].

(* operatore rotazione destra n-volte *)
let rec ror_ex_n (e:exadecim) (n:nat) on n ≝
 match n with
  [ O ⇒ e
  | S n' ⇒ ror_ex_n (ror_ex e) n' ].

(* operatore rotazione sinistra con carry *)
definition rcl_ex ≝
λe:exadecim.λc:bool.match c with
 [ true ⇒ match e with
  [ x0 ⇒ pair exadecim bool x1 false | x1 ⇒ pair exadecim bool x3 false
  | x2 ⇒ pair exadecim bool x5 false | x3 ⇒ pair exadecim bool x7 false
  | x4 ⇒ pair exadecim bool x9 false | x5 ⇒ pair exadecim bool xB false
  | x6 ⇒ pair exadecim bool xD false | x7 ⇒ pair exadecim bool xF false
  | x8 ⇒ pair exadecim bool x1 true  | x9 ⇒ pair exadecim bool x3 true
  | xA ⇒ pair exadecim bool x5 true  | xB ⇒ pair exadecim bool x7 true
  | xC ⇒ pair exadecim bool x9 true  | xD ⇒ pair exadecim bool xB true
  | xE ⇒ pair exadecim bool xD true  | xF ⇒ pair exadecim bool xF true ]
 | false ⇒ match e with
  [ x0 ⇒ pair exadecim bool x0 false | x1 ⇒ pair exadecim bool x2 false
  | x2 ⇒ pair exadecim bool x4 false | x3 ⇒ pair exadecim bool x6 false
  | x4 ⇒ pair exadecim bool x8 false | x5 ⇒ pair exadecim bool xA false
  | x6 ⇒ pair exadecim bool xC false | x7 ⇒ pair exadecim bool xE false
  | x8 ⇒ pair exadecim bool x0 true  | x9 ⇒ pair exadecim bool x2 true
  | xA ⇒ pair exadecim bool x4 true  | xB ⇒ pair exadecim bool x6 true
  | xC ⇒ pair exadecim bool x8 true  | xD ⇒ pair exadecim bool xA true
  | xE ⇒ pair exadecim bool xC true  | xF ⇒ pair exadecim bool xE true ]
 ].

(* operatore shift sinistro *)
definition shl_ex ≝
λe:exadecim.match e with
 [ x0 ⇒ pair exadecim bool x0 false | x1 ⇒ pair exadecim bool x2 false
 | x2 ⇒ pair exadecim bool x4 false | x3 ⇒ pair exadecim bool x6 false
 | x4 ⇒ pair exadecim bool x8 false | x5 ⇒ pair exadecim bool xA false
 | x6 ⇒ pair exadecim bool xC false | x7 ⇒ pair exadecim bool xE false
 | x8 ⇒ pair exadecim bool x0 true  | x9 ⇒ pair exadecim bool x2 true
 | xA ⇒ pair exadecim bool x4 true  | xB ⇒ pair exadecim bool x6 true
 | xC ⇒ pair exadecim bool x8 true  | xD ⇒ pair exadecim bool xA true
 | xE ⇒ pair exadecim bool xC true  | xF ⇒ pair exadecim bool xE true ].

(* operatore rotazione sinistra *)
definition rol_ex ≝
λe:exadecim.match e with
 [ x0 ⇒ x0 | x1 ⇒ x2 | x2 ⇒ x4 | x3 ⇒ x6
 | x4 ⇒ x8 | x5 ⇒ xA | x6 ⇒ xC | x7 ⇒ xE
 | x8 ⇒ x1 | x9 ⇒ x3 | xA ⇒ x5 | xB ⇒ x7
 | xC ⇒ x9 | xD ⇒ xB | xE ⇒ xD | xF ⇒ xF ].

(* operatore rotazione sinistra n-volte *)
let rec rol_ex_n (e:exadecim) (n:nat) on n ≝
 match n with
  [ O ⇒ e
  | S n' ⇒ rol_ex_n (rol_ex e) n' ].

(* operatore not/complemento a 1 *)
definition not_ex ≝
λe:exadecim.match e with
 [ x0 ⇒ xF | x1 ⇒ xE | x2 ⇒ xD | x3 ⇒ xC
 | x4 ⇒ xB | x5 ⇒ xA | x6 ⇒ x9 | x7 ⇒ x8
 | x8 ⇒ x7 | x9 ⇒ x6 | xA ⇒ x5 | xB ⇒ x4
 | xC ⇒ x3 | xD ⇒ x2 | xE ⇒ x1 | xF ⇒ x0 ].

(* operatore somma con carry *)
definition plus_ex ≝
λe1,e2:exadecim.λc:bool.
  match c with
   [ true ⇒
      match e1 with
       [ x0 ⇒
           match e2 with
            [ x0 ⇒ pair exadecim bool x1 false
            | x1 ⇒ pair exadecim bool x2 false
            | x2 ⇒ pair exadecim bool x3 false
            | x3 ⇒ pair exadecim bool x4 false
            | x4 ⇒ pair exadecim bool x5 false
            | x5 ⇒ pair exadecim bool x6 false
            | x6 ⇒ pair exadecim bool x7 false
            | x7 ⇒ pair exadecim bool x8 false
            | x8 ⇒ pair exadecim bool x9 false
            | x9 ⇒ pair exadecim bool xA false
            | xA ⇒ pair exadecim bool xB false
            | xB ⇒ pair exadecim bool xC false
            | xC ⇒ pair exadecim bool xD false
            | xD ⇒ pair exadecim bool xE false
            | xE ⇒ pair exadecim bool xF false
            | xF ⇒ pair exadecim bool x0 true ] 
       | x1 ⇒
           match e2 with
            [ x0 ⇒ pair exadecim bool x2 false
            | x1 ⇒ pair exadecim bool x3 false
            | x2 ⇒ pair exadecim bool x4 false
            | x3 ⇒ pair exadecim bool x5 false
            | x4 ⇒ pair exadecim bool x6 false
            | x5 ⇒ pair exadecim bool x7 false
            | x6 ⇒ pair exadecim bool x8 false
            | x7 ⇒ pair exadecim bool x9 false
            | x8 ⇒ pair exadecim bool xA false
            | x9 ⇒ pair exadecim bool xB false
            | xA ⇒ pair exadecim bool xC false
            | xB ⇒ pair exadecim bool xD false
            | xC ⇒ pair exadecim bool xE false
            | xD ⇒ pair exadecim bool xF false
            | xE ⇒ pair exadecim bool x0 true
            | xF ⇒ pair exadecim bool x1 true ] 
       | x2 ⇒
           match e2 with
            [ x0 ⇒ pair exadecim bool x3 false
            | x1 ⇒ pair exadecim bool x4 false
            | x2 ⇒ pair exadecim bool x5 false
            | x3 ⇒ pair exadecim bool x6 false
            | x4 ⇒ pair exadecim bool x7 false
            | x5 ⇒ pair exadecim bool x8 false
            | x6 ⇒ pair exadecim bool x9 false
            | x7 ⇒ pair exadecim bool xA false
            | x8 ⇒ pair exadecim bool xB false
            | x9 ⇒ pair exadecim bool xC false
            | xA ⇒ pair exadecim bool xD false
            | xB ⇒ pair exadecim bool xE false
            | xC ⇒ pair exadecim bool xF false
            | xD ⇒ pair exadecim bool x0 true
            | xE ⇒ pair exadecim bool x1 true
            | xF ⇒ pair exadecim bool x2 true ] 
       | x3 ⇒
           match e2 with
            [ x0 ⇒ pair exadecim bool x4 false
            | x1 ⇒ pair exadecim bool x5 false
            | x2 ⇒ pair exadecim bool x6 false
            | x3 ⇒ pair exadecim bool x7 false
            | x4 ⇒ pair exadecim bool x8 false
            | x5 ⇒ pair exadecim bool x9 false
            | x6 ⇒ pair exadecim bool xA false
            | x7 ⇒ pair exadecim bool xB false
            | x8 ⇒ pair exadecim bool xC false
            | x9 ⇒ pair exadecim bool xD false
            | xA ⇒ pair exadecim bool xE false
            | xB ⇒ pair exadecim bool xF false
            | xC ⇒ pair exadecim bool x0 true
            | xD ⇒ pair exadecim bool x1 true
            | xE ⇒ pair exadecim bool x2 true
            | xF ⇒ pair exadecim bool x3 true ] 
       | x4 ⇒
           match e2 with
            [ x0 ⇒ pair exadecim bool x5 false
            | x1 ⇒ pair exadecim bool x6 false
            | x2 ⇒ pair exadecim bool x7 false
            | x3 ⇒ pair exadecim bool x8 false
            | x4 ⇒ pair exadecim bool x9 false
            | x5 ⇒ pair exadecim bool xA false
            | x6 ⇒ pair exadecim bool xB false
            | x7 ⇒ pair exadecim bool xC false
            | x8 ⇒ pair exadecim bool xD false
            | x9 ⇒ pair exadecim bool xE false
            | xA ⇒ pair exadecim bool xF false
            | xB ⇒ pair exadecim bool x0 true
            | xC ⇒ pair exadecim bool x1 true
            | xD ⇒ pair exadecim bool x2 true
            | xE ⇒ pair exadecim bool x3 true
            | xF ⇒ pair exadecim bool x4 true ] 
       | x5 ⇒
           match e2 with
            [ x0 ⇒ pair exadecim bool x6 false
            | x1 ⇒ pair exadecim bool x7 false
            | x2 ⇒ pair exadecim bool x8 false
            | x3 ⇒ pair exadecim bool x9 false
            | x4 ⇒ pair exadecim bool xA false
            | x5 ⇒ pair exadecim bool xB false
            | x6 ⇒ pair exadecim bool xC false
            | x7 ⇒ pair exadecim bool xD false
            | x8 ⇒ pair exadecim bool xE false
            | x9 ⇒ pair exadecim bool xF false
            | xA ⇒ pair exadecim bool x0 true
            | xB ⇒ pair exadecim bool x1 true
            | xC ⇒ pair exadecim bool x2 true
            | xD ⇒ pair exadecim bool x3 true
            | xE ⇒ pair exadecim bool x4 true
            | xF ⇒ pair exadecim bool x5 true ] 
       | x6 ⇒
           match e2 with
            [ x0 ⇒ pair exadecim bool x7 false
            | x1 ⇒ pair exadecim bool x8 false
            | x2 ⇒ pair exadecim bool x9 false
            | x3 ⇒ pair exadecim bool xA false
            | x4 ⇒ pair exadecim bool xB false
            | x5 ⇒ pair exadecim bool xC false
            | x6 ⇒ pair exadecim bool xD false
            | x7 ⇒ pair exadecim bool xE false
            | x8 ⇒ pair exadecim bool xF false
            | x9 ⇒ pair exadecim bool x0 true
            | xA ⇒ pair exadecim bool x1 true
            | xB ⇒ pair exadecim bool x2 true
            | xC ⇒ pair exadecim bool x3 true
            | xD ⇒ pair exadecim bool x4 true
            | xE ⇒ pair exadecim bool x5 true
            | xF ⇒ pair exadecim bool x6 true ] 
       | x7 ⇒
           match e2 with
            [ x0 ⇒ pair exadecim bool x8 false
            | x1 ⇒ pair exadecim bool x9 false
            | x2 ⇒ pair exadecim bool xA false
            | x3 ⇒ pair exadecim bool xB false
            | x4 ⇒ pair exadecim bool xC false
            | x5 ⇒ pair exadecim bool xD false
            | x6 ⇒ pair exadecim bool xE false
            | x7 ⇒ pair exadecim bool xF false
            | x8 ⇒ pair exadecim bool x0 true
            | x9 ⇒ pair exadecim bool x1 true
            | xA ⇒ pair exadecim bool x2 true
            | xB ⇒ pair exadecim bool x3 true
            | xC ⇒ pair exadecim bool x4 true
            | xD ⇒ pair exadecim bool x5 true
            | xE ⇒ pair exadecim bool x6 true
            | xF ⇒ pair exadecim bool x7 true ] 
       | x8 ⇒
           match e2 with
            [ x0 ⇒ pair exadecim bool x9 false
            | x1 ⇒ pair exadecim bool xA false
            | x2 ⇒ pair exadecim bool xB false
            | x3 ⇒ pair exadecim bool xC false
            | x4 ⇒ pair exadecim bool xD false
            | x5 ⇒ pair exadecim bool xE false
            | x6 ⇒ pair exadecim bool xF false
            | x7 ⇒ pair exadecim bool x0 true
            | x8 ⇒ pair exadecim bool x1 true
            | x9 ⇒ pair exadecim bool x2 true
            | xA ⇒ pair exadecim bool x3 true
            | xB ⇒ pair exadecim bool x4 true
            | xC ⇒ pair exadecim bool x5 true
            | xD ⇒ pair exadecim bool x6 true
            | xE ⇒ pair exadecim bool x7 true
            | xF ⇒ pair exadecim bool x8 true ] 
       | x9 ⇒
           match e2 with
            [ x0 ⇒ pair exadecim bool xA false
            | x1 ⇒ pair exadecim bool xB false
            | x2 ⇒ pair exadecim bool xC false
            | x3 ⇒ pair exadecim bool xD false
            | x4 ⇒ pair exadecim bool xE false
            | x5 ⇒ pair exadecim bool xF false
            | x6 ⇒ pair exadecim bool x0 true
            | x7 ⇒ pair exadecim bool x1 true
            | x8 ⇒ pair exadecim bool x2 true
            | x9 ⇒ pair exadecim bool x3 true
            | xA ⇒ pair exadecim bool x4 true
            | xB ⇒ pair exadecim bool x5 true
            | xC ⇒ pair exadecim bool x6 true
            | xD ⇒ pair exadecim bool x7 true
            | xE ⇒ pair exadecim bool x8 true
            | xF ⇒ pair exadecim bool x9 true ] 
       | xA ⇒
           match e2 with
            [ x0 ⇒ pair exadecim bool xB false
            | x1 ⇒ pair exadecim bool xC false
            | x2 ⇒ pair exadecim bool xD false
            | x3 ⇒ pair exadecim bool xE false
            | x4 ⇒ pair exadecim bool xF false
            | x5 ⇒ pair exadecim bool x0 true
            | x6 ⇒ pair exadecim bool x1 true
            | x7 ⇒ pair exadecim bool x2 true
            | x8 ⇒ pair exadecim bool x3 true
            | x9 ⇒ pair exadecim bool x4 true
            | xA ⇒ pair exadecim bool x5 true
            | xB ⇒ pair exadecim bool x6 true
            | xC ⇒ pair exadecim bool x7 true
            | xD ⇒ pair exadecim bool x8 true
            | xE ⇒ pair exadecim bool x9 true
            | xF ⇒ pair exadecim bool xA true ] 
       | xB ⇒
           match e2 with
            [ x0 ⇒ pair exadecim bool xC false
            | x1 ⇒ pair exadecim bool xD false
            | x2 ⇒ pair exadecim bool xE false
            | x3 ⇒ pair exadecim bool xF false
            | x4 ⇒ pair exadecim bool x0 true
            | x5 ⇒ pair exadecim bool x1 true
            | x6 ⇒ pair exadecim bool x2 true
            | x7 ⇒ pair exadecim bool x3 true
            | x8 ⇒ pair exadecim bool x4 true
            | x9 ⇒ pair exadecim bool x5 true
            | xA ⇒ pair exadecim bool x6 true
            | xB ⇒ pair exadecim bool x7 true
            | xC ⇒ pair exadecim bool x8 true
            | xD ⇒ pair exadecim bool x9 true
            | xE ⇒ pair exadecim bool xA true
            | xF ⇒ pair exadecim bool xB true ] 
       | xC ⇒
           match e2 with
            [ x0 ⇒ pair exadecim bool xD false
            | x1 ⇒ pair exadecim bool xE false
            | x2 ⇒ pair exadecim bool xF false
            | x3 ⇒ pair exadecim bool x0 true
            | x4 ⇒ pair exadecim bool x1 true
            | x5 ⇒ pair exadecim bool x2 true
            | x6 ⇒ pair exadecim bool x3 true
            | x7 ⇒ pair exadecim bool x4 true
            | x8 ⇒ pair exadecim bool x5 true
            | x9 ⇒ pair exadecim bool x6 true
            | xA ⇒ pair exadecim bool x7 true
            | xB ⇒ pair exadecim bool x8 true
            | xC ⇒ pair exadecim bool x9 true
            | xD ⇒ pair exadecim bool xA true
            | xE ⇒ pair exadecim bool xB true
            | xF ⇒ pair exadecim bool xC true ] 
       | xD ⇒
           match e2 with
            [ x0 ⇒ pair exadecim bool xE false
            | x1 ⇒ pair exadecim bool xF false
            | x2 ⇒ pair exadecim bool x0 true
            | x3 ⇒ pair exadecim bool x1 true
            | x4 ⇒ pair exadecim bool x2 true
            | x5 ⇒ pair exadecim bool x3 true
            | x6 ⇒ pair exadecim bool x4 true
            | x7 ⇒ pair exadecim bool x5 true
            | x8 ⇒ pair exadecim bool x6 true
            | x9 ⇒ pair exadecim bool x7 true
            | xA ⇒ pair exadecim bool x8 true
            | xB ⇒ pair exadecim bool x9 true
            | xC ⇒ pair exadecim bool xA true
            | xD ⇒ pair exadecim bool xB true
            | xE ⇒ pair exadecim bool xC true
            | xF ⇒ pair exadecim bool xD true ] 
       | xE ⇒
           match e2 with
            [ x0 ⇒ pair exadecim bool xF false
            | x1 ⇒ pair exadecim bool x0 true
            | x2 ⇒ pair exadecim bool x1 true
            | x3 ⇒ pair exadecim bool x2 true
            | x4 ⇒ pair exadecim bool x3 true
            | x5 ⇒ pair exadecim bool x4 true
            | x6 ⇒ pair exadecim bool x5 true
            | x7 ⇒ pair exadecim bool x6 true
            | x8 ⇒ pair exadecim bool x7 true
            | x9 ⇒ pair exadecim bool x8 true
            | xA ⇒ pair exadecim bool x9 true
            | xB ⇒ pair exadecim bool xA true
            | xC ⇒ pair exadecim bool xB true
            | xD ⇒ pair exadecim bool xC true
            | xE ⇒ pair exadecim bool xD true
            | xF ⇒ pair exadecim bool xE true ]
       | xF ⇒
           match e2 with
            [ x0 ⇒ pair exadecim bool x0 true
            | x1 ⇒ pair exadecim bool x1 true
            | x2 ⇒ pair exadecim bool x2 true
            | x3 ⇒ pair exadecim bool x3 true
            | x4 ⇒ pair exadecim bool x4 true
            | x5 ⇒ pair exadecim bool x5 true
            | x6 ⇒ pair exadecim bool x6 true
            | x7 ⇒ pair exadecim bool x7 true
            | x8 ⇒ pair exadecim bool x8 true
            | x9 ⇒ pair exadecim bool x9 true
            | xA ⇒ pair exadecim bool xA true
            | xB ⇒ pair exadecim bool xB true
            | xC ⇒ pair exadecim bool xC true
            | xD ⇒ pair exadecim bool xD true
            | xE ⇒ pair exadecim bool xE true
            | xF ⇒ pair exadecim bool xF true ] 
       ]
   | false ⇒
      match e1 with
       [ x0 ⇒
           match e2 with
            [ x0 ⇒ pair exadecim bool x0 false
            | x1 ⇒ pair exadecim bool x1 false
            | x2 ⇒ pair exadecim bool x2 false
            | x3 ⇒ pair exadecim bool x3 false
            | x4 ⇒ pair exadecim bool x4 false
            | x5 ⇒ pair exadecim bool x5 false
            | x6 ⇒ pair exadecim bool x6 false
            | x7 ⇒ pair exadecim bool x7 false
            | x8 ⇒ pair exadecim bool x8 false
            | x9 ⇒ pair exadecim bool x9 false
            | xA ⇒ pair exadecim bool xA false
            | xB ⇒ pair exadecim bool xB false
            | xC ⇒ pair exadecim bool xC false
            | xD ⇒ pair exadecim bool xD false
            | xE ⇒ pair exadecim bool xE false
            | xF ⇒ pair exadecim bool xF false ] 
       | x1 ⇒
           match e2 with
            [ x0 ⇒ pair exadecim bool x1 false
            | x1 ⇒ pair exadecim bool x2 false
            | x2 ⇒ pair exadecim bool x3 false
            | x3 ⇒ pair exadecim bool x4 false
            | x4 ⇒ pair exadecim bool x5 false
            | x5 ⇒ pair exadecim bool x6 false
            | x6 ⇒ pair exadecim bool x7 false
            | x7 ⇒ pair exadecim bool x8 false
            | x8 ⇒ pair exadecim bool x9 false
            | x9 ⇒ pair exadecim bool xA false
            | xA ⇒ pair exadecim bool xB false
            | xB ⇒ pair exadecim bool xC false
            | xC ⇒ pair exadecim bool xD false
            | xD ⇒ pair exadecim bool xE false
            | xE ⇒ pair exadecim bool xF false
            | xF ⇒ pair exadecim bool x0 true ] 
       | x2 ⇒
           match e2 with
            [ x0 ⇒ pair exadecim bool x2 false
            | x1 ⇒ pair exadecim bool x3 false
            | x2 ⇒ pair exadecim bool x4 false
            | x3 ⇒ pair exadecim bool x5 false
            | x4 ⇒ pair exadecim bool x6 false
            | x5 ⇒ pair exadecim bool x7 false
            | x6 ⇒ pair exadecim bool x8 false
            | x7 ⇒ pair exadecim bool x9 false
            | x8 ⇒ pair exadecim bool xA false
            | x9 ⇒ pair exadecim bool xB false
            | xA ⇒ pair exadecim bool xC false
            | xB ⇒ pair exadecim bool xD false
            | xC ⇒ pair exadecim bool xE false
            | xD ⇒ pair exadecim bool xF false
            | xE ⇒ pair exadecim bool x0 true
            | xF ⇒ pair exadecim bool x1 true ] 
       | x3 ⇒
           match e2 with
            [ x0 ⇒ pair exadecim bool x3 false
            | x1 ⇒ pair exadecim bool x4 false
            | x2 ⇒ pair exadecim bool x5 false
            | x3 ⇒ pair exadecim bool x6 false
            | x4 ⇒ pair exadecim bool x7 false
            | x5 ⇒ pair exadecim bool x8 false
            | x6 ⇒ pair exadecim bool x9 false
            | x7 ⇒ pair exadecim bool xA false
            | x8 ⇒ pair exadecim bool xB false
            | x9 ⇒ pair exadecim bool xC false
            | xA ⇒ pair exadecim bool xD false
            | xB ⇒ pair exadecim bool xE false
            | xC ⇒ pair exadecim bool xF false
            | xD ⇒ pair exadecim bool x0 true
            | xE ⇒ pair exadecim bool x1 true
            | xF ⇒ pair exadecim bool x2 true ] 
       | x4 ⇒
           match e2 with
            [ x0 ⇒ pair exadecim bool x4 false
            | x1 ⇒ pair exadecim bool x5 false
            | x2 ⇒ pair exadecim bool x6 false
            | x3 ⇒ pair exadecim bool x7 false
            | x4 ⇒ pair exadecim bool x8 false
            | x5 ⇒ pair exadecim bool x9 false
            | x6 ⇒ pair exadecim bool xA false
            | x7 ⇒ pair exadecim bool xB false
            | x8 ⇒ pair exadecim bool xC false
            | x9 ⇒ pair exadecim bool xD false
            | xA ⇒ pair exadecim bool xE false
            | xB ⇒ pair exadecim bool xF false
            | xC ⇒ pair exadecim bool x0 true
            | xD ⇒ pair exadecim bool x1 true
            | xE ⇒ pair exadecim bool x2 true
            | xF ⇒ pair exadecim bool x3 true ] 
       | x5 ⇒
           match e2 with
            [ x0 ⇒ pair exadecim bool x5 false
            | x1 ⇒ pair exadecim bool x6 false
            | x2 ⇒ pair exadecim bool x7 false
            | x3 ⇒ pair exadecim bool x8 false
            | x4 ⇒ pair exadecim bool x9 false
            | x5 ⇒ pair exadecim bool xA false
            | x6 ⇒ pair exadecim bool xB false
            | x7 ⇒ pair exadecim bool xC false
            | x8 ⇒ pair exadecim bool xD false
            | x9 ⇒ pair exadecim bool xE false
            | xA ⇒ pair exadecim bool xF false
            | xB ⇒ pair exadecim bool x0 true
            | xC ⇒ pair exadecim bool x1 true
            | xD ⇒ pair exadecim bool x2 true
            | xE ⇒ pair exadecim bool x3 true
            | xF ⇒ pair exadecim bool x4 true ] 
       | x6 ⇒
           match e2 with
            [ x0 ⇒ pair exadecim bool x6 false
            | x1 ⇒ pair exadecim bool x7 false
            | x2 ⇒ pair exadecim bool x8 false
            | x3 ⇒ pair exadecim bool x9 false
            | x4 ⇒ pair exadecim bool xA false
            | x5 ⇒ pair exadecim bool xB false
            | x6 ⇒ pair exadecim bool xC false
            | x7 ⇒ pair exadecim bool xD false
            | x8 ⇒ pair exadecim bool xE false
            | x9 ⇒ pair exadecim bool xF false
            | xA ⇒ pair exadecim bool x0 true
            | xB ⇒ pair exadecim bool x1 true
            | xC ⇒ pair exadecim bool x2 true
            | xD ⇒ pair exadecim bool x3 true
            | xE ⇒ pair exadecim bool x4 true
            | xF ⇒ pair exadecim bool x5 true ] 
       | x7 ⇒
           match e2 with
            [ x0 ⇒ pair exadecim bool x7 false
            | x1 ⇒ pair exadecim bool x8 false
            | x2 ⇒ pair exadecim bool x9 false
            | x3 ⇒ pair exadecim bool xA false
            | x4 ⇒ pair exadecim bool xB false
            | x5 ⇒ pair exadecim bool xC false
            | x6 ⇒ pair exadecim bool xD false
            | x7 ⇒ pair exadecim bool xE false
            | x8 ⇒ pair exadecim bool xF false
            | x9 ⇒ pair exadecim bool x0 true
            | xA ⇒ pair exadecim bool x1 true
            | xB ⇒ pair exadecim bool x2 true
            | xC ⇒ pair exadecim bool x3 true
            | xD ⇒ pair exadecim bool x4 true
            | xE ⇒ pair exadecim bool x5 true
            | xF ⇒ pair exadecim bool x6 true ] 
       | x8 ⇒
           match e2 with
            [ x0 ⇒ pair exadecim bool x8 false
            | x1 ⇒ pair exadecim bool x9 false
            | x2 ⇒ pair exadecim bool xA false
            | x3 ⇒ pair exadecim bool xB false
            | x4 ⇒ pair exadecim bool xC false
            | x5 ⇒ pair exadecim bool xD false
            | x6 ⇒ pair exadecim bool xE false
            | x7 ⇒ pair exadecim bool xF false
            | x8 ⇒ pair exadecim bool x0 true
            | x9 ⇒ pair exadecim bool x1 true
            | xA ⇒ pair exadecim bool x2 true
            | xB ⇒ pair exadecim bool x3 true
            | xC ⇒ pair exadecim bool x4 true
            | xD ⇒ pair exadecim bool x5 true
            | xE ⇒ pair exadecim bool x6 true
            | xF ⇒ pair exadecim bool x7 true ] 
       | x9 ⇒
           match e2 with
            [ x0 ⇒ pair exadecim bool x9 false
            | x1 ⇒ pair exadecim bool xA false
            | x2 ⇒ pair exadecim bool xB false
            | x3 ⇒ pair exadecim bool xC false
            | x4 ⇒ pair exadecim bool xD false
            | x5 ⇒ pair exadecim bool xE false
            | x6 ⇒ pair exadecim bool xF false
            | x7 ⇒ pair exadecim bool x0 true
            | x8 ⇒ pair exadecim bool x1 true
            | x9 ⇒ pair exadecim bool x2 true
            | xA ⇒ pair exadecim bool x3 true
            | xB ⇒ pair exadecim bool x4 true
            | xC ⇒ pair exadecim bool x5 true
            | xD ⇒ pair exadecim bool x6 true
            | xE ⇒ pair exadecim bool x7 true
            | xF ⇒ pair exadecim bool x8 true ] 
       | xA ⇒
           match e2 with
            [ x0 ⇒ pair exadecim bool xA false
            | x1 ⇒ pair exadecim bool xB false
            | x2 ⇒ pair exadecim bool xC false
            | x3 ⇒ pair exadecim bool xD false
            | x4 ⇒ pair exadecim bool xE false
            | x5 ⇒ pair exadecim bool xF false
            | x6 ⇒ pair exadecim bool x0 true
            | x7 ⇒ pair exadecim bool x1 true
            | x8 ⇒ pair exadecim bool x2 true
            | x9 ⇒ pair exadecim bool x3 true
            | xA ⇒ pair exadecim bool x4 true
            | xB ⇒ pair exadecim bool x5 true
            | xC ⇒ pair exadecim bool x6 true
            | xD ⇒ pair exadecim bool x7 true
            | xE ⇒ pair exadecim bool x8 true
            | xF ⇒ pair exadecim bool x9 true ] 
       | xB ⇒
           match e2 with
            [ x0 ⇒ pair exadecim bool xB false
            | x1 ⇒ pair exadecim bool xC false
            | x2 ⇒ pair exadecim bool xD false
            | x3 ⇒ pair exadecim bool xE false
            | x4 ⇒ pair exadecim bool xF false
            | x5 ⇒ pair exadecim bool x0 true
            | x6 ⇒ pair exadecim bool x1 true
            | x7 ⇒ pair exadecim bool x2 true
            | x8 ⇒ pair exadecim bool x3 true
            | x9 ⇒ pair exadecim bool x4 true
            | xA ⇒ pair exadecim bool x5 true
            | xB ⇒ pair exadecim bool x6 true
            | xC ⇒ pair exadecim bool x7 true
            | xD ⇒ pair exadecim bool x8 true
            | xE ⇒ pair exadecim bool x9 true
            | xF ⇒ pair exadecim bool xA true ] 
       | xC ⇒
           match e2 with
            [ x0 ⇒ pair exadecim bool xC false
            | x1 ⇒ pair exadecim bool xD false
            | x2 ⇒ pair exadecim bool xE false
            | x3 ⇒ pair exadecim bool xF false
            | x4 ⇒ pair exadecim bool x0 true
            | x5 ⇒ pair exadecim bool x1 true
            | x6 ⇒ pair exadecim bool x2 true
            | x7 ⇒ pair exadecim bool x3 true
            | x8 ⇒ pair exadecim bool x4 true
            | x9 ⇒ pair exadecim bool x5 true
            | xA ⇒ pair exadecim bool x6 true
            | xB ⇒ pair exadecim bool x7 true
            | xC ⇒ pair exadecim bool x8 true
            | xD ⇒ pair exadecim bool x9 true
            | xE ⇒ pair exadecim bool xA true
            | xF ⇒ pair exadecim bool xB true ] 
       | xD ⇒
           match e2 with
            [ x0 ⇒ pair exadecim bool xD false
            | x1 ⇒ pair exadecim bool xE false
            | x2 ⇒ pair exadecim bool xF false
            | x3 ⇒ pair exadecim bool x0 true
            | x4 ⇒ pair exadecim bool x1 true
            | x5 ⇒ pair exadecim bool x2 true
            | x6 ⇒ pair exadecim bool x3 true
            | x7 ⇒ pair exadecim bool x4 true
            | x8 ⇒ pair exadecim bool x5 true
            | x9 ⇒ pair exadecim bool x6 true
            | xA ⇒ pair exadecim bool x7 true
            | xB ⇒ pair exadecim bool x8 true
            | xC ⇒ pair exadecim bool x9 true
            | xD ⇒ pair exadecim bool xA true
            | xE ⇒ pair exadecim bool xB true
            | xF ⇒ pair exadecim bool xC true ] 
       | xE ⇒
           match e2 with
            [ x0 ⇒ pair exadecim bool xE false
            | x1 ⇒ pair exadecim bool xF false
            | x2 ⇒ pair exadecim bool x0 true
            | x3 ⇒ pair exadecim bool x1 true
            | x4 ⇒ pair exadecim bool x2 true
            | x5 ⇒ pair exadecim bool x3 true
            | x6 ⇒ pair exadecim bool x4 true
            | x7 ⇒ pair exadecim bool x5 true
            | x8 ⇒ pair exadecim bool x6 true
            | x9 ⇒ pair exadecim bool x7 true
            | xA ⇒ pair exadecim bool x8 true
            | xB ⇒ pair exadecim bool x9 true
            | xC ⇒ pair exadecim bool xA true
            | xD ⇒ pair exadecim bool xB true
            | xE ⇒ pair exadecim bool xC true
            | xF ⇒ pair exadecim bool xD true ] 
       | xF ⇒
           match e2 with
            [ x0 ⇒ pair exadecim bool xF false
            | x1 ⇒ pair exadecim bool x0 true
            | x2 ⇒ pair exadecim bool x1 true
            | x3 ⇒ pair exadecim bool x2 true
            | x4 ⇒ pair exadecim bool x3 true
            | x5 ⇒ pair exadecim bool x4 true
            | x6 ⇒ pair exadecim bool x5 true
            | x7 ⇒ pair exadecim bool x6 true
            | x8 ⇒ pair exadecim bool x7 true
            | x9 ⇒ pair exadecim bool x8 true
            | xA ⇒ pair exadecim bool x9 true
            | xB ⇒ pair exadecim bool xA true
            | xC ⇒ pair exadecim bool xB true
            | xD ⇒ pair exadecim bool xC true
            | xE ⇒ pair exadecim bool xD true
            | xF ⇒ pair exadecim bool xE true ]
       ]
   ].

(* operatore somma senza carry *)
definition plus_exnc ≝
λe1,e2:exadecim.fst ?? (plus_ex e1 e2 false).

(* operatore carry della somma *)
definition plus_exc ≝
λe1,e2:exadecim.snd ?? (plus_ex e1 e2 false).

(* operatore Most Significant Bit *)
definition MSB_ex ≝
λe:exadecim.match e with
 [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false
 | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
 | x8 ⇒ true  | x9 ⇒ true  | xA ⇒ true  | xB ⇒ true
 | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true ].

(* esadecimali → naturali *)
definition nat_of_exadecim ≝
λe:exadecim.
 match e with
  [ x0 ⇒ 0 | x1 ⇒ 1 | x2 ⇒ 2  | x3 ⇒ 3  | x4 ⇒ 4  | x5 ⇒ 5  | x6 ⇒ 6  | x7 ⇒ 7
  | x8 ⇒ 8 | x9 ⇒ 9 | xA ⇒ 10 | xB ⇒ 11 | xC ⇒ 12 | xD ⇒ 13 | xE ⇒ 14 | xF ⇒ 15 ].

coercion nat_of_exadecim.

(* naturali → esadecimali *)
let rec exadecim_of_nat n ≝
 match n with [ O ⇒ x0 | S n ⇒
  match n with [ O ⇒ x1 | S n ⇒
   match n with [ O ⇒ x2 | S n ⇒ 
    match n with [ O ⇒ x3 | S n ⇒ 
     match n with [ O ⇒ x4 | S n ⇒ 
      match n with [ O ⇒ x5 | S n ⇒ 
       match n with [ O ⇒ x6 | S n ⇒ 
        match n with [ O ⇒ x7 | S n ⇒ 
         match n with [ O ⇒ x8 | S n ⇒ 
          match n with [ O ⇒ x9 | S n ⇒ 
           match n with [ O ⇒ xA | S n ⇒ 
            match n with [ O ⇒ xB | S n ⇒ 
             match n with [ O ⇒ xC | S n ⇒ 
              match n with [ O ⇒ xD | S n ⇒ 
               match n with [ O ⇒ xE | S n ⇒ 
                match n with [ O ⇒ xF | S n ⇒ exadecim_of_nat n ]]]]]]]]]]]]]]]]. 

(* operatore predecessore *)
definition pred_ex ≝
λe:exadecim.
 match e with
  [ x0 ⇒ xF | x1 ⇒ x0 | x2 ⇒ x1 | x3 ⇒ x2 | x4 ⇒ x3 | x5 ⇒ x4 | x6 ⇒ x5 | x7 ⇒ x6
  | x8 ⇒ x7 | x9 ⇒ x8 | xA ⇒ x9 | xB ⇒ xA | xC ⇒ xB | xD ⇒ xC | xE ⇒ xD | xF ⇒ xE ].

(* operatore successore *)
definition succ_ex ≝
λe:exadecim.
 match e with
  [ x0 ⇒ x1 | x1 ⇒ x2 | x2 ⇒ x3 | x3 ⇒ x4 | x4 ⇒ x5 | x5 ⇒ x6 | x6 ⇒ x7 | x7 ⇒ x8
  | x8 ⇒ x9 | x9 ⇒ xA | xA ⇒ xB | xB ⇒ xC | xC ⇒ xD | xD ⇒ xE | xE ⇒ xF | xF ⇒ x0 ].

(* operatore neg/complemento a 2 *)
definition compl_ex ≝
λe:exadecim.match e with
 [ x0 ⇒ x0 | x1 ⇒ xF | x2 ⇒ xE | x3 ⇒ xD
 | x4 ⇒ xC | x5 ⇒ xB | x6 ⇒ xA | x7 ⇒ x9
 | x8 ⇒ x8 | x9 ⇒ x7 | xA ⇒ x6 | xB ⇒ x5
 | xC ⇒ x4 | xD ⇒ x3 | xE ⇒ x2 | xF ⇒ x1 ].

(* iteratore sugli esadecimali *)
definition forall_exadecim ≝ λP.
 P x0 ⊗ P x1 ⊗ P x2 ⊗ P x3 ⊗ P x4 ⊗ P x5 ⊗ P x6 ⊗ P x7 ⊗
 P x8 ⊗ P x9 ⊗ P xA ⊗ P xB ⊗ P xC ⊗ P xD ⊗ P xE ⊗ P xF.

(* ********************** *)
(* TEOREMI/LEMMMI/ASSIOMI *)
(* ********************** *)

(* ESPERIMENTO UTILIZZO DELL'ITERATORE *)

(*
lemma forall_exadecim_eqProp_left_aux :
 ∀P.(∀e:exadecim.P e = true) →
 ((P x0 ⊗ P x1 ⊗ P x2 ⊗ P x3 ⊗ P x4 ⊗ P x5 ⊗ P x6 ⊗ P x7 ⊗
   P x8 ⊗ P x9 ⊗ P xA ⊗ P xB ⊗ P xC ⊗ P xD ⊗ P xE ⊗ P xF) = true).
 intros;
 elim H; elim P; [ 2: reflexivity; ] elim H; elim P; [ 2: reflexivity; ]
 elim H; elim P; [ 2: reflexivity; ] elim H; elim P; [ 2: reflexivity; ]
 elim H; elim P; [ 2: reflexivity; ] elim H; elim P; [ 2: reflexivity; ]
 elim H; elim P; [ 2: reflexivity; ] elim H; elim P; [ 2: reflexivity; ]
 elim H; elim P; [ 2: reflexivity; ] elim H; elim P; [ 2: reflexivity; ]
 elim H; elim P; [ 2: reflexivity; ] elim H; elim P; [ 2: reflexivity; ]
 elim H; elim P; [ 2: reflexivity; ] elim H; elim P; [ 2: reflexivity; ]
 elim H; elim P; [ 2: reflexivity; ] elim H; elim P; [ 2: reflexivity; ]
 reflexivity.
qed.

lemma forall_exadecim_eqProp_left :
 ∀P.(∀e:exadecim. P e = true) → (forall_exadecim (λe.P e) = true).
 intro;
 elim P 0;
 [ simplify; intro; apply forall_exadecim_eqProp_left_aux; apply H; |
   simplify; intro; apply forall_exadecim_eqProp_left_aux; apply H; |
   autobatch; ].
qed.

lemma forall_exadecim_eqProp_right_aux :
 ∀P.((P x0 ⊗ P x1 ⊗ P x2 ⊗ P x3 ⊗ P x4 ⊗ P x5 ⊗ P x6 ⊗ P x7 ⊗
      P x8 ⊗ P x9 ⊗ P xA ⊗ P xB ⊗ P xC ⊗ P xD ⊗ P xE ⊗ P xF) = true) →
    (∀e:exadecim.P e = true).
 elim daemon.
qed.

lemma forall_exadecim_eqProp_right :
 ∀P.(forall_exadecim (λe.P e) = true) → (∀e:exadecim.P e = true).
 intro;
 elim P 0;
 [ simplify; intro; apply forall_exadecim_eqProp_right_aux; apply H; |
   simplify; intro; apply forall_exadecim_eqProp_right_aux; apply H; |
   autobatch; ].
qed.

lemma lt_nat_of_exadecim_16_forall: ∀e.ltb (nat_of_exadecim e) 16 = true.
 apply forall_exadecim_eqProp_right;
 reflexivity;
qed.
*)

(* FINE DELL'ESPERIMENTO *)

lemma lt_nat_of_exadecim_16: ∀e.nat_of_exadecim e < 16.
 intro;
 elim e;
 simplify;
 unfold;autobatch depth=17 size=20.
qed.

lemma exadecim_of_nat_mod:
 ∀n.exadecim_of_nat n = exadecim_of_nat (n \mod 16).
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
 change in ⊢ (? ? % ?) with (exadecim_of_nat n16);
 change in ⊢ (? ? ? (? (? % ?))) with (16 + n16);
 rewrite > mod_plus;
 change in ⊢ (? ? ? (? (? % ?))) with (n16 \mod 16);
 rewrite < mod_mod;
  [ apply H;
    unfold lt;
    autobatch depth=20 size=20.
  | autobatch
  ]
qed.

lemma nat_of_exadecim_exadecim_of_nat:
 ∀n. nat_of_exadecim (exadecim_of_nat n) = n \mod 16.
 intro;
 rewrite > exadecim_of_nat_mod;
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

lemma exadecim_of_nat_nat_of_exadecim:
 ∀e.exadecim_of_nat (nat_of_exadecim e) = e.
 intro;
 elim e;
 reflexivity.
qed.

lemma plusex_ok:
 ∀b1,b2,c.
  match plus_ex b1 b2 c with
   [ pair r c' ⇒ b1 + b2 + nat_of_bool c = nat_of_exadecim r + nat_of_bool c' * 16 ].
 intros;
 elim b1; (elim b2; (elim c; normalize; reflexivity)).
qed.

lemma eq_eqex_S_x0_false:
 ∀n. n < 15 → eq_ex x0 (exadecim_of_nat (S n)) = false.
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

lemma eqex_true_to_eq: ∀b,b'. eq_ex b b' = true → b=b'.
 intros 2;
 elim b 0;
 elim b' 0;
 simplify;
 intro;
 first [ reflexivity | destruct H ].
qed.

lemma eqex_false_to_not_eq: ∀b,b'. eq_ex b b' = false → b ≠ b'.
 intros 2;
 elim b 0;
 elim b' 0;
 simplify;
 intro;
 try (destruct H);
 intro K;
 destruct K.
qed.

(* nuovi *)

lemma ok_lt_ex : ∀e1,e2:exadecim.
 lt_ex e1 e2 = ltb e1 e2.
 intros;
 elim e1;
 elim e2;
 simplify;
 reflexivity.
 qed.

lemma ok_le_ex : ∀e1,e2:exadecim.
 le_ex e1 e2 = leb e1 e2.
 intros;
 elim e1;
 elim e2;
 simplify;
 reflexivity.
 qed.

lemma ok_gt_ex : ∀e1,e2:exadecim.
 gt_ex e1 e2 = notb (leb e1 e2).
 intros;
 elim e1;
 elim e2;
 simplify;
 reflexivity.
 qed.

lemma ok_ge_ex : ∀e1,e2:exadecim.
 ge_ex e1 e2 = notb (ltb e1 e2).
 intros;
 elim e1;
 elim e2;
 simplify;
 reflexivity.
 qed.

lemma ok_pred_ex : ∀e:exadecim.
 pred_ex e = plus_exnc e xF.
 intros;
 elim e;
 simplify;
 reflexivity.
 qed.

lemma ok_succ_ex : ∀e:exadecim.
 succ_ex e = plus_exnc e x1.
 intros;
 elim e;
 simplify;
 reflexivity.
 qed.

lemma ok_rcr_ex : ∀e:exadecim.∀b:bool.
 rcr_ex e b = 
 pair exadecim bool
  (exadecim_of_nat ((e/2)+match b with [ true ⇒ 8 | false ⇒ 0]))
  (eqb (mod e 2) 1).
 intros;
 elim e;
 elim b;
 simplify in ⊢ (? ? ? (? ? ? (? (? ? %)) ?));
 simplify in ⊢ (? ? ? (? ? ? ? %));
 simplify in ⊢ (? ? ? (? ? ? % ?));
 simplify in ⊢ (? ? % ?);
 reflexivity;
qed.

lemma ok_rcl_ex : ∀e:exadecim.∀b:bool.
 rcl_ex e b =
 pair exadecim bool
  (exadecim_of_nat ((mod (e*2) 16)+match b with [ true ⇒ 1 | false ⇒ 0]))
  (notb (ltb e 8)).
 intros;
 elim e;
 elim b;
 simplify in ⊢ (? ? ? (? ? ? (? (? ? %)) ?));
 simplify in ⊢ (? ? ? (? ? ? % ?));
 simplify in ⊢ (? ? ? (? ? ? ? (? %)));
 simplify in ⊢ (? ? ? (? ? ? ? %));
 simplify in ⊢ (? ? % ?);
 reflexivity.
 qed.

lemma ok_shr_ex : ∀e:exadecim.
 shr_ex e =
 pair exadecim bool
  (exadecim_of_nat (e/2))
  (eqb (mod e 2) 1).
 intros;
 elim e;
 simplify in ⊢ (? ? ? (? ? ? % ?));
 simplify in ⊢ (? ? ? (? ? ? ? %));
 simplify in ⊢ (? ? % ?);
 reflexivity.
qed.

lemma ok_shl_ex : ∀e:exadecim.
 shl_ex e =
 pair exadecim bool
  (exadecim_of_nat (mod (e*2) 16))
  (notb (ltb e 8)).
 intros;
 elim e;
 simplify in ⊢ (? ? ? (? ? ? % ?));
 simplify in ⊢ (? ? ? (? ? ? ? (? %)));
 simplify in ⊢ (? ? ? (? ? ? ? %));
 simplify in ⊢ (? ? % ?);
 reflexivity.
qed.

lemma ok_not_ex : ∀e:exadecim.
 e + (not_ex e) = 15.
 intros;
 elim e;
 simplify;
 reflexivity.
qed.

lemma ok_compl_ex : ∀e:exadecim.
 e + (compl_ex e) = match gt_ex e x0 with [ true ⇒ 16 | false ⇒ 0 ].
 intros;
 elim e;
 simplify;
 reflexivity.
qed.

lemma ok_MSB_ex : ∀e:exadecim.
 MSB_ex e = notb (ltb e 8).
 intros;
 elim e;
 simplify;
 reflexivity.
qed.
