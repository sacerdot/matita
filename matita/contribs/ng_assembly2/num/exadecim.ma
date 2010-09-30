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

include "num/comp_ext.ma".
include "num/bool_lemmas.ma".
include "num/oct.ma".

(* *********** *)
(* ESADECIMALI *)
(* *********** *)

ninductive exadecim : Type ≝
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

(* iteratore sugli esadecimali *)
ndefinition forall_ex ≝ λP.
 P x0 ⊗ P x1 ⊗ P x2 ⊗ P x3 ⊗ P x4 ⊗ P x5 ⊗ P x6 ⊗ P x7 ⊗
 P x8 ⊗ P x9 ⊗ P xA ⊗ P xB ⊗ P xC ⊗ P xD ⊗ P xE ⊗ P xF.

(* operatore = *)
ndefinition eq_ex ≝
λe1,e2:exadecim.
 match e1 with
  [ x0 ⇒ match e2 with [ x0 ⇒ true  | _ ⇒ false ]
  | x1 ⇒ match e2 with [ x1 ⇒ true  | _ ⇒ false ]
  | x2 ⇒ match e2 with [ x2 ⇒ true  | _ ⇒ false ]
  | x3 ⇒ match e2 with [ x3 ⇒ true  | _ ⇒ false ]
  | x4 ⇒ match e2 with [ x4 ⇒ true  | _ ⇒ false ]
  | x5 ⇒ match e2 with [ x5 ⇒ true  | _ ⇒ false ]
  | x6 ⇒ match e2 with [ x6 ⇒ true  | _ ⇒ false ]
  | x7 ⇒ match e2 with [ x7 ⇒ true  | _ ⇒ false ]
  | x8 ⇒ match e2 with [ x8 ⇒ true  | _ ⇒ false ]
  | x9 ⇒ match e2 with [ x9 ⇒ true  | _ ⇒ false ]
  | xA ⇒ match e2 with [ xA ⇒ true  | _ ⇒ false ]
  | xB ⇒ match e2 with [ xB ⇒ true  | _ ⇒ false ]
  | xC ⇒ match e2 with [ xC ⇒ true  | _ ⇒ false ]
  | xD ⇒ match e2 with [ xD ⇒ true  | _ ⇒ false ]
  | xE ⇒ match e2 with [ xE ⇒ true  | _ ⇒ false ]
  | xF ⇒ match e2 with [ xF ⇒ true  | _ ⇒ false ]
  ].

(* operatore < *)
ndefinition lt_ex ≝
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
ndefinition le_ex ≝
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
ndefinition gt_ex ≝
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
ndefinition ge_ex ≝
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
ndefinition and_ex ≝
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
ndefinition or_ex ≝
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
ndefinition xor_ex ≝
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

(* operatore Most Significant Bit *)
ndefinition getMSB_ex ≝
λe:exadecim.match e with
 [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false
 | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
 | x8 ⇒ true  | x9 ⇒ true  | xA ⇒ true  | xB ⇒ true
 | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true ].

ndefinition setMSB_ex ≝
λe:exadecim.match e with
 [ x0 ⇒ x8 | x1 ⇒ x9 | x2 ⇒ xA | x3 ⇒ xB
 | x4 ⇒ xC | x5 ⇒ xD | x6 ⇒ xE | x7 ⇒ xF
 | x8 ⇒ x8 | x9 ⇒ x9 | xA ⇒ xA | xB ⇒ xB
 | xC ⇒ xC | xD ⇒ xD | xE ⇒ xE | xF ⇒ xF ].

ndefinition clrMSB_ex ≝
λe:exadecim.match e with
 [ x0 ⇒ x0 | x1 ⇒ x1 | x2 ⇒ x2 | x3 ⇒ x3
 | x4 ⇒ x4 | x5 ⇒ x5 | x6 ⇒ x6 | x7 ⇒ x7
 | x8 ⇒ x0 | x9 ⇒ x1 | xA ⇒ x2 | xB ⇒ x3
 | xC ⇒ x4 | xD ⇒ x5 | xE ⇒ x6 | xF ⇒ x7 ].

(* operatore Least Significant Bit *)
ndefinition getLSB_ex ≝
λe:exadecim.match e with
 [ x0 ⇒ false | x1 ⇒ true | x2 ⇒ false | x3 ⇒ true
 | x4 ⇒ false | x5 ⇒ true | x6 ⇒ false | x7 ⇒ true
 | x8 ⇒ false | x9 ⇒ true | xA ⇒ false | xB ⇒ true
 | xC ⇒ false | xD ⇒ true | xE ⇒ false | xF ⇒ true ].

ndefinition setLSB_ex ≝
λe:exadecim.match e with
 [ x0 ⇒ x1 | x1 ⇒ x1 | x2 ⇒ x3 | x3 ⇒ x3
 | x4 ⇒ x5 | x5 ⇒ x5 | x6 ⇒ x7 | x7 ⇒ x7
 | x8 ⇒ x9 | x9 ⇒ x9 | xA ⇒ xB | xB ⇒ xB
 | xC ⇒ xD | xD ⇒ xD | xE ⇒ xF | xF ⇒ xF ].

ndefinition clrLSB_ex ≝
λe:exadecim.match e with
 [ x0 ⇒ x0 | x1 ⇒ x0 | x2 ⇒ x2 | x3 ⇒ x2
 | x4 ⇒ x4 | x5 ⇒ x4 | x6 ⇒ x6 | x7 ⇒ x6
 | x8 ⇒ x8 | x9 ⇒ x8 | xA ⇒ xA | xB ⇒ xA
 | xC ⇒ xC | xD ⇒ xC | xE ⇒ xE | xF ⇒ xE ].

(* operatore rotazione destra con carry *)
ndefinition rcr_ex ≝
λc:bool.λe:exadecim.match c with
 [ true ⇒ match e with
  [ x0 ⇒ pair … false x8 | x1 ⇒ pair … true x8
  | x2 ⇒ pair … false x9 | x3 ⇒ pair … true x9
  | x4 ⇒ pair … false xA | x5 ⇒ pair … true xA
  | x6 ⇒ pair … false xB | x7 ⇒ pair … true xB
  | x8 ⇒ pair … false xC | x9 ⇒ pair … true xC
  | xA ⇒ pair … false xD | xB ⇒ pair … true xD
  | xC ⇒ pair … false xE | xD ⇒ pair … true xE
  | xE ⇒ pair … false xF | xF ⇒ pair … true xF ]
 | false ⇒ match e with 
  [ x0 ⇒ pair … false x0 | x1 ⇒ pair … true x0
  | x2 ⇒ pair … false x1 | x3 ⇒ pair … true x1
  | x4 ⇒ pair … false x2 | x5 ⇒ pair … true x2
  | x6 ⇒ pair … false x3 | x7 ⇒ pair … true x3
  | x8 ⇒ pair … false x4 | x9 ⇒ pair … true x4
  | xA ⇒ pair … false x5 | xB ⇒ pair … true x5
  | xC ⇒ pair … false x6 | xD ⇒ pair … true x6
  | xE ⇒ pair … false x7 | xF ⇒ pair … true x7 ]
 ].

(* operatore shift destro *)
ndefinition shr_ex ≝
λe:exadecim.match e with 
 [ x0 ⇒ pair … false x0 | x1 ⇒ pair … true x0
 | x2 ⇒ pair … false x1 | x3 ⇒ pair … true x1
 | x4 ⇒ pair … false x2 | x5 ⇒ pair … true x2
 | x6 ⇒ pair … false x3 | x7 ⇒ pair … true x3
 | x8 ⇒ pair … false x4 | x9 ⇒ pair … true x4
 | xA ⇒ pair … false x5 | xB ⇒ pair … true x5
 | xC ⇒ pair … false x6 | xD ⇒ pair … true x6
 | xE ⇒ pair … false x7 | xF ⇒ pair … true x7 ].

(* operatore rotazione destra *)
ndefinition ror_ex ≝
λe:exadecim.match e with 
 [ x0 ⇒ x0 | x1 ⇒ x8 | x2 ⇒ x1 | x3 ⇒ x9
 | x4 ⇒ x2 | x5 ⇒ xA | x6 ⇒ x3 | x7 ⇒ xB 
 | x8 ⇒ x4 | x9 ⇒ xC | xA ⇒ x5 | xB ⇒ xD 
 | xC ⇒ x6 | xD ⇒ xE | xE ⇒ x7 | xF ⇒ xF ].

(* operatore rotazione sinistra con carry *)
ndefinition rcl_ex ≝
λc:bool.λe:exadecim.match c with
 [ true ⇒ match e with
  [ x0 ⇒ pair … false x1 | x1 ⇒ pair … false x3
  | x2 ⇒ pair … false x5 | x3 ⇒ pair … false x7
  | x4 ⇒ pair … false x9 | x5 ⇒ pair … false xB
  | x6 ⇒ pair … false xD | x7 ⇒ pair … false xF
  | x8 ⇒ pair … true x1  | x9 ⇒ pair … true x3
  | xA ⇒ pair … true x5  | xB ⇒ pair … true x7
  | xC ⇒ pair … true x9  | xD ⇒ pair … true xB
  | xE ⇒ pair … true xD  | xF ⇒ pair … true xF ]
 | false ⇒ match e with
  [ x0 ⇒ pair … false x0 | x1 ⇒ pair … false x2
  | x2 ⇒ pair … false x4 | x3 ⇒ pair … false x6
  | x4 ⇒ pair … false x8 | x5 ⇒ pair … false xA
  | x6 ⇒ pair … false xC | x7 ⇒ pair … false xE
  | x8 ⇒ pair … true x0  | x9 ⇒ pair … true x2
  | xA ⇒ pair … true x4  | xB ⇒ pair … true x6
  | xC ⇒ pair … true x8  | xD ⇒ pair … true xA
  | xE ⇒ pair … true xC  | xF ⇒ pair … true xE ]
 ].

(* operatore shift sinistro *)
ndefinition shl_ex ≝
λe:exadecim.match e with
 [ x0 ⇒ pair … false x0 | x1 ⇒ pair … false x2
 | x2 ⇒ pair … false x4 | x3 ⇒ pair … false x6
 | x4 ⇒ pair … false x8 | x5 ⇒ pair … false xA
 | x6 ⇒ pair … false xC | x7 ⇒ pair … false xE
 | x8 ⇒ pair … true x0  | x9 ⇒ pair … true x2
 | xA ⇒ pair … true x4  | xB ⇒ pair … true x6
 | xC ⇒ pair … true x8  | xD ⇒ pair … true xA
 | xE ⇒ pair … true xC  | xF ⇒ pair … true xE ].

(* operatore rotazione sinistra *)
ndefinition rol_ex ≝
λe:exadecim.match e with
 [ x0 ⇒ x0 | x1 ⇒ x2 | x2 ⇒ x4 | x3 ⇒ x6
 | x4 ⇒ x8 | x5 ⇒ xA | x6 ⇒ xC | x7 ⇒ xE
 | x8 ⇒ x1 | x9 ⇒ x3 | xA ⇒ x5 | xB ⇒ x7
 | xC ⇒ x9 | xD ⇒ xB | xE ⇒ xD | xF ⇒ xF ].

(* operatore not/complemento a 1 *)
ndefinition not_ex ≝
λe:exadecim.match e with
 [ x0 ⇒ xF | x1 ⇒ xE | x2 ⇒ xD | x3 ⇒ xC
 | x4 ⇒ xB | x5 ⇒ xA | x6 ⇒ x9 | x7 ⇒ x8
 | x8 ⇒ x7 | x9 ⇒ x6 | xA ⇒ x5 | xB ⇒ x4
 | xC ⇒ x3 | xD ⇒ x2 | xE ⇒ x1 | xF ⇒ x0 ].

(* operatore somma con data+carry → data+carry *)
ndefinition plus_ex_dc_dc ≝
λc:bool.λe1,e2:exadecim.
 match c with
  [ true ⇒ match e1 with
   [ x0 ⇒ match e2 with
    [ x0 ⇒ pair … false x1 | x1 ⇒ pair … false x2 | x2 ⇒ pair … false x3 | x3 ⇒ pair … false x4
    | x4 ⇒ pair … false x5 | x5 ⇒ pair … false x6 | x6 ⇒ pair … false x7 | x7 ⇒ pair … false x8
    | x8 ⇒ pair … false x9 | x9 ⇒ pair … false xA | xA ⇒ pair … false xB | xB ⇒ pair … false xC
    | xC ⇒ pair … false xD | xD ⇒ pair … false xE | xE ⇒ pair … false xF | xF ⇒ pair … true x0 ] 
   | x1 ⇒ match e2 with
    [ x0 ⇒ pair … false x2 | x1 ⇒ pair … false x3 | x2 ⇒ pair … false x4 | x3 ⇒ pair … false x5
    | x4 ⇒ pair … false x6 | x5 ⇒ pair … false x7 | x6 ⇒ pair … false x8 | x7 ⇒ pair … false x9
    | x8 ⇒ pair … false xA | x9 ⇒ pair … false xB | xA ⇒ pair … false xC | xB ⇒ pair … false xD
    | xC ⇒ pair … false xE | xD ⇒ pair … false xF | xE ⇒ pair … true x0  | xF ⇒ pair … true x1 ] 
   | x2 ⇒ match e2 with
    [ x0 ⇒ pair … false x3 | x1 ⇒ pair … false x4 | x2 ⇒ pair … false x5 | x3 ⇒ pair … false x6
    | x4 ⇒ pair … false x7 | x5 ⇒ pair … false x8 | x6 ⇒ pair … false x9 | x7 ⇒ pair … false xA
    | x8 ⇒ pair … false xB | x9 ⇒ pair … false xC | xA ⇒ pair … false xD | xB ⇒ pair … false xE
    | xC ⇒ pair … false xF | xD ⇒ pair … true x0  | xE ⇒ pair … true x1  | xF ⇒ pair … true x2 ] 
   | x3 ⇒ match e2 with
    [ x0 ⇒ pair … false x4 | x1 ⇒ pair … false x5 | x2 ⇒ pair … false x6 | x3 ⇒ pair … false x7
    | x4 ⇒ pair … false x8 | x5 ⇒ pair … false x9 | x6 ⇒ pair … false xA | x7 ⇒ pair … false xB
    | x8 ⇒ pair … false xC | x9 ⇒ pair … false xD | xA ⇒ pair … false xE | xB ⇒ pair … false xF
    | xC ⇒ pair … true x0  | xD ⇒ pair … true x1  | xE ⇒ pair … true x2  | xF ⇒ pair … true x3 ] 
   | x4 ⇒ match e2 with
    [ x0 ⇒ pair … false x5 | x1 ⇒ pair … false x6 | x2 ⇒ pair … false x7 | x3 ⇒ pair … false x8
    | x4 ⇒ pair … false x9 | x5 ⇒ pair … false xA | x6 ⇒ pair … false xB | x7 ⇒ pair … false xC
    | x8 ⇒ pair … false xD | x9 ⇒ pair … false xE | xA ⇒ pair … false xF | xB ⇒ pair … true x0
    | xC ⇒ pair … true x1  | xD ⇒ pair … true x2  | xE ⇒ pair … true x3  | xF ⇒ pair … true x4 ] 
   | x5 ⇒ match e2 with
    [ x0 ⇒ pair … false x6 | x1 ⇒ pair … false x7 | x2 ⇒ pair … false x8 | x3 ⇒ pair … false x9
    | x4 ⇒ pair … false xA | x5 ⇒ pair … false xB | x6 ⇒ pair … false xC | x7 ⇒ pair … false xD
    | x8 ⇒ pair … false xE | x9 ⇒ pair … false xF | xA ⇒ pair … true x0  | xB ⇒ pair … true x1
    | xC ⇒ pair … true x2  | xD ⇒ pair … true x3  | xE ⇒ pair … true x4  | xF ⇒ pair … true x5 ] 
   | x6 ⇒ match e2 with
    [ x0 ⇒ pair … false x7 | x1 ⇒ pair … false x8 | x2 ⇒ pair … false x9 | x3 ⇒ pair … false xA
    | x4 ⇒ pair … false xB | x5 ⇒ pair … false xC | x6 ⇒ pair … false xD | x7 ⇒ pair … false xE
    | x8 ⇒ pair … false xF | x9 ⇒ pair … true x0  | xA ⇒ pair … true x1  | xB ⇒ pair … true x2
    | xC ⇒ pair … true x3  | xD ⇒ pair … true x4  | xE ⇒ pair … true x5  | xF ⇒ pair … true x6 ] 
   | x7 ⇒ match e2 with
    [ x0 ⇒ pair … false x8 | x1 ⇒ pair … false x9 | x2 ⇒ pair … false xA | x3 ⇒ pair … false xB
    | x4 ⇒ pair … false xC | x5 ⇒ pair … false xD | x6 ⇒ pair … false xE | x7 ⇒ pair … false xF
    | x8 ⇒ pair … true x0  | x9 ⇒ pair … true x1  | xA ⇒ pair … true x2  | xB ⇒ pair … true x3
    | xC ⇒ pair … true x4  | xD ⇒ pair … true x5  | xE ⇒ pair … true x6  | xF ⇒ pair … true x7 ] 
   | x8 ⇒ match e2 with
    [ x0 ⇒ pair … false x9 | x1 ⇒ pair … false xA | x2 ⇒ pair … false xB | x3 ⇒ pair … false xC
    | x4 ⇒ pair … false xD | x5 ⇒ pair … false xE | x6 ⇒ pair … false xF | x7 ⇒ pair … true x0
    | x8 ⇒ pair … true x1  | x9 ⇒ pair … true x2  | xA ⇒ pair … true x3  | xB ⇒ pair … true x4
    | xC ⇒ pair … true x5  | xD ⇒ pair … true x6  | xE ⇒ pair … true x7  | xF ⇒ pair … true x8 ] 
   | x9 ⇒ match e2 with
    [ x0 ⇒ pair … false xA | x1 ⇒ pair … false xB | x2 ⇒ pair … false xC | x3 ⇒ pair … false xD
    | x4 ⇒ pair … false xE | x5 ⇒ pair … false xF | x6 ⇒ pair … true x0  | x7 ⇒ pair … true x1
    | x8 ⇒ pair … true x2  | x9 ⇒ pair … true x3  | xA ⇒ pair … true x4  | xB ⇒ pair … true x5
    | xC ⇒ pair … true x6  | xD ⇒ pair … true x7  | xE ⇒ pair … true x8  | xF ⇒ pair … true x9 ] 
   | xA ⇒ match e2 with
    [ x0 ⇒ pair … false xB | x1 ⇒ pair … false xC | x2 ⇒ pair … false xD | x3 ⇒ pair … false xE
    | x4 ⇒ pair … false xF | x5 ⇒ pair … true x0  | x6 ⇒ pair … true x1  | x7 ⇒ pair … true x2
    | x8 ⇒ pair … true x3  | x9 ⇒ pair … true x4  | xA ⇒ pair … true x5  | xB ⇒ pair … true x6
    | xC ⇒ pair … true x7  | xD ⇒ pair … true x8  | xE ⇒ pair … true x9  | xF ⇒ pair … true xA ] 
   | xB ⇒ match e2 with
    [ x0 ⇒ pair … false xC | x1 ⇒ pair … false xD | x2 ⇒ pair … false xE | x3 ⇒ pair … false xF
    | x4 ⇒ pair … true x0  | x5 ⇒ pair … true x1  | x6 ⇒ pair … true x2  | x7 ⇒ pair … true x3
    | x8 ⇒ pair … true x4  | x9 ⇒ pair … true x5  | xA ⇒ pair … true x6  | xB ⇒ pair … true x7
    | xC ⇒ pair … true x8  | xD ⇒ pair … true x9  | xE ⇒ pair … true xA  | xF ⇒ pair … true xB ] 
   | xC ⇒ match e2 with
    [ x0 ⇒ pair … false xD | x1 ⇒ pair … false xE | x2 ⇒ pair … false xF | x3 ⇒ pair … true x0
    | x4 ⇒ pair … true x1  | x5 ⇒ pair … true x2  | x6 ⇒ pair … true x3  | x7 ⇒ pair … true x4
    | x8 ⇒ pair … true x5  | x9 ⇒ pair … true x6  | xA ⇒ pair … true x7  | xB ⇒ pair … true x8
    | xC ⇒ pair … true x9  | xD ⇒ pair … true xA  | xE ⇒ pair … true xB  | xF ⇒ pair … true xC ] 
   | xD ⇒ match e2 with
    [ x0 ⇒ pair … false xE | x1 ⇒ pair … false xF | x2 ⇒ pair … true x0  | x3 ⇒ pair … true x1
    | x4 ⇒ pair … true x2  | x5 ⇒ pair … true x3  | x6 ⇒ pair … true x4  | x7 ⇒ pair … true x5
    | x8 ⇒ pair … true x6  | x9 ⇒ pair … true x7  | xA ⇒ pair … true x8  | xB ⇒ pair … true x9
    | xC ⇒ pair … true xA  | xD ⇒ pair … true xB  | xE ⇒ pair … true xC  | xF ⇒ pair … true xD ] 
   | xE ⇒ match e2 with
    [ x0 ⇒ pair … false xF | x1 ⇒ pair … true x0  | x2 ⇒ pair … true x1  | x3 ⇒ pair … true x2
    | x4 ⇒ pair … true x3  | x5 ⇒ pair … true x4  | x6 ⇒ pair … true x5  | x7 ⇒ pair … true x6
    | x8 ⇒ pair … true x7  | x9 ⇒ pair … true x8  | xA ⇒ pair … true x9  | xB ⇒ pair … true xA
    | xC ⇒ pair … true xB  | xD ⇒ pair … true xC  | xE ⇒ pair … true xD  | xF ⇒ pair … true xE ]
   | xF ⇒ match e2 with
    [ x0 ⇒ pair … true x0  | x1 ⇒ pair … true x1  | x2 ⇒ pair … true x2  | x3 ⇒ pair … true x3
    | x4 ⇒ pair … true x4  | x5 ⇒ pair … true x5  | x6 ⇒ pair … true x6  | x7 ⇒ pair … true x7
    | x8 ⇒ pair … true x8  | x9 ⇒ pair … true x9  | xA ⇒ pair … true xA  | xB ⇒ pair … true xB
    | xC ⇒ pair … true xC  | xD ⇒ pair … true xD  | xE ⇒ pair … true xE  | xF ⇒ pair … true xF ] 
   ]
  | false ⇒ match e1 with
   [ x0 ⇒ match e2 with
    [ x0 ⇒ pair … false x0 | x1 ⇒ pair … false x1 | x2 ⇒ pair … false x2 | x3 ⇒ pair … false x3
    | x4 ⇒ pair … false x4 | x5 ⇒ pair … false x5 | x6 ⇒ pair … false x6 | x7 ⇒ pair … false x7
    | x8 ⇒ pair … false x8 | x9 ⇒ pair … false x9 | xA ⇒ pair … false xA | xB ⇒ pair … false xB
    | xC ⇒ pair … false xC | xD ⇒ pair … false xD | xE ⇒ pair … false xE | xF ⇒ pair … false xF ] 
   | x1 ⇒ match e2 with
    [ x0 ⇒ pair … false x1 | x1 ⇒ pair … false x2 | x2 ⇒ pair … false x3 | x3 ⇒ pair … false x4
    | x4 ⇒ pair … false x5 | x5 ⇒ pair … false x6 | x6 ⇒ pair … false x7 | x7 ⇒ pair … false x8
    | x8 ⇒ pair … false x9 | x9 ⇒ pair … false xA | xA ⇒ pair … false xB | xB ⇒ pair … false xC
    | xC ⇒ pair … false xD | xD ⇒ pair … false xE | xE ⇒ pair … false xF | xF ⇒ pair … true x0 ] 
   | x2 ⇒ match e2 with
    [ x0 ⇒ pair … false x2 | x1 ⇒ pair … false x3 | x2 ⇒ pair … false x4 | x3 ⇒ pair … false x5
    | x4 ⇒ pair … false x6 | x5 ⇒ pair … false x7 | x6 ⇒ pair … false x8 | x7 ⇒ pair … false x9
    | x8 ⇒ pair … false xA | x9 ⇒ pair … false xB | xA ⇒ pair … false xC | xB ⇒ pair … false xD
    | xC ⇒ pair … false xE | xD ⇒ pair … false xF | xE ⇒ pair … true x0  | xF ⇒ pair … true x1 ] 
   | x3 ⇒ match e2 with
    [ x0 ⇒ pair … false x3 | x1 ⇒ pair … false x4 | x2 ⇒ pair … false x5 | x3 ⇒ pair … false x6
    | x4 ⇒ pair … false x7 | x5 ⇒ pair … false x8 | x6 ⇒ pair … false x9 | x7 ⇒ pair … false xA
    | x8 ⇒ pair … false xB | x9 ⇒ pair … false xC | xA ⇒ pair … false xD | xB ⇒ pair … false xE
    | xC ⇒ pair … false xF | xD ⇒ pair … true x0  | xE ⇒ pair … true x1  | xF ⇒ pair … true x2 ] 
   | x4 ⇒ match e2 with
    [ x0 ⇒ pair … false x4 | x1 ⇒ pair … false x5 | x2 ⇒ pair … false x6 | x3 ⇒ pair … false x7
    | x4 ⇒ pair … false x8 | x5 ⇒ pair … false x9 | x6 ⇒ pair … false xA | x7 ⇒ pair … false xB
    | x8 ⇒ pair … false xC | x9 ⇒ pair … false xD | xA ⇒ pair … false xE | xB ⇒ pair … false xF
    | xC ⇒ pair … true x0  | xD ⇒ pair … true x1  | xE ⇒ pair … true x2  | xF ⇒ pair … true x3 ] 
   | x5 ⇒ match e2 with
    [ x0 ⇒ pair … false x5 | x1 ⇒ pair … false x6 | x2 ⇒ pair … false x7 | x3 ⇒ pair … false x8
    | x4 ⇒ pair … false x9 | x5 ⇒ pair … false xA | x6 ⇒ pair … false xB | x7 ⇒ pair … false xC
    | x8 ⇒ pair … false xD | x9 ⇒ pair … false xE | xA ⇒ pair … false xF | xB ⇒ pair … true x0
    | xC ⇒ pair … true x1  | xD ⇒ pair … true x2  | xE ⇒ pair … true x3  | xF ⇒ pair … true x4 ] 
   | x6 ⇒ match e2 with
    [ x0 ⇒ pair … false x6 | x1 ⇒ pair … false x7 | x2 ⇒ pair … false x8 | x3 ⇒ pair … false x9
    | x4 ⇒ pair … false xA | x5 ⇒ pair … false xB | x6 ⇒ pair … false xC | x7 ⇒ pair … false xD
    | x8 ⇒ pair … false xE | x9 ⇒ pair … false xF | xA ⇒ pair … true x0  | xB ⇒ pair … true x1
    | xC ⇒ pair … true x2  | xD ⇒ pair … true x3  | xE ⇒ pair … true x4  | xF ⇒ pair … true x5 ] 
   | x7 ⇒ match e2 with
    [ x0 ⇒ pair … false x7 | x1 ⇒ pair … false x8 | x2 ⇒ pair … false x9 | x3 ⇒ pair … false xA
    | x4 ⇒ pair … false xB | x5 ⇒ pair … false xC | x6 ⇒ pair … false xD | x7 ⇒ pair … false xE
    | x8 ⇒ pair … false xF | x9 ⇒ pair … true x0  | xA ⇒ pair … true x1  | xB ⇒ pair … true x2
    | xC ⇒ pair … true x3  | xD ⇒ pair … true x4  | xE ⇒ pair … true x5  | xF ⇒ pair … true x6 ] 
   | x8 ⇒ match e2 with
    [ x0 ⇒ pair … false x8 | x1 ⇒ pair … false x9 | x2 ⇒ pair … false xA | x3 ⇒ pair … false xB
    | x4 ⇒ pair … false xC | x5 ⇒ pair … false xD | x6 ⇒ pair … false xE | x7 ⇒ pair … false xF
    | x8 ⇒ pair … true x0  | x9 ⇒ pair … true x1  | xA ⇒ pair … true x2  | xB ⇒ pair … true x3
    | xC ⇒ pair … true x4  | xD ⇒ pair … true x5  | xE ⇒ pair … true x6  | xF ⇒ pair … true x7 ] 
   | x9 ⇒ match e2 with
    [ x0 ⇒ pair … false x9 | x1 ⇒ pair … false xA | x2 ⇒ pair … false xB | x3 ⇒ pair … false xC
    | x4 ⇒ pair … false xD | x5 ⇒ pair … false xE | x6 ⇒ pair … false xF | x7 ⇒ pair … true x0
    | x8 ⇒ pair … true x1  | x9 ⇒ pair … true x2  | xA ⇒ pair … true x3  | xB ⇒ pair … true x4
    | xC ⇒ pair … true x5  | xD ⇒ pair … true x6  | xE ⇒ pair … true x7  | xF ⇒ pair … true x8 ] 
   | xA ⇒ match e2 with
    [ x0 ⇒ pair … false xA | x1 ⇒ pair … false xB | x2 ⇒ pair … false xC | x3 ⇒ pair … false xD
    | x4 ⇒ pair … false xE | x5 ⇒ pair … false xF | x6 ⇒ pair … true x0  | x7 ⇒ pair … true x1
    | x8 ⇒ pair … true x2  | x9 ⇒ pair … true x3  | xA ⇒ pair … true x4  | xB ⇒ pair … true x5
    | xC ⇒ pair … true x6  | xD ⇒ pair … true x7  | xE ⇒ pair … true x8  | xF ⇒ pair … true x9 ] 
   | xB ⇒ match e2 with
    [ x0 ⇒ pair … false xB | x1 ⇒ pair … false xC | x2 ⇒ pair … false xD | x3 ⇒ pair … false xE
    | x4 ⇒ pair … false xF | x5 ⇒ pair … true x0  | x6 ⇒ pair … true x1  | x7 ⇒ pair … true x2
    | x8 ⇒ pair … true x3  | x9 ⇒ pair … true x4  | xA ⇒ pair … true x5  | xB ⇒ pair … true x6
    | xC ⇒ pair … true x7  | xD ⇒ pair … true x8  | xE ⇒ pair … true x9  | xF ⇒ pair … true xA ] 
   | xC ⇒ match e2 with
    [ x0 ⇒ pair … false xC | x1 ⇒ pair … false xD | x2 ⇒ pair … false xE | x3 ⇒ pair … false xF
    | x4 ⇒ pair … true x0  | x5 ⇒ pair … true x1  | x6 ⇒ pair … true x2  | x7 ⇒ pair … true x3
    | x8 ⇒ pair … true x4  | x9 ⇒ pair … true x5  | xA ⇒ pair … true x6  | xB ⇒ pair … true x7
    | xC ⇒ pair … true x8  | xD ⇒ pair … true x9  | xE ⇒ pair … true xA  | xF ⇒ pair … true xB ] 
   | xD ⇒ match e2 with
    [ x0 ⇒ pair … false xD | x1 ⇒ pair … false xE | x2 ⇒ pair … false xF | x3 ⇒ pair … true x0
    | x4 ⇒ pair … true x1  | x5 ⇒ pair … true x2  | x6 ⇒ pair … true x3  | x7 ⇒ pair … true x4
    | x8 ⇒ pair … true x5  | x9 ⇒ pair … true x6  | xA ⇒ pair … true x7  | xB ⇒ pair … true x8
    | xC ⇒ pair … true x9  | xD ⇒ pair … true xA  | xE ⇒ pair … true xB  | xF ⇒ pair … true xC ] 
   | xE ⇒ match e2 with
    [ x0 ⇒ pair … false xE | x1 ⇒ pair … false xF | x2 ⇒ pair … true x0  | x3 ⇒ pair … true x1
    | x4 ⇒ pair … true x2  | x5 ⇒ pair … true x3  | x6 ⇒ pair … true x4  | x7 ⇒ pair … true x5
    | x8 ⇒ pair … true x6  | x9 ⇒ pair … true x7  | xA ⇒ pair … true x8  | xB ⇒ pair … true x9
    | xC ⇒ pair … true xA  | xD ⇒ pair … true xB  | xE ⇒ pair … true xC  | xF ⇒ pair … true xD ] 
   | xF ⇒ match e2 with
    [ x0 ⇒ pair … false xF | x1 ⇒ pair … true x0  | x2 ⇒ pair … true x1  | x3 ⇒ pair … true x2
    | x4 ⇒ pair … true x3  | x5 ⇒ pair … true x4  | x6 ⇒ pair … true x5  | x7 ⇒ pair … true x6
    | x8 ⇒ pair … true x7  | x9 ⇒ pair … true x8  | xA ⇒ pair … true x9  | xB ⇒ pair … true xA
    | xC ⇒ pair … true xB  | xD ⇒ pair … true xC  | xE ⇒ pair … true xD  | xF ⇒ pair … true xE ]
   ]].

(* operatore somma con data → data+carry *)
ndefinition plus_ex_d_dc ≝
λe1,e2:exadecim.
 match e1 with
  [ x0 ⇒ match e2 with
   [ x0 ⇒ pair … false x0 | x1 ⇒ pair … false x1 | x2 ⇒ pair … false x2 | x3 ⇒ pair … false x3
   | x4 ⇒ pair … false x4 | x5 ⇒ pair … false x5 | x6 ⇒ pair … false x6 | x7 ⇒ pair … false x7
   | x8 ⇒ pair … false x8 | x9 ⇒ pair … false x9 | xA ⇒ pair … false xA | xB ⇒ pair … false xB
   | xC ⇒ pair … false xC | xD ⇒ pair … false xD | xE ⇒ pair … false xE | xF ⇒ pair … false xF ]  
  | x1 ⇒ match e2 with
   [ x0 ⇒ pair … false x1 | x1 ⇒ pair … false x2 | x2 ⇒ pair … false x3 | x3 ⇒ pair … false x4
   | x4 ⇒ pair … false x5 | x5 ⇒ pair … false x6 | x6 ⇒ pair … false x7 | x7 ⇒ pair … false x8
   | x8 ⇒ pair … false x9 | x9 ⇒ pair … false xA | xA ⇒ pair … false xB | xB ⇒ pair … false xC
   | xC ⇒ pair … false xD | xD ⇒ pair … false xE | xE ⇒ pair … false xF | xF ⇒ pair … true x0 ] 
  | x2 ⇒ match e2 with
   [ x0 ⇒ pair … false x2 | x1 ⇒ pair … false x3 | x2 ⇒ pair … false x4 | x3 ⇒ pair … false x5
   | x4 ⇒ pair … false x6 | x5 ⇒ pair … false x7 | x6 ⇒ pair … false x8 | x7 ⇒ pair … false x9
   | x8 ⇒ pair … false xA | x9 ⇒ pair … false xB | xA ⇒ pair … false xC | xB ⇒ pair … false xD
   | xC ⇒ pair … false xE | xD ⇒ pair … false xF | xE ⇒ pair … true x0  | xF ⇒ pair … true x1 ] 
  | x3 ⇒ match e2 with
   [ x0 ⇒ pair … false x3 | x1 ⇒ pair … false x4 | x2 ⇒ pair … false x5 | x3 ⇒ pair … false x6
   | x4 ⇒ pair … false x7 | x5 ⇒ pair … false x8 | x6 ⇒ pair … false x9 | x7 ⇒ pair … false xA
   | x8 ⇒ pair … false xB | x9 ⇒ pair … false xC | xA ⇒ pair … false xD | xB ⇒ pair … false xE
   | xC ⇒ pair … false xF | xD ⇒ pair … true x0  | xE ⇒ pair … true x1  | xF ⇒ pair … true x2 ] 
  | x4 ⇒ match e2 with
   [ x0 ⇒ pair … false x4 | x1 ⇒ pair … false x5 | x2 ⇒ pair … false x6 | x3 ⇒ pair … false x7
   | x4 ⇒ pair … false x8 | x5 ⇒ pair … false x9 | x6 ⇒ pair … false xA | x7 ⇒ pair … false xB
   | x8 ⇒ pair … false xC | x9 ⇒ pair … false xD | xA ⇒ pair … false xE | xB ⇒ pair … false xF
   | xC ⇒ pair … true x0  | xD ⇒ pair … true x1  | xE ⇒ pair … true x2  | xF ⇒ pair … true x3 ] 
  | x5 ⇒ match e2 with
   [ x0 ⇒ pair … false x5 | x1 ⇒ pair … false x6 | x2 ⇒ pair … false x7 | x3 ⇒ pair … false x8
   | x4 ⇒ pair … false x9 | x5 ⇒ pair … false xA | x6 ⇒ pair … false xB | x7 ⇒ pair … false xC
   | x8 ⇒ pair … false xD | x9 ⇒ pair … false xE | xA ⇒ pair … false xF | xB ⇒ pair … true x0
   | xC ⇒ pair … true x1  | xD ⇒ pair … true x2  | xE ⇒ pair … true x3  | xF ⇒ pair … true x4 ] 
  | x6 ⇒ match e2 with
   [ x0 ⇒ pair … false x6 | x1 ⇒ pair … false x7 | x2 ⇒ pair … false x8 | x3 ⇒ pair … false x9
   | x4 ⇒ pair … false xA | x5 ⇒ pair … false xB | x6 ⇒ pair … false xC | x7 ⇒ pair … false xD
   | x8 ⇒ pair … false xE | x9 ⇒ pair … false xF | xA ⇒ pair … true x0  | xB ⇒ pair … true x1
   | xC ⇒ pair … true x2  | xD ⇒ pair … true x3  | xE ⇒ pair … true x4  | xF ⇒ pair … true x5 ] 
  | x7 ⇒ match e2 with
   [ x0 ⇒ pair … false x7 | x1 ⇒ pair … false x8 | x2 ⇒ pair … false x9 | x3 ⇒ pair … false xA
   | x4 ⇒ pair … false xB | x5 ⇒ pair … false xC | x6 ⇒ pair … false xD | x7 ⇒ pair … false xE
   | x8 ⇒ pair … false xF | x9 ⇒ pair … true x0  | xA ⇒ pair … true x1  | xB ⇒ pair … true x2
   | xC ⇒ pair … true x3  | xD ⇒ pair … true x4  | xE ⇒ pair … true x5  | xF ⇒ pair … true x6 ] 
  | x8 ⇒ match e2 with
   [ x0 ⇒ pair … false x8 | x1 ⇒ pair … false x9 | x2 ⇒ pair … false xA | x3 ⇒ pair … false xB
   | x4 ⇒ pair … false xC | x5 ⇒ pair … false xD | x6 ⇒ pair … false xE | x7 ⇒ pair … false xF
   | x8 ⇒ pair … true x0  | x9 ⇒ pair … true x1  | xA ⇒ pair … true x2  | xB ⇒ pair … true x3
   | xC ⇒ pair … true x4  | xD ⇒ pair … true x5  | xE ⇒ pair … true x6  | xF ⇒ pair … true x7 ] 
  | x9 ⇒ match e2 with
   [ x0 ⇒ pair … false x9 | x1 ⇒ pair … false xA | x2 ⇒ pair … false xB | x3 ⇒ pair … false xC
   | x4 ⇒ pair … false xD | x5 ⇒ pair … false xE | x6 ⇒ pair … false xF | x7 ⇒ pair … true x0
   | x8 ⇒ pair … true x1  | x9 ⇒ pair … true x2  | xA ⇒ pair … true x3  | xB ⇒ pair … true x4
   | xC ⇒ pair … true x5  | xD ⇒ pair … true x6  | xE ⇒ pair … true x7  | xF ⇒ pair … true x8 ] 
  | xA ⇒ match e2 with
   [ x0 ⇒ pair … false xA | x1 ⇒ pair … false xB | x2 ⇒ pair … false xC | x3 ⇒ pair … false xD
   | x4 ⇒ pair … false xE | x5 ⇒ pair … false xF | x6 ⇒ pair … true x0  | x7 ⇒ pair … true x1
   | x8 ⇒ pair … true x2  | x9 ⇒ pair … true x3  | xA ⇒ pair … true x4  | xB ⇒ pair … true x5
   | xC ⇒ pair … true x6  | xD ⇒ pair … true x7  | xE ⇒ pair … true x8  | xF ⇒ pair … true x9 ] 
  | xB ⇒ match e2 with
   [ x0 ⇒ pair … false xB | x1 ⇒ pair … false xC | x2 ⇒ pair … false xD | x3 ⇒ pair … false xE
   | x4 ⇒ pair … false xF | x5 ⇒ pair … true x0  | x6 ⇒ pair … true x1  | x7 ⇒ pair … true x2
   | x8 ⇒ pair … true x3  | x9 ⇒ pair … true x4  | xA ⇒ pair … true x5  | xB ⇒ pair … true x6
   | xC ⇒ pair … true x7  | xD ⇒ pair … true x8  | xE ⇒ pair … true x9  | xF ⇒ pair … true xA ] 
  | xC ⇒ match e2 with
   [ x0 ⇒ pair … false xC | x1 ⇒ pair … false xD | x2 ⇒ pair … false xE | x3 ⇒ pair … false xF
   | x4 ⇒ pair … true x0  | x5 ⇒ pair … true x1  | x6 ⇒ pair … true x2  | x7 ⇒ pair … true x3
   | x8 ⇒ pair … true x4  | x9 ⇒ pair … true x5  | xA ⇒ pair … true x6  | xB ⇒ pair … true x7
   | xC ⇒ pair … true x8  | xD ⇒ pair … true x9  | xE ⇒ pair … true xA  | xF ⇒ pair … true xB ] 
  | xD ⇒ match e2 with
   [ x0 ⇒ pair … false xD | x1 ⇒ pair … false xE | x2 ⇒ pair … false xF | x3 ⇒ pair … true x0
   | x4 ⇒ pair … true x1  | x5 ⇒ pair … true x2  | x6 ⇒ pair … true x3  | x7 ⇒ pair … true x4
   | x8 ⇒ pair … true x5  | x9 ⇒ pair … true x6  | xA ⇒ pair … true x7  | xB ⇒ pair … true x8
   | xC ⇒ pair … true x9  | xD ⇒ pair … true xA  | xE ⇒ pair … true xB  | xF ⇒ pair … true xC ] 
  | xE ⇒ match e2 with
   [ x0 ⇒ pair … false xE | x1 ⇒ pair … false xF | x2 ⇒ pair … true x0  | x3 ⇒ pair … true x1
   | x4 ⇒ pair … true x2  | x5 ⇒ pair … true x3  | x6 ⇒ pair … true x4  | x7 ⇒ pair … true x5
   | x8 ⇒ pair … true x6  | x9 ⇒ pair … true x7  | xA ⇒ pair … true x8  | xB ⇒ pair … true x9
   | xC ⇒ pair … true xA  | xD ⇒ pair … true xB  | xE ⇒ pair … true xC  | xF ⇒ pair … true xD ] 
  | xF ⇒ match e2 with
   [ x0 ⇒ pair … false xF | x1 ⇒ pair … true x0  | x2 ⇒ pair … true x1  | x3 ⇒ pair … true x2
   | x4 ⇒ pair … true x3  | x5 ⇒ pair … true x4  | x6 ⇒ pair … true x5  | x7 ⇒ pair … true x6
   | x8 ⇒ pair … true x7  | x9 ⇒ pair … true x8  | xA ⇒ pair … true x9  | xB ⇒ pair … true xA
   | xC ⇒ pair … true xB  | xD ⇒ pair … true xC  | xE ⇒ pair … true xD  | xF ⇒ pair … true xE ]
  ].

(* operatore somma con data+carry → data *)
ndefinition plus_ex_dc_d ≝
λc:bool.λe1,e2:exadecim.
 match c with
  [ true ⇒ match e1 with
   [ x0 ⇒ match e2 with
    [ x0 ⇒ x1 | x1 ⇒ x2 | x2 ⇒ x3 | x3 ⇒ x4 | x4 ⇒ x5 | x5 ⇒ x6 | x6 ⇒ x7 | x7 ⇒ x8
    | x8 ⇒ x9 | x9 ⇒ xA | xA ⇒ xB | xB ⇒ xC | xC ⇒ xD | xD ⇒ xE | xE ⇒ xF | xF ⇒ x0 ] 
   | x1 ⇒ match e2 with
    [ x0 ⇒ x2 | x1 ⇒ x3 | x2 ⇒ x4 | x3 ⇒ x5 | x4 ⇒ x6 | x5 ⇒ x7 | x6 ⇒ x8 | x7 ⇒ x9
    | x8 ⇒ xA | x9 ⇒ xB | xA ⇒ xC | xB ⇒ xD | xC ⇒ xE | xD ⇒ xF | xE ⇒ x0 | xF ⇒ x1 ] 
   | x2 ⇒ match e2 with
    [ x0 ⇒ x3 | x1 ⇒ x4 | x2 ⇒ x5 | x3 ⇒ x6 | x4 ⇒ x7 | x5 ⇒ x8 | x6 ⇒ x9 | x7 ⇒ xA
    | x8 ⇒ xB | x9 ⇒ xC | xA ⇒ xD | xB ⇒ xE | xC ⇒ xF | xD ⇒ x0 | xE ⇒ x1 | xF ⇒ x2 ]
   | x3 ⇒ match e2 with
    [ x0 ⇒ x4 | x1 ⇒ x5 | x2 ⇒ x6 | x3 ⇒ x7 | x4 ⇒ x8 | x5 ⇒ x9 | x6 ⇒ xA | x7 ⇒ xB
    | x8 ⇒ xC | x9 ⇒ xD | xA ⇒ xE | xB ⇒ xF | xC ⇒ x0 | xD ⇒ x1 | xE ⇒ x2 | xF ⇒ x3 ]
   | x4 ⇒ match e2 with
    [ x0 ⇒ x5 | x1 ⇒ x6 | x2 ⇒ x7 | x3 ⇒ x8 | x4 ⇒ x9 | x5 ⇒ xA | x6 ⇒ xB | x7 ⇒ xC
    | x8 ⇒ xD | x9 ⇒ xE | xA ⇒ xF | xB ⇒ x0 | xC ⇒ x1 | xD ⇒ x2 | xE ⇒ x3 | xF ⇒ x4 ]
   | x5 ⇒ match e2 with
    [ x0 ⇒ x6 | x1 ⇒ x7 | x2 ⇒ x8 | x3 ⇒ x9 | x4 ⇒ xA | x5 ⇒ xB | x6 ⇒ xC | x7 ⇒ xD
    | x8 ⇒ xE | x9 ⇒ xF | xA ⇒ x0 | xB ⇒ x1 | xC ⇒ x2 | xD ⇒ x3 | xE ⇒ x4 | xF ⇒ x5 ]
   | x6 ⇒ match e2 with
    [ x0 ⇒ x7 | x1 ⇒ x8 | x2 ⇒ x9 | x3 ⇒ xA | x4 ⇒ xB | x5 ⇒ xC | x6 ⇒ xD | x7 ⇒ xE
    | x8 ⇒ xF | x9 ⇒ x0 | xA ⇒ x1 | xB ⇒ x2 | xC ⇒ x3 | xD ⇒ x4 | xE ⇒ x5 | xF ⇒ x6 ]
   | x7 ⇒ match e2 with
    [ x0 ⇒ x8 | x1 ⇒ x9 | x2 ⇒ xA | x3 ⇒ xB | x4 ⇒ xC | x5 ⇒ xD | x6 ⇒ xE | x7 ⇒ xF
    | x8 ⇒ x0 | x9 ⇒ x1 | xA ⇒ x2 | xB ⇒ x3 | xC ⇒ x4 | xD ⇒ x5 | xE ⇒ x6 | xF ⇒ x7 ]
   | x8 ⇒ match e2 with
    [ x0 ⇒ x9 | x1 ⇒ xA | x2 ⇒ xB | x3 ⇒ xC | x4 ⇒ xD | x5 ⇒ xE | x6 ⇒ xF | x7 ⇒ x0
    | x8 ⇒ x1 | x9 ⇒ x2 | xA ⇒ x3 | xB ⇒ x4 | xC ⇒ x5 | xD ⇒ x6 | xE ⇒ x7 | xF ⇒ x8 ]
   | x9 ⇒ match e2 with
    [ x0 ⇒ xA | x1 ⇒ xB | x2 ⇒ xC | x3 ⇒ xD | x4 ⇒ xE | x5 ⇒ xF | x6 ⇒ x0 | x7 ⇒ x1
    | x8 ⇒ x2 | x9 ⇒ x3 | xA ⇒ x4 | xB ⇒ x5 | xC ⇒ x6 | xD ⇒ x7 | xE ⇒ x8 | xF ⇒ x9 ]
   | xA ⇒ match e2 with
    [ x0 ⇒ xB | x1 ⇒ xC | x2 ⇒ xD | x3 ⇒ xE | x4 ⇒ xF | x5 ⇒ x0 | x6 ⇒ x1 | x7 ⇒ x2
    | x8 ⇒ x3 | x9 ⇒ x4 | xA ⇒ x5 | xB ⇒ x6 | xC ⇒ x7 | xD ⇒ x8 | xE ⇒ x9 | xF ⇒ xA ]
   | xB ⇒ match e2 with
    [ x0 ⇒ xC | x1 ⇒ xD | x2 ⇒ xE | x3 ⇒ xF | x4 ⇒ x0 | x5 ⇒ x1 | x6 ⇒ x2 | x7 ⇒ x3
    | x8 ⇒ x4 | x9 ⇒ x5 | xA ⇒ x6 | xB ⇒ x7 | xC ⇒ x8 | xD ⇒ x9 | xE ⇒ xA | xF ⇒ xB ]
   | xC ⇒ match e2 with
     [ x0 ⇒ xD | x1 ⇒ xE | x2 ⇒ xF | x3 ⇒ x0 | x4 ⇒ x1 | x5 ⇒ x2 | x6 ⇒ x3 | x7 ⇒ x4
    | x8 ⇒ x5 | x9 ⇒ x6 | xA ⇒ x7 | xB ⇒ x8 | xC ⇒ x9 | xD ⇒ xA | xE ⇒ xB | xF ⇒ xC ]
   | xD ⇒ match e2 with
    [ x0 ⇒ xE | x1 ⇒ xF | x2 ⇒ x0 | x3 ⇒ x1 | x4 ⇒ x2 | x5 ⇒ x3 | x6 ⇒ x4 | x7 ⇒ x5
    | x8 ⇒ x6 | x9 ⇒ x7 | xA ⇒ x8 | xB ⇒ x9 | xC ⇒ xA | xD ⇒ xB | xE ⇒ xC | xF ⇒ xD ]
   | xE ⇒ match e2 with
    [ x0 ⇒ xF | x1 ⇒ x0 | x2 ⇒ x1 | x3 ⇒ x2 | x4 ⇒ x3 | x5 ⇒ x4 | x6 ⇒ x5 | x7 ⇒ x6
    | x8 ⇒ x7 | x9 ⇒ x8 | xA ⇒ x9 | xB ⇒ xA | xC ⇒ xB | xD ⇒ xC | xE ⇒ xD | xF ⇒ xE ]
   | xF ⇒ match e2 with
    [ x0 ⇒ x0 | x1 ⇒ x1 | x2 ⇒ x2 | x3 ⇒ x3 | x4 ⇒ x4 | x5 ⇒ x5 | x6 ⇒ x6 | x7 ⇒ x7
    | x8 ⇒ x8 | x9 ⇒ x9 | xA ⇒ xA | xB ⇒ xB | xC ⇒ xC | xD ⇒ xD | xE ⇒ xE | xF ⇒ xF ]
   ]
  | false ⇒ match e1 with
   [ x0 ⇒ match e2 with
    [ x0 ⇒ x0 | x1 ⇒ x1 | x2 ⇒ x2 | x3 ⇒ x3 | x4 ⇒ x4 | x5 ⇒ x5 | x6 ⇒ x6 | x7 ⇒ x7
    | x8 ⇒ x8 | x9 ⇒ x9 | xA ⇒ xA | xB ⇒ xB | xC ⇒ xC | xD ⇒ xD | xE ⇒ xE | xF ⇒ xF ] 
   | x1 ⇒ match e2 with
    [ x0 ⇒ x1 | x1 ⇒ x2 | x2 ⇒ x3 | x3 ⇒ x4 | x4 ⇒ x5 | x5 ⇒ x6 | x6 ⇒ x7 | x7 ⇒ x8
    | x8 ⇒ x9 | x9 ⇒ xA | xA ⇒ xB | xB ⇒ xC | xC ⇒ xD | xD ⇒ xE | xE ⇒ xF | xF ⇒ x0 ] 
   | x2 ⇒ match e2 with
    [ x0 ⇒ x2 | x1 ⇒ x3 | x2 ⇒ x4 | x3 ⇒ x5 | x4 ⇒ x6 | x5 ⇒ x7 | x6 ⇒ x8 | x7 ⇒ x9
    | x8 ⇒ xA | x9 ⇒ xB | xA ⇒ xC | xB ⇒ xD | xC ⇒ xE | xD ⇒ xF | xE ⇒ x0 | xF ⇒ x1 ] 
   | x3 ⇒ match e2 with
    [ x0 ⇒ x3 | x1 ⇒ x4 | x2 ⇒ x5 | x3 ⇒ x6 | x4 ⇒ x7 | x5 ⇒ x8 | x6 ⇒ x9 | x7 ⇒ xA
    | x8 ⇒ xB | x9 ⇒ xC | xA ⇒ xD | xB ⇒ xE | xC ⇒ xF | xD ⇒ x0 | xE ⇒ x1 | xF ⇒ x2 ]
   | x4 ⇒ match e2 with
    [ x0 ⇒ x4 | x1 ⇒ x5 | x2 ⇒ x6 | x3 ⇒ x7 | x4 ⇒ x8 | x5 ⇒ x9 | x6 ⇒ xA | x7 ⇒ xB
    | x8 ⇒ xC | x9 ⇒ xD | xA ⇒ xE | xB ⇒ xF | xC ⇒ x0 | xD ⇒ x1 | xE ⇒ x2 | xF ⇒ x3 ]
   | x5 ⇒ match e2 with
    [ x0 ⇒ x5 | x1 ⇒ x6 | x2 ⇒ x7 | x3 ⇒ x8 | x4 ⇒ x9 | x5 ⇒ xA | x6 ⇒ xB | x7 ⇒ xC
    | x8 ⇒ xD | x9 ⇒ xE | xA ⇒ xF | xB ⇒ x0 | xC ⇒ x1 | xD ⇒ x2 | xE ⇒ x3 | xF ⇒ x4 ]
   | x6 ⇒ match e2 with
    [ x0 ⇒ x6 | x1 ⇒ x7 | x2 ⇒ x8 | x3 ⇒ x9 | x4 ⇒ xA | x5 ⇒ xB | x6 ⇒ xC | x7 ⇒ xD
    | x8 ⇒ xE | x9 ⇒ xF | xA ⇒ x0 | xB ⇒ x1 | xC ⇒ x2 | xD ⇒ x3 | xE ⇒ x4 | xF ⇒ x5 ]
   | x7 ⇒ match e2 with
    [ x0 ⇒ x7 | x1 ⇒ x8 | x2 ⇒ x9 | x3 ⇒ xA | x4 ⇒ xB | x5 ⇒ xC | x6 ⇒ xD | x7 ⇒ xE
    | x8 ⇒ xF | x9 ⇒ x0 | xA ⇒ x1 | xB ⇒ x2 | xC ⇒ x3 | xD ⇒ x4 | xE ⇒ x5 | xF ⇒ x6 ]
   | x8 ⇒ match e2 with
    [ x0 ⇒ x8 | x1 ⇒ x9 | x2 ⇒ xA | x3 ⇒ xB | x4 ⇒ xC | x5 ⇒ xD | x6 ⇒ xE | x7 ⇒ xF
    | x8 ⇒ x0 | x9 ⇒ x1 | xA ⇒ x2 | xB ⇒ x3 | xC ⇒ x4 | xD ⇒ x5 | xE ⇒ x6 | xF ⇒ x7 ]
   | x9 ⇒ match e2 with
    [ x0 ⇒ x9 | x1 ⇒ xA | x2 ⇒ xB | x3 ⇒ xC | x4 ⇒ xD | x5 ⇒ xE | x6 ⇒ xF | x7 ⇒ x0
    | x8 ⇒ x1 | x9 ⇒ x2 | xA ⇒ x3 | xB ⇒ x4 | xC ⇒ x5 | xD ⇒ x6 | xE ⇒ x7 | xF ⇒ x8 ]
   | xA ⇒ match e2 with
    [ x0 ⇒ xA | x1 ⇒ xB | x2 ⇒ xC | x3 ⇒ xD | x4 ⇒ xE | x5 ⇒ xF | x6 ⇒ x0 | x7 ⇒ x1
    | x8 ⇒ x2 | x9 ⇒ x3 | xA ⇒ x4 | xB ⇒ x5 | xC ⇒ x6 | xD ⇒ x7 | xE ⇒ x8 | xF ⇒ x9 ]
   | xB ⇒ match e2 with
    [ x0 ⇒ xB | x1 ⇒ xC | x2 ⇒ xD | x3 ⇒ xE | x4 ⇒ xF | x5 ⇒ x0 | x6 ⇒ x1 | x7 ⇒ x2
    | x8 ⇒ x3 | x9 ⇒ x4 | xA ⇒ x5 | xB ⇒ x6 | xC ⇒ x7 | xD ⇒ x8 | xE ⇒ x9 | xF ⇒ xA ]
   | xC ⇒ match e2 with
    [ x0 ⇒ xC | x1 ⇒ xD | x2 ⇒ xE | x3 ⇒ xF | x4 ⇒ x0 | x5 ⇒ x1 | x6 ⇒ x2 | x7 ⇒ x3
    | x8 ⇒ x4 | x9 ⇒ x5 | xA ⇒ x6 | xB ⇒ x7 | xC ⇒ x8 | xD ⇒ x9 | xE ⇒ xA | xF ⇒ xB ]
   | xD ⇒ match e2 with
     [ x0 ⇒ xD | x1 ⇒ xE | x2 ⇒ xF | x3 ⇒ x0 | x4 ⇒ x1 | x5 ⇒ x2 | x6 ⇒ x3 | x7 ⇒ x4
    | x8 ⇒ x5 | x9 ⇒ x6 | xA ⇒ x7 | xB ⇒ x8 | xC ⇒ x9 | xD ⇒ xA | xE ⇒ xB | xF ⇒ xC ]
   | xE ⇒ match e2 with
    [ x0 ⇒ xE | x1 ⇒ xF | x2 ⇒ x0 | x3 ⇒ x1 | x4 ⇒ x2 | x5 ⇒ x3 | x6 ⇒ x4 | x7 ⇒ x5
    | x8 ⇒ x6 | x9 ⇒ x7 | xA ⇒ x8 | xB ⇒ x9 | xC ⇒ xA | xD ⇒ xB | xE ⇒ xC | xF ⇒ xD ]
   | xF ⇒ match e2 with
    [ x0 ⇒ xF | x1 ⇒ x0 | x2 ⇒ x1 | x3 ⇒ x2 | x4 ⇒ x3 | x5 ⇒ x4 | x6 ⇒ x5 | x7 ⇒ x6
    | x8 ⇒ x7 | x9 ⇒ x8 | xA ⇒ x9 | xB ⇒ xA | xC ⇒ xB | xD ⇒ xC | xE ⇒ xD | xF ⇒ xE ]
   ]].

(* operatore somma con data → data *)
ndefinition plus_ex_d_d ≝
λe1,e2:exadecim.
 match e1 with
  [ x0 ⇒ match e2 with
   [ x0 ⇒ x0 | x1 ⇒ x1 | x2 ⇒ x2 | x3 ⇒ x3 | x4 ⇒ x4 | x5 ⇒ x5 | x6 ⇒ x6 | x7 ⇒ x7
   | x8 ⇒ x8 | x9 ⇒ x9 | xA ⇒ xA | xB ⇒ xB | xC ⇒ xC | xD ⇒ xD | xE ⇒ xE | xF ⇒ xF ] 
  | x1 ⇒ match e2 with
   [ x0 ⇒ x1 | x1 ⇒ x2 | x2 ⇒ x3 | x3 ⇒ x4 | x4 ⇒ x5 | x5 ⇒ x6 | x6 ⇒ x7 | x7 ⇒ x8
   | x8 ⇒ x9 | x9 ⇒ xA | xA ⇒ xB | xB ⇒ xC | xC ⇒ xD | xD ⇒ xE | xE ⇒ xF | xF ⇒ x0 ] 
  | x2 ⇒ match e2 with
   [ x0 ⇒ x2 | x1 ⇒ x3 | x2 ⇒ x4 | x3 ⇒ x5 | x4 ⇒ x6 | x5 ⇒ x7 | x6 ⇒ x8 | x7 ⇒ x9
   | x8 ⇒ xA | x9 ⇒ xB | xA ⇒ xC | xB ⇒ xD | xC ⇒ xE | xD ⇒ xF | xE ⇒ x0 | xF ⇒ x1 ] 
  | x3 ⇒ match e2 with
   [ x0 ⇒ x3 | x1 ⇒ x4 | x2 ⇒ x5 | x3 ⇒ x6 | x4 ⇒ x7 | x5 ⇒ x8 | x6 ⇒ x9 | x7 ⇒ xA
   | x8 ⇒ xB | x9 ⇒ xC | xA ⇒ xD | xB ⇒ xE | xC ⇒ xF | xD ⇒ x0 | xE ⇒ x1 | xF ⇒ x2 ]
  | x4 ⇒ match e2 with
   [ x0 ⇒ x4 | x1 ⇒ x5 | x2 ⇒ x6 | x3 ⇒ x7 | x4 ⇒ x8 | x5 ⇒ x9 | x6 ⇒ xA | x7 ⇒ xB
   | x8 ⇒ xC | x9 ⇒ xD | xA ⇒ xE | xB ⇒ xF | xC ⇒ x0 | xD ⇒ x1 | xE ⇒ x2 | xF ⇒ x3 ]
  | x5 ⇒ match e2 with
   [ x0 ⇒ x5 | x1 ⇒ x6 | x2 ⇒ x7 | x3 ⇒ x8 | x4 ⇒ x9 | x5 ⇒ xA | x6 ⇒ xB | x7 ⇒ xC
   | x8 ⇒ xD | x9 ⇒ xE | xA ⇒ xF | xB ⇒ x0 | xC ⇒ x1 | xD ⇒ x2 | xE ⇒ x3 | xF ⇒ x4 ]
  | x6 ⇒ match e2 with
   [ x0 ⇒ x6 | x1 ⇒ x7 | x2 ⇒ x8 | x3 ⇒ x9 | x4 ⇒ xA | x5 ⇒ xB | x6 ⇒ xC | x7 ⇒ xD
   | x8 ⇒ xE | x9 ⇒ xF | xA ⇒ x0 | xB ⇒ x1 | xC ⇒ x2 | xD ⇒ x3 | xE ⇒ x4 | xF ⇒ x5 ]
  | x7 ⇒ match e2 with
   [ x0 ⇒ x7 | x1 ⇒ x8 | x2 ⇒ x9 | x3 ⇒ xA | x4 ⇒ xB | x5 ⇒ xC | x6 ⇒ xD | x7 ⇒ xE
   | x8 ⇒ xF | x9 ⇒ x0 | xA ⇒ x1 | xB ⇒ x2 | xC ⇒ x3 | xD ⇒ x4 | xE ⇒ x5 | xF ⇒ x6 ]
  | x8 ⇒ match e2 with
   [ x0 ⇒ x8 | x1 ⇒ x9 | x2 ⇒ xA | x3 ⇒ xB | x4 ⇒ xC | x5 ⇒ xD | x6 ⇒ xE | x7 ⇒ xF
   | x8 ⇒ x0 | x9 ⇒ x1 | xA ⇒ x2 | xB ⇒ x3 | xC ⇒ x4 | xD ⇒ x5 | xE ⇒ x6 | xF ⇒ x7 ]
  | x9 ⇒ match e2 with
   [ x0 ⇒ x9 | x1 ⇒ xA | x2 ⇒ xB | x3 ⇒ xC | x4 ⇒ xD | x5 ⇒ xE | x6 ⇒ xF | x7 ⇒ x0
   | x8 ⇒ x1 | x9 ⇒ x2 | xA ⇒ x3 | xB ⇒ x4 | xC ⇒ x5 | xD ⇒ x6 | xE ⇒ x7 | xF ⇒ x8 ]
  | xA ⇒ match e2 with
   [ x0 ⇒ xA | x1 ⇒ xB | x2 ⇒ xC | x3 ⇒ xD | x4 ⇒ xE | x5 ⇒ xF | x6 ⇒ x0 | x7 ⇒ x1
   | x8 ⇒ x2 | x9 ⇒ x3 | xA ⇒ x4 | xB ⇒ x5 | xC ⇒ x6 | xD ⇒ x7 | xE ⇒ x8 | xF ⇒ x9 ]
  | xB ⇒ match e2 with
   [ x0 ⇒ xB | x1 ⇒ xC | x2 ⇒ xD | x3 ⇒ xE | x4 ⇒ xF | x5 ⇒ x0 | x6 ⇒ x1 | x7 ⇒ x2
   | x8 ⇒ x3 | x9 ⇒ x4 | xA ⇒ x5 | xB ⇒ x6 | xC ⇒ x7 | xD ⇒ x8 | xE ⇒ x9 | xF ⇒ xA ]
  | xC ⇒ match e2 with
   [ x0 ⇒ xC | x1 ⇒ xD | x2 ⇒ xE | x3 ⇒ xF | x4 ⇒ x0 | x5 ⇒ x1 | x6 ⇒ x2 | x7 ⇒ x3
   | x8 ⇒ x4 | x9 ⇒ x5 | xA ⇒ x6 | xB ⇒ x7 | xC ⇒ x8 | xD ⇒ x9 | xE ⇒ xA | xF ⇒ xB ]
  | xD ⇒ match e2 with
   [ x0 ⇒ xD | x1 ⇒ xE | x2 ⇒ xF | x3 ⇒ x0 | x4 ⇒ x1 | x5 ⇒ x2 | x6 ⇒ x3 | x7 ⇒ x4
   | x8 ⇒ x5 | x9 ⇒ x6 | xA ⇒ x7 | xB ⇒ x8 | xC ⇒ x9 | xD ⇒ xA | xE ⇒ xB | xF ⇒ xC ]
  | xE ⇒ match e2 with
   [ x0 ⇒ xE | x1 ⇒ xF | x2 ⇒ x0 | x3 ⇒ x1 | x4 ⇒ x2 | x5 ⇒ x3 | x6 ⇒ x4 | x7 ⇒ x5
   | x8 ⇒ x6 | x9 ⇒ x7 | xA ⇒ x8 | xB ⇒ x9 | xC ⇒ xA | xD ⇒ xB | xE ⇒ xC | xF ⇒ xD ]
  | xF ⇒ match e2 with
   [ x0 ⇒ xF | x1 ⇒ x0 | x2 ⇒ x1 | x3 ⇒ x2 | x4 ⇒ x3 | x5 ⇒ x4 | x6 ⇒ x5 | x7 ⇒ x6
   | x8 ⇒ x7 | x9 ⇒ x8 | xA ⇒ x9 | xB ⇒ xA | xC ⇒ xB | xD ⇒ xC | xE ⇒ xD | xF ⇒ xE ]
  ].

(* operatore somma con data+carry → carry *)
ndefinition plus_ex_dc_c ≝
λc:bool.λe1,e2:exadecim.
 match c with
  [ true ⇒ match e1 with
   [ x0 ⇒ match e2 with
    [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
    | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ true  ] 
   | x1 ⇒ match e2 with
    [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
    | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false | xC ⇒ false | xD ⇒ false | xE ⇒ true  | xF ⇒ true  ] 
   | x2 ⇒ match e2 with
    [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
    | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false | xC ⇒ false | xD ⇒ true  | xE ⇒ true  | xF ⇒ true  ] 
   | x3 ⇒ match e2 with
    [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
    | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true  ] 
   | x4 ⇒ match e2 with
    [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
    | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ true  | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true  ] 
   | x5 ⇒ match e2 with
    [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
    | x8 ⇒ false | x9 ⇒ false | xA ⇒ true  | xB ⇒ true  | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true  ] 
   | x6 ⇒ match e2 with
    [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
    | x8 ⇒ false | x9 ⇒ true  | xA ⇒ true  | xB ⇒ true  | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true  ] 
   | x7 ⇒ match e2 with
    [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
    | x8 ⇒ true  | x9 ⇒ true  | xA ⇒ true  | xB ⇒ true  | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true  ] 
   | x8 ⇒ match e2 with
    [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ true
    | x8 ⇒ true  | x9 ⇒ true  | xA ⇒ true  | xB ⇒ true  | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true  ] 
   | x9 ⇒ match e2 with
    [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false | x4 ⇒ false | x5 ⇒ false | x6 ⇒ true  | x7 ⇒ true
    | x8 ⇒ true  | x9 ⇒ true  | xA ⇒ true  | xB ⇒ true  | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true  ] 
   | xA ⇒ match e2 with
    [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false | x4 ⇒ false | x5 ⇒ true  | x6 ⇒ true  | x7 ⇒ true
    | x8 ⇒ true  | x9 ⇒ true  | xA ⇒ true  | xB ⇒ true  | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true  ] 
   | xB ⇒ match e2 with
    [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false | x4 ⇒ true  | x5 ⇒ true  | x6 ⇒ true  | x7 ⇒ true
    | x8 ⇒ true  | x9 ⇒ true  | xA ⇒ true  | xB ⇒ true  | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true  ] 
   | xC ⇒ match e2 with
    [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ true  | x4 ⇒ true  | x5 ⇒ true  | x6 ⇒ true  | x7 ⇒ true
    | x8 ⇒ true  | x9 ⇒ true  | xA ⇒ true  | xB ⇒ true  | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true  ] 
   | xD ⇒ match e2 with
    [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ true  | x3 ⇒ true  | x4 ⇒ true  | x5 ⇒ true  | x6 ⇒ true  | x7 ⇒ true
    | x8 ⇒ true  | x9 ⇒ true  | xA ⇒ true  | xB ⇒ true  | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true  ] 
   | xE ⇒ match e2 with
    [ x0 ⇒ false | x1 ⇒ true  | x2 ⇒ true  | x3 ⇒ true  | x4 ⇒ true  | x5 ⇒ true  | x6 ⇒ true  | x7 ⇒ true
    | x8 ⇒ true  | x9 ⇒ true  | xA ⇒ true  | xB ⇒ true  | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true  ]
   | xF ⇒ match e2 with
    [ x0 ⇒ true  | x1 ⇒ true  | x2 ⇒ true  | x3 ⇒ true  | x4 ⇒ true  | x5 ⇒ true  | x6 ⇒ true  | x7 ⇒ true
    | x8 ⇒ true  | x9 ⇒ true  | xA ⇒ true  | xB ⇒ true  | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true  ]  
   ]
  | false ⇒ match e1 with
   [ x0 ⇒ match e2 with
    [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
    | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ] 
   | x1 ⇒ match e2 with
    [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
    | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ true  ] 
   | x2 ⇒ match e2 with
    [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
    | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false | xC ⇒ false | xD ⇒ false | xE ⇒ true  | xF ⇒ true  ] 
   | x3 ⇒ match e2 with
    [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
    | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false | xC ⇒ false | xD ⇒ true  | xE ⇒ true  | xF ⇒ true  ] 
   | x4 ⇒ match e2 with
    [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
    | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true  ] 
   | x5 ⇒ match e2 with
    [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
    | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ true  | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true  ] 
   | x6 ⇒ match e2 with
    [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
    | x8 ⇒ false | x9 ⇒ false | xA ⇒ true  | xB ⇒ true  | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true  ] 
   | x7 ⇒ match e2 with
    [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
    | x8 ⇒ false | x9 ⇒ true  | xA ⇒ true  | xB ⇒ true  | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true  ] 
   | x8 ⇒ match e2 with
    [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
    | x8 ⇒ true  | x9 ⇒ true  | xA ⇒ true  | xB ⇒ true  | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true  ] 
   | x9 ⇒ match e2 with
    [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ true
    | x8 ⇒ true  | x9 ⇒ true  | xA ⇒ true  | xB ⇒ true  | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true  ] 
   | xA ⇒ match e2 with
    [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false | x4 ⇒ false | x5 ⇒ false | x6 ⇒ true  | x7 ⇒ true
    | x8 ⇒ true  | x9 ⇒ true  | xA ⇒ true  | xB ⇒ true  | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true  ] 
   | xB ⇒ match e2 with
    [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false | x4 ⇒ false | x5 ⇒ true  | x6 ⇒ true  | x7 ⇒ true
    | x8 ⇒ true  | x9 ⇒ true  | xA ⇒ true  | xB ⇒ true  | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true  ] 
   | xC ⇒ match e2 with
    [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false | x4 ⇒ true  | x5 ⇒ true  | x6 ⇒ true  | x7 ⇒ true
    | x8 ⇒ true  | x9 ⇒ true  | xA ⇒ true  | xB ⇒ true  | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true  ] 
   | xD ⇒ match e2 with
    [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ true  | x4 ⇒ true  | x5 ⇒ true  | x6 ⇒ true  | x7 ⇒ true
    | x8 ⇒ true  | x9 ⇒ true  | xA ⇒ true  | xB ⇒ true  | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true  ] 
   | xE ⇒ match e2 with
    [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ true  | x3 ⇒ true  | x4 ⇒ true  | x5 ⇒ true  | x6 ⇒ true  | x7 ⇒ true
    | x8 ⇒ true  | x9 ⇒ true  | xA ⇒ true  | xB ⇒ true  | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true  ] 
   | xF ⇒ match e2 with
    [ x0 ⇒ false | x1 ⇒ true  | x2 ⇒ true  | x3 ⇒ true  | x4 ⇒ true  | x5 ⇒ true  | x6 ⇒ true  | x7 ⇒ true
    | x8 ⇒ true  | x9 ⇒ true  | xA ⇒ true  | xB ⇒ true  | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true  ] 
   ]].

(* operatore somma con data → carry *)
ndefinition plus_ex_d_c ≝
λe1,e2:exadecim.
 match e1 with
  [ x0 ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
   | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ] 
  | x1 ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
   | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ true  ] 
  | x2 ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
   | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false | xC ⇒ false | xD ⇒ false | xE ⇒ true  | xF ⇒ true  ] 
  | x3 ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
   | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false | xC ⇒ false | xD ⇒ true  | xE ⇒ true  | xF ⇒ true  ] 
  | x4 ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
   | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true  ] 
  | x5 ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
   | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ true  | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true  ] 
  | x6 ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
   | x8 ⇒ false | x9 ⇒ false | xA ⇒ true  | xB ⇒ true  | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true  ] 
  | x7 ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
   | x8 ⇒ false | x9 ⇒ true  | xA ⇒ true  | xB ⇒ true  | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true  ] 
  | x8 ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
   | x8 ⇒ true  | x9 ⇒ true  | xA ⇒ true  | xB ⇒ true  | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true  ] 
  | x9 ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ true
   | x8 ⇒ true  | x9 ⇒ true  | xA ⇒ true  | xB ⇒ true  | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true  ] 
  | xA ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false | x4 ⇒ false | x5 ⇒ false | x6 ⇒ true  | x7 ⇒ true
   | x8 ⇒ true  | x9 ⇒ true  | xA ⇒ true  | xB ⇒ true  | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true  ] 
  | xB ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false | x4 ⇒ false | x5 ⇒ true  | x6 ⇒ true  | x7 ⇒ true
   | x8 ⇒ true  | x9 ⇒ true  | xA ⇒ true  | xB ⇒ true  | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true  ] 
  | xC ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false | x4 ⇒ true  | x5 ⇒ true  | x6 ⇒ true  | x7 ⇒ true
   | x8 ⇒ true  | x9 ⇒ true  | xA ⇒ true  | xB ⇒ true  | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true  ] 
  | xD ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ true  | x4 ⇒ true  | x5 ⇒ true  | x6 ⇒ true  | x7 ⇒ true
   | x8 ⇒ true  | x9 ⇒ true  | xA ⇒ true  | xB ⇒ true  | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true  ] 
  | xE ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ true  | x3 ⇒ true  | x4 ⇒ true  | x5 ⇒ true  | x6 ⇒ true  | x7 ⇒ true
   | x8 ⇒ true  | x9 ⇒ true  | xA ⇒ true  | xB ⇒ true  | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true  ] 
  | xF ⇒ match e2 with
   [ x0 ⇒ false | x1 ⇒ true  | x2 ⇒ true  | x3 ⇒ true  | x4 ⇒ true  | x5 ⇒ true  | x6 ⇒ true  | x7 ⇒ true
   | x8 ⇒ true  | x9 ⇒ true  | xA ⇒ true  | xB ⇒ true  | xC ⇒ true  | xD ⇒ true  | xE ⇒ true  | xF ⇒ true  ] 
  ].

(* operatore predecessore *)
ndefinition pred_ex ≝
λe:exadecim.
 match e with
  [ x0 ⇒ xF | x1 ⇒ x0 | x2 ⇒ x1 | x3 ⇒ x2
  | x4 ⇒ x3 | x5 ⇒ x4 | x6 ⇒ x5 | x7 ⇒ x6
  | x8 ⇒ x7 | x9 ⇒ x8 | xA ⇒ x9 | xB ⇒ xA
  | xC ⇒ xB | xD ⇒ xC | xE ⇒ xD | xF ⇒ xE ].

(* operatore successore *)
ndefinition succ_ex ≝
λe:exadecim.
 match e with
  [ x0 ⇒ x1 | x1 ⇒ x2 | x2 ⇒ x3 | x3 ⇒ x4
  | x4 ⇒ x5 | x5 ⇒ x6 | x6 ⇒ x7 | x7 ⇒ x8
  | x8 ⇒ x9 | x9 ⇒ xA | xA ⇒ xB | xB ⇒ xC
  | xC ⇒ xD | xD ⇒ xE | xE ⇒ xF | xF ⇒ x0 ].

(* operatore neg/complemento a 2 *)
ndefinition compl_ex ≝
λe:exadecim.match e with
 [ x0 ⇒ x0 | x1 ⇒ xF | x2 ⇒ xE | x3 ⇒ xD
 | x4 ⇒ xC | x5 ⇒ xB | x6 ⇒ xA | x7 ⇒ x9
 | x8 ⇒ x8 | x9 ⇒ x7 | xA ⇒ x6 | xB ⇒ x5
 | xC ⇒ x4 | xD ⇒ x3 | xE ⇒ x2 | xF ⇒ x1 ].

(* operatore abs *)
ndefinition abs_ex ≝
λe:exadecim.match getMSB_ex e with
 [ true ⇒ compl_ex e | false ⇒ e ].

(* operatore x in [inf,sup] o in sup],[inf *)
ndefinition inrange_ex ≝
λx,inf,sup:exadecim.
 match le_ex inf sup with
  [ true ⇒ and_bool | false ⇒ or_bool ]
 (le_ex inf x) (le_ex x sup).

(* esadecimali ricorsivi *)
ninductive rec_exadecim : exadecim → Type ≝
  ex_O : rec_exadecim x0
| ex_S : ∀n.rec_exadecim n → rec_exadecim (succ_ex n).

(* esadecimali → esadecimali ricorsivi *)
ndefinition ex_to_recex ≝
λn.match n return λx.rec_exadecim x with
 [ x0 ⇒ ex_O
 | x1 ⇒ ex_S ? ex_O
 | x2 ⇒ ex_S ? (ex_S ? ex_O)
 | x3 ⇒ ex_S ? (ex_S ? (ex_S ? ex_O))
 | x4 ⇒ ex_S ? (ex_S ? (ex_S ? (ex_S ? ex_O)))
 | x5 ⇒ ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? ex_O))))
 | x6 ⇒ ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? ex_O)))))
 | x7 ⇒ ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? ex_O))))))
 | x8 ⇒ ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? ex_O)))))))
 | x9 ⇒ ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? ex_O))))))))
 | xA ⇒ ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? ex_O)))))))))
 | xB ⇒ ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? ex_O))))))))))
 | xC ⇒ ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? ex_O)))))))))))
 | xD ⇒ ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? ex_O))))))))))))
 | xE ⇒ ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? ex_O)))))))))))))
 | xF ⇒ ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? (ex_S ? ex_O))))))))))))))
 ].

(* ottali → esadecimali *)
ndefinition ex_of_oct ≝
λn.match n with
 [ o0 ⇒ x0 | o1 ⇒ x1 | o2 ⇒ x2 | o3 ⇒ x3 | o4 ⇒ x4 | o5 ⇒ x5 | o6 ⇒ x6 | o7 ⇒ x7 ].

(* esadecimali xNNNN → ottali *)
ndefinition oct_of_exL ≝
λn.match n with
  [ x0 ⇒ o0 | x1 ⇒ o1 | x2 ⇒ o2 | x3 ⇒ o3 | x4 ⇒ o4 | x5 ⇒ o5 | x6 ⇒ o6 | x7 ⇒ o7
  | x8 ⇒ o0 | x9 ⇒ o1 | xA ⇒ o2 | xB ⇒ o3 | xC ⇒ o4 | xD ⇒ o5 | xE ⇒ o6 | xF ⇒ o7 ].

(* esadecimali NNNNx → ottali *)
ndefinition oct_of_exH ≝
λn.match n with
  [ x0 ⇒ o0 | x1 ⇒ o0 | x2 ⇒ o1 | x3 ⇒ o1 | x4 ⇒ o2 | x5 ⇒ o2 | x6 ⇒ o3 | x7 ⇒ o3
  | x8 ⇒ o4 | x9 ⇒ o4 | xA ⇒ o5 | xB ⇒ o5 | xC ⇒ o6 | xD ⇒ o6 | xE ⇒ o7 | xF ⇒ o7 ].

ndefinition exadecim_destruct_aux ≝
Πe1,e2.ΠP:Prop.ΠH:e1 = e2.
 match eq_ex e1 e2 with [ true ⇒ P → P | false ⇒ P ].

ndefinition exadecim_destruct : exadecim_destruct_aux.
 #e1; #e2; #P; #H;
 nrewrite < H;
 nelim e1;
 nnormalize;
 napply (λx.x).
nqed.

nlemma eq_to_eqex : ∀n1,n2.n1 = n2 → eq_ex n1 n2 = true.
 #n1; #n2; #H;
 nrewrite > H;
 nelim n2;
 nnormalize;
 napply refl_eq.
nqed.

nlemma neqex_to_neq : ∀n1,n2.eq_ex n1 n2 = false → n1 ≠ n2.
 #n1; #n2; #H;
 napply (not_to_not (n1 = n2) (eq_ex n1 n2 = true) …);
 ##[ ##1: napply (eq_to_eqex n1 n2)
 ##| ##2: napply (eqfalse_to_neqtrue … H)
 ##]
nqed.

nlemma eqex_to_eq : ∀n1,n2.eq_ex n1 n2 = true → n1 = n2.
 #n1; #n2;
 ncases n1;
 ncases n2;
 nnormalize;
 ##[ ##1,18,35,52,69,86,103,120,137,154,171,188,205,222,239,256: #H; napply refl_eq
 ##| ##*: #H; (*ndestruct lentissima...*) napply (bool_destruct … H)
 ##]
nqed.

nlemma neq_to_neqex : ∀n1,n2.n1 ≠ n2 → eq_ex n1 n2 = false.
 #n1; #n2; #H;
 napply (neqtrue_to_eqfalse (eq_ex n1 n2));
 napply (not_to_not (eq_ex n1 n2 = true) (n1 = n2) ? H);
 napply (eqex_to_eq n1 n2).
nqed.

nlemma decidable_ex : ∀x,y:exadecim.decidable (x = y).
 #x; #y; nnormalize;
 napply (or2_elim (eq_ex x y = true) (eq_ex x y = false) ? (decidable_bexpr ?));
 ##[ ##1: #H; napply (or2_intro1 (x = y) (x ≠ y) (eqex_to_eq … H))
 ##| ##2: #H; napply (or2_intro2 (x = y) (x ≠ y) (neqex_to_neq … H))
 ##]
nqed.

nlemma symmetric_eqex : symmetricT exadecim bool eq_ex.
 #n1; #n2;
 napply (or2_elim (n1 = n2) (n1 ≠ n2) ? (decidable_ex n1 n2));
 ##[ ##1: #H; nrewrite > H; napply refl_eq
 ##| ##2: #H; nrewrite > (neq_to_neqex n1 n2 H);
          napply (symmetric_eq ? (eq_ex n2 n1) false);
          napply (neq_to_neqex n2 n1 (symmetric_neq ? n1 n2 H))
 ##]
nqed.

nlemma exadecim_is_comparable : comparable.
 @ exadecim
  ##[ napply x0
  ##| napply forall_ex
  ##| napply eq_ex
  ##| napply eqex_to_eq
  ##| napply eq_to_eqex
  ##| napply neqex_to_neq
  ##| napply neq_to_neqex
  ##| napply decidable_ex
  ##| napply symmetric_eqex
  ##]
nqed.

unification hint 0 ≔ ⊢ carr exadecim_is_comparable ≡ exadecim.

nlemma exadecim_is_comparable_ext : comparable_ext.
 napply mk_comparable_ext;
  ##[ napply exadecim_is_comparable
  ##| napply lt_ex
  ##| napply le_ex
  ##| napply gt_ex
  ##| napply ge_ex
  ##| napply and_ex
  ##| napply or_ex
  ##| napply xor_ex
  ##| napply getMSB_ex
  ##| napply setMSB_ex
  ##| napply clrMSB_ex
  ##| napply getLSB_ex
  ##| napply setLSB_ex
  ##| napply clrLSB_ex
  ##| napply rcr_ex
  ##| napply shr_ex
  ##| napply ror_ex
  ##| napply rcl_ex
  ##| napply shl_ex
  ##| napply rol_ex
  ##| napply not_ex
  ##| napply plus_ex_dc_dc
  ##| napply plus_ex_d_dc
  ##| napply plus_ex_dc_d
  ##| napply plus_ex_d_d
  ##| napply plus_ex_dc_c
  ##| napply plus_ex_d_c
  ##| napply pred_ex
  ##| napply succ_ex
  ##| napply compl_ex
  ##| napply abs_ex
  ##| napply inrange_ex
  ##]
nqed.

unification hint 0 ≔ ⊢ carr (comp_base exadecim_is_comparable_ext) ≡ exadecim.
