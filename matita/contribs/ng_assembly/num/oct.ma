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

include "num/bool.ma".

(* ****** *)
(* OTTALI *)
(* ****** *)

ninductive oct : Type ≝
  o0: oct
| o1: oct
| o2: oct
| o3: oct
| o4: oct
| o5: oct
| o6: oct
| o7: oct.

(* iteratore sugli ottali *)
ndefinition forall_oct ≝ λP.
 P o0 ⊗ P o1 ⊗ P o2 ⊗ P o3 ⊗ P o4 ⊗ P o5 ⊗ P o6 ⊗ P o7.

(* operatore = *)
ndefinition eq_oct ≝
λn1,n2:oct.
 match n1 with
  [ o0 ⇒ match n2 with [ o0 ⇒ true  | _ ⇒ false ]
  | o1 ⇒ match n2 with [ o1 ⇒ true  | _ ⇒ false ] 
  | o2 ⇒ match n2 with [ o2 ⇒ true  | _ ⇒ false ]
  | o3 ⇒ match n2 with [ o3 ⇒ true  | _ ⇒ false ] 
  | o4 ⇒ match n2 with [ o4 ⇒ true  | _ ⇒ false ]  
  | o5 ⇒ match n2 with [ o5 ⇒ true  | _ ⇒ false ] 
  | o6 ⇒ match n2 with [ o6 ⇒ true  | _ ⇒ false ]  
  | o7 ⇒ match n2 with [ o7 ⇒ true  | _ ⇒ false ] 
  ].

(* operatore and *)
ndefinition and_oct ≝
λe1,e2:oct.match e1 with
 [ o0 ⇒ match e2 with
  [ o0 ⇒ o0 | o1 ⇒ o0 | o2 ⇒ o0 | o3 ⇒ o0 
  | o4 ⇒ o0 | o5 ⇒ o0 | o6 ⇒ o0 | o7 ⇒ o0 ]
 | o1 ⇒ match e2 with
  [ o0 ⇒ o0 | o1 ⇒ o1 | o2 ⇒ o0 | o3 ⇒ o1 
  | o4 ⇒ o0 | o5 ⇒ o1 | o6 ⇒ o0 | o7 ⇒ o1 ]
 | o2 ⇒ match e2 with
  [ o0 ⇒ o0 | o1 ⇒ o0 | o2 ⇒ o2 | o3 ⇒ o2 
  | o4 ⇒ o0 | o5 ⇒ o0 | o6 ⇒ o2 | o7 ⇒ o2 ]
 | o3 ⇒ match e2 with
  [ o0 ⇒ o0 | o1 ⇒ o1 | o2 ⇒ o2 | o3 ⇒ o3 
  | o4 ⇒ o0 | o5 ⇒ o1 | o6 ⇒ o2 | o7 ⇒ o3 ]
 | o4 ⇒ match e2 with
  [ o0 ⇒ o0 | o1 ⇒ o0 | o2 ⇒ o0 | o3 ⇒ o0 
  | o4 ⇒ o4 | o5 ⇒ o4 | o6 ⇒ o4 | o7 ⇒ o4 ]
 | o5 ⇒ match e2 with
  [ o0 ⇒ o0 | o1 ⇒ o1 | o2 ⇒ o0 | o3 ⇒ o1 
  | o4 ⇒ o4 | o5 ⇒ o5 | o6 ⇒ o4 | o7 ⇒ o5 ]
 | o6 ⇒ match e2 with
  [ o0 ⇒ o0 | o1 ⇒ o0 | o2 ⇒ o2 | o3 ⇒ o2 
  | o4 ⇒ o4 | o5 ⇒ o4 | o6 ⇒ o6 | o7 ⇒ o6 ]
 | o7 ⇒ match e2 with
  [ o0 ⇒ o0 | o1 ⇒ o1 | o2 ⇒ o2 | o3 ⇒ o3 
  | o4 ⇒ o4 | o5 ⇒ o5 | o6 ⇒ o6 | o7 ⇒ o7 ]
 ]. 

(* operatore or *)
ndefinition or_oct ≝
λe1,e2:oct.match e1 with
 [ o0 ⇒ match e2 with
  [ o0 ⇒ o0 | o1 ⇒ o1 | o2 ⇒ o2 | o3 ⇒ o3 
  | o4 ⇒ o4 | o5 ⇒ o5 | o6 ⇒ o6 | o7 ⇒ o7 ]
 | o1 ⇒ match e2 with
  [ o0 ⇒ o1 | o1 ⇒ o1 | o2 ⇒ o3 | o3 ⇒ o3 
  | o4 ⇒ o5 | o5 ⇒ o5 | o6 ⇒ o7 | o7 ⇒ o7 ]
 | o2 ⇒ match e2 with
  [ o0 ⇒ o2 | o1 ⇒ o3 | o2 ⇒ o2 | o3 ⇒ o3 
  | o4 ⇒ o6 | o5 ⇒ o7 | o6 ⇒ o6 | o7 ⇒ o7 ]
 | o3 ⇒ match e2 with
  [ o0 ⇒ o3 | o1 ⇒ o3 | o2 ⇒ o3 | o3 ⇒ o3 
  | o4 ⇒ o7 | o5 ⇒ o7 | o6 ⇒ o7 | o7 ⇒ o7 ]
 | o4 ⇒ match e2 with
  [ o0 ⇒ o4 | o1 ⇒ o5 | o2 ⇒ o6 | o3 ⇒ o7 
  | o4 ⇒ o4 | o5 ⇒ o5 | o6 ⇒ o6 | o7 ⇒ o7 ]
 | o5 ⇒ match e2 with
  [ o0 ⇒ o5 | o1 ⇒ o5 | o2 ⇒ o7 | o3 ⇒ o7 
  | o4 ⇒ o5 | o5 ⇒ o5 | o6 ⇒ o7 | o7 ⇒ o7 ]
 | o6 ⇒ match e2 with
  [ o0 ⇒ o6 | o1 ⇒ o7 | o2 ⇒ o6 | o3 ⇒ o7 
  | o4 ⇒ o6 | o5 ⇒ o7 | o6 ⇒ o6 | o7 ⇒ o7 ]
 | o7 ⇒ match e2 with
  [ o0 ⇒ o7 | o1 ⇒ o7 | o2 ⇒ o7 | o3 ⇒ o7 
  | o4 ⇒ o7 | o5 ⇒ o7 | o6 ⇒ o7 | o7 ⇒ o7 ]
 ].

(* operatore xor *)
ndefinition xor_oct ≝
λe1,e2:oct.match e1 with
 [ o0 ⇒ match e2 with
  [ o0 ⇒ o0 | o1 ⇒ o1 | o2 ⇒ o2 | o3 ⇒ o3 
  | o4 ⇒ o4 | o5 ⇒ o5 | o6 ⇒ o6 | o7 ⇒ o7 ] 
 | o1 ⇒ match e2 with
  [ o0 ⇒ o1 | o1 ⇒ o0 | o2 ⇒ o3 | o3 ⇒ o2 
  | o4 ⇒ o5 | o5 ⇒ o4 | o6 ⇒ o7 | o7 ⇒ o6 ] 
 | o2 ⇒ match e2 with
  [ o0 ⇒ o2 | o1 ⇒ o3 | o2 ⇒ o0 | o3 ⇒ o1 
  | o4 ⇒ o6 | o5 ⇒ o7 | o6 ⇒ o4 | o7 ⇒ o5 ] 
 | o3 ⇒ match e2 with
  [ o0 ⇒ o3 | o1 ⇒ o2 | o2 ⇒ o1 | o3 ⇒ o0 
  | o4 ⇒ o7 | o5 ⇒ o6 | o6 ⇒ o5 | o7 ⇒ o4 ] 
 | o4 ⇒ match e2 with
  [ o0 ⇒ o4 | o1 ⇒ o5 | o2 ⇒ o6 | o3 ⇒ o7 
  | o4 ⇒ o0 | o5 ⇒ o1 | o6 ⇒ o2 | o7 ⇒ o3 ] 
 | o5 ⇒ match e2 with
  [ o0 ⇒ o5 | o1 ⇒ o4 | o2 ⇒ o7 | o3 ⇒ o6 
  | o4 ⇒ o1 | o5 ⇒ o0 | o6 ⇒ o3 | o7 ⇒ o2 ] 
 | o6 ⇒ match e2 with
  [ o0 ⇒ o6 | o1 ⇒ o7 | o2 ⇒ o4 | o3 ⇒ o5 
  | o4 ⇒ o2 | o5 ⇒ o3 | o6 ⇒ o0 | o7 ⇒ o1 ] 
 | o7 ⇒ match e2 with
  [ o0 ⇒ o7 | o1 ⇒ o6 | o2 ⇒ o5 | o3 ⇒ o4 
  | o4 ⇒ o3 | o5 ⇒ o2 | o6 ⇒ o1 | o7 ⇒ o0 ] 
 ].

(* operatore successore *)
ndefinition succ_oct ≝
λn.match n with
 [ o0 ⇒ o1 | o1 ⇒ o2 | o2 ⇒ o3 | o3 ⇒ o4 | o4 ⇒ o5 | o5 ⇒ o6 | o6 ⇒ o7 | o7 ⇒ o0 ].

(* ottali ricorsivi *)
ninductive rec_oct : oct → Type ≝
  oc_O : rec_oct o0
| oc_S : ∀n.rec_oct n → rec_oct (succ_oct n).

(* ottali → ottali ricorsivi *)
ndefinition oct_to_recoct ≝
λn.match n return λx.rec_oct x with
 [ o0 ⇒ oc_O
 | o1 ⇒ oc_S ? oc_O
 | o2 ⇒ oc_S ? (oc_S ? oc_O)
 | o3 ⇒ oc_S ? (oc_S ? (oc_S ? oc_O))
 | o4 ⇒ oc_S ? (oc_S ? (oc_S ? (oc_S ? oc_O)))
 | o5 ⇒ oc_S ? (oc_S ? (oc_S ? (oc_S ? (oc_S ? oc_O))))
 | o6 ⇒ oc_S ? (oc_S ? (oc_S ? (oc_S ? (oc_S ? (oc_S ? oc_O)))))
 | o7 ⇒ oc_S ? (oc_S ? (oc_S ? (oc_S ? (oc_S ? (oc_S ? (oc_S ? oc_O))))))
 ].
