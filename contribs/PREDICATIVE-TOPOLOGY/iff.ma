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

(* STATO: COMPILA *)

set "baseuri" "cic:/matita/logic/iff".

include "../../library/logic/connectives.ma".

definition Iff : Prop \to Prop \to Prop \def
   \lambda A,B. (A \to B) \land (B \to A).
   
 (*CSC: the URI must disappear: there is a bug now *)
interpretation "logical iff" 'iff x y = (cic:/matita/logic/iff/Iff.con x y).

notation > "hvbox(a break \liff b)" 
  left associative with precedence 25
for @{ 'iff $a $b }.

notation < "hvbox(a break \leftrightarrow b)" 
  left associative with precedence 25
for @{ 'iff $a $b }.
