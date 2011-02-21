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

include "lambda/types.ma".

(* all(P,l) holds when P holds for all members of l *)
let rec all (P:T→Prop) l on l ≝ match l with 
   [ nil ⇒ True
   | cons A D ⇒ P A ∧ all P D
   ].

(* Appl F l generalizes App applying F to a list of arguments
 * The head of l is applied first
 *)
let rec Appl F l on l ≝ match l with 
   [ nil ⇒ F
   | cons A D ⇒ Appl (App F A) D  
   ].

(* STRONGLY NORMALIZING TERMS *************************************************)

(* SN(t) holds when t is strongly normalizing *)
(* FG: we axiomatize it for now because we dont have reduction yet *)
axiom SN: T → Prop.

(* axiomatization of SN *******************************************************)

axiom sn_sort: ∀l,n. all SN l → SN (Appl (Sort n) l).

axiom sn_rel: ∀l,i. all SN l → SN (Appl (Rel i) l).

axiom sn_lambda: ∀B,F. SN B → SN F → SN (Lambda B F).

axiom sn_beta: ∀F,A,B,l. SN B → SN A →
               SN (Appl F[0:=A] l) → SN (Appl (Lambda B F) (A::l)).
