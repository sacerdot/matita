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

include "arithmetics/nat.ma".

(* Policy: term metavariables: A, B, C, D
           de Bruijn indexes : i, j, h, k
*)
inductive term: Type[0] ≝
| VRef: nat → term         (* variable reference by index, starts at zero *)
| Abst: term → term        (* function formation *)
| Appl: term → term → term (* function application, argument comes first *)
.

notation "hvbox( # term 90 i )"
 non associative with precedence 55
 for @{ 'VariableReferenceByIndex $i }.

interpretation "term construction (variable reference by index)"
   'VariableReferenceByIndex i = (VRef i).

notation "hvbox( 𝛌 term 55 A )"
   non associative with precedence 55
   for @{ 'Abstraction $A }.

interpretation "term construction (abstraction)"
   'Abstraction A = (Abst A).

notation "hvbox( @ term 55 C . break term 55 A )"
   non associative with precedence 55
   for @{ 'Application $C $A }.

interpretation "term construction (application)"
   'Application C A = (Appl C A).

lemma prova_notazione: ∀A,i. @A.𝛌#i = @A.𝛌#i.
// qed-.
