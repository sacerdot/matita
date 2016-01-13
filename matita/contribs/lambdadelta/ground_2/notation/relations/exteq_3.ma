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

(* GENERAL NOTATION USED BY THE FORMAL SYSTEM λδ ****************************)

notation < "hvbox( v1 ≐ break term 46 v2 )"
   non associative with precedence 45
   for @{ 'ExtEq $M $v1 $v2 }.

notation > "hvbox( v1 ≐ break term 46 v2 )"
   non associative with precedence 45
   for @{ 'ExtEq ? $v1 $v2 }.

notation > "hvbox( v1 ≐ break ⦋ term 46 M ⦌ break term 46 v2 )"
   non associative with precedence 45
   for @{ 'ExtEq $M $v1 $v2 }.
