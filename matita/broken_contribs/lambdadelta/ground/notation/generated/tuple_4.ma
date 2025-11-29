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

(* NOTATION FOR GROUND ******************************************************)

notation > "hvbox( 〈 term 19 a0 opt ( : break term 19 A0 ), break term 19 a1 opt ( : break term 19 A1 ) 〉 )"
  non associative with precedence 90
  for @{ 'Tuple ${default @{$A0}@{?}} ${default @{$A1}@{?}} $a0 $a1 }.

notation < "hvbox( 〈 term 19 a0, break term 19 a1 〉 )"
  non associative with precedence 90
  for @{ 'Tuple $A0 $A1 $a0 $a1 }.
