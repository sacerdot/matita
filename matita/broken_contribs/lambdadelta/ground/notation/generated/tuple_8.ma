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

notation > "hvbox( 〈 term 19 a0 opt ( : break term 19 A0 ), break term 19 a1 opt ( : break term 19 A1 ), break term 19 a2 opt ( : break term 19 A2 ), break term 19 a3 opt ( : break term 19 A3 ) 〉 )"
  non associative with precedence 90
  for @{ 'Tuple ${default @{$A0}@{?}} ${default @{$A1}@{?}} ${default @{$A2}@{?}} ${default @{$A3}@{?}} $a0 $a1 $a2 $a3 }.

notation < "hvbox( 〈 term 19 a0, break term 19 a1, break term 19 a2, break term 19 a3 〉 )"
  non associative with precedence 90
  for @{ 'Tuple $A0 $A1 $A2 $A3 $a0 $a1 $a2 $a3 }.
