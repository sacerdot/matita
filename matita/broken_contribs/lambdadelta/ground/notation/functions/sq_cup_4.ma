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

notation < "hvbox( x1 ⊔ break x2 )"
  left associative with precedence 55
  for @{ 'SqCup $X1 $X2 $x1 $x2 }.

notation > "hvbox( x1 ⊔ opt ( { break term 46 X1, term 46 X2 } ) break term 56 x2 )"
  non associative with precedence 55
  for @{ 'SqCup ${default @{$X1}@{?}} ${default @{$X2}@{?}} $x1 $x2 }.
