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

(* GROUND NOTATION **********************************************************)

notation < "hvbox( v1 ≗ break term 46 v2 )"
  non associative with precedence 45
  for @{ 'RingEq $M $v1 $v2 }.

notation > "hvbox( v1 ≗ break term 46 v2 )"
  non associative with precedence 45
  for @{ 'RingEq ? $v1 $v2 }.

notation > "hvbox( v1 ≗{ break term 46 M } break term 46 v2 )"
  non associative with precedence 45
  for @{ 'RingEq $M $v1 $v2 }.
