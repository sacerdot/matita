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

notation < "hvbox( ⇂*[ break term 46 n ] break term 75 a )"
  non associative with precedence 75
  for @{ 'DownHarpoonRightStar $S $n $a }.

notation > "hvbox( ⇂*[ break term 46 n ] break term 75 a )"
  non associative with precedence 75
  for @{ 'DownHarpoonRightStar ? $n $a }.

notation > "hvbox( ⇂*{ term 46 S }[ break term 46 n ] break term 75 a )"
  non associative with precedence 75
  for @{ 'DownHarpoonRightStar $S $n $a }.
