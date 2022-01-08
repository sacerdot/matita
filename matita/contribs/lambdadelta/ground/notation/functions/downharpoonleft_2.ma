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

notation < "hvbox( ⇃ term 70 a )"
  non associative with precedence 70
  for @{ 'DownHarpoonLeft $S $a }.

notation > "hvbox( ⇃ term 70 a )"
  non associative with precedence 70
  for @{ 'DownHarpoonLeft ? $a }.

notation > "hvbox( ⇃{ term 46 S } break term 70 a )"
  non associative with precedence 70
  for @{ 'DownHarpoonLeft $S $a }.
