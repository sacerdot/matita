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

notation < "hvbox( a ⧸≬ break term 46 u )"
  non associative with precedence 45
  for @{ 'NotBetween $S $a $u }.

notation > "hvbox( a ⧸≬ break term 46 u )"
  non associative with precedence 45
  for @{ 'NotBetween ? $a $u }.

notation > "hvbox( a ⧸≬{ break term 46 S } break term 46 u )"
  non associative with precedence 45
  for @{ 'NotBetween $S $a $u }.
