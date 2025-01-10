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

notation < "hvbox( x1 /𝐝𝐛𝐟 break x2 )"
  left associative with precedence 60
  for @{ 'SlashDBF $X $x1 $x2 }.

notation > "hvbox( x1 /𝐝𝐛𝐟 opt ( { break term 46 X } ) break term 61 x2 )"
  non associative with precedence 60
  for @{ 'SlashDBF ${default @{$X}@{?}} $x1 $x2 }.
