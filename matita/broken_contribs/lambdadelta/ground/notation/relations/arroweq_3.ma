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

notation < "hvbox( term 46 u1 ⇔ break term 46 u2 )"
  non associative with precedence 45
  for @{ 'ArrowEq $S $u1 $u2 }.

notation > "hvbox( u1 ⇔ opt ( ❪ break term 46 S ❫ ) break term 46 u2 )"
  non associative with precedence 45
  for @{ 'ArrowEq ${default @{$S}@{?}} $u1 $u2 }.
