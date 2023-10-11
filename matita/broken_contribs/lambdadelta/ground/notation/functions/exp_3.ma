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

notation < "hvbox( term 66 f ^ break term 90 x )"
  non associative with precedence 65
  for @{ 'Exp $X $f $x }.

notation > "hvbox( f ^ opt ( { break term 46 X } ) break term 90 x )"
  non associative with precedence 65
  for @{ 'Exp ${default @{$X}@{?}} $f $x }.
