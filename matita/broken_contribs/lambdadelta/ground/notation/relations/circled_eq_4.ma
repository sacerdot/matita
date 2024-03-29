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

notation < "hvbox( f1 ⊜ break term 46 f2 )"
  non associative with precedence 45
  for @{ 'CircledEq $A $B $f1 $f2 }.

notation > "hvbox( f1 ⊜ break term 46 f2 )"
  non associative with precedence 45
  for @{ 'CircledEq ? ? $f1 $f2 }.

notation > "hvbox( f1 ⊜{ break term 46 A, break term 46 B } break term 46 f2 )"
  non associative with precedence 45
  for @{ 'CircledEq $A $B $f1 $f2 }.
