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

(* GENERAL NOTATION USED BY THE FORMAL SYSTEM λδ ****************************)

notation < "hvbox( f ^ break x )"
  left associative with precedence 75
  for @{ 'Exp $X $f $x }.

notation > "hvbox( f ^ break x )"
  left associative with precedence 75
  for @{ 'Exp ? $f $x }.

notation > "hvbox( f ^{ break term 46 X } break term 75 x )"
  non associative with precedence 75
  for @{ 'Exp $X $f $x }.
