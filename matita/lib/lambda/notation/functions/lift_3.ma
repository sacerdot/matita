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

notation "hvbox( ↑ [ term 46 d , break term 46 h ] break term 46 M )"
  non associative with precedence 46
  for @{ 'Lift $h $d $M }.

notation > "hvbox( ↑ [ term 46 h ] break term 46 M )"
  non associative with precedence 46
  for @{ 'Lift $h 0 $M }.

notation > "hvbox( ↑ term 46 M )"
  non associative with precedence 46
  for @{ 'Lift 1 0 $M }.
