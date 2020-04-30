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

(* Note: the notation with "/" does not work *)
notation "hvbox( [ term 46 d break ↙ term 46 N ] break term 46 M )"
  non associative with precedence 46
  for @{ 'DSubst $N $d $M }.

notation > "hvbox( [ ↙ term 46 N ] break term 46 M )"
  non associative with precedence 46
  for @{ 'DSubst $N 0 $M }.
