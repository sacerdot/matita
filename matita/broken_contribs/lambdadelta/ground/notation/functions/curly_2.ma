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

notation < "hvbox( ❴ term 19 a1 ❵ )"
  non associative with precedence 70
  for @{ 'Curly $S $a1 }.

notation > "hvbox( ❴ term 19 a1 opt ( : break term 19 S ) ❵ )"
  non associative with precedence 70
  for @{ 'Curly ${default @{$S}@{?}} $a1 }.
