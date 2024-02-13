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

notation < "hvbox( 𝐗❨ break term 46 l ❩ )"
  non associative with precedence 70
  for @{ 'SubsetX $S $l }.

notation > "hvbox( 𝐗 opt ( { term 46 S } ) ❨ break term 46 l ❩ )"
  non associative with precedence 70
  for @{ 'SubsetX ${default @{$S}@{?}} $l }.
