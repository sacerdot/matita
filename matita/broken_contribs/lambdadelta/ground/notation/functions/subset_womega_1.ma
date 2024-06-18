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

notation < "hvbox( 𝐖𝛀 )"
  non associative with precedence 70
  for @{ 'SubsetWOmega $S }.

notation > "hvbox( 𝐖𝛀 opt ( { term 46 S } ) )"
  non associative with precedence 70
  for @{ 'SubsetWOmega ${default @{$S}@{?}} }.
