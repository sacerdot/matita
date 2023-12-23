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

notation < "hvbox( ❴ ident i ❘ break term 19 P ❵ )"
  non associative with precedence 19
  for @{ λ${ident i}. $P }.

notation > "hvbox( ❴ ident i opt ( { : break term 19 T ) ❘ break term 19 P ❵ )"
  non associative with precedence 19
  for @{ λ${ident i}:${default @{$T}@{?}}. $P }.
