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

notation > "hvbox( ❨ term 19 Y ❩ opt ( ❪ break term 46 X ❫ ) break term 70 Z )"
  non associative with precedence 70
  for @{ 'Parenthesis ${default @{$X}@{?}} $Y $Z }.

notation < "hvbox( ❨ term 19 Y ❩ break term 70 Z )"
  non associative with precedence 70
  for @{ 'Parenthesis $X $Y $Z }.
