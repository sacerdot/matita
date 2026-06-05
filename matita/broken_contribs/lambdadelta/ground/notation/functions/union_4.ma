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

notation < "hvbox(∪∪ term 46 U1 break | term 46 U2 break | term 69 U3)"
  non associative with precedence 70
  for  @{ 'Union $S $U1 $U2 $U3 }.

notation > "hvbox(∪∪ opt( ❪ term 46 S ❫ ) term 46 U1 break | term 46 U2 break | term 69 U3)"
  non associative with precedence 70
  for  @{ 'Union ${default @{$S}@{?}} $U1 $U2 $U3 }.
