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

notation < "hvbox( f @ break a )"
  right associative with precedence 70
  for @{ 'CommercialAt $A $B $f $a }.

notation > "hvbox( f @ opt ( ❪ break term 46 A, break term 46 B ❫ ) break term 70 a )"
  non associative with precedence 70
  for @{ 'CommercialAt ${default @{$A}@{?}} ${default @{$B}@{?}} $f $a }.
