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

(* NOTE: This file was generated by xoa, do not edit ************************)

(* Note: multiple existental quantifier (4, 1) *)
notation > "hvbox(∃∃ ident x0 break . term 19 P0 break & term 19 P1 break & term 19 P2 break & term 19 P3)"
  non associative with precedence 20
  for @{ 'Ex (λ${ident x0}.$P0) (λ${ident x0}.$P1) (λ${ident x0}.$P2) (λ${ident x0}.$P3) }.

notation < "hvbox(∃∃ ident x0 break . term 19 P0 break & term 19 P1 break & term 19 P2 break & term 19 P3)"
  non associative with precedence 20
  for @{ 'Ex (λ${ident x0}:$T0.$P0) (λ${ident x0}:$T0.$P1) (λ${ident x0}:$T0.$P2) (λ${ident x0}:$T0.$P3) }.

