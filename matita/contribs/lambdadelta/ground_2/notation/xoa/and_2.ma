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

(* GENERAL NOTATION USED BY THE FORMAL SYSTEM λδ ****************************)

notation > "hvbox(∧∧ term 34 P0 break & term 34 P1)"
 non associative with precedence 35
 for @{ 'and $P0 $P1 }.
