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

(* NOTATION FOR THE FORMAL SYSTEM λδ ****************************************)

notation "hvbox( L1 ≋ⓧ*[ break term 46 n1, break term 46 n2 ] break term 46 L2 )"
   non associative with precedence 45
   for @{ 'VoidStarEq $L1 $n1 $n2 $L2 }.
