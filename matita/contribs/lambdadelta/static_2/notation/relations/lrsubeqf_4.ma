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

notation "hvbox( ⦃ term 46 L1, break term 46 f1 ⦄ ⫃ 𝐅+ ⦃ break term 46 L2, break term 46 f2 ⦄ )"
   non associative with precedence 45
   for @{ 'LRSubEqF $L1 $f1 $L2 $f2 }.
