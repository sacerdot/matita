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

notation "hvbox( ⦃ term 46 G1, break term 46 L1, break term 46 T1 ⦄ ≡ break [ term 46 d ] break ⦃ term 46 G2, break term 46 L2 , break term 46 T2 ⦄ )"
   non associative with precedence 45
   for @{ 'LazyEq $d $G1 $L1 $T1 $G2 $L2 $T2 }.
