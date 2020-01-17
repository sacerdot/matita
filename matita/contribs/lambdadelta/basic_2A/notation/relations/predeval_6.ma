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

notation "hvbox( ⦃ term 46 G, break term 46 L ⦄ ⊢ break term 46 T1 ➡ * break [ term 46 h , break term 46 g ] break 𝐍 ⦃ term 46 T2 ⦄ )"
   non associative with precedence 45
   for @{ 'PRedEval $h $g $G $L $T1 $T2 }.
