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

(* NOTATION FOR DELAYED UPDATING ********************************************)

notation "hvbox( t1 Ꟈ➡*𝐝𝐛𝐟[ break term 46 u1, break term 46 u2 ] break term 46 t2 )"
  non associative with precedence 45
  for @{ 'DStrokeBlackRightArrowStarDBF $t1 $u1 $u2 $t2 }.


