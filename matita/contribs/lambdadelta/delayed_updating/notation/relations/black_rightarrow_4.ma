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

notation "hvbox( t1 ➡ 'd' 'f' [ break term 46 p, break term 46 q ] break term 46 t2 )"
   non associative with precedence 45
   for @{ 'BlackRightArrow $t1 $p $q $t2 }.
