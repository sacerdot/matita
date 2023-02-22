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

(* NOTATION FOR THE "models" COMPONENT **************************************)

notation < "hvbox( L ⨁[ break term 46 gv ] break term 46 lv ≘ break term 46 v )"
   non associative with precedence 45
   for @{ 'ROPlus $M $gv $L $lv $v }.

notation > "hvbox( L ⨁[ break term 46 gv ] break term 46 lv ≘ break term 46 v )"
   non associative with precedence 45
   for @{ 'ROPlus ? $gv $L $lv $v }.

notation > "hvbox( L ⨁{ break term 46 M }[ break term 46 gv ] break term 46 lv ≘ break term 46 v )"
   non associative with precedence 45
   for @{ 'ROPlus $M $gv $L $lv $v }.
