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

notation < "hvbox( ⟦ term 46 T ⟧[ break term 46 gv, break term 46 lv ] )"
   non associative with precedence 75
   for @{ 'WBrackets $M $gv $lv $T }.

notation > "hvbox( ⟦ term 46 T ⟧[ break term 46 gv, break term 46 lv ] )"
   non associative with precedence 75
   for @{ 'WBrackets ? $gv $lv $T }.

notation > "hvbox( ⟦ term 46 T ⟧{ break term 46 M }[ break term 46 gv , break term 46 lv ] )"
   non associative with precedence 75
   for @{ 'WBrackets $M $gv $lv $T }.
