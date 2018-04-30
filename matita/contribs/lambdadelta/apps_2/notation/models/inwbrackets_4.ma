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

notation < "hvbox( lv ϵ ⟦ break term 46 L ⟧[ break term 46 gv ] )"
   non associative with precedence 45
   for @{ 'InWBrackets $M $gv $L $lv }.

notation > "hvbox( lv ϵ ⟦ break term 46 L ⟧[ break term 46 gv ] )"
   non associative with precedence 45
   for @{ 'InWBrackets ? $gv $L $lv }.

notation > "hvbox( lv ϵ ⟦ break term 46 L ⟧{ break term 46 M }[ break term 46 gv ] )"
   non associative with precedence 45
   for @{ 'InWBrackets $M $gv $L $lv }.
