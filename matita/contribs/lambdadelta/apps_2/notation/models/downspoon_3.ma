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

notation < "hvbox( ⫰[ break term 46 i ] break term 46 lv )"
   non associative with precedence 46
   for @{ 'DownSpoon $M $d $lv }.

notation > "hvbox( ⫰[ break term 46 i ] break term 46 lv )"
   non associative with precedence 46
   for @{ 'DownSpoon ? $d $lv }.

notation > "hvbox( ⫰{ term 46 M }[ break term 46 i ] break term 46 lv )"
   non associative with precedence 46
   for @{ 'DownSpoon $M $d $lv }.
