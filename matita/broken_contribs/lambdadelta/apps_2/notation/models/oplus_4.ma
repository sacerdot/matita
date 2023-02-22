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

notation < "hvbox( d1 ⊕[ break term 46 p ] break term 46 d2 )"
   non associative with precedence 47
   for @{ 'OPlus $M $p $d1 $d2 }.

notation > "hvbox( d1 ⊕[ break term 46 p ] break term 46 d2 )"
   non associative with precedence 47
   for @{ 'OPlus ? $p $d1 $d2 }.

notation > "hvbox( d1 ⊕{ break term 46 M }[ break term 46 p ] break term 46 d2 )"
   non associative with precedence 47
   for @{ 'OPlus $M $p $d1 $d2 }.
