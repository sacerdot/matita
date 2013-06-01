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

(* NOTATION FOR THE "functional" COMPONENT ********************************)

notation "hvbox( T . break ④ { term 46 I } break { term 46 T1 , break term 46 T2 , break term 46 T3 } )"
 non associative with precedence 50
 for @{ 'DxItem4 $T $I $T1 $T2 $T3 }.

notation "hvbox( ↑ [ term 46 d , break term 46 e ] break term 46 T )"
   non associative with precedence 46
   for @{ 'Lift $d $e $T }.

notation "hvbox( T1 ⇨ break term 46 T2 )"
   non associative with precedence 45
   for @{ 'SRed $T1 $T2 }.
