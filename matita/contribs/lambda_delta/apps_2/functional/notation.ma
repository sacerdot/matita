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

notation "hvbox( ↑ [ d , break e ] break term 60 T )"
   non associative with precedence 60
   for @{ 'Lift $d $e $T }.

notation "hvbox( [ d ← break V ] break term 60 T )"
   non associative with precedence 60
   for @{ 'Subst $V $d $T }.

notation "hvbox( T1 ⇨ break term 46 T2 )"
   non associative with precedence 45
   for @{ 'SRed $T1 $T2 }.
