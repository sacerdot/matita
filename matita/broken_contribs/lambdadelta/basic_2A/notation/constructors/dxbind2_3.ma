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

notation > "hvbox( T . break ②{ term 46 I } break term 47 T1 )"
 non associative with precedence 46
 for @{ 'DxBind2 $T $I $T1 }.

notation "hvbox( T . break ⓑ { term 46 I } break term 48 T1 )"
 non associative with precedence 47
 for @{ 'DxBind2 $T $I $T1 }.
