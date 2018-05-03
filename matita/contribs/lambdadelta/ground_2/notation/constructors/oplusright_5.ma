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

(* GENERAL NOTATION USED BY THE FORMAL SYSTEM λδ ****************************)

notation < "hvbox( { term 46 hd1, break term 46 hd2 }⨮ break term 46 tl )"
  non associative with precedence 47
  for @{ 'OPlusRight $S1 $S2 $hd1 $hd2 $tl }.

notation > "hvbox( { term 46 hd1, break term 46 hd2 }⨮ break term 46 tl )"
  non associative with precedence 47
  for @{ 'OPlusRight ? ? $hd1 $hd2 $tl }.
(*
(**) fix pair notation
notation > "hvbox( { term 46 hd1, break term 46 hd2 }⨮{ break term 46 S1, break term 46 S2 } break term 46 tl )"
  non associative with precedence 47
  for @{ 'OPlusRight $S1 $S2 $hd1 $hd2 $tl }.
*)
