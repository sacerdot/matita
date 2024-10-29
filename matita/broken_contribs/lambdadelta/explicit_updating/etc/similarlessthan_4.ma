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

(* NOTATION FOR EXPLICIT UPDATING *******************************************)

notation "hvbox( t1 ⪝ [ break term 46 R ] break term 46 t0 ⪝ break term 46 t2 )"
  non associative with precedence 45
  for @{ 'SimilarLessThan $t1 $R $t0 $t2 }.
