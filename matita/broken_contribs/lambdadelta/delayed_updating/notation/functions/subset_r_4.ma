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

(* NOTATION FOR DELAYED UPDATING ********************************************)

notation "hvbox( 𝐑❨ break term 46 p, break term 46 b, break term 46 q, break term 46 n ❩ )"
  non associative with precedence 70
  for @{ 'SubsetR $p $b $q $n }.
