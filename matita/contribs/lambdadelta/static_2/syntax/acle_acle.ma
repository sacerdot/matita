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

include "static_2/syntax/acle.ma".

(* APPLICABILITY CONDITION PREORDER *****************************************)

(* Main properties **********************************************************)

theorem acle_trans: Transitive … acle.
#a1 #a #Ha1 #a2 #Ha2 #m1 #Hm1
elim (Ha1 … Hm1) -Ha1 -Hm1 #m #Ha #Hm1
elim (Ha2 … Ha) -Ha2 -Ha #m2 #Ha2 #Hm2
/3 width=5 by transitive_le, ex2_intro/
qed-.
