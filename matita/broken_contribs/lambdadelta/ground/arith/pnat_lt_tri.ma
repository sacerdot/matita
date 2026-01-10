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

include "ground/arith/pnat_tri.ma".
include "ground/arith/pnat_lt.ma".

(* STRICT ORDER FOR POSITIVE INTEGERS ***************************************)

(* Properties with ptri *****************************************************)

lemma ptri_lt (A) (p1) (p2) (a1) (a2) (a3):
      p1 < p2 → a1 = ptri A p1 p2 a1 a2 a3.
#A #p1 #p2 #a1 #a2 #a3 #Hp @(plt_ind_alt … Hp) -Hp //
qed-.

lemma ptri_gt (A) (p1) (p2) (a1) (a2) (a3):
      p2 < p1 → a3 = ptri A p1 p2 a1 a2 a3.
#A #p1 #p2 #a1 #a2 #a3 #Hp @(plt_ind_alt … Hp) -Hp //
qed-.
