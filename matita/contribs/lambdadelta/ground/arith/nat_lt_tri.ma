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

include "ground/arith/nat_succ_tri.ma".
include "ground/arith/nat_lt.ma".

(* STRICT ORDER FOR NON-NEGATIVE INTEGERS ***********************************)

(* Destructions with ntri ***************************************************)

(*** tri_lt *)
lemma ntri_lt (A) (a1) (a2) (a3) (n1) (n2):
      n1 < n2 → a1 = ntri A n1 n2 a1 a2 a3.
#A #a1 #a2 #a3 #n1 #n2 #H @(nlt_ind_alt … H) -H //
qed-.

(*** tri_gt *)
lemma ntri_gt (A) (a1) (a2) (a3) (n1) (n2):
      n2 < n1 → a3 = ntri A n1 n2 a1 a2 a3.
#A #a1 #a2 #a3 #n1 #n2 #H @(nlt_ind_alt … H) -H //
qed-.
