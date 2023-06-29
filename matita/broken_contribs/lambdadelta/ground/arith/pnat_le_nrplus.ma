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

include "ground/arith/pnat_le.ma".
include "ground/arith/nat_rplus_succ.ma".

(* ORDER FOR POSITIVE INTEGERS **********************************************)

(* Constructions with nrplus ************************************************)

lemma ple_nrplus_dx (n) (p1) (p2):
      p1 ≤ p2 → p1+n ≤ p2+n.
#n @(nat_ind_succ … n) -n
/3 width=1 by ple_succ_bi/
qed.
