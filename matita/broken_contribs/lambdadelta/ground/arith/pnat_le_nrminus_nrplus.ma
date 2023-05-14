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

include "ground/arith/nat_rminus.ma".
include "ground/arith/nat_rplus_succ.ma".
include "ground/arith/pnat_le_pred.ma".

(* ORDER FOR POSITIVE INTEGERS **********************************************)

(* Constructions with nrminus and nrplus ************************************)

lemma ple_nrminus_dx (n) (p) (q):
      p + n ≤ q → p ≤ q - n.
#n @(nat_ind_succ … n) -n //
#n #IH #p #q
<nrplus_succ_shift <nrminus_succ_dx #Hn
lapply (IH … Hn) -IH -Hn #Hn
elim (ple_inv_succ_sn … Hn) -Hn #Hn #_ //
qed. 
