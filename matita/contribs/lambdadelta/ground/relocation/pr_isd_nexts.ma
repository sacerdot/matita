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

include "ground/relocation/pr_nexts.ma".
include "ground/relocation/pr_isd.ma".

(* DIVERGENCE CONDITION FOR PARTIAL RELOCATION MAPS *************************)

(* Constructions with pr_nexts **********************************************)

(*** isdiv_nexts *)
lemma pr_isd_nexts (n) (f): šāØfā© ā šāØā*[n]fā©.
#n @(nat_ind_succ ā¦ n) -n /3 width=3 by pr_isd_next/
qed.

(* Inversions with pr_nexts *************************************************)

(*** isdiv_inv_nexts *)
lemma pr_isd_inv_nexts (n) (g): šāØā*[n]gā© ā šāØgā©.
#n @(nat_ind_succ ā¦ n) -n /3 width=3 by pr_isd_inv_next/
qed-.
