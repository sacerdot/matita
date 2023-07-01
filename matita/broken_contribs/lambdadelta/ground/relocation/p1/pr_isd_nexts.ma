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

include "ground/relocation/p1/pr_nexts.ma".
include "ground/relocation/p1/pr_isd.ma".

(* DIVERGENCE CONDITION FOR PARTIAL RELOCATION MAPS *************************)

(* Constructions with pr_nexts **********************************************)

(*** isdiv_nexts *)
lemma pr_isd_nexts (n) (f): 𝛀❨f❩ → 𝛀❨↑*[n]f❩.
#n @(nat_ind_succ … n) -n /3 width=3 by pr_isd_next/
qed.

(* Inversions with pr_nexts *************************************************)

(*** isdiv_inv_nexts *)
lemma pr_isd_inv_nexts (n) (g): 𝛀❨↑*[n]g❩ → 𝛀❨g❩.
#n @(nat_ind_succ … n) -n /3 width=3 by pr_isd_inv_next/
qed-.
