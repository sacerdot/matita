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

include "ground/relocation/p1/pr_tls.ma".
include "ground/relocation/p1/pr_isd_tl.ma".

(* DIVERGENCE CONDITION FOR PARTIAL RELOCATION MAPS *************************)

(* Constructions with pr_tls ************************************************)

(*** isdiv_tls *)
lemma pr_isd_tls (n) (g): 𝛀❨g❩ → 𝛀❨⫰*[n]g❩.
#n @(nat_ind_succ … n) -n /3 width=1 by pr_isd_tl/
qed.
