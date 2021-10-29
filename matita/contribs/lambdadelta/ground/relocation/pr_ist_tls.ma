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

include "ground/relocation/pr_tls.ma".
include "ground/relocation/pr_ist.ma".

(* TOTALITY CONDITION FOR PARTIAL RELOCATION MAPS ***************************)

(* Constructions with pr_tls ************************************************)

(*** istot_tls *)
lemma pr_ist_tls (n) (f): 𝐓❨f❩ → 𝐓❨⫰*[n]f❩.
#n @(nat_ind_succ … n) -n //
#n #IH #f #Hf <pr_tls_succ
/3 width=1 by pr_ist_tl/
qed.
