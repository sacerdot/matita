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
include "ground/relocation/p1/pr_isi_tl.ma".

(* IDENTITY CONDITION FOR PARTIAL RELOCATION MAPS ***************************)

(* Constructions with pr_tls ************************************************)

(*** isid_tls *)
lemma pr_isi_tls (n) (f): 𝐈❨f❩ → 𝐈❨⫰*[n]f❩.
#n @(nat_ind_succ … n) -n /3 width=1 by pr_isi_tl/
qed.
