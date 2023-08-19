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
include "ground/relocation/p1/pr_sle.ma".

(* INCLUSION FOR PARTIAL RELOCATION MAPS ************************************)

(* Constructions with pr_tls ************************************************)

(*** sle_tls *)
lemma pr_sle_tls:
      ∀f1,f2. f1 ⊆ f2 → ∀n. ⫰*[n] f1 ⊆ ⫰*[n] f2.
#f1 #f2 #Hf12 #n @(nat_ind_succ … n) -n
/2 width=5 by pr_sle_tl/
qed.
