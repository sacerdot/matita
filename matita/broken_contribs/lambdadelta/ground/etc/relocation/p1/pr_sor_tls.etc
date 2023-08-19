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
include "ground/relocation/p1/pr_sor.ma".

(* RELATIONAL UNION FOR PARTIAL RELOCATION MAPS *****************************)

(* Constructions with pr_tls ************************************************)

(*** sor_tls *)
lemma pr_sor_tls:
      ∀f1,f2,f. f1 ⋓ f2 ≘ f →
      ∀n. ⫰*[n]f1 ⋓ ⫰*[n]f2 ≘ ⫰*[n]f.
#f1 #f2 #f #Hf #n @(nat_ind_succ … n) -n
/2 width=1 by pr_sor_tl/
qed.
