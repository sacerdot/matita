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
include "ground/relocation/pr_pat.ma".
include "ground/relocation/pr_after.ma".

(* RELATIONAL COMPOSITION FOR PARTIAL RELOCATION MAPS ***********************)

(* Constructions with pr_pat and pr_tls *************************************)

(* Note: this requires ↑ on first n *)
(*** after_tls *)
lemma pr_after_tls_sn_tls (n):
      ∀f1,f2,f. ＠⧣❨𝟏, f1❩ ≘ ↑n →
      f1 ⊚ f2 ≘ f → ⫰*[n]f1 ⊚ f2 ≘ ⫰*[n]f.
#n @(nat_ind_succ … n) -n //
#n #IH #f1 #f2 #f #Hf1 #Hf
cases (pr_pat_inv_unit_succ … Hf1) -Hf1 [ |*: // ] #g1 #Hg1 #H1
cases (pr_after_inv_next_sn … Hf … H1) -Hf #g #Hg #H0 destruct
<pr_tls_swap <pr_tls_swap /2 width=1 by/
qed.
