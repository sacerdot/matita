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
include "ground/relocation/pr_nat.ma".
include "ground/relocation/pr_coafter.ma".

(* RELATIONAL CO-COMPOSITION FOR PARTIAL RELOCATION MAPS ********************)

(* Constructions with pr_nat and pr_tls *************************************)

(*** coafter_tls *)
lemma pr_coafter_tls_bi_tls (n2) (n1):
      ∀f1,f2,f. ＠§❨n1, f1❩ ≘ n2 →
      f1 ~⊚ f2 ≘ f → ⫰*[n2]f1 ~⊚ ⫰*[n1]f2 ≘ ⫰*[n2]f.
#n2 @(nat_ind_succ … n2) -n2 [ #n1 | #n2 #IH * [| #n1 ] ] #f1 #f2 #f #Hf1 #Hf
[ elim (pr_nat_inv_zero_dx … Hf1) -Hf1 [ |*: // ] #g1 #Hg1 #H1 destruct //
| elim (pr_nat_inv_zero_succ … Hf1) -Hf1 [ |*: // ] #g1 #Hg1 #H1
  elim (pr_coafter_inv_next_sn … Hf … H1) -Hf #g #Hg #H0 destruct
  lapply (IH … Hg1 Hg) -IH -Hg1 -Hg //
| elim (pr_nat_inv_succ_dx … Hf1) -Hf1 [1,3: * |*: // ] #g1 [ #n1 ] #Hg1 [ #H ] #H1
  [ elim (pr_coafter_inv_push_sn … Hf … H1) -Hf * #g2 #g #Hg #H2 #H0 destruct
    lapply (IH … Hg1 Hg) -IH -Hg1 -Hg #H //
  | elim (pr_coafter_inv_next_sn … Hf … H1) -Hf #g #Hg #H0 destruct
    lapply (IH … Hg1 Hg) -IH -Hg1 -Hg #H //
  ]
]
qed.

(*** coafter_tls_O *)
lemma pr_coafter_tls_sn_tls:
      ∀n,f1,f2,f. ＠§❨𝟎, f1❩ ≘ n →
      f1 ~⊚ f2 ≘ f → ⫰*[n]f1 ~⊚ f2 ≘ ⫰*[n]f.
/2 width=1 by pr_coafter_tls_bi_tls/ qed.
