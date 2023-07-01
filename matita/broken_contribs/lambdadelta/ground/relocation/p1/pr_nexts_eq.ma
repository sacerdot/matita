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

include "ground/relocation/p1/pr_tl_eq.ma".
include "ground/relocation/p1/pr_nexts.ma".

(* ITERATED NEXT FOR PARTIAL RELOCATION MAPS ********************************)

(* Constructions with pr_eq *************************************************)

(*** nexts_eq_repl *)
lemma pr_nexts_eq_repl (n):
      pr_eq_repl (λf1,f2. ↑*[n] f1 ≐ ↑*[n] f2).
#n @(nat_ind_succ … n) -n
/3 width=5 by pr_eq_next/
qed.

(* Inversions with pr_eq ****************************************************)

lemma pr_eq_inv_nexts_push_bi (f1) (f2) (n1) (n2):
      ↑*[n1] ⫯f1 ≐ ↑*[n2] ⫯f2 →
      ∧∧ n1 = n2 & f1 ≐ f2.
#f1 #f2
#n1 @(nat_ind_succ … n1) -n1 [| #n1 #IH ]
#n2 @(nat_ind_succ … n2) -n2 [2,4: #n2 #_ ]
[ <pr_nexts_zero <pr_nexts_succ #H
  elim (pr_eq_inv_push_next … H) -H //
| <pr_nexts_succ <pr_nexts_succ #H
  lapply (pr_eq_inv_next_bi … H ????) -H [5:|*: // ] #H
  elim (IH … H) -IH -H /2 width=1 by conj/
| <pr_nexts_zero <pr_nexts_zero #H
  lapply (pr_eq_inv_push_bi … H ????) -H [5:|*: // ] #H
  /2 width=1 by conj/
| <pr_nexts_succ <pr_nexts_zero #H
  elim (pr_eq_inv_next_push … H) -H //
]
qed-.
