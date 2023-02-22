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

include "ground/relocation/pr_tls_eq.ma".
include "ground/relocation/pr_pushs.ma".

(* ITERATED TAIL FOR PARTIAL RELOCATION MAPS ********************************)

(* Inversions with pr_pushs and pr_eq ***************************************)

(*** eq_inv_pushs_sn *)
lemma pr_eq_inv_pushs_sn (n):
      ∀f1,g2. ⫯*[n] f1 ≐ g2 →
      ∧∧ f1 ≐ ⫰*[n]g2 & ⫯*[n]⫰*[n]g2 = g2.
#n @(nat_ind_succ … n) -n /2 width=1 by conj/
#n #IH #f1 #g2 #H
elim (pr_eq_inv_push_sn … H) -H [|*: // ] #Hf10 *
elim (IH … Hf10) -IH -Hf10 #Hf12 #H1
<pr_tls_succ /2 width=1 by conj/
qed-.

(*** eq_inv_pushs_dx *)
lemma pr_eq_inv_pushs_dx (n):
      ∀f2,g1. g1 ≐ ⫯*[n] f2 →
      ∧∧ ⫰*[n]g1 ≐ f2 & ⫯*[n]⫰*[n]g1 = g1.
#n @(nat_ind_succ … n) -n /2 width=1 by conj/
#n #IH #f2 #g1 #H
elim (pr_eq_inv_push_dx … H) -H [|*: // ] #Hf02 *
elim (IH … Hf02) -IH -Hf02 #Hf12 #H2
<pr_tls_succ /2 width=1 by conj/
qed-.
