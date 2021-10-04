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

include "ground/relocation/pr_sle_sle.ma".
include "ground/relocation/pr_sor.ma".

(* RELATIONAL UNION FOR PARTIAL RELOCATION MAPS *****************************)

(* Inversions with pr_sle ***************************************************)

(*** sor_inv_sle_sn *)
corec lemma pr_sor_inv_sle_sn:
            ∀f1,f2,f. f1 ⋓ f2 ≘ f → f1 ⊆ f.
#f1 #f2 #f * -f1 -f2 -f
#f1 #f2 #f #g1 #g2 #g #Hf #H1 #H2 #H0
/3 width=5 by pr_sle_push, pr_sle_next, pr_sle_weak/
qed-.

(*** sor_inv_sle_dx *)
corec lemma pr_sor_inv_sle_dx:
            ∀f1,f2,f. f1 ⋓ f2 ≘ f → f2 ⊆ f.
#f1 #f2 #f * -f1 -f2 -f
#f1 #f2 #f #g1 #g2 #g #Hf #H1 #H2 #H0
/3 width=5 by pr_sle_push, pr_sle_next, pr_sle_weak/
qed-.

(*** sor_inv_sle_sn_trans *)
lemma pr_sor_inv_sle_sn_trans:
      ∀f1,f2,f. f1 ⋓ f2 ≘ f → ∀g. g ⊆ f1 → g ⊆ f.
/3 width=4 by pr_sor_inv_sle_sn, pr_sle_trans/ qed-.

(*** sor_inv_sle_dx_trans *)
lemma pr_sor_inv_sle_dx_trans:
      ∀f1,f2,f. f1 ⋓ f2 ≘ f → ∀g. g ⊆ f2 → g ⊆ f.
/3 width=4 by pr_sor_inv_sle_dx, pr_sle_trans/ qed-.

(*** sor_inv_sle *)
axiom pr_sor_inv_sle_bi:
      ∀f1,f2,f. f1 ⋓ f2 ≘ f → ∀g. f1 ⊆ g → f2 ⊆ g → f ⊆ g.

(* Constructions with pr_sle ************************************************)

(*** sor_sle_dx *)
corec lemma pr_sor_sle_dx:
            ∀f1,f2. f1 ⊆ f2 → f1 ⋓ f2 ≘ f2.
#f1 #f2 * -f1 -f2
/3 width=7 by pr_sor_push_bi, pr_sor_next_bi, pr_sor_push_next/
qed.

(*** sor_sle_sn *)
corec lemma pr_sor_sle_sn:
            ∀f1,f2. f1 ⊆ f2 → f2 ⋓ f1 ≘ f2.
#f1 #f2 * -f1 -f2
/3 width=7 by pr_sor_push_bi, pr_sor_next_bi, pr_sor_next_push/
qed.
