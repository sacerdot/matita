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

include "ground/relocation/gr_sle_sle.ma".
include "ground/relocation/gr_sor.ma".

(* RELATIONAL UNION FOR GENERIC RELOCATION MAPS ***********************************************************)

(* Inversion lemmas with inclusion ******************************************)

(*** sor_inv_sle_sn *)
corec lemma gr_sor_inv_sle_sn:
            ∀f1,f2,f. f1 ⋓ f2 ≘ f → f1 ⊆ f.
#f1 #f2 #f * -f1 -f2 -f
#f1 #f2 #f #g1 #g2 #g #Hf #H1 #H2 #H0
/3 width=5 by gr_sle_push, gr_sle_next, gr_sle_weak/
qed-.

(*** sor_inv_sle_dx *)
corec lemma gr_sor_inv_sle_dx:
            ∀f1,f2,f. f1 ⋓ f2 ≘ f → f2 ⊆ f.
#f1 #f2 #f * -f1 -f2 -f
#f1 #f2 #f #g1 #g2 #g #Hf #H1 #H2 #H0
/3 width=5 by gr_sle_push, gr_sle_next, gr_sle_weak/
qed-.

(*** sor_inv_sle_sn_trans *)
lemma gr_sor_inv_sle_sn_trans:
      ∀f1,f2,f. f1 ⋓ f2 ≘ f → ∀g. g ⊆ f1 → g ⊆ f.
/3 width=4 by gr_sor_inv_sle_sn, gr_sle_trans/ qed-.

(*** sor_inv_sle_dx_trans *)
lemma gr_sor_inv_sle_dx_trans:
      ∀f1,f2,f. f1 ⋓ f2 ≘ f → ∀g. g ⊆ f2 → g ⊆ f.
/3 width=4 by gr_sor_inv_sle_dx, gr_sle_trans/ qed-.

(*** sor_inv_sle *)
axiom gr_sor_inv_sle_bi:
      ∀f1,f2,f. f1 ⋓ f2 ≘ f → ∀g. f1 ⊆ g → f2 ⊆ g → f ⊆ g.

(* Properties with inclusion ************************************************)

(*** sor_sle_dx *)
corec lemma gr_sor_sle_dx:
            ∀f1,f2. f1 ⊆ f2 → f1 ⋓ f2 ≘ f2.
#f1 #f2 * -f1 -f2
/3 width=7 by gr_sor_push_bi, gr_sor_next_bi, gr_sor_push_next/
qed.

(*** sor_sle_sn *)
corec lemma gr_sor_sle_sn:
            ∀f1,f2. f1 ⊆ f2 → f2 ⋓ f1 ≘ f2.
#f1 #f2 * -f1 -f2
/3 width=7 by gr_sor_push_bi, gr_sor_next_bi, gr_sor_next_push/
qed.
