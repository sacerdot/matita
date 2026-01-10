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

include "ground/arith/pnat_iter.ma".
include "ground/arith/nat_split.ma".

(* ITERATED FUNCTION FOR NON-NEGATIVE INTEGERS ******************************)

(*** iter *)
definition niter (n:ℕ) (A:Type[0]) (f:A→A) (a:A): A ≝
           nsplit … a (λp.(f^❪A❫p) a) n
.

interpretation
  "iterated function (non-negative integers)"
  'Exp A f n = (niter n A f).

(* Basic constructions ******************************************************)

(*** iter_O *)
lemma niter_zero (A) (f) (a): a = (f^❪A❫𝟎) a.
// qed.

lemma niter_pos (A) (f) (p): f^p ⊜ f^❪A❫(⁤p).
// qed.

(* Advanced constructions ***************************************************)

(*** iter_n_Sm *)
lemma niter_appl (A) (f) (n): f ∘ f^n ⊜ f^❪A❫n ∘ f.
#A #f * //
#p @exteq_repl
/2 width=5 by piter_appl, compose_repl_fwd_dx/
qed.

lemma niter_compose (A) (B) (f) (g) (h) (n):
      h ∘ f ⊜ g ∘ h → h ∘ (f^❪A❫n) ⊜ (g^❪B❫n) ∘ h.
#A #B #f #g #h * //
#p #H @exteq_repl
/2 width=5 by piter_compose, compose_repl_fwd_dx/
qed.
