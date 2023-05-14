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

include "ground/arith/nat_lt.ma".

(* WELL-FOUNDED INDUCTION ***************************************************)

fact wf1_ind_nlt_aux (A1) (f:A1→ℕ) (Q:predicate …):
     (∀n. (∀a1. f a1 < n → Q a1) → ∀a1. f a1 = n → Q a1) →
     ∀n,a1. f a1 = n → Q a1.
#A1 #f #Q #H #n @(nat_ind_lt … n) -n /3 width=3 by/
qed-.

(*** f_ind *)
lemma wf1_ind_nlt (A1) (f:A1→ℕ) (Q:predicate …):
      (∀n. (∀a1. f a1 < n → Q a1) → ∀a1. f a1 = n → Q a1) →
      ∀a1. Q a1.
#A #f #Q #H #a1 @(wf1_ind_nlt_aux … H) -H //
qed-.
