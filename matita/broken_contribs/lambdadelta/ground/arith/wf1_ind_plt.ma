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

include "ground/arith/pnat_lt.ma".

(* WELL-FOUNDED INDUCTION ***************************************************)

fact wf1_ind_plt_aux (A1) (f:A1→ℤ⁺) (Q:predicate …):
     (∀p. (∀a1. f a1 < p → Q a1) → ∀a1. f a1 = p → Q a1) →
     ∀p,a1. f a1 = p → Q a1.
#A1 #f #Q #H #p @(pnat_ind_lt … p) -p /3 width=3 by/
qed-.

lemma wf1_ind_plt (A1) (f:A1→ℤ⁺) (Q:predicate …):
      (∀p. (∀a1. f a1 < p → Q a1) → ∀a1. f a1 = p → Q a1) →
      ∀a1. Q a1.
#A #f #Q #H #a1 @(wf1_ind_plt_aux … H) -H //
qed-.
