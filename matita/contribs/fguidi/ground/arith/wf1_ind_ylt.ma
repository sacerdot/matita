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

include "ground/arith/ynat_lt_le.ma".

(* WELL-FOUNDED INDUCTION ***************************************************)

(*** ynat_f_ind_aux *)
fact wf1_ind_ylt_aux (A1) (f:A1→ynat) (Q:predicate …):
     (∀y. (∀a1. f a1 < y → Q a1) → ∀a1. f a1 = y → Q a1) →
     ∀y,a1. f a1 = y → Q a1.
#A1 #f #Q #H #y @(ynat_ind_lt … y) -y /3 width=3 by/
qed-.

(*** ynat_f_ind *)
lemma wf1_ind_ylt (A1) (f:A1→ynat) (Q:predicate …):
      (∀y. (∀a1. f a1 < y → Q a1) → ∀a1. f a1 = y → Q a1) →
      ∀a1. Q a1.
#A #f #Q #H #a1 @(wf1_ind_ylt_aux … H) -H //
qed-.
