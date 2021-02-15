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

fact wf2_ind_nlt_aux (A1) (A2) (f:A1→A2→nat) (Q:relation2 …):
     (∀n. (∀a1,a2. f a1 a2 < n → Q a1 a2) → ∀a1,a2. f a1 a2 = n → Q a1 a2) →
     ∀n,a1,a2. f a1 a2 = n → Q a1 a2.
#A1 #A2 #f #Q #H #n @(nat_ind_lt … n) -n /3 width=3 by/
qed-.

(*** f2_ind *)
lemma wf2_ind_nlt (A1) (A2) (f:A1→A2→nat) (Q:relation2 …):
      (∀n. (∀a1,a2. f a1 a2 < n → Q a1 a2) → ∀a1,a2. f a1 a2 = n → Q a1 a2) →
      ∀a1,a2. Q a1 a2.
#A1 #A2 #f #Q #H #a1 #a2 @(wf2_ind_nlt_aux … H) -H //
qed-.
