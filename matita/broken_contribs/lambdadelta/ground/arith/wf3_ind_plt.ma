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

fact wf3_ind_plt_aux (A1) (A2) (A3) (f:A1→A2→A3→ℕ⁺) (Q:relation3 …):
     (∀n. (∀a1,a2,a3. f a1 a2 a3 < n → Q a1 a2 a3) → ∀a1,a2,a3. f a1 a2 a3 = n → Q a1 a2 a3) →
     ∀n,a1,a2,a3. f a1 a2 a3 = n → Q a1 a2 a3.
#A1 #A2 #A3 #f #Q #H #n @(pnat_ind_lt … n) -n /3 width=3 by/
qed-.

lemma wf3_ind_plt (A1) (A2) (A3) (f:A1→A2→A3→ℕ⁺) (Q:relation3 …):
      (∀n. (∀a1,a2,a3. f a1 a2 a3 < n → Q a1 a2 a3) → ∀a1,a2,a3. f a1 a2 a3 = n → Q a1 a2 a3) →
      ∀a1,a2,a3. Q a1 a2 a3.
#A1 #A2 #A3 #f #Q #H #a1 #a2 #a3 @(wf3_ind_plt_aux … H) -H //
qed-.
