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

include "Basic_2/reducibility/cpr.ma".

(* CONTEXT-SENSITIVE NORMAL TERMS *******************************************)

definition cnf: lenv → predicate term ≝ λL. NF … (cpr L) (eq …).

interpretation
   "context-sensitive normality (term)"
   'Normal L T = (cnf L T). 

(* Basic properties *********************************************************)

(* Basic_1: was: nf2_sort *)
lemma cnf_sort: ∀L,k. L ⊢ 𝐍[⋆k].
#L #k #X #H
>(cpr_inv_sort1 … H) //
qed.

axiom cnf_dec: ∀L,T1. L ⊢ 𝐍[T1] ∨
               ∃∃T2. L ⊢ T1 ➡ T2 & (T1 = T2 → False).

(* Basic_1: removed theorems 1: nf2_abst_shift *)
