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

include "basic_2/reducibility/fpr.ma".

(* CONTEXT-FREE PARALLEL COMPUTATION ON CLOSURES ****************************)

definition fprs: bi_relation lenv term ≝ bi_TC … fpr.

interpretation "context-free parallel computation (closure)"
   'FocalizedPRedStar L1 T1 L2 T2 = (fprs L1 T1 L2 T2).

(* Basic properties *********************************************************)

lemma fprs_refl: bi_reflexive … fprs.
/2 width=1/ qed.

lemma fprs_strap1: ∀L1,L,L2,T1,T,T2. ⦃L1, T1⦄ ➡* ⦃L, T⦄ → ⦃L, T⦄ ➡ ⦃L2, T2⦄ →
                   ⦃L1, T1⦄ ➡* ⦃L2, T2⦄.
/2 width=4/ qed.

lemma fprs_strap2: ∀L1,L,L2,T1,T,T2. ⦃L1, T1⦄ ➡ ⦃L, T⦄ → ⦃L, T⦄ ➡* ⦃L2, T2⦄ →
                   ⦃L1, T1⦄ ➡* ⦃L2, T2⦄.
/2 width=4/ qed.
