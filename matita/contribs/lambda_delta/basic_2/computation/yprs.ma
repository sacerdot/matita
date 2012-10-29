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

include "basic_2/reducibility/ypr.ma".

(* HYPER PARALLEL COMPUTATION ON CLOSURES ***********************************)

definition yprs: ∀h. sd h → bi_relation lenv term ≝
                 λh,g. bi_TC … (ypr h g).

interpretation "hyper parallel computation (closure)"
   'YPRedStar h g L1 T1 L2 T2 = (yprs h g L1 T1 L2 T2).

(* Basic eliminators ********************************************************)

lemma yprs_ind: ∀h,g,L1,T1. ∀R:relation2 lenv term. R L1 T1 →
                (∀L,L2,T,T2. h ⊢ ⦃L1, T1⦄ •⥸*[g] ⦃L, T⦄ → h ⊢ ⦃L, T⦄ •⥸[g] ⦃L2, T2⦄ → R L T → R L2 T2) →
                ∀L2,T2. h ⊢ ⦃L1, T1⦄ •⥸*[g] ⦃L2, T2⦄ → R L2 T2.
/3 width=7 by bi_TC_star_ind/ qed-.

lemma yprs_ind_dx: ∀h,g,L2,T2. ∀R:relation2 lenv term. R L2 T2 →
                   (∀L1,L,T1,T. h ⊢ ⦃L1, T1⦄ •⥸[g] ⦃L, T⦄ → h ⊢ ⦃L, T⦄ •⥸*[g] ⦃L2, T2⦄ → R L T → R L1 T1) →
                   ∀L1,T1. h ⊢ ⦃L1, T1⦄ •⥸*[g] ⦃L2, T2⦄ → R L1 T1.
/3 width=7 by bi_TC_star_ind_dx/ qed-.

(* Basic properties *********************************************************)

lemma yprs_refl: ∀h,g. bi_reflexive … (yprs h g).
/2 width=1/ qed.

lemma yprs_strap1: ∀h,g,L1,L,L2,T1,T,T2. h ⊢ ⦃L1, T1⦄ •⥸*[g] ⦃L, T⦄ →
                   h ⊢ ⦃L, T⦄ •⥸[g] ⦃L2, T2⦄ → h ⊢ ⦃L1, T1⦄ •⥸*[g] ⦃L2, T2⦄.
/2 width=4/ qed.

lemma yprs_strap2: ∀h,g,L1,L,L2,T1,T,T2. h ⊢ ⦃L1, T1⦄ •⥸[g] ⦃L, T⦄ →
                   h ⊢ ⦃L, T⦄ •⥸*[g] ⦃L2, T2⦄ → h ⊢ ⦃L1, T1⦄ •⥸*[g] ⦃L2, T2⦄.
/2 width=4/ qed.
