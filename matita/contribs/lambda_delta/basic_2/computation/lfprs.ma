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

include "basic_2/reducibility/lfpr.ma".

(* FOCALIZED PARALLEL COMPUTATION ON LOCAL ENVIRONMENTS *********************)

definition lfprs: relation lenv ≝ TC … lfpr.

interpretation
  "focalized parallel computation (environment)"
  'FocalizedPRedStar L1 L2 = (lfprs L1 L2).

(* Basic eliminators ********************************************************)

lemma lfprs_ind: ∀L1. ∀R:predicate lenv. R L1 →
                 (∀L,L2. ⦃L1⦄ ➡* ⦃L⦄ → ⦃L⦄ ➡ ⦃L2⦄ → R L → R L2) →
                 ∀L2. ⦃L1⦄ ➡* ⦃L2⦄ → R L2.
#L1 #R #HL1 #IHL1 #L2 #HL12
@(TC_star_ind … HL1 IHL1 … HL12) //
qed-.

lemma lfprs_ind_dx: ∀L2. ∀R:predicate lenv. R L2 →
                    (∀L1,L. ⦃L1⦄ ➡ ⦃L⦄ → ⦃L⦄ ➡* ⦃L2⦄ → R L → R L1) →
                    ∀L1. ⦃L1⦄ ➡* ⦃L2⦄ → R L1.
#L2 #R #HL2 #IHL2 #L1 #HL12
@(TC_star_ind_dx … HL2 IHL2 … HL12) //
qed-.

(* Basic properties *********************************************************)

lemma lfprs_refl: ∀L. ⦃L⦄ ➡* ⦃L⦄.
/2 width=1/ qed.

lemma lfprs_strap1: ∀L1,L,L2. ⦃L1⦄ ➡* ⦃L⦄ → ⦃L⦄ ➡ ⦃L2⦄ → ⦃L1⦄ ➡* ⦃L2⦄.
/2 width=3/ qed.

lemma lfprs_strap2: ∀L1,L,L2. ⦃L1⦄ ➡ ⦃L⦄ → ⦃L⦄ ➡* ⦃L2⦄ → ⦃L1⦄ ➡* ⦃L2⦄.
/2 width=3/ qed.
