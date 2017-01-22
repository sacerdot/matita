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

include "basic_2/computation/lfprs.ma".
include "basic_2/equivalence/lfpcs.ma".

(* FOCALIZED PARALLEL EQUIVALENCE ON LOCAL ENVIRONMENTS *********************)

(* Properties on focalized computation for local environments ***************)

lemma lfpcs_lfprs_dx: ∀L1,L2. ⦃L1⦄ ➡* ⦃L2⦄ → ⦃L1⦄ ⬌* ⦃L2⦄.
#L1 #L2 #H @(lfprs_ind … H) -L2 /width=1/ /3 width=3/
qed.

lemma lfpcs_lfprs_sn: ∀L1,L2. ⦃L2⦄ ➡* ⦃L1⦄ → ⦃L1⦄ ⬌* ⦃L2⦄.
#L1 #L2 #H @(lfprs_ind_dx … H) -L2 /width=1/ /3 width=3/
qed.

lemma lfpcs_lfprs_strap1: ∀L1,L. ⦃L1⦄ ⬌* ⦃L⦄ → ∀L2. ⦃L⦄ ➡* ⦃L2⦄ → ⦃L1⦄ ⬌* ⦃L2⦄.
#L1 #L #HL1 #L2 #H @(lfprs_ind … H) -L2 /width=1/ /2 width=3/
qed.

lemma lfpcs_lfprs_strap2: ∀L1,L. ⦃L1⦄ ➡* ⦃L⦄ → ∀L2. ⦃L⦄ ⬌* ⦃L2⦄ → ⦃L1⦄ ⬌* ⦃L2⦄.
#L1 #L #H #L2 #HL2 @(lfprs_ind_dx … H) -L1 /width=1/ /2 width=3/
qed.

lemma lfpcs_lfprs_div: ∀L1,L. ⦃L1⦄ ⬌* ⦃L⦄ → ∀L2. ⦃L2⦄ ➡* ⦃L⦄ → ⦃L1⦄ ⬌* ⦃L2⦄.
#L1 #L #HL1 #L2 #H @(lfprs_ind_dx … H) -L2 /width=1/ /2 width=3/
qed.

lemma lfpcs_lfprs_conf: ∀L1,L. ⦃L⦄ ➡* ⦃L1⦄ → ∀L2. ⦃L⦄ ⬌* ⦃L2⦄ → ⦃L1⦄ ⬌* ⦃L2⦄.
#L1 #L #H #L2 #HL2 @(lfprs_ind … H) -L1 /width=1/ /2 width=3/
qed.

lemma lfprs_div: ∀L1,L. ⦃L1⦄ ➡* ⦃L⦄ → ∀L2. ⦃L2⦄ ➡* ⦃L⦄ → ⦃L1⦄ ⬌* ⦃L2⦄.
#L1 #L #HL1 #L2 #H @(lfprs_ind_dx … H) -L2 /2 width=1/ /2 width=3/
qed.
