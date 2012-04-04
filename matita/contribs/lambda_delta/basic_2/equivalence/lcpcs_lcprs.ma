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

include "basic_2/computation/lcprs.ma".
include "basic_2/equivalence/lcpcs.ma".

(* CONTEXT-SENSITIVE PARALLEL EQUIVALENCE ON LOCAL ENVIRONMENTS *************)

(* Properties about context sensitive computation on local environments *****)

lemma lcpcs_lcprs_dx: ∀L1,L2. L1 ⊢ ➡* L2 → L1 ⊢ ⬌* L2.
#L1 #L2 #H @(lcprs_ind … H) -L2 /width=1/ /3 width=3/
qed.

lemma lcpcs_lcprs_sn: ∀L1,L2. L2 ⊢ ➡* L1 → L1 ⊢ ⬌* L2.
#L1 #L2 #H @(lcprs_ind_dx … H) -L2 /width=1/ /3 width=3/
qed.

lemma lcpcs_lcprs_strap1: ∀L1,L. L1 ⊢ ⬌* L → ∀L2. L ⊢ ➡* L2 → L1 ⊢ ⬌* L2.
#L1 #L #HL1 #L2 #H @(lcprs_ind … H) -L2 /width=1/ /2 width=3/
qed.

lemma lcpcs_lcprs_strap2: ∀L1,L. L1 ⊢ ➡* L → ∀L2. L ⊢ ⬌* L2 → L1 ⊢ ⬌* L2.
#L1 #L #H #L2 #HL2 @(lcprs_ind_dx … H) -L1 /width=1/ /2 width=3/
qed.

lemma lcpcs_lcprs_div: ∀L1,L. L1 ⊢ ⬌* L → ∀L2. L2 ⊢ ➡* L → L1 ⊢ ⬌* L2.
#L1 #L #HL1 #L2 #H @(lcprs_ind_dx … H) -L2 /width=1/ /2 width=3/
qed.

lemma lcpcs_lcprs_conf: ∀L1,L. L ⊢ ➡* L1 → ∀L2. L ⊢ ⬌* L2 → L1 ⊢ ⬌* L2.
#L1 #L #H #L2 #HL2 @(lcprs_ind … H) -L1 /width=1/ /2 width=3/
qed.

lemma lcprs_div: ∀L1,L. L1 ⊢ ➡* L → ∀L2. L2 ⊢ ➡* L → L1 ⊢ ⬌* L2.
#L1 #L #HL1 #L2 #H @(lcprs_ind_dx … H) -L2 /2 width=1/ /2 width=3/
qed.
