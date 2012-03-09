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

include "Basic_2/reducibility/lcpr.ma".

(* CONTEXT-SENSITIVE PARALLEL COMPUTATION ON LOCAL ENVIRONMENTS *************)

definition lcprs: relation lenv ≝ TC … lcpr.

interpretation
  "context-sensitive parallel computation (environment)"
  'CPRedStar L1 L2 = (lcprs L1 L2).

(* Basic eliminators ********************************************************)

lemma lcprs_ind: ∀L1. ∀R:predicate lenv. R L1 →
                 (∀L,L2. L1 ⊢ ➡* L → L ⊢ ➡ L2 → R L → R L2) →
                 ∀L2. L1 ⊢ ➡* L2 → R L2.
#L1 #R #HL1 #IHL1 #L2 #HL12 @(TC_star_ind … HL1 IHL1 … HL12) //
qed-.

(* Basic properties *********************************************************)

lemma lcprs_refl: ∀L. L ⊢ ➡* L.
/2 width=1/ qed.

lemma lcprs_strap1: ∀L1,L,L2.
                    L1 ⊢ ➡* L → L ⊢ ➡ L2 → L1 ⊢ ➡* L2.
/2 width=3/ qed.

lemma lcprs_strap2: ∀L1,L,L2.
                    L1 ⊢ ➡ L → L ⊢ ➡* L2 → L1 ⊢ ➡* L2.
/2 width=3/ qed.
