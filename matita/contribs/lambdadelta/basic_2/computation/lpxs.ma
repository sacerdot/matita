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

include "basic_2/notation/relations/predsnstar_4.ma".
include "basic_2/reduction/lpx.ma".
include "basic_2/computation/lprs.ma".

(* SN EXTENDED PARALLEL COMPUTATION ON LOCAL ENVIRONMENTS *******************)

definition lpxs: ∀h. sd h → relation lenv ≝ λh,g. TC … (lpx h g).

interpretation "extended parallel computation (local environment, sn variant)"
   'PRedSnStar h g L1 L2 = (lpxs h g L1 L2).

(* Basic eliminators ********************************************************)

lemma lpxs_ind: ∀h,g,L1. ∀R:predicate lenv. R L1 →
                (∀L,L2. ⦃h, L1⦄ ⊢ ➡*[g] L → ⦃h, L⦄ ⊢ ➡[g] L2 → R L → R L2) →
                ∀L2. ⦃h, L1⦄ ⊢ ➡*[g] L2 → R L2.
#h #g #L1 #R #HL1 #IHL1 #L2 #HL12
@(TC_star_ind … HL1 IHL1 … HL12) //
qed-.

lemma lpxs_ind_dx: ∀h,g,L2. ∀R:predicate lenv. R L2 →
                   (∀L1,L. ⦃h, L1⦄ ⊢ ➡[g] L → ⦃h, L⦄ ⊢ ➡*[g] L2 → R L → R L1) →
                   ∀L1. ⦃h, L1⦄ ⊢ ➡*[g] L2 → R L1.
#h #g #L2 #R #HL2 #IHL2 #L1 #HL12
@(TC_star_ind_dx … HL2 IHL2 … HL12) //
qed-.

(* Basic properties *********************************************************)

lemma lprs_lpxs: ∀h,g,L1,L2. L1 ⊢ ➡* L2 → ⦃h, L1⦄ ⊢ ➡*[g] L2.
/3 width=3/ qed.

lemma lpx_lpxs: ∀h,g,L1,L2. ⦃h, L1⦄ ⊢ ➡[g] L2 → ⦃h, L1⦄ ⊢ ➡*[g] L2.
/2 width=1/ qed.

lemma lpxs_refl: ∀h,g,L. ⦃h, L⦄ ⊢ ➡*[g] L.
/2 width=1/ qed.

lemma lpxs_strap1: ∀h,g,L1,L,L2. ⦃h, L1⦄ ⊢ ➡*[g] L → ⦃h, L⦄ ⊢ ➡[g] L2 → ⦃h, L1⦄ ⊢ ➡*[g] L2.
/2 width=3/ qed.

lemma lpxs_strap2: ∀h,g,L1,L,L2. ⦃h, L1⦄ ⊢ ➡[g] L → ⦃h, L⦄ ⊢ ➡*[g] L2 → ⦃h, L1⦄ ⊢ ➡*[g] L2.
/2 width=3/ qed.

lemma lpxs_pair_refl: ∀h,g,L1,L2. ⦃h, L1⦄ ⊢ ➡*[g] L2 → ∀I,V. ⦃h, L1. ⓑ{I}V⦄ ⊢ ➡*[g] L2. ⓑ{I}V.
/2 width=1 by TC_lpx_sn_pair_refl/ qed.

(* Basic inversion lemmas ***************************************************)

lemma lpxs_inv_atom1: ∀h,g,L2. ⦃h, ⋆⦄ ⊢ ➡*[g] L2 → L2 = ⋆.
/2 width=2 by TC_lpx_sn_inv_atom1/ qed-.

lemma lpxs_inv_atom2: ∀h,g,L1. ⦃h, L1⦄ ⊢ ➡*[g] ⋆ → L1 = ⋆.
/2 width=2 by TC_lpx_sn_inv_atom2/ qed-.

(* Basic forward lemmas *****************************************************)

lemma lpxs_fwd_length: ∀h,g,L1,L2. ⦃h, L1⦄ ⊢ ➡*[g] L2 → |L1| = |L2|.
/2 width=2 by TC_lpx_sn_fwd_length/ qed-.
