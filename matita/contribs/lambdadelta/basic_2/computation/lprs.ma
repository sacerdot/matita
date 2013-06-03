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

include "basic_2/grammar/lpx_sn_tc.ma".
include "basic_2/reduction/lpr.ma".

(* SN PARALLEL COMPUTATION ON LOCAL ENVIRONMENTS ****************************)

definition lprs: relation lenv ≝ TC … lpr.

interpretation "parallel computation (local environment, sn variant)"
   'PRedSnStar L1 L2 = (lprs L1 L2).

(* Basic eliminators ********************************************************)

lemma lprs_ind: ∀L1. ∀R:predicate lenv. R L1 →
                (∀L,L2. L1 ⊢ ➡* L → L ⊢ ➡ L2 → R L → R L2) →
                ∀L2. L1 ⊢ ➡* L2 → R L2.
#L1 #R #HL1 #IHL1 #L2 #HL12
@(TC_star_ind … HL1 IHL1 … HL12) //
qed-.

lemma lprs_ind_dx: ∀L2. ∀R:predicate lenv. R L2 →
                   (∀L1,L. L1 ⊢ ➡ L → L ⊢ ➡* L2 → R L → R L1) →
                   ∀L1. L1 ⊢ ➡* L2 → R L1.
#L2 #R #HL2 #IHL2 #L1 #HL12
@(TC_star_ind_dx … HL2 IHL2 … HL12) //
qed-.

(* Basic properties *********************************************************)

lemma lpr_lprs: ∀L1,L2. L1 ⊢ ➡ L2 → L1 ⊢ ➡* L2.
/2 width=1/ qed.

lemma lprs_refl: ∀L. L ⊢ ➡* L.
/2 width=1/ qed.

lemma lprs_strap1: ∀L1,L,L2. L1 ⊢ ➡* L → L ⊢ ➡ L2 → L1 ⊢ ➡* L2.
/2 width=3/ qed.

lemma lprs_strap2: ∀L1,L,L2. L1 ⊢ ➡ L → L ⊢ ➡* L2 → L1 ⊢ ➡* L2.
/2 width=3/ qed.

lemma lprs_pair_refl: ∀L1,L2. L1 ⊢ ➡* L2 → ∀I,V. L1. ⓑ{I} V ⊢ ➡* L2. ⓑ{I} V.
/2 width=1 by TC_lpx_sn_pair_refl/ qed.

(* Basic inversion lemmas ***************************************************)

lemma lprs_inv_atom1: ∀L2. ⋆ ⊢ ➡* L2 → L2 = ⋆.
/2 width=2 by TC_lpx_sn_inv_atom1/ qed-.

lemma lprs_inv_atom2: ∀L1. L1 ⊢ ➡* ⋆ → L1 = ⋆.
/2 width=2 by TC_lpx_sn_inv_atom2/ qed-.

(* Basic forward lemmas *****************************************************)

lemma lprs_fwd_length: ∀L1,L2. L1 ⊢ ➡* L2 → |L1| = |L2|.
/2 width=2 by TC_lpx_sn_fwd_length/ qed-.