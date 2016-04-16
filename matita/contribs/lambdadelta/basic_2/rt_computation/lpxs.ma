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

include "basic_2/notation/relations/predsnstar_5.ma".
include "basic_2/reduction/lpx.ma".
include "basic_2/computation/lprs.ma".

(* SN EXTENDED PARALLEL COMPUTATION ON LOCAL ENVIRONMENTS *******************)

definition lpxs: ∀h. sd h → relation3 genv lenv lenv ≝
                 λh,o,G. TC … (lpx h o G).

interpretation "extended parallel computation (local environment, sn variant)"
   'PRedSnStar h o G L1 L2 = (lpxs h o G L1 L2).

(* Basic eliminators ********************************************************)

lemma lpxs_ind: ∀h,o,G,L1. ∀R:predicate lenv. R L1 →
                (∀L,L2. ⦃G, L1⦄ ⊢ ➡*[h, o] L → ⦃G, L⦄ ⊢ ➡[h, o] L2 → R L → R L2) →
                ∀L2. ⦃G, L1⦄ ⊢ ➡*[h, o] L2 → R L2.
#h #o #G #L1 #R #HL1 #IHL1 #L2 #HL12
@(TC_star_ind … HL1 IHL1 … HL12) //
qed-.

lemma lpxs_ind_dx: ∀h,o,G,L2. ∀R:predicate lenv. R L2 →
                   (∀L1,L. ⦃G, L1⦄ ⊢ ➡[h, o] L → ⦃G, L⦄ ⊢ ➡*[h, o] L2 → R L → R L1) →
                   ∀L1. ⦃G, L1⦄ ⊢ ➡*[h, o] L2 → R L1.
#h #o #G #L2 #R #HL2 #IHL2 #L1 #HL12
@(TC_star_ind_dx … HL2 IHL2 … HL12) //
qed-.

(* Basic properties *********************************************************)

lemma lprs_lpxs: ∀h,o,G,L1,L2. ⦃G, L1⦄ ⊢ ➡* L2 → ⦃G, L1⦄ ⊢ ➡*[h, o] L2.
/3 width=3 by lpr_lpx, monotonic_TC/ qed.

lemma lpx_lpxs: ∀h,o,G,L1,L2. ⦃G, L1⦄ ⊢ ➡[h, o] L2 → ⦃G, L1⦄ ⊢ ➡*[h, o] L2.
/2 width=1 by inj/ qed.

lemma lpxs_refl: ∀h,o,G,L. ⦃G, L⦄ ⊢ ➡*[h, o] L.
/2 width=1 by lprs_lpxs/ qed.

lemma lpxs_strap1: ∀h,o,G,L1,L,L2. ⦃G, L1⦄ ⊢ ➡*[h, o] L → ⦃G, L⦄ ⊢ ➡[h, o] L2 → ⦃G, L1⦄ ⊢ ➡*[h, o] L2.
/2 width=3 by step/ qed.

lemma lpxs_strap2: ∀h,o,G,L1,L,L2. ⦃G, L1⦄ ⊢ ➡[h, o] L → ⦃G, L⦄ ⊢ ➡*[h, o] L2 → ⦃G, L1⦄ ⊢ ➡*[h, o] L2.
/2 width=3 by TC_strap/ qed.

lemma lpxs_pair_refl: ∀h,o,G,L1,L2. ⦃G, L1⦄ ⊢ ➡*[h, o] L2 → ∀I,V. ⦃G, L1.ⓑ{I}V⦄ ⊢ ➡*[h, o] L2.ⓑ{I}V.
/2 width=1 by TC_lpx_sn_pair_refl/ qed.

(* Basic inversion lemmas ***************************************************)

lemma lpxs_inv_atom1: ∀h,o,G,L2. ⦃G, ⋆⦄ ⊢ ➡*[h, o] L2 → L2 = ⋆.
/2 width=2 by TC_lpx_sn_inv_atom1/ qed-.

lemma lpxs_inv_atom2: ∀h,o,G,L1. ⦃G, L1⦄ ⊢ ➡*[h, o] ⋆ → L1 = ⋆.
/2 width=2 by TC_lpx_sn_inv_atom2/ qed-.

(* Basic forward lemmas *****************************************************)

lemma lpxs_fwd_length: ∀h,o,G,L1,L2. ⦃G, L1⦄ ⊢ ➡*[h, o] L2 → |L1| = |L2|.
/2 width=2 by TC_lpx_sn_fwd_length/ qed-.
