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
                 λh,g,G. TC … (lpx h g G).

interpretation "extended parallel computation (local environment, sn variant)"
   'PRedSnStar h g G L1 L2 = (lpxs h g G L1 L2).

(* Basic eliminators ********************************************************)

lemma lpxs_ind: ∀h,g,G,L1. ∀R:predicate lenv. R L1 →
                (∀L,L2. ⦃G, L1⦄ ⊢ ➡*[h, g] L → ⦃G, L⦄ ⊢ ➡[h, g] L2 → R L → R L2) →
                ∀L2. ⦃G, L1⦄ ⊢ ➡*[h, g] L2 → R L2.
#h #g #G #L1 #R #HL1 #IHL1 #L2 #HL12
@(TC_star_ind … HL1 IHL1 … HL12) //
qed-.

lemma lpxs_ind_dx: ∀h,g,G,L2. ∀R:predicate lenv. R L2 →
                   (∀L1,L. ⦃G, L1⦄ ⊢ ➡[h, g] L → ⦃G, L⦄ ⊢ ➡*[h, g] L2 → R L → R L1) →
                   ∀L1. ⦃G, L1⦄ ⊢ ➡*[h, g] L2 → R L1.
#h #g #G #L2 #R #HL2 #IHL2 #L1 #HL12
@(TC_star_ind_dx … HL2 IHL2 … HL12) //
qed-.

(* Basic properties *********************************************************)

lemma lprs_lpxs: ∀h,g,G,L1,L2. ⦃G, L1⦄ ⊢ ➡* L2 → ⦃G, L1⦄ ⊢ ➡*[h, g] L2.
/3 width=3 by lpr_lpx, monotonic_TC/ qed.

lemma lpx_lpxs: ∀h,g,G,L1,L2. ⦃G, L1⦄ ⊢ ➡[h, g] L2 → ⦃G, L1⦄ ⊢ ➡*[h, g] L2.
/2 width=1 by inj/ qed.

lemma lpxs_refl: ∀h,g,G,L. ⦃G, L⦄ ⊢ ➡*[h, g] L.
/2 width=1 by lprs_lpxs/ qed.

lemma lpxs_strap1: ∀h,g,G,L1,L,L2. ⦃G, L1⦄ ⊢ ➡*[h, g] L → ⦃G, L⦄ ⊢ ➡[h, g] L2 → ⦃G, L1⦄ ⊢ ➡*[h, g] L2.
/2 width=3 by step/ qed.

lemma lpxs_strap2: ∀h,g,G,L1,L,L2. ⦃G, L1⦄ ⊢ ➡[h, g] L → ⦃G, L⦄ ⊢ ➡*[h, g] L2 → ⦃G, L1⦄ ⊢ ➡*[h, g] L2.
/2 width=3 by TC_strap/ qed.

lemma lpxs_pair_refl: ∀h,g,G,L1,L2. ⦃G, L1⦄ ⊢ ➡*[h, g] L2 → ∀I,V. ⦃G, L1.ⓑ{I}V⦄ ⊢ ➡*[h, g] L2.ⓑ{I}V.
/2 width=1 by TC_lpx_sn_pair_refl/ qed.

(* Basic inversion lemmas ***************************************************)

lemma lpxs_inv_atom1: ∀h,g,G,L2. ⦃G, ⋆⦄ ⊢ ➡*[h, g] L2 → L2 = ⋆.
/2 width=2 by TC_lpx_sn_inv_atom1/ qed-.

lemma lpxs_inv_atom2: ∀h,g,G,L1. ⦃G, L1⦄ ⊢ ➡*[h, g] ⋆ → L1 = ⋆.
/2 width=2 by TC_lpx_sn_inv_atom2/ qed-.

(* Basic forward lemmas *****************************************************)

lemma lpxs_fwd_length: ∀h,g,G,L1,L2. ⦃G, L1⦄ ⊢ ➡*[h, g] L2 → |L1| = |L2|.
/2 width=2 by TC_lpx_sn_fwd_length/ qed-.
