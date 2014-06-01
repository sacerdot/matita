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

include "basic_2/notation/relations/predsnstar_3.ma".
include "basic_2/substitution/lpx_sn_tc.ma".
include "basic_2/reduction/lpr.ma".

(* SN PARALLEL COMPUTATION ON LOCAL ENVIRONMENTS ****************************)

definition lprs: relation3 genv lenv lenv ≝
                 λG. TC … (lpr G).

interpretation "parallel computation (local environment, sn variant)"
   'PRedSnStar G L1 L2 = (lprs G L1 L2).

(* Basic eliminators ********************************************************)

lemma lprs_ind: ∀G,L1. ∀R:predicate lenv. R L1 →
                (∀L,L2. ⦃G, L1⦄ ⊢ ➡* L → ⦃G, L⦄ ⊢ ➡ L2 → R L → R L2) →
                ∀L2. ⦃G, L1⦄ ⊢ ➡* L2 → R L2.
#G #L1 #R #HL1 #IHL1 #L2 #HL12
@(TC_star_ind … HL1 IHL1 … HL12) //
qed-.

lemma lprs_ind_dx: ∀G,L2. ∀R:predicate lenv. R L2 →
                   (∀L1,L. ⦃G, L1⦄ ⊢ ➡ L → ⦃G, L⦄ ⊢ ➡* L2 → R L → R L1) →
                   ∀L1. ⦃G, L1⦄ ⊢ ➡* L2 → R L1.
#G #L2 #R #HL2 #IHL2 #L1 #HL12
@(TC_star_ind_dx … HL2 IHL2 … HL12) //
qed-.

(* Basic properties *********************************************************)

lemma lpr_lprs: ∀G,L1,L2. ⦃G, L1⦄ ⊢ ➡ L2 → ⦃G, L1⦄ ⊢ ➡* L2.
/2 width=1/ qed.

lemma lprs_refl: ∀G,L. ⦃G, L⦄ ⊢ ➡* L.
/2 width=1/ qed.

lemma lprs_strap1: ∀G,L1,L,L2. ⦃G, L1⦄ ⊢ ➡* L → ⦃G, L⦄ ⊢ ➡ L2 → ⦃G, L1⦄ ⊢ ➡* L2.
/2 width=3/ qed.

lemma lprs_strap2: ∀G,L1,L,L2. ⦃G, L1⦄ ⊢ ➡ L → ⦃G, L⦄ ⊢ ➡* L2 → ⦃G, L1⦄ ⊢ ➡* L2.
/2 width=3/ qed.

lemma lprs_pair_refl: ∀G,L1,L2. ⦃G, L1⦄ ⊢ ➡* L2 → ∀I,V. ⦃G, L1.ⓑ{I}V⦄ ⊢ ➡* L2.ⓑ{I}V.
/2 width=1 by TC_lpx_sn_pair_refl/ qed.

(* Basic inversion lemmas ***************************************************)

lemma lprs_inv_atom1: ∀G,L2. ⦃G, ⋆⦄ ⊢ ➡* L2 → L2 = ⋆.
/2 width=2 by TC_lpx_sn_inv_atom1/ qed-.

lemma lprs_inv_atom2: ∀G,L1. ⦃G, L1⦄ ⊢ ➡* ⋆ → L1 = ⋆.
/2 width=2 by TC_lpx_sn_inv_atom2/ qed-.

(* Basic forward lemmas *****************************************************)

lemma lprs_fwd_length: ∀G,L1,L2. ⦃G, L1⦄ ⊢ ➡* L2 → |L1| = |L2|.
/2 width=2 by TC_lpx_sn_fwd_length/ qed-.
