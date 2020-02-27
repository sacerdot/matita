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

include "basic_2/computation/lfprs_lfprs.ma".
include "basic_2/conversion/lfpc_lfpc.ma".
include "basic_2/equivalence/lfpcs_lfprs.ma".

(* FOCALIZED PARALLEL EQUIVALENCE ON LOCAL ENVIRONMENTS *********************)

(* Advanced inversion lemmas ************************************************)

lemma lfpcs_inv_lfprs: ∀L1,L2. ⦃L1⦄ ⬌* ⦃L2⦄ →
                       ∃∃L. ⦃L1⦄ ➡* ⦃L⦄ & ⦃L2⦄ ➡* ⦃L⦄.
#L1 #L2 #H @(lfpcs_ind … H) -L2
[ /3 width=3/
| #L #L2 #_ #HL2 * #L0 #HL10 elim HL2 -HL2 #HL2 #HL0
  [ elim (lfprs_strip … HL0 … HL2) -L #L #HL0 #HL2
    lapply (lfprs_strap1 … HL10 … HL0) -L0 /2 width=3/
  | lapply (lfprs_strap2 … HL2 … HL0) -L /2 width=3/
  ]
]
qed-.

(* Advanced properties ******************************************************)

lemma lfpcs_strip: ∀L,L1. ⦃L⦄ ⬌* ⦃L1⦄ → ∀L2. ⦃L⦄ ⬌ ⦃L2⦄ →
                   ∃∃L0. ⦃L1⦄ ⬌ ⦃L0⦄ & ⦃L2⦄ ⬌* ⦃L0⦄.
/3 width=3/ qed.

(* Main properties **********************************************************)

theorem lfpcs_trans: ∀L1,L. ⦃L1⦄ ⬌* ⦃L⦄ → ∀L2. ⦃L⦄ ⬌* ⦃L2⦄ → ⦃L1⦄ ⬌* ⦃L2⦄.
/2 width=3/ qed.

theorem lfpcs_canc_sn: ∀L,L1,L2. ⦃L⦄ ⬌* ⦃L1⦄ → ⦃L⦄ ⬌* ⦃L2⦄ → ⦃L1⦄ ⬌* ⦃L2⦄.
/3 width=3 by lfpcs_trans, lfpcs_sym/ qed.

theorem lfpcs_canc_dx: ∀L,L1,L2. ⦃L1⦄ ⬌* ⦃L⦄ → ⦃L2⦄ ⬌* ⦃L⦄ → ⦃L1⦄ ⬌* ⦃L2⦄.
/3 width=3 by lfpcs_trans, lfpcs_sym/ qed.
