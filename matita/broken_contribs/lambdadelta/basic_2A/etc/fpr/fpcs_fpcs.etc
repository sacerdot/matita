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

include "basic_2/computation/fprs_fprs.ma".
include "basic_2/conversion/fpc_fpc.ma".
include "basic_2/equivalence/fpcs_fprs.ma".

(* CONTEXT-FREE PARALLEL EQUIVALENCE ON CLOSURES ****************************)

(* Advanced inversion lemmas ************************************************)

lemma fpcs_inv_fprs: ∀L1,L2,T1,T2. ⦃L1, T1⦄ ⬌* ⦃L2, T2⦄ →
                     ∃∃L,T. ⦃L1, T1⦄ ➡* ⦃L, T⦄ & ⦃L2, T2⦄ ➡* ⦃L, T⦄.
#L1 #L2 #T1 #T2 #H @(fpcs_ind … H) -L2 -T2
[ /3 width=4/
| #L #L2 #T #T2 #_ #HT2 * #L0 #T0 #HT10 elim HT2 -HT2 #HT2 #HT0
  [ elim (fprs_strip … HT2 … HT0) -L -T #L #T #HT2 #HT0
    lapply (fprs_strap1 … HT10 … HT0) -L0 -T0 /2 width=4/
  | lapply (fprs_strap2 … HT2 … HT0) -L -T /2 width=4/
  ]
]
qed-.

(* Advanced properties ******************************************************)

lemma fpr_fprs_conf: ∀L,L1,L2,T,T1,T2. ⦃L, T⦄ ➡* ⦃L1, T1⦄ → ⦃L, T⦄ ➡ ⦃L2, T2⦄ → ⦃L1, T1⦄ ⬌* ⦃L2, T2⦄.
#L #L1 #L2 #T #T1 #T2 #HT1 #HT2
elim (fprs_strip … HT2 … HT1) /2 width=4 by fpr_fprs_div/
qed-.

lemma fprs_fpr_conf: ∀L,L1,L2,T,T1,T2. ⦃L, T⦄ ➡* ⦃L1, T1⦄ → ⦃L, T⦄ ➡ ⦃L2, T2⦄ → ⦃L2, T2⦄ ⬌* ⦃L1, T1⦄.
#L #L1 #L2 #T #T1 #T2 #HT1 #HT2
elim (fprs_strip … HT2 … HT1) /2 width=4 by fprs_fpr_div/
qed-.

lemma fprs_conf: ∀L,L1,L2,T,T1,T2. ⦃L, T⦄ ➡* ⦃L1, T1⦄ → ⦃L, T⦄ ➡* ⦃L2, T2⦄ → ⦃L1, T1⦄ ⬌* ⦃L2, T2⦄.
#L #L1 #L2 #T #T1 #T2 #HT1 #HT2
elim (fprs_conf … HT1 … HT2) /2 width=4/
qed-.

lemma fpcs_strip: ∀L0,L1,T0,T1. ⦃L0, T0⦄ ⬌ ⦃L1, T1⦄ →
                  ∀L2,T2. ⦃L0, T0⦄ ⬌* ⦃L2, T2⦄ →
                  ∃∃L,T. ⦃L1, T1⦄ ⬌* ⦃L, T⦄ & ⦃L2, T2⦄ ⬌ ⦃L, T⦄.
/3 width=4/ qed.

(* Main properties **********************************************************)

theorem fpcs_trans: bi_transitive … fpcs.
/2 width=4/ qed.

theorem fpcs_canc_sn: ∀L,L1,L2,T,T1,T2. ⦃L, T⦄ ⬌* ⦃L1, T1⦄ → ⦃L, T⦄ ⬌* ⦃L2, T2⦄ → ⦃L1, T1⦄ ⬌* ⦃L2, T2⦄.
/3 width=4 by fpcs_trans, fpcs_sym/ qed. (**) (* /3 width=3/ is too slow *)

theorem fpcs_canc_dx: ∀L1,L2,L,T1,T2,T. ⦃L1, T1⦄ ⬌* ⦃L, T⦄ → ⦃L2, T2⦄ ⬌* ⦃L, T⦄ → ⦃L1, T1⦄ ⬌* ⦃L2, T2⦄.
/3 width=4 by fpcs_trans, fpcs_sym/ qed. (**) (* /3 width=3/ is too slow *)
