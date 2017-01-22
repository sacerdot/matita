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

include "basic_2/reducibility/lfpr.ma".
include "basic_2/reducibility/cfpr_cpr.ma".

(* FOCALIZED PARALLEL REDUCTION ON LOCAL ENVIRONMENTS ***********************)

(* Properties on context-free parallel reduction for closures ***************)

lemma fpr_lfpr: ∀L1,L2,T1,T2. ⦃L1, T1⦄ ➡ ⦃L2, T2⦄ → ⦃L1⦄ ➡ ⦃L2⦄.
#L1 #L2 #T1 #T2 #H
elim (fpr_inv_all … H) -H /2 width=3/
qed.

(* Inversion lemmas on context-free parallel reduction for closures *********)

lemma lfpr_inv_fpr: ∀L1,L2. ⦃L1⦄ ➡ ⦃L2⦄ → ∀T. ⦃L1, T⦄ ➡ ⦃L2, T⦄.
#L1 #L2 * /2 width=4/
qed-.
