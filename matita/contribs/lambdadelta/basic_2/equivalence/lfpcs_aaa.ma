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

include "basic_2/computation/lfprs_aaa.ma".
include "basic_2/equivalence/lfpcs_lfpcs.ma".

(* FOCALIZED PARALLEL EQUIVALENCE ON LOCAL ENVIRONMENTS *********************)

(* Main properties about atomic arity assignment on terms *******************)

theorem aaa_lfpcs_mono: ∀L1,L2. ⦃L1⦄ ⬌* ⦃L2⦄ →
                        ∀T,A1. L1 ⊢ T ⁝ A1 → ∀A2. L2 ⊢ T ⁝ A2 →
                        A1 = A2.
#L1 #L2 #HL12 #T #A1 #HT1 #A2 #HT2
elim (lfpcs_inv_lfprs … HL12) -HL12 #L #HL1 #HL2
lapply (aaa_lfprs_conf … HT1 … HL1) -L1 #HT1
lapply (aaa_lfprs_conf … HT2 … HL2) -L2 #HT2
lapply (aaa_mono … HT1 … HT2) -L -T //
qed-.
