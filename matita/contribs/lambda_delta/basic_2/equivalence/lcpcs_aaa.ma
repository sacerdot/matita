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

include "basic_2/computation/lcprs_aaa.ma".
include "basic_2/equivalence/cpcs_cpcs.ma".
include "basic_2/equivalence/lcpcs_lcpcs.ma".

(* CONTEXT-SENSITIVE PARALLEL EQUIVALENCE ON LOCAL EBVIRONMENTS *************)

(* Main properties about atomic arity assignment on terms *******************)

theorem aaa_lcpcs_mono: ∀L1,L2. L1 ⊢ ⬌* L2 →
                        ∀T,A1. L1 ⊢ T ⁝ A1 → ∀A2. L2 ⊢ T ⁝ A2 →
                        A1 = A2.
#L1 #L2 #HL12 #T #A1 #HT1 #A2 #HT2
elim (lcpcs_inv_lcprs … HL12) -HL12 #L #HL1 #HL2
lapply (aaa_lcprs_conf … HT1 … HL1) -L1 #HT1
lapply (aaa_lcprs_conf … HT2 … HL2) -L2 #HT2
lapply (aaa_mono … HT1 … HT2) -L -T //
qed-.

theorem aaa_cpcs_mono: ∀L,T1,T2. L ⊢ T1 ⬌* T2 →
                       ∀A1. L ⊢ T1 ⁝ A1 → ∀A2. L ⊢ T2 ⁝ A2 →
                       A1 = A2.
#L #T1 #T2 #HT12 #A1 #HA1 #A2 #HA2
elim (cpcs_inv_cprs … HT12) -HT12 #T #HT1 #HT2
lapply (aaa_cprs_conf … HA1 … HT1) -T1 #HA1
lapply (aaa_cprs_conf … HA2 … HT2) -T2 #HA2
lapply (aaa_mono … HA1 … HA2) -L -T //
qed-.
