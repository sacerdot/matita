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

include "basic_2/computation/cprs_aaa.ma".
include "basic_2/equivalence/cpcs_cpcs.ma".

(* CONTEXT-SENSITIVE PARALLEL EQUIVALENCE ON TERMS **************************)

(* Main properties about atomic arity assignment on terms *******************)

theorem aaa_cpcs_mono: ∀L,T1,T2. L ⊢ T1 ⬌* T2 →
                       ∀A1. L ⊢ T1 ⁝ A1 → ∀A2. L ⊢ T2 ⁝ A2 →
                       A1 = A2.
#L #T1 #T2 #HT12 #A1 #HA1 #A2 #HA2
elim (cpcs_inv_cprs … HT12) -HT12 #T #HT1 #HT2
lapply (aaa_cprs_conf … HA1 … HT1) -T1 #HA1
lapply (aaa_cprs_conf … HA2 … HT2) -T2 #HA2
lapply (aaa_mono … HA1 … HA2) -L -T //
qed-.