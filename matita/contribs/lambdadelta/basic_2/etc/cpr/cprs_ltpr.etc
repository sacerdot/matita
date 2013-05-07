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

include "basic_2/reducibility/cpr_ltpr.ma".
include "basic_2/computation/cprs.ma".

(* CONTEXT-SENSITIVE PARALLEL COMPUTATION ON TERMS **************************)

(* Properties concerning parallel unfold on terms ***************************)

(* Basic_1: was only: pr3_subst1 *)
lemma cprs_tpss_ltpr: ∀L1,T1,U1,d,e. L1 ⊢ T1 ▶* [d, e] U1 →
                      ∀L2. L1 ➡ L2 → ∀T2. L2 ⊢ T1 ➡* T2 →
                      ∃∃U2. L2 ⊢ U1 ➡* U2 & L2 ⊢ T2 ▶* [d, e] U2.
#L1 #T1 #U1 #d #e #HTU1 #L2 #HL12 #T2 #HT12 elim HT12 -T2
[ #T2 #HT12
  elim (cpr_tpss_ltpr … HL12 … HT12 … HTU1) -L1 -T1 /3 width=3/
| #T #T2 #_ #HT2 * #U #HU1 #HTU
  elim (cpr_tpss_ltpr … HT2 … HTU) -L1 -T // /3 width=3/
]
qed.
