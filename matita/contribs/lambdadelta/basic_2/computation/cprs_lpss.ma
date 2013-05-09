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

include "basic_2/substitution/lpss_cpss.ma".
include "basic_2/reduction/lpr_lpss.ma".
include "basic_2/computation/cprs.ma".

(* CONTEXT-SENSITIVE PARALLEL COMPUTATION ON TERMS **************************)

(* Properties on parallel substitution for terms ****************************)

(* Basic_1: was: pr3_subst1 *)
lemma cprs_cpss_conf: ∀L,T0,T1. L ⊢ T0 ➡* T1 → ∀T2. L ⊢ T0 ▶* T2 →
                      ∃∃T. L ⊢ T1 ▶* T & L ⊢ T2 ➡* T.
#L @TC_strip1 /2 width=3 by cpr_cpss_conf/ qed-. (**) (* auto /3 width=3/ fails because a δ-expansion gets in the way *)

(* Properties on sn parallel substitution for local environments ************)

lemma cprs_lpss_conf_dx: ∀L0,T0,T1. L0 ⊢ T0 ➡* T1 → ∀L1. L0 ⊢ ▶* L1 →
                         ∃∃T. L1 ⊢ T1 ▶* T & L1 ⊢ T0 ➡* T.
#L0 #T0 #T1 #H elim H -T1
[ #T1 #HT01 #L1 #HL01
  elim (cpr_lpss_conf_dx … HT01 … HL01) -L0 /3 width=3/
| #T #T1 #_ #HT1 #IHT0 #L1 #HL01
  elim (IHT0 … HL01) #T2 #HT2 #HT02
  elim (cpr_lpss_conf_dx … HT1 … HL01) -L0 #T3 #HT13 #HT3
  elim (cpr_cpss_conf … HT3 … HT2) -T #T #HT3 #HT2
  lapply (cpss_trans … HT13 … HT3) -T3
  lapply (cprs_strap1 … HT02 … HT2) -T2 /2 width=3/
]
qed-.

lemma cprs_lpss_conf_sn: ∀L0,T0,T1. L0 ⊢ T0 ➡* T1 → ∀L1. L0 ⊢ ▶* L1 →
                         ∃∃T. L0 ⊢ T1 ▶* T & L1 ⊢ T0 ➡* T.
#L0 #T0 #T1 #HT01 #L1 #HL01
elim (cprs_lpss_conf_dx … HT01 … HL01) -HT01 #T #HT1
lapply (lpss_cpss_trans … HL01 … HT1) -HT1 /2 width=3/
qed-.
