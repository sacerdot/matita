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

include "basic_2/computation/cprs_cprs.ma".
include "basic_2/computation/lcprs_lcprs.ma".

(* CONTEXT-SENSITIVE PARALLEL COMPUTATION ON TERMS **************************)

(* Properties exploiting context-senstive computation on local environments *)

(* Basic_1: was just: pr3_pr3_pr3_t *)
lemma lcprs_cprs_trans: ∀L1,L2. L1 ⊢ ➡* L2 →
                        ∀T1,T2. L2 ⊢ T1 ➡* T2 → L1 ⊢ T1 ➡* T2.
#L1 #L2 #HL12 @(lcprs_ind … HL12) -L2 // /3 width=3/
qed.

lemma lcprs_cpr_trans: ∀L1,L2. L1 ⊢ ➡* L2 →
                       ∀T1,T2. L2 ⊢ T1 ➡ T2 → L1 ⊢ T1 ➡* T2.
/3 width=3 by lcprs_cprs_trans, inj/ qed.

(* Advanced inversion lemmas ************************************************)

(* Basic_1: was pr3_gen_abbr *)
lemma cprs_inv_abbr1: ∀a,L,V1,T1,U2. L ⊢ ⓓ{a}V1. T1 ➡* U2 →
                      (∃∃V2,T2. L ⊢ V1 ➡* V2 & L. ⓓV1 ⊢ T1 ➡* T2 &
                                U2 = ⓓ{a}V2. T2
                      ) ∨
                      ∃∃T2. L. ⓓV1 ⊢ T1 ➡* T2 & ⇧[0, 1] U2 ≡ T2 & a = true.
#a #L #V1 #T1 #U2 #H @(cprs_ind … H) -U2 /3 width=5/
#U0 #U2 #_ #HU02 * *
[ #V0 #T0 #HV10 #HT10 #H destruct
  elim (cpr_inv_abbr1 … HU02) -HU02 *
  [ #V #V2 #T2 #HV0 #HV2 #HT02 #H destruct
    lapply (cpr_intro … HV0 … HV2) -HV2 #HV02
    lapply (ltpr_cpr_trans (L.ⓓV0) … HT02) /2 width=1/ -V #HT02
    lapply (lcprs_cprs_trans (L. ⓓV1) … HT02) -HT02 /2 width=1/ /4 width=5/
  | #T2 #HT02 #HUT2
    lapply (lcprs_cpr_trans (L.ⓓV1) … HT02) -HT02 /2 width=1/ -V0 #HT02
    lapply (cprs_trans … HT10 … HT02) -T0 /3 width=3/
  ]
| #U1 #HTU1 #HU01
  elim (lift_total U2 0 1) #U #HU2
  lapply (cpr_lift (L.ⓓV1) … HU01 … HU2 HU02) -U0 /2 width=1/ /4 width=3/
]
qed-.
