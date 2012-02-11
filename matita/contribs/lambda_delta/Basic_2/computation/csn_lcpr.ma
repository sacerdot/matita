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

include "Basic_2/reducibility/lcpr_cpr.ma".
include "Basic_2/computation/cprs_lcpr.ma".
include "Basic_2/computation/csn_cprs.ma".
include "Basic_2/computation/csn_lift.ma".

(* CONTEXT-SENSITIVE STRONGLY NORMALIZING TERMS *****************************)

(* Advanced properties ******************************************************)

lemma csn_lcpr_trans: ∀L1,L2. L1 ⊢ ➡ L2 → ∀T. L1 ⊢ ⬇* T → L2 ⊢ ⬇* T.
#L1 #L2 #HL12 #T #H @(csn_ind_cprs … H) -T #T #_ #IHT
@csn_intro #T0 #HLT0 #HT0
@IHT /2 width=2/ -IHT -HT0 /2 width=3/
qed.

lemma csn_abbr: ∀L,V. L ⊢ ⬇* V → ∀T. L. ⓓV ⊢ ⬇* T → L ⊢ ⬇* ⓓV. T.
#L #V #HV @(csn_ind … HV) -V #V #_ #IHV #T #HT @(csn_ind_cprs … HT) -T #T #HT #IHT
@csn_intro #X #H1 #H2
elim (cpr_inv_abbr1 … H1) -H1 *
[ #V0 #V1 #T1 #HLV0 #HLV01 #HLT1 #H destruct
  lapply (cpr_intro … HLV0 HLV01) -HLV01 #HLV1
  lapply (ltpr_cpr_trans (L. ⓓV) … HLT1) /2 width=1/ -V0 #HLT1
  elim (eq_false_inv_tpair … H2) -H2
  [ #HV1 @IHV // /2 width=1/ -HV1
    @(csn_lcpr_trans (L. ⓓV)) /2 width=1/ -HLV1 /2 width=3/
  | -IHV -HLV1 * #H destruct /3 width=1/
  ]
| -IHV -IHT -H2 #T0 #HT0 #HLT0
  lapply (csn_inv_lift … HT … HT0) -HT /2 width=3/
]
qed.
