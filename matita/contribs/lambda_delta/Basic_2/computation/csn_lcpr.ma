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
include "Basic_2/computation/cprs_cprs.ma".
include "Basic_2/computation/csn_lift.ma".
include "Basic_2/computation/csn_cpr.ma".
include "Basic_2/computation/csn_cprs.ma".

(* CONTEXT-SENSITIVE STRONGLY NORMALIZING TERMS *****************************)

(* Advanced properties ******************************************************)

lemma csn_lcpr_conf: ∀L1,L2. L1 ⊢ ➡ L2 → ∀T. L1 ⊢ ⬇* T → L2 ⊢ ⬇* T.
#L1 #L2 #HL12 #T #H @(csn_ind_cprs … H) -T #T #_ #IHT
@csn_intro #T0 #HLT0 #HT0
@IHT /2 width=2/ -IHT -HT0 /2 width=3/
qed.

lemma csn_abbr: ∀L,V. L ⊢ ⬇* V → ∀T. L. ⓓV ⊢ ⬇* T → L ⊢ ⬇* ⓓV. T.
#L #V #HV elim HV -V #V #_ #IHV #T #HT @(csn_ind_cprs … HT) -T #T #HT #IHT
@csn_intro #X #H1 #H2
elim (cpr_inv_abbr1 … H1) -H1 *
[ #V0 #V1 #T1 #HLV0 #HLV01 #HLT1 #H destruct
  lapply (cpr_intro … HLV0 HLV01) -HLV01 #HLV1
  lapply (ltpr_cpr_trans (L. ⓓV) … HLT1) /2 width=1/ -V0 #HLT1
  elim (eq_false_inv_tpair … H2) -H2
  [ #HV1 @IHV // /2 width=1/ -HV1
    @(csn_lcpr_conf (L. ⓓV)) /2 width=1/ -HLV1 /2 width=3/
  | -IHV -HLV1 * #H destruct /3 width=1/
  ]
| -IHV -IHT -H2 #T0 #HT0 #HLT0
  lapply (csn_inv_lift … HT … HT0) -HT /2 width=3/
]
qed.

fact csn_appl_beta_aux: ∀L,W. L ⊢ ⬇* W → ∀U. L ⊢ ⬇* U →
                        ∀V,T. U = ⓓV. T → L ⊢ ⬇* ⓐV. ⓛW. T.
#L #W #H elim H -W #W #_ #IHW #X #H @(csn_ind_cprs … H) -X #X #HVT #IHVT #V #T #H destruct
lapply (csn_fwd_pair_sn … HVT) #HV
lapply (csn_fwd_bind_dx … HVT) #HT -HVT
@csn_intro #X #H #H2
elim (cpr_inv_appl1 … H) -H *
[ #V0 #Y #HLV0 #H #H0 destruct
  elim (cpr_inv_abst1 … H Abbr V) -H #W0 #T0 #HLW0 #HLT0 #H destruct
  elim (eq_false_inv_beta … H2) -H2
  [ -IHVT #HW0 @IHW -IHW [1,5: // |3: skip ] -HLW0 /2 width=1/ -HW0
    @csn_abbr /2 width=3/ -HV
    @(csn_lcpr_conf (L. ⓓV)) /2 width=1/ -V0 /2 width=3/
  | -IHW -HLW0 -HV -HT * #H #HVT0 destruct
    @(IHVT … HVT0) -IHVT -HVT0 // /2 width=1/
  ]
| -IHW -IHVT -H2 #V0 #W0 #T0 #T1 #HLV0 #HLT01 #H1 #H2 destruct
  lapply (lcpr_cpr_trans (L. ⓓV) … HLT01) -HLT01 /2 width=1/ #HLT01
  @csn_abbr /2 width=3/ -HV
  @(csn_lcpr_conf (L. ⓓV)) /2 width=1/ -V0 /2 width=3/
| -IHW -IHVT -HV -HT -H2 #V0 #V1 #W0 #W1 #T0 #T1 #_ #_ #_ #_ #H destruct
]
qed.

(* Basic_1: was: sn3_beta *)
lemma csn_appl_beta: ∀L,W. L ⊢ ⬇* W → ∀V,T. L ⊢ ⬇* (ⓓV. T) → (**)
                     L ⊢ ⬇* ⓐV. ⓛW. T.
/2 width=3/ qed.
