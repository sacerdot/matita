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

include "basic_2/reducibility/cpr_tpss.ma".
include "basic_2/reducibility/cpr_cpr.ma".
include "basic_2/reducibility/cfpr_ltpss.ma".

(* CONTEXT-SENSITIVE PARALLEL REDUCTION ON CLOSURES *************************)

(* Advanced properties ******************************************************)

lemma fpr_all: ∀L1,L. L1 ➡ L → ∀L2,T1,T2. L ⊢ T1 ➡ T2 →
               L ⊢ ▶* [0, |L|] L2 → ⦃L1, T1⦄ ➡ ⦃L2, T2⦄.
#L1 #L #H elim H -L1 -L
[ #L2 #T1 #T2 #HT12 #HL2
  lapply (ltpss_sn_inv_atom1 … HL2) -HL2 #H destruct
  lapply (cpr_inv_atom … HT12) -HT12 /2 width=1/
| #I #L1 #L #V1 #V #_ #HV1 #IH #X #T1 #T2 #HT12 #H
  elim (ltpss_sn_inv_tpss21 … H ?) -H // <minus_plus_m_m #L2 #V2 #HL2 #HV2 #H destruct
  lapply (cpr_bind_dx false … HV1 HT12) -HV1 -HT12 #HT12
  lapply (cpr_tpss_trans … HT12 (-ⓑ{I}V2.T2) 0 (|L|) ?) -HT12 /2 width=1/ -HV2 /3 width=1/
]
qed.

(* Advanced inversion lemmas ************************************************)

lemma cfpr_inv_all: ∀L1,L2,L0,T1,T2. L0 ⊢ ⦃L1, T1⦄ ➡ ⦃L2, T2⦄ →
                    ∃∃L. L0 @@ L1 ➡ L0 @@ L & L0 @@ L ⊢ T1 ➡ T2 &
                         L0 @@ L ⊢ ▶* [0, |L0| + |L|] L0 @@ L2.
#L1 @(lenv_ind_dx … L1) -L1
[ #L2 #L0 #T1 #T2 #H
  elim (cfpr_inv_atom1 … H) -H #HT12 #H destruct /3 width=4/
| #I #L1 #V1 #IH #X #L0 #T1 #T2 #H
  elim (cfpr_inv_pair1 … H) -H #L2 #V #V2 #HV1 #HV2 #HT12 #H destruct
  elim (IH … HT12) -IH -HT12 #L #HL1 #HT12 #HL2
  elim (ltpr_inv_append1 … HL1) -HL1 #X #Y #HX #HY #H
  lapply (ltpr_fwd_length … HX) -HX #HX
  elim (append_inj_dx … H ?) -H // -HX #_ #H destruct -X
  lapply (ltpss_sn_fwd_length … HL2) >append_length >append_length #H
  lapply (injective_plus_r … H) -H #H
  @(ex3_intro … (⋆.ⓑ{I}V@@Y)) <append_assoc // -HT12
  <append_assoc [ /3 width=1/ ] -HV1 -HY
  >append_length <associative_plus
  @(ltpss_sn_dx_trans_eq … HL2) -HL2 >H -H >commutative_plus /3 width=1/
]
qed-.

lemma fpr_inv_all: ∀L1,L2,T1,T2. ⦃L1, T1⦄ ➡ ⦃L2, T2⦄ →
                   ∃∃L. L1 ➡ L & L ⊢ T1 ➡ T2 & L ⊢ ▶* [0, |L|] L2.
#L1 #L2 #T1 #T2 #H
lapply (fpr_cfpr … H) -H #H
elim (cfpr_inv_all … H) -H /2 width=4/
qed-.
