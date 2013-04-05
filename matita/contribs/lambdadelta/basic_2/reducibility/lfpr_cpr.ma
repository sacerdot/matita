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

include "basic_2/unfold/ltpss_sn_ltpss_sn.ma".
include "basic_2/reducibility/ltpr_ldrop.ma".
include "basic_2/reducibility/cpr.ma".
include "basic_2/reducibility/lfpr.ma".

(* FOCALIZED PARALLEL REDUCTION FOR LOCAL ENVIRONMENTS **********************)

(* Advanced properties ******************************************************)

lemma lfpr_pair_cpr: ∀L1,L2. ⦃L1⦄ ➡ ⦃L2⦄ → ∀V1,V2. L2 ⊢ V1 ➡ V2 →
                     ∀I. ⦃L1. ⓑ{I} V1⦄ ➡ ⦃L2. ⓑ{I} V2⦄.
#L1 #L2 * #L #HL1 #HL2 #V1 #V2 *
<(ltpss_sn_fwd_length … HL2) #V #HV1 #HV2 #I
lapply (ltpss_sn_tpss_trans_eq … HV2 … HL2) -HV2 #V2
@(ex2_intro … (L.ⓑ{I}V)) /2 width=1/ (**) (* explicit constructor *)
qed.

(* Properties on supclosure *************************************************)
(*
lamma fsub_cpr_trans: ∀L1,L2,T1,T2. ⦃L1, T1⦄ ⊃ ⦃L2, T2⦄ → ∀U2. L2 ⊢ T2 ➡ U2 →
                      ∃∃L,U1. ⦃L1⦄ ➡ ⦃L⦄ & L ⊢ T1 ➡ U1 & ⦃L, U1⦄ ⊃ ⦃L2, U2⦄.
#L1 #L2 #T1 #T2 #HT12 #U2 * #T #H1 #H2
elim (fsub_tpr_trans … HT12 … H1) -T2 #L #U #HL1 #HT1U #HUT
elim (fsup_tpss_trans_full … HUT … H2) -T  -HUT -H2 #L #U #HL1 #HT1U #HUT






 #H elim H -L1 -L2 -T1 -T2 [1,2,3,4,5: /3 width=5/ ]
#L1 #K1 #K2 #T1 #T2 #U1 #d #e #HLK1 #HTU1 #_ #IHT12 #U2 #HTU2
elim (IHT12 … HTU2) -IHT12 -HTU2 #K #T #HK1 #HT1 #HK2
elim (lift_total T d e) #U #HTU
elim (ldrop_ltpr_trans … HLK1 … HK1) -HLK1 -HK1 #L #HL1 #HLK
lapply (tpr_lift … HT1 … HTU1 … HTU) -HT1 -HTU1 /3 width=11/
qed-.
*)