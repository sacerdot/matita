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
include "basic_2/reducibility/cpr.ma".
include "basic_2/reducibility/lfpr.ma".

(* FOCALIZED PARALLEL REDUCTION FOR LOCAL ENVIRONMENTS **********************)

(* Advanced properties ****************************************************)

lemma lfpr_pair_cpr: ∀L1,L2. ⦃L1⦄ ➡ ⦃L2⦄ → ∀V1,V2. L2 ⊢ V1 ➡ V2 →
                     ∀I. ⦃L1. ⓑ{I} V1⦄ ➡ ⦃L2. ⓑ{I} V2⦄.
#L1 #L2 * #L #HL1 #HL2 #V1 #V2 *
<(ltpss_sn_fwd_length … HL2) #V #HV1 #HV2 #I
lapply (ltpss_sn_tpss_trans_eq … HV2 … HL2) -HV2 #V2
@(ex2_1_intro … (L.ⓑ{I}V)) /2 width=1/ (**) (* explicit constructor *)
qed.
