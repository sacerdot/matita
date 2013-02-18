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

include "basic_2/unfold/ltpss_sn_alt.ma".
include "basic_2/computation/dxprs_ltpss_dx.ma".

(* DECOMPOSED EXTENDED PARALLEL COMPUTATION ON TERMS ************************)

(* Properties about sn parallel unfold **************************************)

lemma dxprs_ltpss_sn_conf: ∀h,g,L1,L2,d,e. L1 ⊢ ▶* [d, e] L2 →
                           ∀T,U1. ⦃h, L1⦄ ⊢ T •*➡*[g] U1 →
                           ∃∃U2. ⦃h, L2⦄ ⊢ T •*➡*[g] U2 & L1 ⊢ U1 ▶* [d, e] U2.
#h #g #L1 #L2 #d #e #H
lapply (ltpss_sn_ltpssa … H) -H #H @(ltpssa_ind … H) -L2 [ /2 width=3/ ]
#L #L2 #HL1 #HL2 #IHL1 #T #U1 #HTU1
lapply (ltpssa_ltpss_sn … HL1) -HL1 #HL1
lapply (ltpss_sn_dx_trans_eq … HL1 … HL2) -HL1 #HL12
elim (IHL1 … HTU1) -IHL1 -HTU1 #U #HTU #HU1
elim (dxprs_ltpss_dx_conf … HTU … HL2) -HTU -HL2 #U2 #HTU2 #HU2
lapply (ltpss_sn_tpss_trans_eq … HU2 … HL12) -HU2 -HL12 #HU2
lapply (tpss_trans_eq … HU1 HU2) -U /2 width=3/
qed-.
