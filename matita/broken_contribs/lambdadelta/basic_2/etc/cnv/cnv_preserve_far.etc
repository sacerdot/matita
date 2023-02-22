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

include "basic_2/dynamic/cnv_cpm_trans.ma".

(* CONTEXT-SENSITIVE NATIVE VALIDITY FOR TERMS ******************************)

(* Far properties for preservation ******************************************)

fact cnv_cpms_trans_lpr_far (a) (h) (o):
                            ∀G0,L0,T0.
                            (∀G1,L1,T1. ⦃G0, L0, T0⦄ >[h, o] ⦃G1, L1, T1⦄ → IH_cnv_cpms_conf_lpr a h G1 L1 T1) →
                            (∀G1,L1,T1. ⦃G0, L0, T0⦄ >[h, o] ⦃G1, L1, T1⦄ → IH_cnv_cpm_trans_lpr a h G1 L1 T1) →
                            ∀G1,L1,T1. G0 = G1 → L0 = L1 → T0 = T1 → IH_cnv_cpms_trans_lpr a h G1 L1 T1.
#a #h #o #G0 #L0 #T0 #IH2 #IH1 #G1 #L1 #T1 #HG #HL #HT #H0 #n #T2 #H destruct
@(cpms_ind_dx … H) -n -T2
[ #L2 #HL12 @(cnv_cpm_trans_lpr_aux … IH2 IH1 … H0 … 0 T1 … HL12) -L2 -IH2 -IH1 -H0 //
| #n2 #n2 #T #T2 #HT1 #IH #HT2 #L2 #HL12 destruct
  @(cnv_cpm_trans_lpr_aux … o … HT2 … HL12) [1,2,3,6,7,8,9: /2 width=2 by/ ] -n2 -L2 -T2 -IH
  /3 width=4 by cpms_fpbg_trans/
]
qed-.
