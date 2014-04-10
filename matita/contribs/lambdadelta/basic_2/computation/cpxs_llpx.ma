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

include "basic_2/reduction/llpx_ldrop.ma".
include "basic_2/computation/cpxs_cpxs.ma".

(* CONTEXT-SENSITIVE EXTENDED PARALLEL COMPUTATION ON TERMS *****************)

(* Properties on lazy sn reduction on local environments ********************)

lemma cpxs_llpx_conf: ∀h,g,G. s_r_confluent1 … (cpxs h g G) (llpx h g G 0).
/3 width=5 by llpx_cpx_conf, s_r_conf1_LTC1/ qed-.

lemma llpx_cpx_trans: ∀h,g,G. s_r_transitive … (cpx h g G) (llpx h g G 0).
#h #g #G #L2 #T1 #T2 #HT12 elim HT12 -G -L2 -T1 -T2
[ /2 width=3 by/
| /3 width=2 by cpx_cpxs, cpx_sort/
| #I #G #L2 #K2 #V0 #V2 #W2 #i #HLK2 #_ #HVW2 #IHV02 #L1 #HL12
  elim (llpx_inv_lref_ge_dx … HL12 … HLK2) -L2
  /5 width=8 by cpxs_delta, cpxs_strap2, llpx_cpx_conf/
| #a #I #G #L2 #V1 #V2 #T1 #T2 #_ #_ #IHV12 #IHT12 #L1 #HL12
  elim (llpx_inv_bind_O … HL12) -HL12 /4 width=1 by cpxs_bind/
| #I #G #L2 #V1 #V2 #T1 #T2 #_ #_ #IHV12 #IHT12 #L1 #HL12
  elim (llpx_inv_flat … HL12) -HL12 /3 width=1 by cpxs_flat/
| #G #L2 #V2 #T1 #T #T2 #_ #HT2 #IHT1 #L1 #HL12
  elim (llpx_inv_bind_O … HL12) /3 width=3 by cpxs_zeta/
| #G #L2 #V2 #T1 #T2 #HT12 #IHT12 #L1 #HL12
  elim (llpx_inv_flat … HL12) /3 width=1 by cpxs_tau/
| #G #L2 #V1 #V2 #T2 #HV12 #IHV12 #L1 #HL12
  elim (llpx_inv_flat … HL12) /3 width=1 by cpxs_ti/
| #a #G #L2 #V1 #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #IHV12 #IHW12 #IHT12 #L1 #HL12
  elim (llpx_inv_flat … HL12) -HL12 #HV1 #HL12
  elim (llpx_inv_bind_O … HL12) /3 width=3 by cpxs_beta/
| #a #G #L2 #V1 #V #V2 #W1 #W2 #T1 #T2 #_ #HV2 #_ #_ #IHV1 #IHW12 #IHT12 #L1 #HL12
  elim (llpx_inv_flat … HL12) -HL12 #HV1 #HL12
  elim (llpx_inv_bind_O … HL12) /3 width=3 by cpxs_theta/
]
qed-.

lemma llpx_cpxs_trans: ∀h,g,G. s_rs_transitive … (cpx h g G) (llpx h g G 0).
#h #g #G @s_r_trans_LTC1 /2 width=3 by llpx_cpx_trans, llpx_cpx_conf/ (**) (* full auto fails here but works in cprs_cprs *)
qed-.
