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

include "basic_2/substitution/drop_leq.ma".
include "basic_2/reduction/cpx.ma".

(* CONTEXT-SENSITIVE EXTENDED PARALLEL REDUCTION FOR TERMS ******************)

(* Properties on equivalence for local environments *************************)

lemma leq_cpx_trans: ∀h,g,G. lsub_trans … (cpx h g G) (leq 0 (∞)).
#h #g #G #L1 #T1 #T2 #H elim H -G -L1 -T1 -T2
[ //
| /2 width=2 by cpx_st/
| #I #G #L1 #K1 #V1 #V2 #W2 #i #HLK1 #_ #HVW2 #IHV12 #L2 #HL12
  elim (leq_drop_trans_be … HL12 … HLK1) // -HL12 -HLK1 /3 width=7 by cpx_delta/
|4,9: /4 width=1 by cpx_bind, cpx_beta, leq_pair_O_Y/
|5,7,8: /3 width=1 by cpx_flat, cpx_eps, cpx_ct/
|6,10: /4 width=3 by cpx_zeta, cpx_theta, leq_pair_O_Y/
]
qed-.
