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

include "basic_2A/multiple/lleq_fqus.ma".
include "basic_2A/multiple/lleq_lleq.ma".
include "basic_2A/reduction/lpx_lleq.ma".
include "basic_2A/reduction/fpb.ma".

(* "RST" PROPER PARALLEL COMPUTATION FOR CLOSURES ***************************)

(* Properties on lazy equivalence for local environments ********************)

lemma lleq_fpb_trans: ∀h,g,F,K1,K2,T. K1 ≡[T, 0] K2 →
                      ∀G,L2,U. ⦃F, K2, T⦄ ≻[h, g] ⦃G, L2, U⦄ →
                      ∃∃L1. ⦃F, K1, T⦄ ≻[h, g] ⦃G, L1, U⦄ & L1 ≡[U, 0] L2.
#h #g #F #K1 #K2 #T #HT #G #L2 #U * -G -L2 -U
[ #G #L2 #U #H2 elim (lleq_fqu_trans … H2 … HT) -K2
  /3 width=3 by fpb_fqu, ex2_intro/
| /4 width=10 by fpb_cpx, cpx_lleq_conf_sn, lleq_cpx_trans, ex2_intro/
| #L2 #HKL2 #HnKL2 elim (lleq_lpx_trans … HKL2 … HT) -HKL2
  /6 width=3 by fpb_lpx, lleq_canc_sn, ex2_intro/ (* 2 lleq_canc_sn *)
]
qed-.
