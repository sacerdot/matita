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

include "basic_2/multiple/lleq_fqus.ma".
include "basic_2/multiple/lleq_lleq.ma".
include "basic_2/computation/cpxs_lleq.ma".
include "basic_2/computation/lpxs_lleq.ma".
include "basic_2/computation/fpbu.ma".

(* UNITARY "BIG TREE" PROPER PARALLEL COMPUTATION FOR CLOSURES **************)

(* Properties on lazy equivalence for local environments ********************)

lemma lleq_fpbu_trans: ∀h,g,F,K1,K2,T. K1 ≡[T, 0] K2 →
                       ∀G,L2,U. ⦃F, K2, T⦄ ≻[h, g] ⦃G, L2, U⦄ →
                       ∃∃L1. ⦃F, K1, T⦄ ≻[h, g] ⦃G, L1, U⦄ & L1 ≡[U, 0] L2.
#h #g #F #K1 #K2 #T #HT #G #L2 #U * -G -L2 -U
[ #G #L2 #U #H2 elim (lleq_fqup_trans … H2 … HT) -K2
  /3 width=3 by fpbu_fqup, ex2_intro/
| /4 width=10 by fpbu_cpxs, cpxs_lleq_conf_sn, lleq_cpxs_trans, ex2_intro/
| #L2 #HKL2 #HnKL2 elim (lleq_lpxs_trans … HKL2 … HT) -HKL2
  /6 width=3 by fpbu_lpxs, lleq_canc_sn, ex2_intro/ (* 2 lleq_canc_sn *)
]
qed-.
