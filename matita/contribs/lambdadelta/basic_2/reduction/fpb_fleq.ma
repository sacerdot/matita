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

include "basic_2/multiple/fleq.ma".
include "basic_2/reduction/fpb_lleq.ma".

(* "RST" PROPER PARALLEL COMPUTATION FOR CLOSURES ***************************)

(* Properties on lazy equivalence for closures ******************************)

lemma fleq_fpb_trans: ∀h,g,F1,F2,K1,K2,T1,T2. ⦃F1, K1, T1⦄ ≡[0] ⦃F2, K2, T2⦄ →
                      ∀G2,L2,U2. ⦃F2, K2, T2⦄ ≻[h, g] ⦃G2, L2, U2⦄ →
                      ∃∃G1,L1,U1. ⦃F1, K1, T1⦄ ≻[h, g] ⦃G1, L1, U1⦄ & ⦃G1, L1, U1⦄ ≡[0] ⦃G2, L2, U2⦄.
#h #g #F1 #F2 #K1 #K2 #T1 #T2 * -F2 -K2 -T2
#K2 #HK12 #G2 #L2 #U2 #H12 elim (lleq_fpb_trans … HK12 … H12) -K2
/3 width=5 by fleq_intro, ex2_3_intro/
qed-.

(* Inversion lemmas on lazy equivalence for closures ************************)

lemma fpb_inv_fleq: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ≻[h, g] ⦃G2, L2, T2⦄ →
                    ⦃G1, L1, T1⦄ ≡[0] ⦃G2, L2, T2⦄ → ⊥.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 * -G2 -L2 -T2
[ #G2 #L2 #T2 #H12 #H elim (fleq_inv_gen … H) -H
  /3 width=8 by lleq_fwd_length, fqu_inv_eq/
| #T2 #_ #HnT #H elim (fleq_inv_gen … H) -H /2 width=1 by/
| #L2 #_ #HnL #H elim (fleq_inv_gen … H) -H /2 width=1 by/
]
qed-.

