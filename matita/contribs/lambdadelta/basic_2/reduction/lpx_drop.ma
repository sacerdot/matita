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

include "basic_2/substitution/lpx_sn_drop.ma".
include "basic_2/reduction/cpx_lift.ma".
include "basic_2/reduction/lpx.ma".

(* SN EXTENDED PARALLEL REDUCTION FOR LOCAL ENVIRONMENTS ********************)

(* Properties on local environment slicing ***********************************)

lemma lpx_drop_conf: ∀h,g,G. dropable_sn (lpx h g G).
/3 width=6 by lpx_sn_deliftable_dropable, cpx_inv_lift1/ qed-.

lemma drop_lpx_trans: ∀h,g,G. dedropable_sn (lpx h g G).
/3 width=10 by lpx_sn_liftable_dedropable, cpx_lift/ qed-.

lemma lpx_drop_trans_O1: ∀h,g,G. dropable_dx (lpx h g G).
/2 width=3 by lpx_sn_dropable/ qed-.

(* Properties on supclosure *************************************************)

lemma fqu_lpx_trans: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐ ⦃G2, L2, T2⦄ →
                     ∀K2. ⦃G2, L2⦄ ⊢ ➡[h, g] K2 →
                     ∃∃K1,T. ⦃G1, L1⦄ ⊢ ➡[h, g] K1 & ⦃G1, L1⦄ ⊢ T1 ➡[h, g] T & ⦃G1, K1, T⦄ ⊐ ⦃G2, K2, T2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G1 -G2 -L1 -L2 -T1 -T2
/3 width=5 by fqu_lref_O, fqu_pair_sn, fqu_flat_dx, lpx_pair, ex3_2_intro/
[ #a #I #G2 #L2 #V2 #T2 #X #H elim (lpx_inv_pair1 … H) -H
  #K2 #W2 #HLK2 #HVW2 #H destruct
  /3 width=5 by fqu_fquq, cpx_pair_sn, fqu_bind_dx, ex3_2_intro/
| #G #L1 #K1 #T1 #U1 #e #HLK1 #HTU1 #K2 #HK12
  elim (drop_lpx_trans … HLK1 … HK12) -HK12
  /3 width=7 by fqu_drop, ex3_2_intro/
]
qed-.

lemma fquq_lpx_trans: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐⸮ ⦃G2, L2, T2⦄ →
                      ∀K2. ⦃G2, L2⦄ ⊢ ➡[h, g] K2 →
                      ∃∃K1,T. ⦃G1, L1⦄ ⊢ ➡[h, g] K1 & ⦃G1, L1⦄ ⊢ T1 ➡[h, g] T & ⦃G1, K1, T⦄ ⊐⸮ ⦃G2, K2, T2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H #K2 #HLK2 elim (fquq_inv_gen … H) -H
[ #HT12 elim (fqu_lpx_trans … HT12 … HLK2) /3 width=5 by fqu_fquq, ex3_2_intro/
| * #H1 #H2 #H3 destruct /2 width=5 by ex3_2_intro/
]
qed-.

lemma lpx_fqu_trans: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐ ⦃G2, L2, T2⦄ →
                     ∀K1. ⦃G1, K1⦄ ⊢ ➡[h, g] L1 →
                     ∃∃K2,T. ⦃G1, K1⦄ ⊢ T1 ➡[h, g] T & ⦃G1, K1, T⦄ ⊐ ⦃G2, K2, T2⦄ & ⦃G2, K2⦄ ⊢ ➡[h, g] L2.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G1 -G2 -L1 -L2 -T1 -T2
/3 width=7 by fqu_pair_sn, fqu_bind_dx, fqu_flat_dx, lpx_pair, ex3_2_intro/
[ #I #G1 #L1 #V1 #X #H elim (lpx_inv_pair2 … H) -H
  #K1 #W1 #HKL1 #HWV1 #H destruct elim (lift_total V1 0 1)
  /4 width=7 by cpx_delta, fqu_drop, drop_drop, ex3_2_intro/
| #G #L1 #K1 #T1 #U1 #e #HLK1 #HTU1 #L0 #HL01
  elim (lpx_drop_trans_O1 … HL01 … HLK1) -L1
  /3 width=5 by fqu_drop, ex3_2_intro/
]
qed-.

lemma lpx_fquq_trans: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐⸮ ⦃G2, L2, T2⦄ →
                      ∀K1. ⦃G1, K1⦄ ⊢ ➡[h, g] L1 →
                      ∃∃K2,T. ⦃G1, K1⦄ ⊢ T1 ➡[h, g] T & ⦃G1, K1, T⦄ ⊐⸮ ⦃G2, K2, T2⦄ & ⦃G2, K2⦄ ⊢ ➡[h, g] L2.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H #K1 #HKL1 elim (fquq_inv_gen … H) -H
[ #HT12 elim (lpx_fqu_trans … HT12 … HKL1) /3 width=5 by fqu_fquq, ex3_2_intro/
| * #H1 #H2 #H3 destruct /2 width=5 by ex3_2_intro/
]
qed-.
