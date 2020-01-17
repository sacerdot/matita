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

include "basic_2A/multiple/fleq_fleq.ma".
include "basic_2A/reduction/fpbq_alt.ma".
include "basic_2A/computation/fpbg.ma".

(* "QRST" PROPER PARALLEL COMPUTATION FOR CLOSURES **************************)

(* Properties on lazy equivalence for closures ******************************)

lemma fpbg_fleq_trans: ∀h,g,G1,G,L1,L,T1,T. ⦃G1, L1, T1⦄ >≡[h, g] ⦃G, L, T⦄ →
                       ∀G2,L2,T2. ⦃G, L, T⦄ ≡[0] ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ >≡[h, g] ⦃G2, L2, T2⦄.
/3 width=5 by fpbg_fpbq_trans, fleq_fpbq/ qed-.

lemma fleq_fpbg_trans: ∀h,g,G,G2,L,L2,T,T2. ⦃G, L, T⦄ >≡[h, g] ⦃G2, L2, T2⦄ →
                       ∀G1,L1,T1. ⦃G1, L1, T1⦄ ≡[0] ⦃G, L, T⦄ → ⦃G1, L1, T1⦄ >≡[h, g] ⦃G2, L2, T2⦄.
#h #g #G #G2 #L #L2 #T #T2 * #G0 #L0 #T0 #H0 #H02 #G1 #L1 #T1 #H1
elim (fleq_fpb_trans …  H1 … H0) -G -L -T
/4 width=9 by fpbs_strap2, fleq_fpbq, ex2_3_intro/
qed-.

(* alternative definition of fpbs *******************************************)

lemma fleq_fpbs: ∀h,g,G1,G2,L1,L2,T1,T2.
                 ⦃G1, L1, T1⦄ ≡[0] ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ≥[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 * /2 width=1 by lleq_fpbs/
qed.

lemma fpbg_fwd_fpbs: ∀h,g,G1,G2,L1,L2,T1,T2.
                     ⦃G1, L1, T1⦄ >≡[h,g] ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ≥[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 *
/3 width=5 by fpbs_strap2, fpb_fpbq/
qed-.

lemma fpbs_fpbg: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ≥[h, g] ⦃G2, L2, T2⦄ →
                 ⦃G1, L1, T1⦄ ≡[0] ⦃G2, L2, T2⦄ ∨
                 ⦃G1, L1, T1⦄ >≡[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H @(fpbs_ind … H) -G2 -L2 -T2
[ /2 width=1 by or_introl/
| #G #G2 #L #L2 #T #T2 #_ #H2 * #H1 @(fpbq_ind_alt … H2) -H2 #H2
  [ /3 width=5 by fleq_trans, or_introl/
  | elim (fleq_fpb_trans … H1 … H2) -G -L -T
    /4 width=5 by ex2_3_intro, or_intror, fleq_fpbs/
  | /3 width=5 by fpbg_fleq_trans, or_intror/
  | /4 width=5 by fpbg_fpbq_trans, fpb_fpbq, or_intror/
  ]
]
qed-.

(* Advanced properties of "qrst" parallel computation on closures ***********)

lemma fpbs_fpb_trans: ∀h,g,F1,F2,K1,K2,T1,T2. ⦃F1, K1, T1⦄ ≥[h, g] ⦃F2, K2, T2⦄ →
                      ∀G2,L2,U2. ⦃F2, K2, T2⦄ ≻[h, g] ⦃G2, L2, U2⦄ →
                      ∃∃G1,L1,U1. ⦃F1, K1, T1⦄ ≻[h, g] ⦃G1, L1, U1⦄ & ⦃G1, L1, U1⦄ ≥[h, g] ⦃G2, L2, U2⦄.
#h #g #F1 #F2 #K1 #K2 #T1 #T2 #H elim (fpbs_fpbg … H) -H
[ #H12 #G2 #L2 #U2 #H2 elim (fleq_fpb_trans … H12 … H2) -F2 -K2 -T2
  /3 width=5 by fleq_fpbs, ex2_3_intro/
| * #H1 #H2 #H3 #H4 #H5 #H6 #H7 #H8 #H9
  @(ex2_3_intro … H4) -H4 /3 width=5 by fpbs_strap1, fpb_fpbq/
]
qed-.
