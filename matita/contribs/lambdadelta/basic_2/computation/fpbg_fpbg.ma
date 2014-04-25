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

include "basic_2/computation/fpbc_fpbs.ma".
include "basic_2/computation/fpbg_fleq.ma".

(* GENERAL "BIG TREE" PROPER PARALLEL COMPUTATION FOR CLOSURES **************)

(* Advanced inversion lemmas ************************************************)

lemma fpbg_inv_fpbu_sn: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ >≡[h, g] ⦃G2, L2, T2⦄ →
                        ∃∃G,L,T. ⦃G1, L1, T1⦄ ≻[h, g] ⦃G, L, T⦄ & ⦃G, L, T⦄ ≥[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H @(fpbg_ind_dx … H) -G1 -L1 -T1
[ #G1 #L1 #T1 * /3 width=5 by fleq_fpbs, ex2_3_intro/
| #G1 #G #L1 #L #T1 #T *
  #G0 #L0 #T0 #H10 #H0 #_ *
  /5 width=9 by fpbu_fwd_fpbs, fpbs_trans, fleq_fpbs, ex2_3_intro/
]
qed-.

(* Advanced forward lemmas **************************************************)

lemma fpbg_fwd_fpbs: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ >≡[h, g] ⦃G2, L2, T2⦄ →
                     ⦃G1, L1, T1⦄ ≥[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H @(fpbg_ind … H) -G2 -L2 -T2
[2: #G #G2 #L #L2 #T #T2 #_ #H2 #IH1 @(fpbs_trans … IH1) -IH1 ] (**) (* full auto fails *)
/2 width=1 by fpbc_fwd_fpbs/
qed-.

(* Advanced properties ******************************************************)

lemma fpbs_fpbu_trans: ∀h,g,F1,F2,K1,K2,T1,T2. ⦃F1, K1, T1⦄ ≥[h, g] ⦃F2, K2, T2⦄ →
                       ∀G2,L2,U2. ⦃F2, K2, T2⦄ ≻[h, g] ⦃G2, L2, U2⦄ →
                       ∃∃G1,L1,U1. ⦃F1, K1, T1⦄ ≻[h, g] ⦃G1, L1, U1⦄ & ⦃G1, L1, U1⦄ ≥[h, g] ⦃G2, L2, U2⦄.
/5 width=5 by fpbg_inv_fpbu_sn, fpbs_fpbg_trans, fpbc_fpbg, fpbu_fpbc/ qed-.

(* Man properties ***********************************************************)

theorem fpbg_trans: ∀h,g. tri_transitive … (fpbg h g).
/2 width=5 by tri_TC_transitive/ qed-.
