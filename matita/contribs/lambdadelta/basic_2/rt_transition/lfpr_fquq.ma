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

include "basic_2/s_transition/fquq.ma".
include "basic_2/rt_transition/cpm_drops.ma".
include "basic_2/rt_transition/cpr.ma".
include "basic_2/rt_transition/lfpr_fqup.ma".

(* PARALLEL R-TRANSITION FOR LOCAL ENV.S ON REFERRED ENTRIES ****************)

(* Properties with supclosure ***********************************************)

lemma fqu_cpr_trans_dx: ∀h,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐ ⦃G2, L2, T2⦄ →
                        ∀U2. ⦃G2, L2⦄ ⊢ T2 ➡[h] U2 →
                        ∃∃L,U1. ⦃G1, L1⦄ ⊢ ➡[h, T1] L & ⦃G1, L⦄ ⊢ T1 ➡[h] U1 & ⦃G1, L, U1⦄ ⊐ ⦃G2, L2, U2⦄.
#h #G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G1 -G2 -L1 -L2 -T1 -T2
/3 width=5 by lfpr_pair, cpr_pair_sn, cpr_flat, cpm_bind, fqu_lref_O, fqu_pair_sn, fqu_bind_dx, fqu_flat_dx, ex3_2_intro/
#I #G #L #V #U #T #HUT #U2 #HU2 elim (cpm_lifts_sn … HU2 (Ⓣ) … HUT) -U
/3 width=9 by fqu_drop, drops_refl, drops_drop, ex3_2_intro/
qed-.

(* Basic_2A1: uses: fqu_lpr_trans *)
lemma fqu_cpr_trans_sn: ∀h,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐ ⦃G2, L2, T2⦄ →
                        ∀U2. ⦃G2, L2⦄ ⊢ T2 ➡[h] U2 →
                        ∃∃L,U1. ⦃G1, L1⦄ ⊢ ➡[h, T1] L & ⦃G1, L1⦄ ⊢ T1 ➡[h] U1 & ⦃G1, L, U1⦄ ⊐ ⦃G2, L2, U2⦄.
#h #G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G1 -G2 -L1 -L2 -T1 -T2
/3 width=5 by lfpr_pair, cpr_pair_sn, cpr_flat, cpm_bind, fqu_lref_O, fqu_pair_sn, fqu_bind_dx, fqu_flat_dx, ex3_2_intro/
#I #G #L #V #U #T #HUT #U2 #HU2 elim (cpm_lifts_sn … HU2 (Ⓣ) … HUT) -U
/3 width=9 by fqu_drop, drops_refl, drops_drop, ex3_2_intro/
qed-.

(* Properties with optional supclosure **************************************)

lemma fquq_cpr_trans_dx: ∀h,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐⸮ ⦃G2, L2, T2⦄ →
                         ∀U2. ⦃G2, L2⦄ ⊢ T2 ➡[h] U2 →
                         ∃∃L,U1. ⦃G1, L1⦄ ⊢ ➡[h, T1] L & ⦃G1, L⦄ ⊢ T1 ➡[h] U1 & ⦃G1, L, U1⦄ ⊐⸮ ⦃G2, L2, U2⦄.
#h #G1 #G2 #L1 #L2 #T1 #T2 #H elim H -H
[ #HT12 #U2 #HTU2 elim (fqu_cpr_trans_dx … HT12 … HTU2) /3 width=5 by fqu_fquq, ex3_2_intro/
| * #H1 #H2 #H3 destruct /2 width=5 by ex3_2_intro/
]
qed-.

(* Basic_2A1: uses: fquq_lpr_trans *)
lemma fquq_cpr_trans_sn: ∀h,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐⸮ ⦃G2, L2, T2⦄ →
                         ∀U2. ⦃G2, L2⦄ ⊢ T2 ➡[h] U2 →
                         ∃∃L,U1. ⦃G1, L1⦄ ⊢ ➡[h, T1] L & ⦃G1, L1⦄ ⊢ T1 ➡[h] U1 & ⦃G1, L, U1⦄ ⊐⸮ ⦃G2, L2, U2⦄.
#h #G1 #G2 #L1 #L2 #T1 #T2 #H elim H -H
[ #HT12 #U2 #HTU2 elim (fqu_cpr_trans_sn … HT12 … HTU2) /3 width=5 by fqu_fquq, ex3_2_intro/
| * #H1 #H2 #H3 destruct /2 width=5 by ex3_2_intro/
]
qed-.
