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

include "basic_2/computation/lpxs_lpxs.ma".
include "basic_2/computation/fpbs_alt.ma".
include "basic_2/computation/fpbg.ma".

(* GENERAL "BIG TREE" PROPER PARALLEL COMPUTATION FOR CLOSURES **************)

(* Advanced forward lemmas **************************************************)

lemma fpbg_fwd_fpbs: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ >[h, g] ⦃G2, L2, T2⦄ →
                     ⦃G1, L1, T1⦄ ≥[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G2 -L2 -T2
/3 width=5 by cpxs_fqus_lpxs_fpbs, cpxs_fqup_fpbs, fpbs_trans, lpxs_fpbs, cpxs_fpbs/
qed-.

lemma fpbg_fwd_fpbc_sn: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ >[h, g] ⦃G2, L2, T2⦄ →
                        ∃∃G,L,T. ⦃G1, L1, T1⦄ ≻[h, g] ⦃G, L, T⦄ & ⦃G, L, T⦄ ≥[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G2 -L2 -T2
[ /4 width=5 by fpbc_cpxs, lpxs_fpbs, ex2_3_intro/
| #G2 #L #L2 #T #T2 #HT1 #HT2 #HL2 elim (eq_term_dec T1 T) #H destruct
  [ -HT1 /3 width=5 by fpbc_fqup, lpxs_fpbs, ex2_3_intro/
  | /5 width=9 by fpbc_cpxs, fpbsa_inv_fpbs, fqup_fqus, ex3_2_intro, ex2_3_intro/
  ]
| #G2 #L #L0 #L2 #T #T2 #HT1 #HT2 #HL0 #H0 #HL02 #H02
  lapply (lpxs_trans … HL0 … HL02) #HL2
  elim (eq_term_dec T1 T) #H destruct
  [ -HT1 elim (fqus_inv_gen … HT2) -HT2
    [ /3 width=5 by fpbc_fqup, lpxs_fpbs, ex2_3_intro/
    | * #H1 #H2 #H3 destruct
      /4 width=5 by fpbc_lpxs, lpxs_fpbs, ex2_3_intro/
    ]
  | /4 width=9 by fpbc_cpxs, fpbsa_inv_fpbs, ex3_2_intro, ex2_3_intro/
  ]
]
qed-.

(* Advanced properties ******************************************************)

lemma fqu_fpbs_fpbg: ∀h,g,G1,G,G2,L1,L,L2,T1,T,T2. ⦃G1, L1, T1⦄ ⊃ ⦃G, L, T⦄ →
                     ⦃G, L, T⦄ ≥[h, g] ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ >[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G #G2 #L1 #L #L2 #T1 #T #T2 #H1 #H elim(fpbs_fpbsa … H) -H
#L0 #T0 #HT0 #HT02 #HL02 elim (fqu_cpxs_trans … HT0 … H1) -T
/3 width=7 by fpbg_fqup, fqus_strap2_fqu/
qed.
