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
include "basic_2/computation/fpbs_alt.ma".
include "basic_2/computation/fpbu_lleq.ma".

(* UNITARY "BIG TREE" PROPER PARALLEL COMPUTATION FOR CLOSURES **************)

(* Properties on lazy equivalence for closures ******************************)

lemma fleq_fpbu_trans: ∀h,g,F1,F2,K1,K2,T1,T2. ⦃F1, K1, T1⦄ ≡[0] ⦃F2, K2, T2⦄ →
                       ∀G2,L2,U2. ⦃F2, K2, T2⦄ ≻[h, g] ⦃G2, L2, U2⦄ →
                       ∃∃G1,L1,U1. ⦃F1, K1, T1⦄ ≻[h, g] ⦃G1, L1, U1⦄ & ⦃G1, L1, U1⦄ ≡[0] ⦃G2, L2, U2⦄.
#h #g #F1 #F2 #K1 #K2 #T1 #T2 * -F2 -K2 -T2
#K2 #HK12 #G2 #L2 #U2 #H12 elim (lleq_fpbu_trans … HK12 … H12) -K2
/3 width=5 by fleq_intro, ex2_3_intro/
qed-.

lemma fpb_fpbu: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ≽[h, g] ⦃G2, L2, T2⦄ →
                ⦃G1, L1, T1⦄ ≡[0] ⦃G2, L2, T2⦄ ∨
                ⦃G1, L1, T1⦄ ≻[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 * -G2 -L2 -T2
[ #G2 #L2 #T2 #H elim (fquq_inv_gen … H) -H
  [ /4 width=1 by fpbu_fqup, fqu_fqup, or_intror/
  | * #H1 #H2 #H3 destruct /2 width=1 by or_introl/
  ]
| #T2 #HT12 elim (eq_term_dec T1 T2)
  #HnT12 destruct /4 width=1 by fpbu_cpxs, cpx_cpxs, or_intror, or_introl/
| #L2 #HL12 elim (lleq_dec … T1 L1 L2 0)
  /4 width=3 by fpbu_lpxs, fleq_intro, lpx_lpxs, or_intror, or_introl/
| /3 width=1 by fleq_intro, or_introl/ 
]
qed-.

lemma fpbs_fpbu_sn: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ≥[h, g] ⦃G2, L2, T2⦄ →
                    ⦃G1, L1, T1⦄ ≡[0] ⦃G2, L2, T2⦄ ∨
                    ∃∃G,L,T. ⦃G1, L1, T1⦄ ≻[h, g] ⦃G, L, T⦄ & ⦃G, L, T⦄ ≥[h, g] ⦃G2, L2, T2⦄.
(* ALTERNATIVE PROOF
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H @(fpbs_ind_dx … H) -G1 -L1 -T1
[ /2 width=1 by or_introl/
| #G1 #G #L1 #L #T1 #T #H1 #_ * [ #H2 | * #G0 #L0 #T0 #H0 #H02 ]
  elim (fpb_fpbu … H1) -H1 #H1
  [ /3 width=1 by  
*)
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H elim(fpbs_inv_alt … H) -H
#L0 #L #T #HT1 #HT2 #HL0 #HL2 elim (eq_term_dec T1 T) #H destruct
[ -HT1 elim (fqus_inv_gen … HT2) -HT2
  [ /4 width=11 by fpbs_intro_alt, fpbu_fqup, ex2_3_intro, or_intror/
  | * #HG #HL #HT destruct elim (lleq_dec T2 L0 L 0) #H
    [ /4 width=3 by fleq_intro, lleq_trans, or_introl/
    | /5 width=5 by fpbu_lpxs, lleq_fpbs, ex2_3_intro, or_intror/
    ]
  ]
| elim (cpxs_neq_inv_step_sn … HT1 H) -HT1 -H
  /5 width=11 by fpbs_intro_alt, fpbu_cpxs, cpx_cpxs, ex2_3_intro, or_intror/
]
qed-.
