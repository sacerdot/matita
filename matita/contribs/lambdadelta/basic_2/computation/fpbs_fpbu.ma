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
include "basic_2/reduction/fpbu.ma".
include "basic_2/computation/fpbs_alt.ma".

(* "QRST" PARALLEL COMPUTATION FOR CLOSURES *********************************)

(* Properties on extended context-sensitive parallel computation for terms **)

lemma fpbs_cpx_trans_neq: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ≥[h, g] ⦃G2, L2, T2⦄ →
                          ∀U2. ⦃G2, L2⦄ ⊢ T2 ➡[h, g] U2 → (T2 = U2 → ⊥) →
                          ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ➡[h, g] U1 & T1 = U1 → ⊥ & ⦃G1, L1, U1⦄ ≥[h, g] ⦃G2, L2, U2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H #U2 #HTU2 #HnTU2 elim (fpbs_inv_alt … H) -H
#L00 #L0 #T0 #HT10 #H10 #HL00 #HL02 lapply (lleq_cpx_trans … HTU2 … HL02) -HTU2
#HTU2 lapply (cpx_lleq_conf_sn … HTU2 … HL02) -HL02
#HL02 lapply (lpxs_cpx_trans … HTU2 … HL00) -HTU2
#HTU2 elim (fqus_cpxs_trans_neq … H10 … HTU2 HnTU2) -H10 -HTU2 -HnTU2
#U0 #HTU0 #HnTU0 #HU02 elim (eq_term_dec T1 T0) #HnT10 destruct
[ -HT10 elim (cpxs_neq_inv_step_sn … HTU0 HnTU0) -HTU0 -HnTU0
| -HnTU0 elim (cpxs_neq_inv_step_sn … HT10 HnT10) -HT10 -HnT10
]
/4 width=10 by fpbs_intro_alt, cpxs_trans, ex3_intro/
qed-.

(* Properties on "rst" proper parallel reduction on closures ****************)

lemma fpbu_fpbs: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ≻[h, g] ⦃G2, L2, T2⦄ →
                 ⦃G1, L1, T1⦄ ≥[h, g] ⦃G2, L2, T2⦄.
/3 width=1 by fpb_fpbs, fpbu_fwd_fpb/ qed.

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
  [ #H elim (fqup_inv_step_sn … H) -H
    /4 width=11 by fpbs_intro_alt, fpbu_fqu, ex2_3_intro, or_intror/
  | * #HG #HL #HT destruct elim (lleq_dec T2 L0 L 0) #H
    [ /4 width=3 by fleq_intro, lleq_trans, or_introl/
    | elim (lpxs_nlleq_inv_step_sn … HL0 H) -HL0 -H
      /5 width=7 by lpxs_lleq_fpbs, fpbu_lpx, lleq_trans, ex2_3_intro, or_intror/
    ]
  ]
| elim (cpxs_neq_inv_step_sn … HT1 H) -HT1 -H
  /5 width=11 by fpbs_intro_alt, fpbu_cpx, ex2_3_intro, or_intror/
]
qed-.
