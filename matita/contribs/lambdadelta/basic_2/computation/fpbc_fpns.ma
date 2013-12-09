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

include "basic_2/relocation/lleq_lleq.ma".
include "basic_2/computation/fpns.ma".
include "basic_2/computation/fpbs_alt.ma".
include "basic_2/computation/fpbc.ma".

(* ATOMIC "BIG TREE" PROPER PARALLEL COMPUTATION FOR CLOSURES ***************)

(* Forward lemmas on parallel computation for "big tree" normal forms *******)

lemma fpbs_fwd_fpbc_sn: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ≥[h, g] ⦃G2, L2, T2⦄ →
                        ⦃G1, L1, T1⦄ ⊢ ⋕➡*[h, g] ⦃G2, L2, T2⦄ ∨
                        ∃∃G,L,T. ⦃G1, L1, T1⦄ ≻[h, g] ⦃G, L, T⦄ & ⦃G, L, T⦄ ≥[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H elim(fpbs_fpbsa … H) -H
#L #T #HT1 #HT2 #HL2 elim (eq_term_dec T1 T) #H destruct
[ -HT1 elim (fqus_inv_gen … HT2) -HT2
  [ #HT2 @or_intror
    /5 width=9 by fpbsa_inv_fpbs, fpbc_fqup, ex3_2_intro, ex2_3_intro, or_intror/
  | * #HG #HL #HT destruct elim (lleq_dec T2 L L2 0) #H
    [ /3 width=1 by fpns_intro, or_introl/
    | /5 width=5 by fpbc_lpxs, ex2_3_intro, or_intror/
    ]
  ]
| elim (cpxs_neq_inv_step_sn … HT1 H) -HT1 -H
  /5 width=9 by fpbsa_inv_fpbs, fpbc_cpxs, cpx_cpxs, ex3_2_intro, ex2_3_intro, or_intror/
]
qed-.
