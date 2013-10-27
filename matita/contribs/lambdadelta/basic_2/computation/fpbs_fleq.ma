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

include "basic_2/reduction/fpbc.ma".
include "basic_2/computation/fleq.ma".
include "basic_2/computation/fpbs_alt.ma".

(* "BIG TREE" PARALLEL COMPUTATION FOR CLOSURES *****************************)

(* Forward lemmas on equivalent "big tree" normal forms *********************)

lemma fpbs_fwd_fpb_sn: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ≥[h, g] ⦃G2, L2, T2⦄ →
                       ⦃G1, L1, T1⦄ ⋕[h, g] ⦃G2, L2, T2⦄ ∨
                       ∃∃G,L,T. ⦃G1, L1, T1⦄ ≻[h, g] ⦃G, L, T⦄ & ⦃G, L, T⦄ ≥[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H elim(fpbs_fpbsa … H) -H
#L #T #HT1 #HT2 #HL2 elim (eq_term_dec T1 T) #H destruct
[ -HT1 elim (fqus_inv_gen … HT2) -HT2
  [ #HT2 elim (fqup_inv_step_sn … HT2) -HT2
    /5 width=9 by fpbsa_inv_fpbs, fpbc_fqu, ex3_2_intro, ex2_3_intro, or_intror/
  | * #HG #HL #HT destruct /3 width=1 by and3_intro, or_introl/
  ]
| elim (cpxs_neq_inv_step_sn … HT1 H) -HT1 -H
  /5 width=9 by fpbsa_inv_fpbs, fpbc_cpx, ex3_2_intro, ex2_3_intro, or_intror/
]
qed-.
