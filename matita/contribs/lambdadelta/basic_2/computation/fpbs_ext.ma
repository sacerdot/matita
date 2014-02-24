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

include "basic_2/computation/fpbs_alt.ma".

(* "BIG TREE" PARALLEL COMPUTATION FOR CLOSURES *****************************)

(* Properties on extended context-sensitive parallel computation for terms **)

lemma fpbs_cpxs_trans_neq: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ≥[h, g] ⦃G2, L2, T2⦄ →
                           ∀U2. ⦃G2, L2⦄ ⊢ T2 ➡*[h, g] U2 → (T2 = U2 → ⊥) →
                           ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ➡*[h, g] U1 & T1 = U1 → ⊥ & ⦃G1, L1, U1⦄ ≥[h, g] ⦃G2, L2, U2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H #U2 #HTU2 #HnTU2 elim (fpbs_fpbsa … H) -H
#L0 #T0 #HT10 #H10 #HL02 elim (eq_term_dec T1 T0) [ -HT10 | -HnTU2 ]
[ #H destruct lapply (lpxs_cpxs_trans … HTU2 … HL02) -HTU2
  #HTU2 elim (fqus_cpxs_trans_neq … H10 … HTU2 HnTU2) -T2
  /3 width=6 by fqus_lpxs_fpbs, ex3_intro/
| /4 width=6 by fpbs_cpxs_trans, fqus_lpxs_fpbs, ex3_intro/
]
qed-.
