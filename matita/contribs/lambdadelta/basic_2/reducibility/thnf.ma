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

include "basic_2/grammar/tshf.ma".
include "basic_2/reducibility/tpr.ma".

(* CONTEXT-FREE WEAK HEAD NORMAL TERMS **************************************)

definition thnf: predicate term ≝ NF … tpr tshf.

interpretation
   "context-free head normality (term)"
   'HdNormal T = (thnf T).

(* Basic inversion lemmas ***************************************************)

lemma thnf_inv_tshf: ∀T. 𝐇𝐍⦃T⦄ → T ≈ T.
normalize /2 width=1/
qed-.

(* Basic properties *********************************************************)

lemma tpr_tshf: ∀T1,T2. T1 ➡ T2 → T1 ≈ T1 → T1 ≈ T2.
#T1 #T2 #H elim H -T1 -T2 //
[ #I #V1 #V2 #T1 #T2 #_ #_ #_ #IHT12 #H
  elim (tshf_inv_flat1 … H) -H #W2 #U2 #HT1U2 #HT1 #_ #H1 #H2 destruct
  lapply (IHT12 HT1U2) -IHT12 -HT1U2 #HUT2
  lapply (simple_tshf_repl_dx … HUT2 HT1) /2 width=1/
| #a #V1 #V2 #W #T1 #T2 #_ #_ #_ #_ #H
  elim (tshf_inv_flat1 … H) -H #W2 #U2 #_ #H
  elim (simple_inv_bind … H)
| #a #I #V1 #V2 #T1 #T #T2 #_ #_ #_ #_ #_ #H
  elim (tshf_inv_bind1 … H) -H #W2 #U2 #H1 * #H2 destruct //
| #a #V2 #V1 #V #W1 #W2 #T1 #T2 #_ #_ #_ #_ #_ #_ #_ #H
  elim (tshf_inv_flat1 … H) -H #U1 #U2 #_ #H
  elim (simple_inv_bind … H)
| #V #T #T1 #T2 #_ #_ #_ #H
  elim (tshf_inv_bind1 … H) -H #W2 #U2 #H1 * #H2 destruct
| #V #T1 #T2 #_ #_ #H
  elim (tshf_inv_flat1 … H) -H #W2 #U2 #_ #_ #_ #H destruct
]
qed.

lemma thnf_tshf: ∀T. T ≈ T → 𝐇𝐍⦃T⦄.
/3 width=1/ qed.
