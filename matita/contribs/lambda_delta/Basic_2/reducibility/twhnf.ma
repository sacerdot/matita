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

include "Basic_2/grammar/thom.ma".
include "Basic_2/reducibility/tpr.ma".

(* CONTEXT-FREE WEAK HEAD NORMAL TERMS **************************************)

definition twhnf: predicate term ≝ NF … tpr thom.

interpretation
   "context-free weak head normality (term)"
   'WHdNormal T = (twhnf T).

(* Basic inversion lemmas ***************************************************)

lemma twhnf_inv_thom: ∀T. 𝕎ℍℕ[T] → T ≈ T.
normalize /2 depth=1/
qed-.

(* Basic properties *********************************************************)

lemma tpr_thom: ∀T1,T2. T1 ⇒ T2 → T1 ≈ T1 → T1 ≈ T2.
#T1 #T2 #H elim H -T1 T2 //
[ #I #V1 #V2 #T1 #T2 #_ #_ #_ #IHT12 #H
  elim (thom_inv_flat1 … H) -H #W2 #U2 #HT1U2 #HT1 #_ #H1 #H2 destruct -I T1 V1;
  lapply (IHT12 HT1U2) -IHT12 HT1U2 #HUT2
  lapply (simple_thom_repl_dx … HUT2 HT1) /2 width=1/
| #V1 #V2 #W #T1 #T2 #_ #_ #_ #_ #H
  elim (thom_inv_flat1 … H) -H #W2 #U2 #_ #H
  elim (simple_inv_bind … H)
| #I #V1 #V2 #T1 #T #T2 #_ #_ #_ #_ #_ #H
  elim (thom_inv_bind1 … H) -H #W2 #U2 #H destruct -I //
| #V2 #V1 #V #W1 #W2 #T1 #T2 #_ #_ #_ #_ #_ #_ #_ #H
  elim (thom_inv_flat1 … H) -H #U1 #U2 #_ #H
  elim (simple_inv_bind … H)
| #V #T #T1 #T2 #_ #_ #_ #H
  elim (thom_inv_bind1 … H) -H #W2 #U2 #H destruct
| #V #T1 #T2 #_ #_ #H
  elim (thom_inv_flat1 … H) -H #W2 #U2 #_ #_ #_ #H destruct
]
qed.

lemma twhnf_thom: ∀T. T ≈ T → 𝕎ℍℕ[T].
/2/ qed.
