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

include "basic_2/relocation/fsupq.ma".

(* OPTIONAL SUPCLOSURE ******************************************************)

(* alternative definition of fsupq *)
definition fsupqa: bi_relation lenv term ≝ bi_RC … fsup.

interpretation
   "optional structural successor (closure) alternative"
   'SupTermOptAlt L1 T1 L2 T2 = (fsupqa L1 T1 L2 T2).

(* Basic properties *********************************************************)

lemma fsupqa_refl: bi_reflexive … fsupqa.
// qed.

lemma fsupqa_ldrop: ∀K1,K2,T1,T2. ⦃K1, T1⦄ ⊃⊃⸮ ⦃K2, T2⦄ →
                    ∀L1,d,e. ⇩[d, e] L1 ≡ K1 →
                    ∀U1. ⇧[d, e] T1 ≡ U1 → ⦃L1, U1⦄ ⊃⊃⸮ ⦃K2, T2⦄.
#K1 #K2 #T1 #T2 * [ /3 width=7/ ] * #H1 #H2 destruct
#L1 #d #e #HLK #U1 #HTU elim (eq_or_gt e) [2: /3 width=5/ ] #H destruct
>(ldrop_inv_O2 … HLK) -L1 >(lift_inv_O2 … HTU) -T2 -d //
qed.

(* Main properties **********************************************************)

theorem fsupq_fsupqa: ∀L1,L2,T1,T2. ⦃L1, T1⦄ ⊃⸮ ⦃L2, T2⦄ → ⦃L1, T1⦄ ⊃⊃⸮ ⦃L2, T2⦄.
#L1 #L2 #T1 #T2 #H elim H -L1 -L2 -T1 -T2 // /2 width=1/ /2 width=7/
qed.

(* Main inversion properties ************************************************)

theorem fsupqa_inv_fsupq: ∀L1,L2,T1,T2. ⦃L1, T1⦄ ⊃⊃⸮ ⦃L2, T2⦄ → ⦃L1, T1⦄ ⊃⸮ ⦃L2, T2⦄.
#L1 #L2 #T1 #T2 #H elim H -H /2 width=1/
* #H1 #H2 destruct //
qed-.
