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

include "basic_2/grammar/term_simple.ma".

(* SAME HEAD TERM FORMS *****************************************************)

inductive tshf: relation term ≝
   | tshf_atom: ∀I. tshf (⓪{I}) (⓪{I})
   | tshf_abst: ∀V1,V2,T1,T2. tshf (ⓛV1. T1) (ⓛV2. T2)
   | tshf_appl: ∀V1,V2,T1,T2. tshf T1 T2 → 𝐒⦃T1⦄ → 𝐒⦃T2⦄ →
                tshf (ⓐV1. T1) (ⓐV2. T2)
.

interpretation "same head form (term)" 'napart T1 T2 = (tshf T1 T2).

(* Basic properties *********************************************************)

lemma tshf_sym: ∀T1,T2. T1 ≈ T2 → T2 ≈ T1.
#T1 #T2 #H elim H -T1 -T2 /2 width=1/
qed.

lemma tshf_refl2: ∀T1,T2. T1 ≈ T2 → T2 ≈ T2.
#T1 #T2 #H elim H -T1 -T2 // /2 width=1/
qed.

lemma tshf_refl1: ∀T1,T2. T1 ≈ T2 → T1 ≈ T1.
/3 width=2/ qed.

lemma simple_tshf_repl_dx: ∀T1,T2. T1 ≈ T2 → 𝐒⦃T1⦄ → 𝐒⦃T2⦄.
#T1 #T2 #H elim H -T1 -T2 //
#V1 #V2 #T1 #T2 #H
elim (simple_inv_bind … H)
qed. (**) (* remove from index *)

lemma simple_tshf_repl_sn: ∀T1,T2. T1 ≈ T2 → 𝐒⦃T2⦄ → 𝐒⦃T1⦄.
/3 width=3/ qed-.

(* Basic inversion lemmas ***************************************************)

fact tshf_inv_bind1_aux: ∀T1,T2. T1 ≈ T2 → ∀I,W1,U1. T1 = ⓑ{I}W1.U1 →
                         ∃∃W2,U2. I = Abst & T2 = ⓛW2. U2.
#T1 #T2 * -T1 -T2
[ #J #I #W1 #U1 #H destruct
| #V1 #V2 #T1 #T2 #I #W1 #U1 #H destruct /2 width=3/
| #V1 #V2 #T1 #T2 #H_ #_ #_ #I #W1 #U1 #H destruct
]
qed.

lemma tshf_inv_bind1: ∀I,W1,U1,T2. ⓑ{I}W1.U1 ≈ T2 →
                      ∃∃W2,U2. I = Abst & T2 = ⓛW2. U2.
/2 width=5/ qed-.

fact tshf_inv_flat1_aux: ∀T1,T2. T1 ≈ T2 → ∀I,W1,U1. T1 = ⓕ{I}W1.U1 →
                         ∃∃W2,U2. U1 ≈ U2 & 𝐒⦃U1⦄ & 𝐒⦃U2⦄ &
                                  I = Appl & T2 = ⓐW2. U2.
#T1 #T2 * -T1 -T2
[ #J #I #W1 #U1 #H destruct
| #V1 #V2 #T1 #T2 #I #W1 #U1 #H destruct
| #V1 #V2 #T1 #T2 #HT12 #HT1 #HT2 #I #W1 #U1 #H destruct /2 width=5/
]
qed.

lemma tshf_inv_flat1: ∀I,W1,U1,T2. ⓕ{I}W1.U1 ≈ T2 →
                      ∃∃W2,U2. U1 ≈ U2 & 𝐒⦃U1⦄ & 𝐒⦃U2⦄ &
                               I = Appl & T2 = ⓐW2. U2.
/2 width=4/ qed-.
