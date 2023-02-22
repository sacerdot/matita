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

set "baseuri" "cic:/matita/formal_topology/".
include "logic/equality.ma".

axiom S: Type.

axiom leq: S → S → Prop.

notation "hvbox(A break ⊆ B)" with precedence 64
for @{ 'subseteq $A $B}.

interpretation "Subseteq" 'subseteq A B = (leq A B).

axiom leq_refl: ∀A. A ⊆ A.
axiom leq_antisym: ∀A,B. A ⊆ B → B ⊆ A → A=B.
axiom leq_tran: ∀A,B,C. A ⊆ B → B ⊆ C → A ⊆ C.

axiom i: S → S.

axiom i_contrattivita: ∀A. i A ⊆ A.
axiom i_idempotenza: ∀A. i (i A) = i A.
axiom i_monotonia: ∀A,B. A ⊆ B → i A ⊆ i B.

axiom c: S → S.

axiom c_espansivita: ∀A. A ⊆ c A.
axiom c_idempotenza: ∀A. c (c A) = c A.
axiom c_monotonia: ∀A,B. A ⊆ B → c A ⊆ c B.

axiom m: S → S.

axiom m_antimonotonia: ∀A,B. A ⊆ B → m B ⊆ m A.
axiom m_saturazione: ∀A. A ⊆ m (m A).
axiom m_puntofisso: ∀A. m A = m (m (m A)).

lemma l1: ∀A,B. i A ⊆ B → i A ⊆ i B. intros; rewrite < i_idempotenza; auto. qed.
lemma l2: ∀A,B. A ⊆ c B → c A ⊆ c B. intros; rewrite < c_idempotenza in ⊢ (? ? %); auto. qed.

theorem geq1: ∀A. i (i A) = i A. intros. auto. qed.
theorem geq2: ∀A. c (c A) = c A. intros. auto. qed.
theorem geq3: ∀A. i (i (c A)) = i (c A). intros. auto. qed.
theorem geq4: ∀A. c (c (i A)) = c (i A). intros. auto. qed.
theorem geq5: ∀A. i (c (i (c A))) = i (c A). intros. auto depth=4. qed.
theorem geq6: ∀A. c (i (c (i A))) = c (i A). intros. auto depth=4. qed.
theorem gse1: ∀A. i A ⊆ A. intros. auto. qed.
theorem gse2: ∀A. A ⊆ c A. intros. auto. qed.
theorem gse3: ∀A. i A ⊆ i (c (i A)). intros. auto. qed.
theorem gse4: ∀A. i (c (i A)) ⊆ i (c A). intros. auto. qed.
theorem gse5: ∀A. i (c (i A)) ⊆ c (i A). intros. auto. qed.
theorem gse6: ∀A. i (c A) ⊆ c (i (c A)). intros. auto. qed.
theorem gse7: ∀A. c (i A) ⊆ c (i (c A)). intros. auto. qed.
theorem gse8: ∀A. c (i (c A)) ⊆ c A. intros. auto. qed.

axiom th1: ∀A. c (m A) ⊆ m (i A).
axiom th2: ∀A. i (m A) ⊆ m (c A).

theorem se1: ∀A. i (c (m (c A))) ⊆ i (m (i (c A))). intros; auto. qed.
theorem se2: ∀A. i (m (i (c A))) ⊆ m (c (i (c A))). intros; auto. qed.
theorem se3: ∀A. c (i (m A)) ⊆ c (i (c (m (c A)))). intros; auto depth=4. qed.
theorem se4: ∀A. c (i (c (m (c A)))) ⊆ c (i (m (i (c A)))). intros; auto. qed.
theorem se5: ∀A. i (c (m (c A))) ⊆ c (i (c (m (c A)))). intros; auto. qed.
theorem se6: ∀A. i (m (i (c A))) ⊆ c (i (m (i (c A)))). intros; auto. qed.
theorem se7: ∀A. m (c A) ⊆ m A. intros; auto. qed.
theorem se8: ∀A. i (c (m (c A))) ⊆ i (c (m A)). intros; auto. qed.
theorem se9: ∀A. i (c (m A)) ⊆ i (m (i A)). intros; auto. qed.
theorem se10: ∀A. i (m (i (c A))) ⊆ i (m (i A)). intros; auto depth=4. qed.
theorem se11: ∀A. i (m (i A)) ⊆ m (c (i A)). intros; auto. qed.
theorem se12: ∀A. m (c (i (c A))) ⊆ m (c (i A)). intros; auto. qed.
theorem se13: ∀A. m (c A) ⊆ m (c (i (c A))). intros; auto. qed.
theorem se14: ∀A. i (c (m A)) ⊆ c (i (c (m A))). intros; auto. qed.
theorem se15: ∀A. c (i (c (m A))) ⊆ c (m A). intros; auto. qed.
theorem se16: ∀A. c (i (m (i A))) ⊆ c (m (c (i A))). intros; auto depth=4. qed.
theorem se17: ∀A. c (m (c (i A))) ⊆ m (i (c (i A))). intros; auto. qed.
theorem se18: ∀A. m (i (c A)) ⊆ m (i (c (i A))). intros; auto. qed.
theorem se19: ∀A. m (i (c (i A))) ⊆ m (i A). intros; auto. qed.
theorem se20: ∀A. c (m (c A)) ⊆ c (m A). intros; auto. qed.
theorem se21: ∀A. c (m (c A)) ⊆ c (m (c (i (c A)))). intros; auto. qed.
theorem se22: ∀A. c (m (c (i (c A)))) ⊆ m (i (c A)). intros; auto. qed.
theorem se23: ∀A. c (i (c (m (c A)))) ⊆ c (i (c (m A))). intros; auto. qed.
theorem se24: ∀A. c (i (c (m (c A)))) ⊆ c (m (c A)). intros; auto. qed.
theorem se25: ∀A. m (c A) ⊆ c (m (c A)). intros; auto. qed.
theorem se26: ∀A. c (i (m (i (c A)))) ⊆ c (i (m (c (i (c A))))). intros; auto. qed.
theorem se27: ∀A. m (c (i (c A))) ⊆ c (m (c (i (c A)))). intros; auto. qed.
theorem se28: ∀A. m (c (i A)) ⊆ c (m (c (i A))). intros; auto. qed.
theorem se29: ∀A. m A ⊆ c (m A). intros; auto. qed.
theorem se30: ∀A. i (m A) ⊆ i (c (i (m A))). intros; auto. qed.
theorem se31: ∀A. i (c (i (m A))) ⊆ c (i (m A)). intros; auto. qed.
theorem se32: ∀A. i (c (i (m A))) ⊆ i (c (m (c A))). intros; auto. qed.
theorem se33: ∀A. c (i (c (m A))) ⊆ c (i (m (i A))). intros; auto. qed.
theorem se34: ∀A. i (m (i A)) ⊆ c (i (m (i A))). intros; auto. qed.
theorem se35: ∀A. c (i (m (i (c A)))) ⊆ c (i (m (i A))). intros; auto. qed.
theorem se36: ∀A. c (m (c (i (c A)))) ⊆ c (m (c (i A))). intros; auto. qed.

theorem th5: ∀A. i (m (c A)) = i (m A). intros; auto depth=4. qed.
theorem th6: ∀A. c (m (i A)) = m (i A). intros; auto width=2 depth=5. qed.
theorem th7: ∀A. i (m (i A)) = i (c (i (m (i A)))). intros; auto. qed.
theorem th8: ∀A. i (m (i A)) = i (m (i (c (i A)))). intros; auto. qed.
theorem th9: ∀A. i (c (m (c (i A)))) = i (m (i A)). intros; auto depth=4. qed.

(* theorem th7: ∀A. i (m (i A)) = i (s (i A)). *)
