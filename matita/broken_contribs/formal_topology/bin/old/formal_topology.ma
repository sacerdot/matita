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

lemma l1: ∀A,B. i A ⊆ B → i A ⊆ i B.
 intros; rewrite < i_idempotenza; apply (i_monotonia (i A) B H).
qed.
lemma l2: ∀A,B. A ⊆ c B → c A ⊆ c B.
 intros; rewrite < c_idempotenza in ⊢ (? ? %); apply (c_monotonia A (c B) H).
qed.

axiom th1: ∀A. c (m A) ⊆ m (i A).
axiom th2: ∀A. i (m A) ⊆ m (c A).

(************** start of generated part *********************)

