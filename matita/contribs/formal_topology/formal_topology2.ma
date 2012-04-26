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

axiom comp: S → S → S.
coercion cic:/matita/formal_topology/comp.con 1.

axiom comp_assoc: ∀A,B,C:S. A (B C) = (A B) C.

axiom one: S.

notation "1" with precedence 89
for @{ 'unit }.

interpretation "Unit" 'unit = one.
 
axiom one_left: ∀A. 1 A = A.
axiom one_right: ∀A:S. A 1 = A.

axiom eps: S.
axiom eps_idempotent: eps = eps eps.

notation "hvbox(A break ⊆ B)" with precedence 64
for @{ 'subseteq $A $B}.

interpretation "Subseteq" 'subseteq A B = (eq ? A (comp eps B)).

axiom leq_refl: ∀A. A ⊆ A.
axiom leq_antisym: ∀A,B. A ⊆ B → B ⊆ A → A=B.
axiom leq_tran: ∀A,B,C. A ⊆ B → B ⊆ C → A ⊆ C.

axiom i: S.

axiom i_contrattivita: i ⊆ 1.
axiom i_idempotenza: i i = i.
axiom i_monotonia: ∀A,B. A ⊆ B → i A ⊆ i B.

axiom c: S.

axiom c_espansivita: 1 ⊆ c.
axiom c_idempotenza: c c = c.
axiom c_monotonia: ∀A,B. A ⊆ B → c A ⊆ c B.

axiom m: S.

axiom m_antimonotonia: ∀A,B. A ⊆ B → m B ⊆ m A.
axiom m_saturazione: 1 ⊆ m m.
axiom m_puntofisso: m = m (m m).

theorem th1: c m ⊆ m i. intros; auto. qed.
theorem th2: ∀A. i (m A) ⊆ (m (c A)). intros; auto. qed.
theorem th3: ∀A. i A ⊆ (m (c (m A))). intros; auto. qed.
theorem th4: ∀A. c A ⊆ (m (i (m A))). intros; auto. qed.

theorem th5: ∀A. i (m A) = i (m (c A)). intros; auto. qed.
theorem th6: ∀A. m (i A) = c (m (i A)). intros; auto. qed.

theorem th7: ∀A. i (m (i A)) = i (s (i A)).
