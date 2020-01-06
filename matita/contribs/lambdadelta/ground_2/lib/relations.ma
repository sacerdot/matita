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

include "basics/relations.ma".
include "ground_2/xoa/and_3.ma".
include "ground_2/xoa/ex_2_2.ma".
include "ground_2/lib/logic.ma".

(* GENERIC RELATIONS ********************************************************)

definition replace_2 (A) (B): relation3 (relation2 A B) (relation A) (relation B) ≝
           λR,Sa,Sb. ∀a1,b1. R a1 b1 → ∀a2. Sa a1 a2 → ∀b2. Sb b1 b2 → R a2 b2.

(* Inclusion ****************************************************************)

definition subR2 (S1) (S2): relation (relation2 S1 S2) ≝
           λR1,R2. (∀a1,a2. R1 a1 a2 → R2 a1 a2).

interpretation "2-relation inclusion"
   'subseteq R1 R2 = (subR2 ?? R1 R2).

definition subR3 (S1) (S2) (S3): relation (relation3 S1 S2 S3) ≝
           λR1,R2. (∀a1,a2,a3. R1 a1 a2 a3 → R2 a1 a2 a3).

interpretation "3-relation inclusion"
   'subseteq R1 R2 = (subR3 ??? R1 R2).

(* Properties of relations **************************************************)

definition relation5: Type[0] → Type[0] → Type[0] → Type[0] → Type[0] → Type[0] ≝
           λA,B,C,D,E.A→B→C→D→E→Prop.

definition relation6: Type[0] → Type[0] → Type[0] → Type[0] → Type[0] → Type[0] → Type[0] ≝
           λA,B,C,D,E,F.A→B→C→D→E→F→Prop.

(**) (* we don't use "∀a. reflexive … (R a)" since auto seems to dislike repeatd δ-expansion *)
definition c_reflexive (A) (B): predicate (relation3 A B B) ≝
           λR. ∀a,b. R a b b.

definition Decidable: Prop → Prop ≝ λR. R ∨ (R → ⊥).

definition Transitive (A) (R:relation A): Prop ≝
           ∀a1,a0. R a1 a0 → ∀a2. R a0 a2 → R a1 a2.

definition left_cancellable (A) (R:relation A): Prop ≝
           ∀a0,a1. R a0 a1 → ∀a2. R a0 a2 → R a1 a2.

definition right_cancellable (A) (R:relation A): Prop ≝
           ∀a1,a0. R a1 a0 → ∀a2. R a2 a0 → R a1 a2.

definition pw_confluent2 (A) (R1,R2:relation A): predicate A ≝
           λa0.
           ∀a1. R1 a0 a1 → ∀a2. R2 a0 a2 →
           ∃∃a. R2 a1 a & R1 a2 a.

definition confluent2 (A): relation (relation A) ≝
           λR1,R2.
           ∀a0. pw_confluent2 A R1 R2 a0.

definition transitive2 (A) (R1,R2:relation A): Prop ≝
           ∀a1,a0. R1 a1 a0 → ∀a2. R2 a0 a2 →
           ∃∃a. R2 a1 a & R1 a a2.

definition bi_confluent (A) (B) (R: bi_relation A B): Prop ≝
           ∀a0,a1,b0,b1. R a0 b0 a1 b1 → ∀a2,b2. R a0 b0 a2 b2 →
           ∃∃a,b. R a1 b1 a b & R a2 b2 a b.

definition lsub_trans (A) (B): relation2 (A→relation B) (relation A) ≝
           λR1,R2.
           ∀L2,T1,T2. R1 L2 T1 T2 → ∀L1. R2 L1 L2 → R1 L1 T1 T2.

definition s_r_confluent1 (A) (B): relation2 (A→relation B) (B→relation A) ≝
           λR1,R2.
           ∀L1,T1,T2. R1 L1 T1 T2 → ∀L2. R2 T1 L1 L2 → R2 T2 L1 L2.

definition is_mono (B:Type[0]): predicate (predicate B) ≝
           λR. ∀b1. R b1 → ∀b2. R b2 → b1 = b2.

definition is_inj2 (A,B:Type[0]): predicate (relation2 A B) ≝
           λR. ∀a1,b. R a1 b → ∀a2. R a2 b → a1 = a2.

(* Main properties of equality **********************************************)

theorem canc_sn_eq (A): left_cancellable A (eq …).
// qed-.

theorem canc_dx_eq (A): right_cancellable A (eq …).
// qed-.

(* Normal form and strong normalization *************************************)

definition NF (A): relation A → relation A → predicate A ≝
           λR,S,a1. ∀a2. R a1 a2 → S a1 a2.

definition NF_dec (A): relation A → relation A → Prop ≝
           λR,S. ∀a1. NF A R S a1 ∨
           ∃∃a2. R … a1 a2 & (S a1 a2 → ⊥).

inductive SN (A) (R,S:relation A): predicate A ≝
| SN_intro: ∀a1. (∀a2. R a1 a2 → (S a1 a2 → ⊥) → SN A R S a2) → SN A R S a1
.

lemma NF_to_SN (A) (R) (S): ∀a. NF A R S a → SN A R S a.
#A #R #S #a1 #Ha1
@SN_intro #a2 #HRa12 #HSa12
elim HSa12 -HSa12 /2 width=1 by/
qed.

definition NF_sn (A): relation A → relation A → predicate A ≝
   λR,S,a2. ∀a1. R a1 a2 → S a1 a2.

inductive SN_sn (A) (R,S:relation A): predicate A ≝
| SN_sn_intro: ∀a2. (∀a1. R a1 a2 → (S a1 a2 → ⊥) → SN_sn A R S a1) → SN_sn A R S a2
.

lemma NF_to_SN_sn (A) (R) (S): ∀a. NF_sn A R S a → SN_sn A R S a.
#A #R #S #a2 #Ha2
@SN_sn_intro #a1 #HRa12 #HSa12
elim HSa12 -HSa12 /2 width=1 by/
qed.

(* Relations on unboxed triples *********************************************)

definition tri_RC (A,B,C): tri_relation A B C → tri_relation A B C ≝
           λR,a1,b1,c1,a2,b2,c2.
           ∨∨ R … a1 b1 c1 a2 b2 c2
            | ∧∧ a1 = a2 & b1 = b2 & c1 = c2.

lemma tri_RC_reflexive (A) (B) (C): ∀R. tri_reflexive A B C (tri_RC … R).
/3 width=1 by and3_intro, or_intror/ qed.
