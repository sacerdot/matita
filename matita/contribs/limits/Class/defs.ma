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

include "preamble.ma".

(* CLASSES:
   - We use typoids with a compatible membership relation
   - The category is intended to be the domain of the membership relation
   - The membership relation is necessary because we need to regard the
     domain of a propositional function (ie a predicative subset) as a
     quantification domain and therefore as a category, but there is no
     type in CIC representing the domain of a propositional function
   - We set up a single equality predicate, parametric on the category,
     defined as the reflexive, symmetic, transitive and compatible closure
     of the "ces" (class equality step) predicate given inside the category.
*) 

record Class: Type ≝ {
   class     :> Type;
   cin       :  class → Prop;
   ces       :  class → class → Prop;
   ces_cin_fw:  ∀c1,c2. cin c1 → ces c1 c2 → cin c2;
   ces_cin_bw:  ∀c1,c2. cin c1 → ces c2 c1 → cin c2
}.

(* equality predicate *******************************************************)

inductive ceq (C:Class): class C → class C → Prop ≝
   | ceq_refl : ∀c. ceq ? c c
   | ceq_trans: ∀c1,c,c2. ces ? c1 c → ceq ? c c2 → ceq ? c1 c2
   | ceq_conf : ∀c1,c,c2. ces ? c c1 → ceq ? c c2 → ceq ? c1 c2
.

(* default inhabitance predicates *******************************************)

definition true_f ≝ λX:Type. λ_:X. True.

definition false_f ≝ λX:Type. λ_:X. False.

(* default foreward compatibilities *****************************************)

theorem const_fw: ∀A:Prop. ∀X:Type. ∀P:X→X→Prop. ∀x1,x2. A → P x1 x2 → A.
intros; autobatch.
qed.

definition true_fw ≝ const_fw True.

definition false_fw ≝ const_fw False.

(* default backward compatibilities *****************************************)

theorem const_bw: ∀A:Prop. ∀X:Type. ∀P:X→X→Prop. ∀x1,x2. A → P x2 x1 → A.
intros; autobatch.
qed.

definition true_bw ≝ const_bw True.

definition false_bw ≝ const_bw False.
