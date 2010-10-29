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

include "logic/connectives.ma".

inductive eq (A: Type[1]) (a: A) : A → CProp[0] ≝
 refl: eq A a a. 

interpretation "leibnitz's equality" 'eq t x y = (eq t x y).
 
lemma eq_ind_CProp0 : ∀A:Type[1].∀a:A.∀P:A → CProp[0].P a → ∀b:A.a = b → P b.
#A; #a; #P; #p; #b; #E; cases E; assumption;
qed.

lemma eq_ind_r_CProp0 : ∀A:Type[1].∀a:A.∀P:A → CProp[0].P a → ∀b:A.b = a → P b.
#A; #a; #P; #p; #b; #E; cases E in p; //;
qed. 

lemma csc : 
 (∀x,y,z.(x∨(y∨z)) = ((x∨y)∨z)) →
 (∀x,y,z.(x∧(y∧z)) = ((x∧y)∧z)) →
 (∀x,y.(x∨y) = (y∨x)) →
 (∀x,y.(x∧y) = (y∧x)) →
 (∀x,y,z.(x∧(y∨z)) = ((x∧y)∨(x∧z))) →
 (∀x.(x∨False) = (x)) →
 (∀x.(x∧True) = (x)) →
 (∀x.(x∧False) = (False)) →
 (∀x.(x∨x) = (x)) →
 (∀x.(x∧x) = (x)) →
 (∀x,y.(x∧(x∨y)) = (x)) →
 (∀x,y.(x∨(x∧y)) = (x)) →
 (∀x,y,z.(x∨(y∧z)) = ((x∨y)∧(x∨z))) →
 (∀x.(x∨True) = (True)) →
 (∀x.(x∧¬x) = (False)) →
 (∀x.(x∨¬x) = (True)) →
 ∀a,b.((a ∧ ¬b) ∨ b) = (a ∨ b).
#H1; #H2; #H3; #H4; #H5; #H6; #H7; #H8; #H9; #H10; #H11; #H12;
#H13; #H14; #H15; #H16; #a; #b;
letin proof ≝ (
let clause_11: ∀x24. eq CProp[0] (And x24 True) x24
 ≝ λx24. H7 x24 in
 let clause_2: ∀x2. eq CProp[0] (Or x2 (Not x2)) True
  ≝ λx2. H16 x2 in
  let clause_5:
   ∀x8.
    ∀x9.
     ∀x10.
      eq CProp[0] (Or x8 (And x9 x10)) (And (Or x8 x9) (Or x8 x10))
   ≝ λx8. λx9. λx10. H13 x8 x9 x10
   in
   let clause_15:
    ∀x35.
     ∀x36. eq CProp[0] (Or x35 x36) (Or x36 x35)
    ≝ λx35. λx36. H3 x35 x36 in
    let clause_194: eq CProp[0] (Or a b) (Or a b)
     ≝ refl ?? in
     let clause_193: eq CProp[0] (And (Or a b) True) (Or a b)
      ≝ eq_ind_r_CProp0 CProp[0] (Or a b)
            (λx:CProp[0]. eq CProp[0] x (Or a b)) clause_194
            (And (Or a b) True) (clause_11 (Or a b)) in
      let clause_192: eq CProp[0] (And (Or a b) (Or b (Not b))) (Or a b)
       ≝ eq_ind_r_CProp0 CProp[0] True
             (λx:CProp[0]. eq CProp[0] (And (Or a b) x) (Or a b)) clause_193
             (Or b (Not b)) (clause_2 b) in
       let clause_191: eq CProp[0] (And (Or b a) (Or b (Not b))) (Or a b)
        ≝ eq_ind_r_CProp0 CProp[0] (Or a b)
              (λx:CProp[0]. eq CProp[0] (And x (Or b (Not b))) (Or a b))
              clause_192 (Or b a) (clause_15 b a) in
        let clause_190: eq CProp[0] (Or b (And a (Not b))) (Or a b)
         ≝ eq_ind_r_CProp0 CProp[0] (And (Or b a) (Or b (Not b)))
               (λx:CProp[0]. eq CProp[0] x (Or a b)) clause_191
               (Or b (And a (Not b))) (clause_5 b a (Not b)) in
         let clause_1: eq CProp[0] (Or (And a (Not b)) b) (Or a b)
          ≝ eq_ind_r_CProp0 CProp[0] (Or b (And a (Not b)))
                (λx:CProp[0]. eq CProp[0] x (Or a b)) clause_190
                (Or (And a (Not b)) b) (clause_15 (And a (Not b)) b) in
          clause_1);
apply proof;
qed.
