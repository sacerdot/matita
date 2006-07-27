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

set "baseuri" "cic:/matita/test/decl".

include "nat/times.ma".
include "nat/orders.ma".

theorem easy: ∀n,m. n * m = O → n = O ∨ m = O.
 assume n: nat.
 assume m: nat.
 (* base case *)
 by (refl_eq ? O) we proved (O = O) (trivial).
 by (or_introl ? ? trivial) we proved (O = O ∨ m = O) (trivial2).
 by (λ_.trivial2) we proved (O*m=O → O=O ∨ m=O) (base_case).
 (* inductive case *)
 we need to prove
  (∀n1. (n1 * m = O → n1 = O ∨ m = O) → (S n1) * m = O → (S n1) = O ∨ m = O)
  (inductive_case).
   assume n1: nat.
   suppose (n1 * m = O → n1 = O ∨ m = O) (inductive_hyp).
   (* base case *)
   by (or_intror ? ? trivial) we proved (S n1 = O ∨ O = O) (pre_base_case2).
   by (λ_.pre_base_case2) we proved (S n1*O = O → S n1 = O ∨ O = O) (base_case2).
   (* inductive case *)
   we need to prove
    (∀m1. (S n1 * m1 = O → S n1 = O ∨ m1 = O) →
      (S n1 * S m1 = O → S n1 = O ∨ S m1 = O)) (inductive_hyp2).
     assume m1: nat.
     suppose (S n1 * m1 = O → S n1 = O ∨ m1 = O) (useless).
     suppose (S n1 * S m1 = O) (absurd_hyp).
     simplify in absurd_hyp.
     by (sym_eq ? ? ? absurd_hyp) we proved (O = S (m1+n1*S m1)) (absurd_hyp').
     by (not_eq_O_S ? absurd_hyp') we proved False (the_absurd).
     by (False_ind ? the_absurd)
   done.
   (* the induction *)
   by (nat_ind (λm.S n1 * m = O → S n1 = O ∨ m = O) base_case2 inductive_hyp2 m)
 done.
 (* the induction *)
 by (nat_ind (λn.n*m=O → n=O ∨ m=O) base_case inductive_case n)
done.
qed.
 
theorem easy2: ∀n,m. n * m = O → n = O ∨ m = O.
 intros 2.
 elim n 0
  [ intro;
    left;
    reflexivity
  | intro;
    elim m 0
    [ intros;
      right;
      reflexivity
    | intros;
      simplify in H2;
      lapply (sym_eq ? ? ? H2);
      elim (not_eq_O_S ? Hletin)
    ]
  ]
qed.


theorem easy3: ∀A:Prop. (A ∧ ∃n:nat.n ≠ n) → True.
 assume P: Prop.
 suppose (P ∧ ∃m:nat.m ≠ m) (H).
 by H we have P (H1) and (∃x:nat.x≠x) (H2).
 (*BUG:
 by H2 let q:nat such that (q ≠ q) (Ineq).
 *)
 (* the next line is wrong, but for the moment it does the job *)
 by H2 let q:nat such that False (Ineq).
 by I done.
qed.

theorem easy4: ∀n,m,p. n = m → S m = S p → n = S p → S n = n.
assume n: nat.
assume m:nat.
assume p:nat.
suppose (n=m) (H).
suppose (S m = S p) (K).
suppose (n = S p) (L).
obtain (S n) = (S m) by (eq_f ? ? ? ? ? H).
             = (S p) by K.
             = n by (sym_eq ? ? ? L)
done.
qed.
