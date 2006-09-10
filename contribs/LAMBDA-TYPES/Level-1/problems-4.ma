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

(* Problematic objects for disambiguation/typechecking ********************)

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/problems".

include "LambdaDelta/theory.ma".

theorem leq_trans:
 \forall (g: G).(\forall (a1: A).(\forall (a2: A).((leq g a1 a2) \to (\forall 
(a3: A).((leq g a2 a3) \to (leq g a1 a3))))))
\def
 \lambda (g: G).(\lambda (a1: A).(\lambda (a2: A).(\lambda (H: (leq g a1 
a2)).(leq_ind g (\lambda (a: A).(\lambda (a0: A).(\forall (a3: A).((leq g a0 
a3) \to (leq g a a3))))) (\lambda (h1: nat).(\lambda (h2: nat).(\lambda (n1: 
nat).(\lambda (n2: nat).(\lambda (k: nat).(\lambda (H0: (eq A (aplus g (ASort 
h1 n1) k) (aplus g (ASort h2 n2) k))).(\lambda (a3: A).(\lambda (H1: (leq g 
(ASort h2 n2) a3)).(let H2 \def (match H1 in leq return (\lambda (a: 
A).(\lambda (a0: A).(\lambda (_: (leq ? a a0)).((eq A a (ASort h2 n2)) \to 
((eq A a0 a3) \to (leq g (ASort h1 n1) a3)))))) with [(leq_sort h0 h3 n0 n3 
k0 H2) \Rightarrow (\lambda (H3: (eq A (ASort h0 n0) (ASort h2 n2))).(\lambda 
(H4: (eq A (ASort h3 n3) a3)).((let H5 \def (f_equal A nat (\lambda (e: 
A).(match e in A return (\lambda (_: A).nat) with [(ASort _ n) \Rightarrow n 
| (AHead _ _) \Rightarrow n0])) (ASort h0 n0) (ASort h2 n2) H3) in ((let H6 
\def (f_equal A nat (\lambda (e: A).(match e in A return (\lambda (_: A).nat) 
with [(ASort n _) \Rightarrow n | (AHead _ _) \Rightarrow h0])) (ASort h0 n0) 
(ASort h2 n2) H3) in (eq_ind nat h2 (\lambda (n: nat).((eq nat n0 n2) \to 
((eq A (ASort h3 n3) a3) \to ((eq A (aplus g (ASort n n0) k0) (aplus g (ASort 
h3 n3) k0)) \to (leq g (ASort h1 n1) a3))))) (\lambda (H7: (eq nat n0 
n2)).(eq_ind nat n2 (\lambda (n: nat).((eq A (ASort h3 n3) a3) \to ((eq A 
(aplus g (ASort h2 n) k0) (aplus g (ASort h3 n3) k0)) \to (leq g (ASort h1 
n1) a3)))) (\lambda (H8: (eq A (ASort h3 n3) a3)).(eq_ind A (ASort h3 n3) 
(\lambda (a: A).((eq A (aplus g (ASort h2 n2) k0) (aplus g (ASort h3 n3) k0)) 
\to (leq g (ASort h1 n1) a))) (\lambda (H9: (eq A (aplus g (ASort h2 n2) k0) 
(aplus g (ASort h3 n3) k0))).(lt_le_e k k0 (leq g (ASort h1 n1) (ASort h3 
n3)) (\lambda (H10: (lt k k0)).(let H_y \def (aplus_reg_r g (ASort h1 n1) 
(ASort h2 n2) k k H0 (minus k0 k)) in (let H11 \def (eq_ind_r nat (plus 
(minus k0 k) k) (\lambda (n: nat).(eq A (aplus g (ASort h1 n1) n) (aplus g 
(ASort h2 n2) n))) H_y k0 (le_plus_minus_sym k k0 (le_S_n k k0 (le_S (S k) k0 
H10)))) in (leq_sort g h1 h3 n1 n3 k0 (trans_eq A (aplus g (ASort h1 n1) k0) 
(aplus g (ASort h2 n2) k0) (aplus g (ASort h3 n3) k0) H11 H9))))) (\lambda 
(H10: (le k0 k)).(let H_y \def (aplus_reg_r g (ASort h2 n2) (ASort h3 n3) k0 
k0 H9 (minus k k0)) in (let H11 \def (eq_ind_r nat (plus (minus k k0) k0) 
(\lambda (n: nat).(eq A (aplus g (ASort h2 n2) n) (aplus g (ASort h3 n3) n))) 
H_y k (le_plus_minus_sym k0 k H10)) in (leq_sort g h1 h3 n1 n3 k (trans_eq A 
(aplus g (ASort h1 n1) k) (aplus g (ASort h2 n2) k) (aplus g (ASort h3 n3) k) 
H0 H11))))))) a3 H8)) n0 (sym_eq nat n0 n2 H7))) h0 (sym_eq nat h0 h2 H6))) 
H5)) H4 H2))) | (leq_head a0 a4 H2 a5 a6 H3) \Rightarrow (\lambda (H4: (eq A 
(AHead a0 a5) (ASort h2 n2))).(\lambda (H5: (eq A (AHead a4 a6) a3)).((let H6 
\def (eq_ind A (AHead a0 a5) (\lambda (e: A).(match e in A return (\lambda 
(_: A).Prop) with [(ASort _ _) \Rightarrow False | (AHead _ _) \Rightarrow 
True])) I (ASort h2 n2) H4) in (False_ind ((eq A (AHead a4 a6) a3) \to ((leq 
g a0 a4) \to ((leq g a5 a6) \to (leq g (ASort h1 n1) a3)))) H6)) H5 H2 
H3)))]) in (H2 (refl_equal A (ASort h2 n2)) (refl_equal A a3))))))))))) 
(\lambda (a3: A).(\lambda (a4: A).(\lambda (_: (leq g a3 a4)).(\lambda (H1: 
((\forall (a5: A).((leq g a4 a5) \to (leq g a3 a5))))).(\lambda (a5: 
A).(\lambda (a6: A).(\lambda (_: (leq g a5 a6)).(\lambda (H3: ((\forall (a7: 
A).((leq g a6 a7) \to (leq g a5 a7))))).(\lambda (a0: A).(\lambda (H4: (leq g 
(AHead a4 a6) a0)).(let H5 \def (match H4 in leq return (\lambda (a: 
A).(\lambda (a7: A).(\lambda (_: (leq ? a a7)).((eq A a (AHead a4 a6)) \to 
((eq A a7 a0) \to (leq g (AHead a3 a5) a0)))))) with [(leq_sort h1 h2 n1 n2 k 
H5) \Rightarrow (\lambda (H6: (eq A (ASort h1 n1) (AHead a4 a6))).(\lambda 
(H7: (eq A (ASort h2 n2) a0)).((let H8 \def (eq_ind A (ASort h1 n1) (\lambda 
(e: A).(match e in A return (\lambda (_: A).Prop) with [(ASort _ _) 
\Rightarrow True | (AHead _ _) \Rightarrow False])) I (AHead a4 a6) H6) in 
(False_ind ((eq A (ASort h2 n2) a0) \to ((eq A (aplus g (ASort h1 n1) k) 
(aplus g (ASort h2 n2) k)) \to (leq g (AHead a3 a5) a0))) H8)) H7 H5))) | 
(leq_head a7 a8 H5 a9 a10 H6) \Rightarrow (\lambda (H7: (eq A (AHead a7 a9) 
(AHead a4 a6))).(\lambda (H8: (eq A (AHead a8 a10) a0)).((let H9 \def 
(f_equal A A (\lambda (e: A).(match e in A return (\lambda (_: A).A) with 
[(ASort _ _) \Rightarrow a9 | (AHead _ a) \Rightarrow a])) (AHead a7 a9) 
(AHead a4 a6) H7) in ((let H10 \def (f_equal A A (\lambda (e: A).(match e in 
A return (\lambda (_: A).A) with [(ASort _ _) \Rightarrow a7 | (AHead a _) 
\Rightarrow a])) (AHead a7 a9) (AHead a4 a6) H7) in (eq_ind A a4 (\lambda (a: 
A).((eq A a9 a6) \to ((eq A (AHead a8 a10) a0) \to ((leq g a a8) \to ((leq g 
a9 a10) \to (leq g (AHead a3 a5) a0)))))) (\lambda (H11: (eq A a9 
a6)).(eq_ind A a6 (\lambda (a: A).((eq A (AHead a8 a10) a0) \to ((leq g a4 
a8) \to ((leq g a a10) \to (leq g (AHead a3 a5) a0))))) (\lambda (H12: (eq A 
(AHead a8 a10) a0)).(eq_ind A (AHead a8 a10) (\lambda (a: A).((leq g a4 a8) 
\to ((leq g a6 a10) \to (leq g (AHead a3 a5) a)))) (\lambda (H13: (leq g a4 
a8)).(\lambda (H14: (leq g a6 a10)).(leq_head g a3 a8 (H1 a8 H13) a5 a10 (H3 
a10 H14)))) a0 H12)) a9 (sym_eq A a9 a6 H11))) a7 (sym_eq A a7 a4 H10))) H9)) 
H8 H5 H6)))]) in (H5 (refl_equal A (AHead a4 a6)) (refl_equal A 
a0))))))))))))) a1 a2 H)))).
