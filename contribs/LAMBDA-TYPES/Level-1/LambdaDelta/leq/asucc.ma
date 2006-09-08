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

(* This file was automatically generated: do not edit *********************)

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/leq/asucc".

include "leq/defs.ma".

include "aplus/props.ma".

theorem asucc_repl:
 \forall (g: G).(\forall (a1: A).(\forall (a2: A).((leq g a1 a2) \to (leq g 
(asucc g a1) (asucc g a2)))))
\def
 \lambda (g: G).(\lambda (a1: A).(\lambda (a2: A).(\lambda (H: (leq g a1 
a2)).(leq_ind g (\lambda (a: A).(\lambda (a0: A).(leq g (asucc g a) (asucc g 
a0)))) (\lambda (h1: nat).(\lambda (h2: nat).(\lambda (n1: nat).(\lambda (n2: 
nat).(\lambda (k: nat).(\lambda (H0: (eq A (aplus g (ASort h1 n1) k) (aplus g 
(ASort h2 n2) k))).((match h1 in nat return (\lambda (n: nat).((eq A (aplus g 
(ASort n n1) k) (aplus g (ASort h2 n2) k)) \to (leq g (match n with [O 
\Rightarrow (ASort O (next g n1)) | (S h) \Rightarrow (ASort h n1)]) (match 
h2 with [O \Rightarrow (ASort O (next g n2)) | (S h) \Rightarrow (ASort h 
n2)])))) with [O \Rightarrow (\lambda (H1: (eq A (aplus g (ASort O n1) k) 
(aplus g (ASort h2 n2) k))).((match h2 in nat return (\lambda (n: nat).((eq A 
(aplus g (ASort O n1) k) (aplus g (ASort n n2) k)) \to (leq g (ASort O (next 
g n1)) (match n with [O \Rightarrow (ASort O (next g n2)) | (S h) \Rightarrow 
(ASort h n2)])))) with [O \Rightarrow (\lambda (H2: (eq A (aplus g (ASort O 
n1) k) (aplus g (ASort O n2) k))).(leq_sort g O O (next g n1) (next g n2) k 
(eq_ind A (aplus g (ASort O n1) (S k)) (\lambda (a: A).(eq A a (aplus g 
(ASort O (next g n2)) k))) (eq_ind A (aplus g (ASort O n2) (S k)) (\lambda 
(a: A).(eq A (aplus g (ASort O n1) (S k)) a)) (eq_ind_r A (aplus g (ASort O 
n2) k) (\lambda (a: A).(eq A (asucc g a) (asucc g (aplus g (ASort O n2) k)))) 
(refl_equal A (asucc g (aplus g (ASort O n2) k))) (aplus g (ASort O n1) k) 
H2) (aplus g (ASort O (next g n2)) k) (aplus_sort_O_S_simpl g n2 k)) (aplus g 
(ASort O (next g n1)) k) (aplus_sort_O_S_simpl g n1 k)))) | (S n) \Rightarrow 
(\lambda (H2: (eq A (aplus g (ASort O n1) k) (aplus g (ASort (S n) n2) 
k))).(leq_sort g O n (next g n1) n2 k (eq_ind A (aplus g (ASort O n1) (S k)) 
(\lambda (a: A).(eq A a (aplus g (ASort n n2) k))) (eq_ind A (aplus g (ASort 
(S n) n2) (S k)) (\lambda (a: A).(eq A (aplus g (ASort O n1) (S k)) a)) 
(eq_ind_r A (aplus g (ASort (S n) n2) k) (\lambda (a: A).(eq A (asucc g a) 
(asucc g (aplus g (ASort (S n) n2) k)))) (refl_equal A (asucc g (aplus g 
(ASort (S n) n2) k))) (aplus g (ASort O n1) k) H2) (aplus g (ASort n n2) k) 
(aplus_sort_S_S_simpl g n2 n k)) (aplus g (ASort O (next g n1)) k) 
(aplus_sort_O_S_simpl g n1 k))))]) H1)) | (S n) \Rightarrow (\lambda (H1: (eq 
A (aplus g (ASort (S n) n1) k) (aplus g (ASort h2 n2) k))).((match h2 in nat 
return (\lambda (n0: nat).((eq A (aplus g (ASort (S n) n1) k) (aplus g (ASort 
n0 n2) k)) \to (leq g (ASort n n1) (match n0 with [O \Rightarrow (ASort O 
(next g n2)) | (S h) \Rightarrow (ASort h n2)])))) with [O \Rightarrow 
(\lambda (H2: (eq A (aplus g (ASort (S n) n1) k) (aplus g (ASort O n2) 
k))).(leq_sort g n O n1 (next g n2) k (eq_ind A (aplus g (ASort O n2) (S k)) 
(\lambda (a: A).(eq A (aplus g (ASort n n1) k) a)) (eq_ind A (aplus g (ASort 
(S n) n1) (S k)) (\lambda (a: A).(eq A a (aplus g (ASort O n2) (S k)))) 
(eq_ind_r A (aplus g (ASort O n2) k) (\lambda (a: A).(eq A (asucc g a) (asucc 
g (aplus g (ASort O n2) k)))) (refl_equal A (asucc g (aplus g (ASort O n2) 
k))) (aplus g (ASort (S n) n1) k) H2) (aplus g (ASort n n1) k) 
(aplus_sort_S_S_simpl g n1 n k)) (aplus g (ASort O (next g n2)) k) 
(aplus_sort_O_S_simpl g n2 k)))) | (S n0) \Rightarrow (\lambda (H2: (eq A 
(aplus g (ASort (S n) n1) k) (aplus g (ASort (S n0) n2) k))).(leq_sort g n n0 
n1 n2 k (eq_ind A (aplus g (ASort (S n) n1) (S k)) (\lambda (a: A).(eq A a 
(aplus g (ASort n0 n2) k))) (eq_ind A (aplus g (ASort (S n0) n2) (S k)) 
(\lambda (a: A).(eq A (aplus g (ASort (S n) n1) (S k)) a)) (eq_ind_r A (aplus 
g (ASort (S n0) n2) k) (\lambda (a: A).(eq A (asucc g a) (asucc g (aplus g 
(ASort (S n0) n2) k)))) (refl_equal A (asucc g (aplus g (ASort (S n0) n2) 
k))) (aplus g (ASort (S n) n1) k) H2) (aplus g (ASort n0 n2) k) 
(aplus_sort_S_S_simpl g n2 n0 k)) (aplus g (ASort n n1) k) 
(aplus_sort_S_S_simpl g n1 n k))))]) H1))]) H0))))))) (\lambda (a3: 
A).(\lambda (a4: A).(\lambda (H0: (leq g a3 a4)).(\lambda (_: (leq g (asucc g 
a3) (asucc g a4))).(\lambda (a5: A).(\lambda (a6: A).(\lambda (_: (leq g a5 
a6)).(\lambda (H3: (leq g (asucc g a5) (asucc g a6))).(leq_head g a3 a4 H0 
(asucc g a5) (asucc g a6) H3))))))))) a1 a2 H)))).

axiom asucc_inj:
 \forall (g: G).(\forall (a1: A).(\forall (a2: A).((leq g (asucc g a1) (asucc 
g a2)) \to (leq g a1 a2))))
.

