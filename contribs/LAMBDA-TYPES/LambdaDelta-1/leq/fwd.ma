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



include "leq/defs.ma".

theorem leq_gen_sort:
 \forall (g: G).(\forall (h1: nat).(\forall (n1: nat).(\forall (a2: A).((leq 
g (ASort h1 n1) a2) \to (ex2_3 nat nat nat (\lambda (n2: nat).(\lambda (h2: 
nat).(\lambda (_: nat).(eq A a2 (ASort h2 n2))))) (\lambda (n2: nat).(\lambda 
(h2: nat).(\lambda (k: nat).(eq A (aplus g (ASort h1 n1) k) (aplus g (ASort 
h2 n2) k))))))))))
\def
 \lambda (g: G).(\lambda (h1: nat).(\lambda (n1: nat).(\lambda (a2: 
A).(\lambda (H: (leq g (ASort h1 n1) a2)).(let H0 \def (match H in leq return 
(\lambda (a: A).(\lambda (a0: A).(\lambda (_: (leq ? a a0)).((eq A a (ASort 
h1 n1)) \to ((eq A a0 a2) \to (ex2_3 nat nat nat (\lambda (n2: nat).(\lambda 
(h2: nat).(\lambda (_: nat).(eq A a2 (ASort h2 n2))))) (\lambda (n2: 
nat).(\lambda (h2: nat).(\lambda (k: nat).(eq A (aplus g (ASort h1 n1) k) 
(aplus g (ASort h2 n2) k))))))))))) with [(leq_sort h0 h2 n0 n2 k H0) 
\Rightarrow (\lambda (H1: (eq A (ASort h0 n0) (ASort h1 n1))).(\lambda (H2: 
(eq A (ASort h2 n2) a2)).((let H3 \def (f_equal A nat (\lambda (e: A).(match 
e in A return (\lambda (_: A).nat) with [(ASort _ n) \Rightarrow n | (AHead _ 
_) \Rightarrow n0])) (ASort h0 n0) (ASort h1 n1) H1) in ((let H4 \def 
(f_equal A nat (\lambda (e: A).(match e in A return (\lambda (_: A).nat) with 
[(ASort n _) \Rightarrow n | (AHead _ _) \Rightarrow h0])) (ASort h0 n0) 
(ASort h1 n1) H1) in (eq_ind nat h1 (\lambda (n: nat).((eq nat n0 n1) \to 
((eq A (ASort h2 n2) a2) \to ((eq A (aplus g (ASort n n0) k) (aplus g (ASort 
h2 n2) k)) \to (ex2_3 nat nat nat (\lambda (n3: nat).(\lambda (h3: 
nat).(\lambda (_: nat).(eq A a2 (ASort h3 n3))))) (\lambda (n3: nat).(\lambda 
(h3: nat).(\lambda (k0: nat).(eq A (aplus g (ASort h1 n1) k0) (aplus g (ASort 
h3 n3) k0)))))))))) (\lambda (H5: (eq nat n0 n1)).(eq_ind nat n1 (\lambda (n: 
nat).((eq A (ASort h2 n2) a2) \to ((eq A (aplus g (ASort h1 n) k) (aplus g 
(ASort h2 n2) k)) \to (ex2_3 nat nat nat (\lambda (n3: nat).(\lambda (h3: 
nat).(\lambda (_: nat).(eq A a2 (ASort h3 n3))))) (\lambda (n3: nat).(\lambda 
(h3: nat).(\lambda (k0: nat).(eq A (aplus g (ASort h1 n1) k0) (aplus g (ASort 
h3 n3) k0))))))))) (\lambda (H6: (eq A (ASort h2 n2) a2)).(eq_ind A (ASort h2 
n2) (\lambda (a: A).((eq A (aplus g (ASort h1 n1) k) (aplus g (ASort h2 n2) 
k)) \to (ex2_3 nat nat nat (\lambda (n3: nat).(\lambda (h3: nat).(\lambda (_: 
nat).(eq A a (ASort h3 n3))))) (\lambda (n3: nat).(\lambda (h3: nat).(\lambda 
(k0: nat).(eq A (aplus g (ASort h1 n1) k0) (aplus g (ASort h3 n3) k0)))))))) 
(\lambda (H7: (eq A (aplus g (ASort h1 n1) k) (aplus g (ASort h2 n2) 
k))).(ex2_3_intro nat nat nat (\lambda (n3: nat).(\lambda (h3: nat).(\lambda 
(_: nat).(eq A (ASort h2 n2) (ASort h3 n3))))) (\lambda (n3: nat).(\lambda 
(h3: nat).(\lambda (k0: nat).(eq A (aplus g (ASort h1 n1) k0) (aplus g (ASort 
h3 n3) k0))))) n2 h2 k (refl_equal A (ASort h2 n2)) H7)) a2 H6)) n0 (sym_eq 
nat n0 n1 H5))) h0 (sym_eq nat h0 h1 H4))) H3)) H2 H0))) | (leq_head a1 a0 H0 
a3 a4 H1) \Rightarrow (\lambda (H2: (eq A (AHead a1 a3) (ASort h1 
n1))).(\lambda (H3: (eq A (AHead a0 a4) a2)).((let H4 \def (eq_ind A (AHead 
a1 a3) (\lambda (e: A).(match e in A return (\lambda (_: A).Prop) with 
[(ASort _ _) \Rightarrow False | (AHead _ _) \Rightarrow True])) I (ASort h1 
n1) H2) in (False_ind ((eq A (AHead a0 a4) a2) \to ((leq g a1 a0) \to ((leq g 
a3 a4) \to (ex2_3 nat nat nat (\lambda (n2: nat).(\lambda (h2: nat).(\lambda 
(_: nat).(eq A a2 (ASort h2 n2))))) (\lambda (n2: nat).(\lambda (h2: 
nat).(\lambda (k: nat).(eq A (aplus g (ASort h1 n1) k) (aplus g (ASort h2 n2) 
k))))))))) H4)) H3 H0 H1)))]) in (H0 (refl_equal A (ASort h1 n1)) (refl_equal 
A a2))))))).

theorem leq_gen_head:
 \forall (g: G).(\forall (a1: A).(\forall (a2: A).(\forall (a: A).((leq g 
(AHead a1 a2) a) \to (ex3_2 A A (\lambda (a3: A).(\lambda (a4: A).(eq A a 
(AHead a3 a4)))) (\lambda (a3: A).(\lambda (_: A).(leq g a1 a3))) (\lambda 
(_: A).(\lambda (a4: A).(leq g a2 a4))))))))
\def
 \lambda (g: G).(\lambda (a1: A).(\lambda (a2: A).(\lambda (a: A).(\lambda 
(H: (leq g (AHead a1 a2) a)).(let H0 \def (match H in leq return (\lambda 
(a0: A).(\lambda (a3: A).(\lambda (_: (leq ? a0 a3)).((eq A a0 (AHead a1 a2)) 
\to ((eq A a3 a) \to (ex3_2 A A (\lambda (a4: A).(\lambda (a5: A).(eq A a 
(AHead a4 a5)))) (\lambda (a4: A).(\lambda (_: A).(leq g a1 a4))) (\lambda 
(_: A).(\lambda (a5: A).(leq g a2 a5))))))))) with [(leq_sort h1 h2 n1 n2 k 
H0) \Rightarrow (\lambda (H1: (eq A (ASort h1 n1) (AHead a1 a2))).(\lambda 
(H2: (eq A (ASort h2 n2) a)).((let H3 \def (eq_ind A (ASort h1 n1) (\lambda 
(e: A).(match e in A return (\lambda (_: A).Prop) with [(ASort _ _) 
\Rightarrow True | (AHead _ _) \Rightarrow False])) I (AHead a1 a2) H1) in 
(False_ind ((eq A (ASort h2 n2) a) \to ((eq A (aplus g (ASort h1 n1) k) 
(aplus g (ASort h2 n2) k)) \to (ex3_2 A A (\lambda (a3: A).(\lambda (a4: 
A).(eq A a (AHead a3 a4)))) (\lambda (a3: A).(\lambda (_: A).(leq g a1 a3))) 
(\lambda (_: A).(\lambda (a4: A).(leq g a2 a4)))))) H3)) H2 H0))) | (leq_head 
a0 a3 H0 a4 a5 H1) \Rightarrow (\lambda (H2: (eq A (AHead a0 a4) (AHead a1 
a2))).(\lambda (H3: (eq A (AHead a3 a5) a)).((let H4 \def (f_equal A A 
(\lambda (e: A).(match e in A return (\lambda (_: A).A) with [(ASort _ _) 
\Rightarrow a4 | (AHead _ a6) \Rightarrow a6])) (AHead a0 a4) (AHead a1 a2) 
H2) in ((let H5 \def (f_equal A A (\lambda (e: A).(match e in A return 
(\lambda (_: A).A) with [(ASort _ _) \Rightarrow a0 | (AHead a6 _) 
\Rightarrow a6])) (AHead a0 a4) (AHead a1 a2) H2) in (eq_ind A a1 (\lambda 
(a6: A).((eq A a4 a2) \to ((eq A (AHead a3 a5) a) \to ((leq g a6 a3) \to 
((leq g a4 a5) \to (ex3_2 A A (\lambda (a7: A).(\lambda (a8: A).(eq A a 
(AHead a7 a8)))) (\lambda (a7: A).(\lambda (_: A).(leq g a1 a7))) (\lambda 
(_: A).(\lambda (a8: A).(leq g a2 a8))))))))) (\lambda (H6: (eq A a4 
a2)).(eq_ind A a2 (\lambda (a6: A).((eq A (AHead a3 a5) a) \to ((leq g a1 a3) 
\to ((leq g a6 a5) \to (ex3_2 A A (\lambda (a7: A).(\lambda (a8: A).(eq A a 
(AHead a7 a8)))) (\lambda (a7: A).(\lambda (_: A).(leq g a1 a7))) (\lambda 
(_: A).(\lambda (a8: A).(leq g a2 a8)))))))) (\lambda (H7: (eq A (AHead a3 
a5) a)).(eq_ind A (AHead a3 a5) (\lambda (a6: A).((leq g a1 a3) \to ((leq g 
a2 a5) \to (ex3_2 A A (\lambda (a7: A).(\lambda (a8: A).(eq A a6 (AHead a7 
a8)))) (\lambda (a7: A).(\lambda (_: A).(leq g a1 a7))) (\lambda (_: 
A).(\lambda (a8: A).(leq g a2 a8))))))) (\lambda (H8: (leq g a1 a3)).(\lambda 
(H9: (leq g a2 a5)).(ex3_2_intro A A (\lambda (a6: A).(\lambda (a7: A).(eq A 
(AHead a3 a5) (AHead a6 a7)))) (\lambda (a6: A).(\lambda (_: A).(leq g a1 
a6))) (\lambda (_: A).(\lambda (a7: A).(leq g a2 a7))) a3 a5 (refl_equal A 
(AHead a3 a5)) H8 H9))) a H7)) a4 (sym_eq A a4 a2 H6))) a0 (sym_eq A a0 a1 
H5))) H4)) H3 H0 H1)))]) in (H0 (refl_equal A (AHead a1 a2)) (refl_equal A 
a))))))).

