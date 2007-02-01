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

set "baseuri" "cic:/matita/LAMBDA-TYPES/LambdaDelta-1/wcpr0/fwd".

include "wcpr0/defs.ma".

theorem wcpr0_gen_sort:
 \forall (x: C).(\forall (n: nat).((wcpr0 (CSort n) x) \to (eq C x (CSort 
n))))
\def
 \lambda (x: C).(\lambda (n: nat).(\lambda (H: (wcpr0 (CSort n) x)).(let H0 
\def (match H in wcpr0 return (\lambda (c: C).(\lambda (c0: C).(\lambda (_: 
(wcpr0 c c0)).((eq C c (CSort n)) \to ((eq C c0 x) \to (eq C x (CSort 
n))))))) with [(wcpr0_refl c) \Rightarrow (\lambda (H0: (eq C c (CSort 
n))).(\lambda (H1: (eq C c x)).(eq_ind C (CSort n) (\lambda (c0: C).((eq C c0 
x) \to (eq C x (CSort n)))) (\lambda (H2: (eq C (CSort n) x)).(eq_ind C 
(CSort n) (\lambda (c0: C).(eq C c0 (CSort n))) (refl_equal C (CSort n)) x 
H2)) c (sym_eq C c (CSort n) H0) H1))) | (wcpr0_comp c1 c2 H0 u1 u2 H1 k) 
\Rightarrow (\lambda (H2: (eq C (CHead c1 k u1) (CSort n))).(\lambda (H3: (eq 
C (CHead c2 k u2) x)).((let H4 \def (eq_ind C (CHead c1 k u1) (\lambda (e: 
C).(match e in C return (\lambda (_: C).Prop) with [(CSort _) \Rightarrow 
False | (CHead _ _ _) \Rightarrow True])) I (CSort n) H2) in (False_ind ((eq 
C (CHead c2 k u2) x) \to ((wcpr0 c1 c2) \to ((pr0 u1 u2) \to (eq C x (CSort 
n))))) H4)) H3 H0 H1)))]) in (H0 (refl_equal C (CSort n)) (refl_equal C 
x))))).

theorem wcpr0_gen_head:
 \forall (k: K).(\forall (c1: C).(\forall (x: C).(\forall (u1: T).((wcpr0 
(CHead c1 k u1) x) \to (or (eq C x (CHead c1 k u1)) (ex3_2 C T (\lambda (c2: 
C).(\lambda (u2: T).(eq C x (CHead c2 k u2)))) (\lambda (c2: C).(\lambda (_: 
T).(wcpr0 c1 c2))) (\lambda (_: C).(\lambda (u2: T).(pr0 u1 u2)))))))))
\def
 \lambda (k: K).(\lambda (c1: C).(\lambda (x: C).(\lambda (u1: T).(\lambda 
(H: (wcpr0 (CHead c1 k u1) x)).(let H0 \def (match H in wcpr0 return (\lambda 
(c: C).(\lambda (c0: C).(\lambda (_: (wcpr0 c c0)).((eq C c (CHead c1 k u1)) 
\to ((eq C c0 x) \to (or (eq C x (CHead c1 k u1)) (ex3_2 C T (\lambda (c2: 
C).(\lambda (u2: T).(eq C x (CHead c2 k u2)))) (\lambda (c2: C).(\lambda (_: 
T).(wcpr0 c1 c2))) (\lambda (_: C).(\lambda (u2: T).(pr0 u1 u2)))))))))) with 
[(wcpr0_refl c) \Rightarrow (\lambda (H0: (eq C c (CHead c1 k u1))).(\lambda 
(H1: (eq C c x)).(eq_ind C (CHead c1 k u1) (\lambda (c0: C).((eq C c0 x) \to 
(or (eq C x (CHead c1 k u1)) (ex3_2 C T (\lambda (c2: C).(\lambda (u2: T).(eq 
C x (CHead c2 k u2)))) (\lambda (c2: C).(\lambda (_: T).(wcpr0 c1 c2))) 
(\lambda (_: C).(\lambda (u2: T).(pr0 u1 u2))))))) (\lambda (H2: (eq C (CHead 
c1 k u1) x)).(eq_ind C (CHead c1 k u1) (\lambda (c0: C).(or (eq C c0 (CHead 
c1 k u1)) (ex3_2 C T (\lambda (c2: C).(\lambda (u2: T).(eq C c0 (CHead c2 k 
u2)))) (\lambda (c2: C).(\lambda (_: T).(wcpr0 c1 c2))) (\lambda (_: 
C).(\lambda (u2: T).(pr0 u1 u2)))))) (or_introl (eq C (CHead c1 k u1) (CHead 
c1 k u1)) (ex3_2 C T (\lambda (c2: C).(\lambda (u2: T).(eq C (CHead c1 k u1) 
(CHead c2 k u2)))) (\lambda (c2: C).(\lambda (_: T).(wcpr0 c1 c2))) (\lambda 
(_: C).(\lambda (u2: T).(pr0 u1 u2)))) (refl_equal C (CHead c1 k u1))) x H2)) 
c (sym_eq C c (CHead c1 k u1) H0) H1))) | (wcpr0_comp c0 c2 H0 u0 u2 H1 k0) 
\Rightarrow (\lambda (H2: (eq C (CHead c0 k0 u0) (CHead c1 k u1))).(\lambda 
(H3: (eq C (CHead c2 k0 u2) x)).((let H4 \def (f_equal C T (\lambda (e: 
C).(match e in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow u0 | 
(CHead _ _ t) \Rightarrow t])) (CHead c0 k0 u0) (CHead c1 k u1) H2) in ((let 
H5 \def (f_equal C K (\lambda (e: C).(match e in C return (\lambda (_: C).K) 
with [(CSort _) \Rightarrow k0 | (CHead _ k1 _) \Rightarrow k1])) (CHead c0 
k0 u0) (CHead c1 k u1) H2) in ((let H6 \def (f_equal C C (\lambda (e: 
C).(match e in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow c0 | 
(CHead c _ _) \Rightarrow c])) (CHead c0 k0 u0) (CHead c1 k u1) H2) in 
(eq_ind C c1 (\lambda (c: C).((eq K k0 k) \to ((eq T u0 u1) \to ((eq C (CHead 
c2 k0 u2) x) \to ((wcpr0 c c2) \to ((pr0 u0 u2) \to (or (eq C x (CHead c1 k 
u1)) (ex3_2 C T (\lambda (c3: C).(\lambda (u3: T).(eq C x (CHead c3 k u3)))) 
(\lambda (c3: C).(\lambda (_: T).(wcpr0 c1 c3))) (\lambda (_: C).(\lambda 
(u3: T).(pr0 u1 u3))))))))))) (\lambda (H7: (eq K k0 k)).(eq_ind K k (\lambda 
(k1: K).((eq T u0 u1) \to ((eq C (CHead c2 k1 u2) x) \to ((wcpr0 c1 c2) \to 
((pr0 u0 u2) \to (or (eq C x (CHead c1 k u1)) (ex3_2 C T (\lambda (c3: 
C).(\lambda (u3: T).(eq C x (CHead c3 k u3)))) (\lambda (c3: C).(\lambda (_: 
T).(wcpr0 c1 c3))) (\lambda (_: C).(\lambda (u3: T).(pr0 u1 u3)))))))))) 
(\lambda (H8: (eq T u0 u1)).(eq_ind T u1 (\lambda (t: T).((eq C (CHead c2 k 
u2) x) \to ((wcpr0 c1 c2) \to ((pr0 t u2) \to (or (eq C x (CHead c1 k u1)) 
(ex3_2 C T (\lambda (c3: C).(\lambda (u3: T).(eq C x (CHead c3 k u3)))) 
(\lambda (c3: C).(\lambda (_: T).(wcpr0 c1 c3))) (\lambda (_: C).(\lambda 
(u3: T).(pr0 u1 u3))))))))) (\lambda (H9: (eq C (CHead c2 k u2) x)).(eq_ind C 
(CHead c2 k u2) (\lambda (c: C).((wcpr0 c1 c2) \to ((pr0 u1 u2) \to (or (eq C 
c (CHead c1 k u1)) (ex3_2 C T (\lambda (c3: C).(\lambda (u3: T).(eq C c 
(CHead c3 k u3)))) (\lambda (c3: C).(\lambda (_: T).(wcpr0 c1 c3))) (\lambda 
(_: C).(\lambda (u3: T).(pr0 u1 u3)))))))) (\lambda (H10: (wcpr0 c1 
c2)).(\lambda (H11: (pr0 u1 u2)).(or_intror (eq C (CHead c2 k u2) (CHead c1 k 
u1)) (ex3_2 C T (\lambda (c3: C).(\lambda (u3: T).(eq C (CHead c2 k u2) 
(CHead c3 k u3)))) (\lambda (c3: C).(\lambda (_: T).(wcpr0 c1 c3))) (\lambda 
(_: C).(\lambda (u3: T).(pr0 u1 u3)))) (ex3_2_intro C T (\lambda (c3: 
C).(\lambda (u3: T).(eq C (CHead c2 k u2) (CHead c3 k u3)))) (\lambda (c3: 
C).(\lambda (_: T).(wcpr0 c1 c3))) (\lambda (_: C).(\lambda (u3: T).(pr0 u1 
u3))) c2 u2 (refl_equal C (CHead c2 k u2)) H10 H11)))) x H9)) u0 (sym_eq T u0 
u1 H8))) k0 (sym_eq K k0 k H7))) c0 (sym_eq C c0 c1 H6))) H5)) H4)) H3 H0 
H1)))]) in (H0 (refl_equal C (CHead c1 k u1)) (refl_equal C x))))))).

