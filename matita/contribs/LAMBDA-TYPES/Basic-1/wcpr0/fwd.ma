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

include "Basic-1/wcpr0/defs.ma".

theorem wcpr0_gen_sort:
 \forall (x: C).(\forall (n: nat).((wcpr0 (CSort n) x) \to (eq C x (CSort 
n))))
\def
 \lambda (x: C).(\lambda (n: nat).(\lambda (H: (wcpr0 (CSort n) 
x)).(insert_eq C (CSort n) (\lambda (c: C).(wcpr0 c x)) (\lambda (c: C).(eq C 
x c)) (\lambda (y: C).(\lambda (H0: (wcpr0 y x)).(wcpr0_ind (\lambda (c: 
C).(\lambda (c0: C).((eq C c (CSort n)) \to (eq C c0 c)))) (\lambda (c: 
C).(\lambda (H1: (eq C c (CSort n))).(let H2 \def (f_equal C C (\lambda (e: 
C).e) c (CSort n) H1) in (eq_ind_r C (CSort n) (\lambda (c0: C).(eq C c0 c0)) 
(refl_equal C (CSort n)) c H2)))) (\lambda (c1: C).(\lambda (c2: C).(\lambda 
(_: (wcpr0 c1 c2)).(\lambda (_: (((eq C c1 (CSort n)) \to (eq C c2 
c1)))).(\lambda (u1: T).(\lambda (u2: T).(\lambda (_: (pr0 u1 u2)).(\lambda 
(k: K).(\lambda (H4: (eq C (CHead c1 k u1) (CSort n))).(let H5 \def (eq_ind C 
(CHead c1 k u1) (\lambda (ee: C).(match ee in C return (\lambda (_: C).Prop) 
with [(CSort _) \Rightarrow False | (CHead _ _ _) \Rightarrow True])) I 
(CSort n) H4) in (False_ind (eq C (CHead c2 k u2) (CHead c1 k u1)) 
H5))))))))))) y x H0))) H))).
(* COMMENTS
Initial nodes: 249
END *)

theorem wcpr0_gen_head:
 \forall (k: K).(\forall (c1: C).(\forall (x: C).(\forall (u1: T).((wcpr0 
(CHead c1 k u1) x) \to (or (eq C x (CHead c1 k u1)) (ex3_2 C T (\lambda (c2: 
C).(\lambda (u2: T).(eq C x (CHead c2 k u2)))) (\lambda (c2: C).(\lambda (_: 
T).(wcpr0 c1 c2))) (\lambda (_: C).(\lambda (u2: T).(pr0 u1 u2)))))))))
\def
 \lambda (k: K).(\lambda (c1: C).(\lambda (x: C).(\lambda (u1: T).(\lambda 
(H: (wcpr0 (CHead c1 k u1) x)).(insert_eq C (CHead c1 k u1) (\lambda (c: 
C).(wcpr0 c x)) (\lambda (c: C).(or (eq C x c) (ex3_2 C T (\lambda (c2: 
C).(\lambda (u2: T).(eq C x (CHead c2 k u2)))) (\lambda (c2: C).(\lambda (_: 
T).(wcpr0 c1 c2))) (\lambda (_: C).(\lambda (u2: T).(pr0 u1 u2)))))) (\lambda 
(y: C).(\lambda (H0: (wcpr0 y x)).(wcpr0_ind (\lambda (c: C).(\lambda (c0: 
C).((eq C c (CHead c1 k u1)) \to (or (eq C c0 c) (ex3_2 C T (\lambda (c2: 
C).(\lambda (u2: T).(eq C c0 (CHead c2 k u2)))) (\lambda (c2: C).(\lambda (_: 
T).(wcpr0 c1 c2))) (\lambda (_: C).(\lambda (u2: T).(pr0 u1 u2)))))))) 
(\lambda (c: C).(\lambda (H1: (eq C c (CHead c1 k u1))).(let H2 \def (f_equal 
C C (\lambda (e: C).e) c (CHead c1 k u1) H1) in (eq_ind_r C (CHead c1 k u1) 
(\lambda (c0: C).(or (eq C c0 c0) (ex3_2 C T (\lambda (c2: C).(\lambda (u2: 
T).(eq C c0 (CHead c2 k u2)))) (\lambda (c2: C).(\lambda (_: T).(wcpr0 c1 
c2))) (\lambda (_: C).(\lambda (u2: T).(pr0 u1 u2)))))) (or_introl (eq C 
(CHead c1 k u1) (CHead c1 k u1)) (ex3_2 C T (\lambda (c2: C).(\lambda (u2: 
T).(eq C (CHead c1 k u1) (CHead c2 k u2)))) (\lambda (c2: C).(\lambda (_: 
T).(wcpr0 c1 c2))) (\lambda (_: C).(\lambda (u2: T).(pr0 u1 u2)))) 
(refl_equal C (CHead c1 k u1))) c H2)))) (\lambda (c0: C).(\lambda (c2: 
C).(\lambda (H1: (wcpr0 c0 c2)).(\lambda (H2: (((eq C c0 (CHead c1 k u1)) \to 
(or (eq C c2 c0) (ex3_2 C T (\lambda (c3: C).(\lambda (u2: T).(eq C c2 (CHead 
c3 k u2)))) (\lambda (c3: C).(\lambda (_: T).(wcpr0 c1 c3))) (\lambda (_: 
C).(\lambda (u2: T).(pr0 u1 u2)))))))).(\lambda (u0: T).(\lambda (u2: 
T).(\lambda (H3: (pr0 u0 u2)).(\lambda (k0: K).(\lambda (H4: (eq C (CHead c0 
k0 u0) (CHead c1 k u1))).(let H5 \def (f_equal C C (\lambda (e: C).(match e 
in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow c0 | (CHead c _ _) 
\Rightarrow c])) (CHead c0 k0 u0) (CHead c1 k u1) H4) in ((let H6 \def 
(f_equal C K (\lambda (e: C).(match e in C return (\lambda (_: C).K) with 
[(CSort _) \Rightarrow k0 | (CHead _ k1 _) \Rightarrow k1])) (CHead c0 k0 u0) 
(CHead c1 k u1) H4) in ((let H7 \def (f_equal C T (\lambda (e: C).(match e in 
C return (\lambda (_: C).T) with [(CSort _) \Rightarrow u0 | (CHead _ _ t) 
\Rightarrow t])) (CHead c0 k0 u0) (CHead c1 k u1) H4) in (\lambda (H8: (eq K 
k0 k)).(\lambda (H9: (eq C c0 c1)).(eq_ind_r K k (\lambda (k1: K).(or (eq C 
(CHead c2 k1 u2) (CHead c0 k1 u0)) (ex3_2 C T (\lambda (c3: C).(\lambda (u3: 
T).(eq C (CHead c2 k1 u2) (CHead c3 k u3)))) (\lambda (c3: C).(\lambda (_: 
T).(wcpr0 c1 c3))) (\lambda (_: C).(\lambda (u3: T).(pr0 u1 u3)))))) (let H10 
\def (eq_ind T u0 (\lambda (t: T).(pr0 t u2)) H3 u1 H7) in (eq_ind_r T u1 
(\lambda (t: T).(or (eq C (CHead c2 k u2) (CHead c0 k t)) (ex3_2 C T (\lambda 
(c3: C).(\lambda (u3: T).(eq C (CHead c2 k u2) (CHead c3 k u3)))) (\lambda 
(c3: C).(\lambda (_: T).(wcpr0 c1 c3))) (\lambda (_: C).(\lambda (u3: T).(pr0 
u1 u3)))))) (let H11 \def (eq_ind C c0 (\lambda (c: C).((eq C c (CHead c1 k 
u1)) \to (or (eq C c2 c) (ex3_2 C T (\lambda (c3: C).(\lambda (u3: T).(eq C 
c2 (CHead c3 k u3)))) (\lambda (c3: C).(\lambda (_: T).(wcpr0 c1 c3))) 
(\lambda (_: C).(\lambda (u3: T).(pr0 u1 u3))))))) H2 c1 H9) in (let H12 \def 
(eq_ind C c0 (\lambda (c: C).(wcpr0 c c2)) H1 c1 H9) in (eq_ind_r C c1 
(\lambda (c: C).(or (eq C (CHead c2 k u2) (CHead c k u1)) (ex3_2 C T (\lambda 
(c3: C).(\lambda (u3: T).(eq C (CHead c2 k u2) (CHead c3 k u3)))) (\lambda 
(c3: C).(\lambda (_: T).(wcpr0 c1 c3))) (\lambda (_: C).(\lambda (u3: T).(pr0 
u1 u3)))))) (or_intror (eq C (CHead c2 k u2) (CHead c1 k u1)) (ex3_2 C T 
(\lambda (c3: C).(\lambda (u3: T).(eq C (CHead c2 k u2) (CHead c3 k u3)))) 
(\lambda (c3: C).(\lambda (_: T).(wcpr0 c1 c3))) (\lambda (_: C).(\lambda 
(u3: T).(pr0 u1 u3)))) (ex3_2_intro C T (\lambda (c3: C).(\lambda (u3: T).(eq 
C (CHead c2 k u2) (CHead c3 k u3)))) (\lambda (c3: C).(\lambda (_: T).(wcpr0 
c1 c3))) (\lambda (_: C).(\lambda (u3: T).(pr0 u1 u3))) c2 u2 (refl_equal C 
(CHead c2 k u2)) H12 H10)) c0 H9))) u0 H7)) k0 H8)))) H6)) H5))))))))))) y x 
H0))) H))))).
(* COMMENTS
Initial nodes: 1133
END *)

