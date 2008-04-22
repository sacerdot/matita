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

include "LambdaDelta-1/csubst0/defs.ma".

theorem csubst0_gen_sort:
 \forall (x: C).(\forall (v: T).(\forall (i: nat).(\forall (n: nat).((csubst0 
i v (CSort n) x) \to (\forall (P: Prop).P)))))
\def
 \lambda (x: C).(\lambda (v: T).(\lambda (i: nat).(\lambda (n: nat).(\lambda 
(H: (csubst0 i v (CSort n) x)).(\lambda (P: Prop).(insert_eq C (CSort n) 
(\lambda (c: C).(csubst0 i v c x)) (\lambda (_: C).P) (\lambda (y: 
C).(\lambda (H0: (csubst0 i v y x)).(csubst0_ind (\lambda (_: nat).(\lambda 
(_: T).(\lambda (c: C).(\lambda (_: C).((eq C c (CSort n)) \to P))))) 
(\lambda (k: K).(\lambda (i0: nat).(\lambda (v0: T).(\lambda (u1: T).(\lambda 
(u2: T).(\lambda (_: (subst0 i0 v0 u1 u2)).(\lambda (c: C).(\lambda (H2: (eq 
C (CHead c k u1) (CSort n))).(let H3 \def (eq_ind C (CHead c k u1) (\lambda 
(ee: C).(match ee in C return (\lambda (_: C).Prop) with [(CSort _) 
\Rightarrow False | (CHead _ _ _) \Rightarrow True])) I (CSort n) H2) in 
(False_ind P H3)))))))))) (\lambda (k: K).(\lambda (i0: nat).(\lambda (c1: 
C).(\lambda (c2: C).(\lambda (v0: T).(\lambda (_: (csubst0 i0 v0 c1 
c2)).(\lambda (_: (((eq C c1 (CSort n)) \to P))).(\lambda (u: T).(\lambda 
(H3: (eq C (CHead c1 k u) (CSort n))).(let H4 \def (eq_ind C (CHead c1 k u) 
(\lambda (ee: C).(match ee in C return (\lambda (_: C).Prop) with [(CSort _) 
\Rightarrow False | (CHead _ _ _) \Rightarrow True])) I (CSort n) H3) in 
(False_ind P H4))))))))))) (\lambda (k: K).(\lambda (i0: nat).(\lambda (v0: 
T).(\lambda (u1: T).(\lambda (u2: T).(\lambda (_: (subst0 i0 v0 u1 
u2)).(\lambda (c1: C).(\lambda (c2: C).(\lambda (_: (csubst0 i0 v0 c1 
c2)).(\lambda (_: (((eq C c1 (CSort n)) \to P))).(\lambda (H4: (eq C (CHead 
c1 k u1) (CSort n))).(let H5 \def (eq_ind C (CHead c1 k u1) (\lambda (ee: 
C).(match ee in C return (\lambda (_: C).Prop) with [(CSort _) \Rightarrow 
False | (CHead _ _ _) \Rightarrow True])) I (CSort n) H4) in (False_ind P 
H5))))))))))))) i v y x H0))) H)))))).

theorem csubst0_gen_head:
 \forall (k: K).(\forall (c1: C).(\forall (x: C).(\forall (u1: T).(\forall 
(v: T).(\forall (i: nat).((csubst0 i v (CHead c1 k u1) x) \to (or3 (ex3_2 T 
nat (\lambda (_: T).(\lambda (j: nat).(eq nat i (s k j)))) (\lambda (u2: 
T).(\lambda (_: nat).(eq C x (CHead c1 k u2)))) (\lambda (u2: T).(\lambda (j: 
nat).(subst0 j v u1 u2)))) (ex3_2 C nat (\lambda (_: C).(\lambda (j: nat).(eq 
nat i (s k j)))) (\lambda (c2: C).(\lambda (_: nat).(eq C x (CHead c2 k 
u1)))) (\lambda (c2: C).(\lambda (j: nat).(csubst0 j v c1 c2)))) (ex4_3 T C 
nat (\lambda (_: T).(\lambda (_: C).(\lambda (j: nat).(eq nat i (s k j))))) 
(\lambda (u2: T).(\lambda (c2: C).(\lambda (_: nat).(eq C x (CHead c2 k 
u2))))) (\lambda (u2: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v u1 
u2)))) (\lambda (_: T).(\lambda (c2: C).(\lambda (j: nat).(csubst0 j v c1 
c2))))))))))))
\def
 \lambda (k: K).(\lambda (c1: C).(\lambda (x: C).(\lambda (u1: T).(\lambda 
(v: T).(\lambda (i: nat).(\lambda (H: (csubst0 i v (CHead c1 k u1) 
x)).(insert_eq C (CHead c1 k u1) (\lambda (c: C).(csubst0 i v c x)) (\lambda 
(_: C).(or3 (ex3_2 T nat (\lambda (_: T).(\lambda (j: nat).(eq nat i (s k 
j)))) (\lambda (u2: T).(\lambda (_: nat).(eq C x (CHead c1 k u2)))) (\lambda 
(u2: T).(\lambda (j: nat).(subst0 j v u1 u2)))) (ex3_2 C nat (\lambda (_: 
C).(\lambda (j: nat).(eq nat i (s k j)))) (\lambda (c2: C).(\lambda (_: 
nat).(eq C x (CHead c2 k u1)))) (\lambda (c2: C).(\lambda (j: nat).(csubst0 j 
v c1 c2)))) (ex4_3 T C nat (\lambda (_: T).(\lambda (_: C).(\lambda (j: 
nat).(eq nat i (s k j))))) (\lambda (u2: T).(\lambda (c2: C).(\lambda (_: 
nat).(eq C x (CHead c2 k u2))))) (\lambda (u2: T).(\lambda (_: C).(\lambda 
(j: nat).(subst0 j v u1 u2)))) (\lambda (_: T).(\lambda (c2: C).(\lambda (j: 
nat).(csubst0 j v c1 c2))))))) (\lambda (y: C).(\lambda (H0: (csubst0 i v y 
x)).(csubst0_ind (\lambda (n: nat).(\lambda (t: T).(\lambda (c: C).(\lambda 
(c0: C).((eq C c (CHead c1 k u1)) \to (or3 (ex3_2 T nat (\lambda (_: 
T).(\lambda (j: nat).(eq nat n (s k j)))) (\lambda (u2: T).(\lambda (_: 
nat).(eq C c0 (CHead c1 k u2)))) (\lambda (u2: T).(\lambda (j: nat).(subst0 j 
t u1 u2)))) (ex3_2 C nat (\lambda (_: C).(\lambda (j: nat).(eq nat n (s k 
j)))) (\lambda (c2: C).(\lambda (_: nat).(eq C c0 (CHead c2 k u1)))) (\lambda 
(c2: C).(\lambda (j: nat).(csubst0 j t c1 c2)))) (ex4_3 T C nat (\lambda (_: 
T).(\lambda (_: C).(\lambda (j: nat).(eq nat n (s k j))))) (\lambda (u2: 
T).(\lambda (c2: C).(\lambda (_: nat).(eq C c0 (CHead c2 k u2))))) (\lambda 
(u2: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j t u1 u2)))) (\lambda (_: 
T).(\lambda (c2: C).(\lambda (j: nat).(csubst0 j t c1 c2))))))))))) (\lambda 
(k0: K).(\lambda (i0: nat).(\lambda (v0: T).(\lambda (u0: T).(\lambda (u2: 
T).(\lambda (H1: (subst0 i0 v0 u0 u2)).(\lambda (c: C).(\lambda (H2: (eq C 
(CHead c k0 u0) (CHead c1 k u1))).(let H3 \def (f_equal C C (\lambda (e: 
C).(match e in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow c | 
(CHead c0 _ _) \Rightarrow c0])) (CHead c k0 u0) (CHead c1 k u1) H2) in ((let 
H4 \def (f_equal C K (\lambda (e: C).(match e in C return (\lambda (_: C).K) 
with [(CSort _) \Rightarrow k0 | (CHead _ k1 _) \Rightarrow k1])) (CHead c k0 
u0) (CHead c1 k u1) H2) in ((let H5 \def (f_equal C T (\lambda (e: C).(match 
e in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow u0 | (CHead _ _ 
t) \Rightarrow t])) (CHead c k0 u0) (CHead c1 k u1) H2) in (\lambda (H6: (eq 
K k0 k)).(\lambda (H7: (eq C c c1)).(eq_ind_r C c1 (\lambda (c0: C).(or3 
(ex3_2 T nat (\lambda (_: T).(\lambda (j: nat).(eq nat (s k0 i0) (s k j)))) 
(\lambda (u3: T).(\lambda (_: nat).(eq C (CHead c0 k0 u2) (CHead c1 k u3)))) 
(\lambda (u3: T).(\lambda (j: nat).(subst0 j v0 u1 u3)))) (ex3_2 C nat 
(\lambda (_: C).(\lambda (j: nat).(eq nat (s k0 i0) (s k j)))) (\lambda (c2: 
C).(\lambda (_: nat).(eq C (CHead c0 k0 u2) (CHead c2 k u1)))) (\lambda (c2: 
C).(\lambda (j: nat).(csubst0 j v0 c1 c2)))) (ex4_3 T C nat (\lambda (_: 
T).(\lambda (_: C).(\lambda (j: nat).(eq nat (s k0 i0) (s k j))))) (\lambda 
(u3: T).(\lambda (c2: C).(\lambda (_: nat).(eq C (CHead c0 k0 u2) (CHead c2 k 
u3))))) (\lambda (u3: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v0 u1 
u3)))) (\lambda (_: T).(\lambda (c2: C).(\lambda (j: nat).(csubst0 j v0 c1 
c2))))))) (let H8 \def (eq_ind T u0 (\lambda (t: T).(subst0 i0 v0 t u2)) H1 
u1 H5) in (eq_ind_r K k (\lambda (k1: K).(or3 (ex3_2 T nat (\lambda (_: 
T).(\lambda (j: nat).(eq nat (s k1 i0) (s k j)))) (\lambda (u3: T).(\lambda 
(_: nat).(eq C (CHead c1 k1 u2) (CHead c1 k u3)))) (\lambda (u3: T).(\lambda 
(j: nat).(subst0 j v0 u1 u3)))) (ex3_2 C nat (\lambda (_: C).(\lambda (j: 
nat).(eq nat (s k1 i0) (s k j)))) (\lambda (c2: C).(\lambda (_: nat).(eq C 
(CHead c1 k1 u2) (CHead c2 k u1)))) (\lambda (c2: C).(\lambda (j: 
nat).(csubst0 j v0 c1 c2)))) (ex4_3 T C nat (\lambda (_: T).(\lambda (_: 
C).(\lambda (j: nat).(eq nat (s k1 i0) (s k j))))) (\lambda (u3: T).(\lambda 
(c2: C).(\lambda (_: nat).(eq C (CHead c1 k1 u2) (CHead c2 k u3))))) (\lambda 
(u3: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v0 u1 u3)))) (\lambda (_: 
T).(\lambda (c2: C).(\lambda (j: nat).(csubst0 j v0 c1 c2))))))) (or3_intro0 
(ex3_2 T nat (\lambda (_: T).(\lambda (j: nat).(eq nat (s k i0) (s k j)))) 
(\lambda (u3: T).(\lambda (_: nat).(eq C (CHead c1 k u2) (CHead c1 k u3)))) 
(\lambda (u3: T).(\lambda (j: nat).(subst0 j v0 u1 u3)))) (ex3_2 C nat 
(\lambda (_: C).(\lambda (j: nat).(eq nat (s k i0) (s k j)))) (\lambda (c2: 
C).(\lambda (_: nat).(eq C (CHead c1 k u2) (CHead c2 k u1)))) (\lambda (c2: 
C).(\lambda (j: nat).(csubst0 j v0 c1 c2)))) (ex4_3 T C nat (\lambda (_: 
T).(\lambda (_: C).(\lambda (j: nat).(eq nat (s k i0) (s k j))))) (\lambda 
(u3: T).(\lambda (c2: C).(\lambda (_: nat).(eq C (CHead c1 k u2) (CHead c2 k 
u3))))) (\lambda (u3: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v0 u1 
u3)))) (\lambda (_: T).(\lambda (c2: C).(\lambda (j: nat).(csubst0 j v0 c1 
c2))))) (ex3_2_intro T nat (\lambda (_: T).(\lambda (j: nat).(eq nat (s k i0) 
(s k j)))) (\lambda (u3: T).(\lambda (_: nat).(eq C (CHead c1 k u2) (CHead c1 
k u3)))) (\lambda (u3: T).(\lambda (j: nat).(subst0 j v0 u1 u3))) u2 i0 
(refl_equal nat (s k i0)) (refl_equal C (CHead c1 k u2)) H8)) k0 H6)) c 
H7)))) H4)) H3)))))))))) (\lambda (k0: K).(\lambda (i0: nat).(\lambda (c0: 
C).(\lambda (c2: C).(\lambda (v0: T).(\lambda (H1: (csubst0 i0 v0 c0 
c2)).(\lambda (H2: (((eq C c0 (CHead c1 k u1)) \to (or3 (ex3_2 T nat (\lambda 
(_: T).(\lambda (j: nat).(eq nat i0 (s k j)))) (\lambda (u2: T).(\lambda (_: 
nat).(eq C c2 (CHead c1 k u2)))) (\lambda (u2: T).(\lambda (j: nat).(subst0 j 
v0 u1 u2)))) (ex3_2 C nat (\lambda (_: C).(\lambda (j: nat).(eq nat i0 (s k 
j)))) (\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k u1)))) (\lambda 
(c3: C).(\lambda (j: nat).(csubst0 j v0 c1 c3)))) (ex4_3 T C nat (\lambda (_: 
T).(\lambda (_: C).(\lambda (j: nat).(eq nat i0 (s k j))))) (\lambda (u2: 
T).(\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k u2))))) (\lambda 
(u2: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v0 u1 u2)))) (\lambda (_: 
T).(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v0 c1 c3))))))))).(\lambda 
(u: T).(\lambda (H3: (eq C (CHead c0 k0 u) (CHead c1 k u1))).(let H4 \def 
(f_equal C C (\lambda (e: C).(match e in C return (\lambda (_: C).C) with 
[(CSort _) \Rightarrow c0 | (CHead c _ _) \Rightarrow c])) (CHead c0 k0 u) 
(CHead c1 k u1) H3) in ((let H5 \def (f_equal C K (\lambda (e: C).(match e in 
C return (\lambda (_: C).K) with [(CSort _) \Rightarrow k0 | (CHead _ k1 _) 
\Rightarrow k1])) (CHead c0 k0 u) (CHead c1 k u1) H3) in ((let H6 \def 
(f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: C).T) with 
[(CSort _) \Rightarrow u | (CHead _ _ t) \Rightarrow t])) (CHead c0 k0 u) 
(CHead c1 k u1) H3) in (\lambda (H7: (eq K k0 k)).(\lambda (H8: (eq C c0 
c1)).(eq_ind_r T u1 (\lambda (t: T).(or3 (ex3_2 T nat (\lambda (_: 
T).(\lambda (j: nat).(eq nat (s k0 i0) (s k j)))) (\lambda (u2: T).(\lambda 
(_: nat).(eq C (CHead c2 k0 t) (CHead c1 k u2)))) (\lambda (u2: T).(\lambda 
(j: nat).(subst0 j v0 u1 u2)))) (ex3_2 C nat (\lambda (_: C).(\lambda (j: 
nat).(eq nat (s k0 i0) (s k j)))) (\lambda (c3: C).(\lambda (_: nat).(eq C 
(CHead c2 k0 t) (CHead c3 k u1)))) (\lambda (c3: C).(\lambda (j: 
nat).(csubst0 j v0 c1 c3)))) (ex4_3 T C nat (\lambda (_: T).(\lambda (_: 
C).(\lambda (j: nat).(eq nat (s k0 i0) (s k j))))) (\lambda (u2: T).(\lambda 
(c3: C).(\lambda (_: nat).(eq C (CHead c2 k0 t) (CHead c3 k u2))))) (\lambda 
(u2: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v0 u1 u2)))) (\lambda (_: 
T).(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v0 c1 c3))))))) (let H9 \def 
(eq_ind C c0 (\lambda (c: C).((eq C c (CHead c1 k u1)) \to (or3 (ex3_2 T nat 
(\lambda (_: T).(\lambda (j: nat).(eq nat i0 (s k j)))) (\lambda (u2: 
T).(\lambda (_: nat).(eq C c2 (CHead c1 k u2)))) (\lambda (u2: T).(\lambda 
(j: nat).(subst0 j v0 u1 u2)))) (ex3_2 C nat (\lambda (_: C).(\lambda (j: 
nat).(eq nat i0 (s k j)))) (\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead 
c3 k u1)))) (\lambda (c3: C).(\lambda (j: nat).(csubst0 j v0 c1 c3)))) (ex4_3 
T C nat (\lambda (_: T).(\lambda (_: C).(\lambda (j: nat).(eq nat i0 (s k 
j))))) (\lambda (u2: T).(\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 
k u2))))) (\lambda (u2: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v0 u1 
u2)))) (\lambda (_: T).(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v0 c1 
c3)))))))) H2 c1 H8) in (let H10 \def (eq_ind C c0 (\lambda (c: C).(csubst0 
i0 v0 c c2)) H1 c1 H8) in (eq_ind_r K k (\lambda (k1: K).(or3 (ex3_2 T nat 
(\lambda (_: T).(\lambda (j: nat).(eq nat (s k1 i0) (s k j)))) (\lambda (u2: 
T).(\lambda (_: nat).(eq C (CHead c2 k1 u1) (CHead c1 k u2)))) (\lambda (u2: 
T).(\lambda (j: nat).(subst0 j v0 u1 u2)))) (ex3_2 C nat (\lambda (_: 
C).(\lambda (j: nat).(eq nat (s k1 i0) (s k j)))) (\lambda (c3: C).(\lambda 
(_: nat).(eq C (CHead c2 k1 u1) (CHead c3 k u1)))) (\lambda (c3: C).(\lambda 
(j: nat).(csubst0 j v0 c1 c3)))) (ex4_3 T C nat (\lambda (_: T).(\lambda (_: 
C).(\lambda (j: nat).(eq nat (s k1 i0) (s k j))))) (\lambda (u2: T).(\lambda 
(c3: C).(\lambda (_: nat).(eq C (CHead c2 k1 u1) (CHead c3 k u2))))) (\lambda 
(u2: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v0 u1 u2)))) (\lambda (_: 
T).(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v0 c1 c3))))))) (or3_intro1 
(ex3_2 T nat (\lambda (_: T).(\lambda (j: nat).(eq nat (s k i0) (s k j)))) 
(\lambda (u2: T).(\lambda (_: nat).(eq C (CHead c2 k u1) (CHead c1 k u2)))) 
(\lambda (u2: T).(\lambda (j: nat).(subst0 j v0 u1 u2)))) (ex3_2 C nat 
(\lambda (_: C).(\lambda (j: nat).(eq nat (s k i0) (s k j)))) (\lambda (c3: 
C).(\lambda (_: nat).(eq C (CHead c2 k u1) (CHead c3 k u1)))) (\lambda (c3: 
C).(\lambda (j: nat).(csubst0 j v0 c1 c3)))) (ex4_3 T C nat (\lambda (_: 
T).(\lambda (_: C).(\lambda (j: nat).(eq nat (s k i0) (s k j))))) (\lambda 
(u2: T).(\lambda (c3: C).(\lambda (_: nat).(eq C (CHead c2 k u1) (CHead c3 k 
u2))))) (\lambda (u2: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v0 u1 
u2)))) (\lambda (_: T).(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v0 c1 
c3))))) (ex3_2_intro C nat (\lambda (_: C).(\lambda (j: nat).(eq nat (s k i0) 
(s k j)))) (\lambda (c3: C).(\lambda (_: nat).(eq C (CHead c2 k u1) (CHead c3 
k u1)))) (\lambda (c3: C).(\lambda (j: nat).(csubst0 j v0 c1 c3))) c2 i0 
(refl_equal nat (s k i0)) (refl_equal C (CHead c2 k u1)) H10)) k0 H7))) u 
H6)))) H5)) H4))))))))))) (\lambda (k0: K).(\lambda (i0: nat).(\lambda (v0: 
T).(\lambda (u0: T).(\lambda (u2: T).(\lambda (H1: (subst0 i0 v0 u0 
u2)).(\lambda (c0: C).(\lambda (c2: C).(\lambda (H2: (csubst0 i0 v0 c0 
c2)).(\lambda (H3: (((eq C c0 (CHead c1 k u1)) \to (or3 (ex3_2 T nat (\lambda 
(_: T).(\lambda (j: nat).(eq nat i0 (s k j)))) (\lambda (u3: T).(\lambda (_: 
nat).(eq C c2 (CHead c1 k u3)))) (\lambda (u3: T).(\lambda (j: nat).(subst0 j 
v0 u1 u3)))) (ex3_2 C nat (\lambda (_: C).(\lambda (j: nat).(eq nat i0 (s k 
j)))) (\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k u1)))) (\lambda 
(c3: C).(\lambda (j: nat).(csubst0 j v0 c1 c3)))) (ex4_3 T C nat (\lambda (_: 
T).(\lambda (_: C).(\lambda (j: nat).(eq nat i0 (s k j))))) (\lambda (u3: 
T).(\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k u3))))) (\lambda 
(u3: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v0 u1 u3)))) (\lambda (_: 
T).(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v0 c1 c3))))))))).(\lambda 
(H4: (eq C (CHead c0 k0 u0) (CHead c1 k u1))).(let H5 \def (f_equal C C 
(\lambda (e: C).(match e in C return (\lambda (_: C).C) with [(CSort _) 
\Rightarrow c0 | (CHead c _ _) \Rightarrow c])) (CHead c0 k0 u0) (CHead c1 k 
u1) H4) in ((let H6 \def (f_equal C K (\lambda (e: C).(match e in C return 
(\lambda (_: C).K) with [(CSort _) \Rightarrow k0 | (CHead _ k1 _) 
\Rightarrow k1])) (CHead c0 k0 u0) (CHead c1 k u1) H4) in ((let H7 \def 
(f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: C).T) with 
[(CSort _) \Rightarrow u0 | (CHead _ _ t) \Rightarrow t])) (CHead c0 k0 u0) 
(CHead c1 k u1) H4) in (\lambda (H8: (eq K k0 k)).(\lambda (H9: (eq C c0 
c1)).(let H10 \def (eq_ind C c0 (\lambda (c: C).((eq C c (CHead c1 k u1)) \to 
(or3 (ex3_2 T nat (\lambda (_: T).(\lambda (j: nat).(eq nat i0 (s k j)))) 
(\lambda (u3: T).(\lambda (_: nat).(eq C c2 (CHead c1 k u3)))) (\lambda (u3: 
T).(\lambda (j: nat).(subst0 j v0 u1 u3)))) (ex3_2 C nat (\lambda (_: 
C).(\lambda (j: nat).(eq nat i0 (s k j)))) (\lambda (c3: C).(\lambda (_: 
nat).(eq C c2 (CHead c3 k u1)))) (\lambda (c3: C).(\lambda (j: nat).(csubst0 
j v0 c1 c3)))) (ex4_3 T C nat (\lambda (_: T).(\lambda (_: C).(\lambda (j: 
nat).(eq nat i0 (s k j))))) (\lambda (u3: T).(\lambda (c3: C).(\lambda (_: 
nat).(eq C c2 (CHead c3 k u3))))) (\lambda (u3: T).(\lambda (_: C).(\lambda 
(j: nat).(subst0 j v0 u1 u3)))) (\lambda (_: T).(\lambda (c3: C).(\lambda (j: 
nat).(csubst0 j v0 c1 c3)))))))) H3 c1 H9) in (let H11 \def (eq_ind C c0 
(\lambda (c: C).(csubst0 i0 v0 c c2)) H2 c1 H9) in (let H12 \def (eq_ind T u0 
(\lambda (t: T).(subst0 i0 v0 t u2)) H1 u1 H7) in (eq_ind_r K k (\lambda (k1: 
K).(or3 (ex3_2 T nat (\lambda (_: T).(\lambda (j: nat).(eq nat (s k1 i0) (s k 
j)))) (\lambda (u3: T).(\lambda (_: nat).(eq C (CHead c2 k1 u2) (CHead c1 k 
u3)))) (\lambda (u3: T).(\lambda (j: nat).(subst0 j v0 u1 u3)))) (ex3_2 C nat 
(\lambda (_: C).(\lambda (j: nat).(eq nat (s k1 i0) (s k j)))) (\lambda (c3: 
C).(\lambda (_: nat).(eq C (CHead c2 k1 u2) (CHead c3 k u1)))) (\lambda (c3: 
C).(\lambda (j: nat).(csubst0 j v0 c1 c3)))) (ex4_3 T C nat (\lambda (_: 
T).(\lambda (_: C).(\lambda (j: nat).(eq nat (s k1 i0) (s k j))))) (\lambda 
(u3: T).(\lambda (c3: C).(\lambda (_: nat).(eq C (CHead c2 k1 u2) (CHead c3 k 
u3))))) (\lambda (u3: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v0 u1 
u3)))) (\lambda (_: T).(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v0 c1 
c3))))))) (or3_intro2 (ex3_2 T nat (\lambda (_: T).(\lambda (j: nat).(eq nat 
(s k i0) (s k j)))) (\lambda (u3: T).(\lambda (_: nat).(eq C (CHead c2 k u2) 
(CHead c1 k u3)))) (\lambda (u3: T).(\lambda (j: nat).(subst0 j v0 u1 u3)))) 
(ex3_2 C nat (\lambda (_: C).(\lambda (j: nat).(eq nat (s k i0) (s k j)))) 
(\lambda (c3: C).(\lambda (_: nat).(eq C (CHead c2 k u2) (CHead c3 k u1)))) 
(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v0 c1 c3)))) (ex4_3 T C nat 
(\lambda (_: T).(\lambda (_: C).(\lambda (j: nat).(eq nat (s k i0) (s k 
j))))) (\lambda (u3: T).(\lambda (c3: C).(\lambda (_: nat).(eq C (CHead c2 k 
u2) (CHead c3 k u3))))) (\lambda (u3: T).(\lambda (_: C).(\lambda (j: 
nat).(subst0 j v0 u1 u3)))) (\lambda (_: T).(\lambda (c3: C).(\lambda (j: 
nat).(csubst0 j v0 c1 c3))))) (ex4_3_intro T C nat (\lambda (_: T).(\lambda 
(_: C).(\lambda (j: nat).(eq nat (s k i0) (s k j))))) (\lambda (u3: 
T).(\lambda (c3: C).(\lambda (_: nat).(eq C (CHead c2 k u2) (CHead c3 k 
u3))))) (\lambda (u3: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v0 u1 
u3)))) (\lambda (_: T).(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v0 c1 
c3)))) u2 c2 i0 (refl_equal nat (s k i0)) (refl_equal C (CHead c2 k u2)) H12 
H11)) k0 H8))))))) H6)) H5))))))))))))) i v y x H0))) H))))))).

