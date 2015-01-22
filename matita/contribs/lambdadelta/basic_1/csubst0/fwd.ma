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

include "Basic-1/csubst0/defs.ma".

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
(* COMMENTS
Initial nodes: 355
END *)

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
(* COMMENTS
Initial nodes: 4039
END *)

theorem csubst0_gen_S_bind_2:
 \forall (b: B).(\forall (x: C).(\forall (c2: C).(\forall (v: T).(\forall 
(v2: T).(\forall (i: nat).((csubst0 (S i) v x (CHead c2 (Bind b) v2)) \to 
(or3 (ex2 T (\lambda (v1: T).(subst0 i v v1 v2)) (\lambda (v1: T).(eq C x 
(CHead c2 (Bind b) v1)))) (ex2 C (\lambda (c1: C).(csubst0 i v c1 c2)) 
(\lambda (c1: C).(eq C x (CHead c1 (Bind b) v2)))) (ex3_2 C T (\lambda (_: 
C).(\lambda (v1: T).(subst0 i v v1 v2))) (\lambda (c1: C).(\lambda (_: 
T).(csubst0 i v c1 c2))) (\lambda (c1: C).(\lambda (v1: T).(eq C x (CHead c1 
(Bind b) v1))))))))))))
\def
 \lambda (b: B).(\lambda (x: C).(\lambda (c2: C).(\lambda (v: T).(\lambda 
(v2: T).(\lambda (i: nat).(\lambda (H: (csubst0 (S i) v x (CHead c2 (Bind b) 
v2))).(insert_eq C (CHead c2 (Bind b) v2) (\lambda (c: C).(csubst0 (S i) v x 
c)) (\lambda (_: C).(or3 (ex2 T (\lambda (v1: T).(subst0 i v v1 v2)) (\lambda 
(v1: T).(eq C x (CHead c2 (Bind b) v1)))) (ex2 C (\lambda (c1: C).(csubst0 i 
v c1 c2)) (\lambda (c1: C).(eq C x (CHead c1 (Bind b) v2)))) (ex3_2 C T 
(\lambda (_: C).(\lambda (v1: T).(subst0 i v v1 v2))) (\lambda (c1: 
C).(\lambda (_: T).(csubst0 i v c1 c2))) (\lambda (c1: C).(\lambda (v1: 
T).(eq C x (CHead c1 (Bind b) v1))))))) (\lambda (y: C).(\lambda (H0: 
(csubst0 (S i) v x y)).(insert_eq nat (S i) (\lambda (n: nat).(csubst0 n v x 
y)) (\lambda (_: nat).((eq C y (CHead c2 (Bind b) v2)) \to (or3 (ex2 T 
(\lambda (v1: T).(subst0 i v v1 v2)) (\lambda (v1: T).(eq C x (CHead c2 (Bind 
b) v1)))) (ex2 C (\lambda (c1: C).(csubst0 i v c1 c2)) (\lambda (c1: C).(eq C 
x (CHead c1 (Bind b) v2)))) (ex3_2 C T (\lambda (_: C).(\lambda (v1: 
T).(subst0 i v v1 v2))) (\lambda (c1: C).(\lambda (_: T).(csubst0 i v c1 
c2))) (\lambda (c1: C).(\lambda (v1: T).(eq C x (CHead c1 (Bind b) v1)))))))) 
(\lambda (y0: nat).(\lambda (H1: (csubst0 y0 v x y)).(csubst0_ind (\lambda 
(n: nat).(\lambda (t: T).(\lambda (c: C).(\lambda (c0: C).((eq nat n (S i)) 
\to ((eq C c0 (CHead c2 (Bind b) v2)) \to (or3 (ex2 T (\lambda (v1: 
T).(subst0 i t v1 v2)) (\lambda (v1: T).(eq C c (CHead c2 (Bind b) v1)))) 
(ex2 C (\lambda (c1: C).(csubst0 i t c1 c2)) (\lambda (c1: C).(eq C c (CHead 
c1 (Bind b) v2)))) (ex3_2 C T (\lambda (_: C).(\lambda (v1: T).(subst0 i t v1 
v2))) (\lambda (c1: C).(\lambda (_: T).(csubst0 i t c1 c2))) (\lambda (c1: 
C).(\lambda (v1: T).(eq C c (CHead c1 (Bind b) v1)))))))))))) (\lambda (k: 
K).(\lambda (i0: nat).(\lambda (v0: T).(\lambda (u1: T).(\lambda (u2: 
T).(\lambda (H2: (subst0 i0 v0 u1 u2)).(\lambda (c: C).(\lambda (H3: (eq nat 
(s k i0) (S i))).(\lambda (H4: (eq C (CHead c k u2) (CHead c2 (Bind b) 
v2))).(let H5 \def (f_equal C C (\lambda (e: C).(match e in C return (\lambda 
(_: C).C) with [(CSort _) \Rightarrow c | (CHead c0 _ _) \Rightarrow c0])) 
(CHead c k u2) (CHead c2 (Bind b) v2) H4) in ((let H6 \def (f_equal C K 
(\lambda (e: C).(match e in C return (\lambda (_: C).K) with [(CSort _) 
\Rightarrow k | (CHead _ k0 _) \Rightarrow k0])) (CHead c k u2) (CHead c2 
(Bind b) v2) H4) in ((let H7 \def (f_equal C T (\lambda (e: C).(match e in C 
return (\lambda (_: C).T) with [(CSort _) \Rightarrow u2 | (CHead _ _ t) 
\Rightarrow t])) (CHead c k u2) (CHead c2 (Bind b) v2) H4) in (\lambda (H8: 
(eq K k (Bind b))).(\lambda (H9: (eq C c c2)).(eq_ind_r C c2 (\lambda (c0: 
C).(or3 (ex2 T (\lambda (v1: T).(subst0 i v0 v1 v2)) (\lambda (v1: T).(eq C 
(CHead c0 k u1) (CHead c2 (Bind b) v1)))) (ex2 C (\lambda (c1: C).(csubst0 i 
v0 c1 c2)) (\lambda (c1: C).(eq C (CHead c0 k u1) (CHead c1 (Bind b) v2)))) 
(ex3_2 C T (\lambda (_: C).(\lambda (v1: T).(subst0 i v0 v1 v2))) (\lambda 
(c1: C).(\lambda (_: T).(csubst0 i v0 c1 c2))) (\lambda (c1: C).(\lambda (v1: 
T).(eq C (CHead c0 k u1) (CHead c1 (Bind b) v1))))))) (let H10 \def (eq_ind T 
u2 (\lambda (t: T).(subst0 i0 v0 u1 t)) H2 v2 H7) in (let H11 \def (eq_ind K 
k (\lambda (k0: K).(eq nat (s k0 i0) (S i))) H3 (Bind b) H8) in (eq_ind_r K 
(Bind b) (\lambda (k0: K).(or3 (ex2 T (\lambda (v1: T).(subst0 i v0 v1 v2)) 
(\lambda (v1: T).(eq C (CHead c2 k0 u1) (CHead c2 (Bind b) v1)))) (ex2 C 
(\lambda (c1: C).(csubst0 i v0 c1 c2)) (\lambda (c1: C).(eq C (CHead c2 k0 
u1) (CHead c1 (Bind b) v2)))) (ex3_2 C T (\lambda (_: C).(\lambda (v1: 
T).(subst0 i v0 v1 v2))) (\lambda (c1: C).(\lambda (_: T).(csubst0 i v0 c1 
c2))) (\lambda (c1: C).(\lambda (v1: T).(eq C (CHead c2 k0 u1) (CHead c1 
(Bind b) v1))))))) (let H12 \def (f_equal nat nat (\lambda (e: nat).(match e 
in nat return (\lambda (_: nat).nat) with [O \Rightarrow i0 | (S n) 
\Rightarrow n])) (S i0) (S i) H11) in (let H13 \def (eq_ind nat i0 (\lambda 
(n: nat).(subst0 n v0 u1 v2)) H10 i H12) in (or3_intro0 (ex2 T (\lambda (v1: 
T).(subst0 i v0 v1 v2)) (\lambda (v1: T).(eq C (CHead c2 (Bind b) u1) (CHead 
c2 (Bind b) v1)))) (ex2 C (\lambda (c1: C).(csubst0 i v0 c1 c2)) (\lambda 
(c1: C).(eq C (CHead c2 (Bind b) u1) (CHead c1 (Bind b) v2)))) (ex3_2 C T 
(\lambda (_: C).(\lambda (v1: T).(subst0 i v0 v1 v2))) (\lambda (c1: 
C).(\lambda (_: T).(csubst0 i v0 c1 c2))) (\lambda (c1: C).(\lambda (v1: 
T).(eq C (CHead c2 (Bind b) u1) (CHead c1 (Bind b) v1))))) (ex_intro2 T 
(\lambda (v1: T).(subst0 i v0 v1 v2)) (\lambda (v1: T).(eq C (CHead c2 (Bind 
b) u1) (CHead c2 (Bind b) v1))) u1 H13 (refl_equal C (CHead c2 (Bind b) 
u1)))))) k H8))) c H9)))) H6)) H5))))))))))) (\lambda (k: K).(\lambda (i0: 
nat).(\lambda (c1: C).(\lambda (c0: C).(\lambda (v0: T).(\lambda (H2: 
(csubst0 i0 v0 c1 c0)).(\lambda (H3: (((eq nat i0 (S i)) \to ((eq C c0 (CHead 
c2 (Bind b) v2)) \to (or3 (ex2 T (\lambda (v1: T).(subst0 i v0 v1 v2)) 
(\lambda (v1: T).(eq C c1 (CHead c2 (Bind b) v1)))) (ex2 C (\lambda (c3: 
C).(csubst0 i v0 c3 c2)) (\lambda (c3: C).(eq C c1 (CHead c3 (Bind b) v2)))) 
(ex3_2 C T (\lambda (_: C).(\lambda (v1: T).(subst0 i v0 v1 v2))) (\lambda 
(c3: C).(\lambda (_: T).(csubst0 i v0 c3 c2))) (\lambda (c3: C).(\lambda (v1: 
T).(eq C c1 (CHead c3 (Bind b) v1)))))))))).(\lambda (u: T).(\lambda (H4: (eq 
nat (s k i0) (S i))).(\lambda (H5: (eq C (CHead c0 k u) (CHead c2 (Bind b) 
v2))).(let H6 \def (f_equal C C (\lambda (e: C).(match e in C return (\lambda 
(_: C).C) with [(CSort _) \Rightarrow c0 | (CHead c _ _) \Rightarrow c])) 
(CHead c0 k u) (CHead c2 (Bind b) v2) H5) in ((let H7 \def (f_equal C K 
(\lambda (e: C).(match e in C return (\lambda (_: C).K) with [(CSort _) 
\Rightarrow k | (CHead _ k0 _) \Rightarrow k0])) (CHead c0 k u) (CHead c2 
(Bind b) v2) H5) in ((let H8 \def (f_equal C T (\lambda (e: C).(match e in C 
return (\lambda (_: C).T) with [(CSort _) \Rightarrow u | (CHead _ _ t) 
\Rightarrow t])) (CHead c0 k u) (CHead c2 (Bind b) v2) H5) in (\lambda (H9: 
(eq K k (Bind b))).(\lambda (H10: (eq C c0 c2)).(eq_ind_r T v2 (\lambda (t: 
T).(or3 (ex2 T (\lambda (v1: T).(subst0 i v0 v1 v2)) (\lambda (v1: T).(eq C 
(CHead c1 k t) (CHead c2 (Bind b) v1)))) (ex2 C (\lambda (c3: C).(csubst0 i 
v0 c3 c2)) (\lambda (c3: C).(eq C (CHead c1 k t) (CHead c3 (Bind b) v2)))) 
(ex3_2 C T (\lambda (_: C).(\lambda (v1: T).(subst0 i v0 v1 v2))) (\lambda 
(c3: C).(\lambda (_: T).(csubst0 i v0 c3 c2))) (\lambda (c3: C).(\lambda (v1: 
T).(eq C (CHead c1 k t) (CHead c3 (Bind b) v1))))))) (let H11 \def (eq_ind C 
c0 (\lambda (c: C).((eq nat i0 (S i)) \to ((eq C c (CHead c2 (Bind b) v2)) 
\to (or3 (ex2 T (\lambda (v1: T).(subst0 i v0 v1 v2)) (\lambda (v1: T).(eq C 
c1 (CHead c2 (Bind b) v1)))) (ex2 C (\lambda (c3: C).(csubst0 i v0 c3 c2)) 
(\lambda (c3: C).(eq C c1 (CHead c3 (Bind b) v2)))) (ex3_2 C T (\lambda (_: 
C).(\lambda (v1: T).(subst0 i v0 v1 v2))) (\lambda (c3: C).(\lambda (_: 
T).(csubst0 i v0 c3 c2))) (\lambda (c3: C).(\lambda (v1: T).(eq C c1 (CHead 
c3 (Bind b) v1))))))))) H3 c2 H10) in (let H12 \def (eq_ind C c0 (\lambda (c: 
C).(csubst0 i0 v0 c1 c)) H2 c2 H10) in (let H13 \def (eq_ind K k (\lambda 
(k0: K).(eq nat (s k0 i0) (S i))) H4 (Bind b) H9) in (eq_ind_r K (Bind b) 
(\lambda (k0: K).(or3 (ex2 T (\lambda (v1: T).(subst0 i v0 v1 v2)) (\lambda 
(v1: T).(eq C (CHead c1 k0 v2) (CHead c2 (Bind b) v1)))) (ex2 C (\lambda (c3: 
C).(csubst0 i v0 c3 c2)) (\lambda (c3: C).(eq C (CHead c1 k0 v2) (CHead c3 
(Bind b) v2)))) (ex3_2 C T (\lambda (_: C).(\lambda (v1: T).(subst0 i v0 v1 
v2))) (\lambda (c3: C).(\lambda (_: T).(csubst0 i v0 c3 c2))) (\lambda (c3: 
C).(\lambda (v1: T).(eq C (CHead c1 k0 v2) (CHead c3 (Bind b) v1))))))) (let 
H14 \def (f_equal nat nat (\lambda (e: nat).(match e in nat return (\lambda 
(_: nat).nat) with [O \Rightarrow i0 | (S n) \Rightarrow n])) (S i0) (S i) 
H13) in (let H15 \def (eq_ind nat i0 (\lambda (n: nat).((eq nat n (S i)) \to 
((eq C c2 (CHead c2 (Bind b) v2)) \to (or3 (ex2 T (\lambda (v1: T).(subst0 i 
v0 v1 v2)) (\lambda (v1: T).(eq C c1 (CHead c2 (Bind b) v1)))) (ex2 C 
(\lambda (c3: C).(csubst0 i v0 c3 c2)) (\lambda (c3: C).(eq C c1 (CHead c3 
(Bind b) v2)))) (ex3_2 C T (\lambda (_: C).(\lambda (v1: T).(subst0 i v0 v1 
v2))) (\lambda (c3: C).(\lambda (_: T).(csubst0 i v0 c3 c2))) (\lambda (c3: 
C).(\lambda (v1: T).(eq C c1 (CHead c3 (Bind b) v1))))))))) H11 i H14) in 
(let H16 \def (eq_ind nat i0 (\lambda (n: nat).(csubst0 n v0 c1 c2)) H12 i 
H14) in (or3_intro1 (ex2 T (\lambda (v1: T).(subst0 i v0 v1 v2)) (\lambda 
(v1: T).(eq C (CHead c1 (Bind b) v2) (CHead c2 (Bind b) v1)))) (ex2 C 
(\lambda (c3: C).(csubst0 i v0 c3 c2)) (\lambda (c3: C).(eq C (CHead c1 (Bind 
b) v2) (CHead c3 (Bind b) v2)))) (ex3_2 C T (\lambda (_: C).(\lambda (v1: 
T).(subst0 i v0 v1 v2))) (\lambda (c3: C).(\lambda (_: T).(csubst0 i v0 c3 
c2))) (\lambda (c3: C).(\lambda (v1: T).(eq C (CHead c1 (Bind b) v2) (CHead 
c3 (Bind b) v1))))) (ex_intro2 C (\lambda (c3: C).(csubst0 i v0 c3 c2)) 
(\lambda (c3: C).(eq C (CHead c1 (Bind b) v2) (CHead c3 (Bind b) v2))) c1 H16 
(refl_equal C (CHead c1 (Bind b) v2))))))) k H9)))) u H8)))) H7)) 
H6)))))))))))) (\lambda (k: K).(\lambda (i0: nat).(\lambda (v0: T).(\lambda 
(u1: T).(\lambda (u2: T).(\lambda (H2: (subst0 i0 v0 u1 u2)).(\lambda (c1: 
C).(\lambda (c0: C).(\lambda (H3: (csubst0 i0 v0 c1 c0)).(\lambda (H4: (((eq 
nat i0 (S i)) \to ((eq C c0 (CHead c2 (Bind b) v2)) \to (or3 (ex2 T (\lambda 
(v1: T).(subst0 i v0 v1 v2)) (\lambda (v1: T).(eq C c1 (CHead c2 (Bind b) 
v1)))) (ex2 C (\lambda (c3: C).(csubst0 i v0 c3 c2)) (\lambda (c3: C).(eq C 
c1 (CHead c3 (Bind b) v2)))) (ex3_2 C T (\lambda (_: C).(\lambda (v1: 
T).(subst0 i v0 v1 v2))) (\lambda (c3: C).(\lambda (_: T).(csubst0 i v0 c3 
c2))) (\lambda (c3: C).(\lambda (v1: T).(eq C c1 (CHead c3 (Bind b) 
v1)))))))))).(\lambda (H5: (eq nat (s k i0) (S i))).(\lambda (H6: (eq C 
(CHead c0 k u2) (CHead c2 (Bind b) v2))).(let H7 \def (f_equal C C (\lambda 
(e: C).(match e in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow c0 
| (CHead c _ _) \Rightarrow c])) (CHead c0 k u2) (CHead c2 (Bind b) v2) H6) 
in ((let H8 \def (f_equal C K (\lambda (e: C).(match e in C return (\lambda 
(_: C).K) with [(CSort _) \Rightarrow k | (CHead _ k0 _) \Rightarrow k0])) 
(CHead c0 k u2) (CHead c2 (Bind b) v2) H6) in ((let H9 \def (f_equal C T 
(\lambda (e: C).(match e in C return (\lambda (_: C).T) with [(CSort _) 
\Rightarrow u2 | (CHead _ _ t) \Rightarrow t])) (CHead c0 k u2) (CHead c2 
(Bind b) v2) H6) in (\lambda (H10: (eq K k (Bind b))).(\lambda (H11: (eq C c0 
c2)).(let H12 \def (eq_ind C c0 (\lambda (c: C).((eq nat i0 (S i)) \to ((eq C 
c (CHead c2 (Bind b) v2)) \to (or3 (ex2 T (\lambda (v1: T).(subst0 i v0 v1 
v2)) (\lambda (v1: T).(eq C c1 (CHead c2 (Bind b) v1)))) (ex2 C (\lambda (c3: 
C).(csubst0 i v0 c3 c2)) (\lambda (c3: C).(eq C c1 (CHead c3 (Bind b) v2)))) 
(ex3_2 C T (\lambda (_: C).(\lambda (v1: T).(subst0 i v0 v1 v2))) (\lambda 
(c3: C).(\lambda (_: T).(csubst0 i v0 c3 c2))) (\lambda (c3: C).(\lambda (v1: 
T).(eq C c1 (CHead c3 (Bind b) v1))))))))) H4 c2 H11) in (let H13 \def 
(eq_ind C c0 (\lambda (c: C).(csubst0 i0 v0 c1 c)) H3 c2 H11) in (let H14 
\def (eq_ind T u2 (\lambda (t: T).(subst0 i0 v0 u1 t)) H2 v2 H9) in (let H15 
\def (eq_ind K k (\lambda (k0: K).(eq nat (s k0 i0) (S i))) H5 (Bind b) H10) 
in (eq_ind_r K (Bind b) (\lambda (k0: K).(or3 (ex2 T (\lambda (v1: T).(subst0 
i v0 v1 v2)) (\lambda (v1: T).(eq C (CHead c1 k0 u1) (CHead c2 (Bind b) 
v1)))) (ex2 C (\lambda (c3: C).(csubst0 i v0 c3 c2)) (\lambda (c3: C).(eq C 
(CHead c1 k0 u1) (CHead c3 (Bind b) v2)))) (ex3_2 C T (\lambda (_: 
C).(\lambda (v1: T).(subst0 i v0 v1 v2))) (\lambda (c3: C).(\lambda (_: 
T).(csubst0 i v0 c3 c2))) (\lambda (c3: C).(\lambda (v1: T).(eq C (CHead c1 
k0 u1) (CHead c3 (Bind b) v1))))))) (let H16 \def (f_equal nat nat (\lambda 
(e: nat).(match e in nat return (\lambda (_: nat).nat) with [O \Rightarrow i0 
| (S n) \Rightarrow n])) (S i0) (S i) H15) in (let H17 \def (eq_ind nat i0 
(\lambda (n: nat).((eq nat n (S i)) \to ((eq C c2 (CHead c2 (Bind b) v2)) \to 
(or3 (ex2 T (\lambda (v1: T).(subst0 i v0 v1 v2)) (\lambda (v1: T).(eq C c1 
(CHead c2 (Bind b) v1)))) (ex2 C (\lambda (c3: C).(csubst0 i v0 c3 c2)) 
(\lambda (c3: C).(eq C c1 (CHead c3 (Bind b) v2)))) (ex3_2 C T (\lambda (_: 
C).(\lambda (v1: T).(subst0 i v0 v1 v2))) (\lambda (c3: C).(\lambda (_: 
T).(csubst0 i v0 c3 c2))) (\lambda (c3: C).(\lambda (v1: T).(eq C c1 (CHead 
c3 (Bind b) v1))))))))) H12 i H16) in (let H18 \def (eq_ind nat i0 (\lambda 
(n: nat).(csubst0 n v0 c1 c2)) H13 i H16) in (let H19 \def (eq_ind nat i0 
(\lambda (n: nat).(subst0 n v0 u1 v2)) H14 i H16) in (or3_intro2 (ex2 T 
(\lambda (v1: T).(subst0 i v0 v1 v2)) (\lambda (v1: T).(eq C (CHead c1 (Bind 
b) u1) (CHead c2 (Bind b) v1)))) (ex2 C (\lambda (c3: C).(csubst0 i v0 c3 
c2)) (\lambda (c3: C).(eq C (CHead c1 (Bind b) u1) (CHead c3 (Bind b) v2)))) 
(ex3_2 C T (\lambda (_: C).(\lambda (v1: T).(subst0 i v0 v1 v2))) (\lambda 
(c3: C).(\lambda (_: T).(csubst0 i v0 c3 c2))) (\lambda (c3: C).(\lambda (v1: 
T).(eq C (CHead c1 (Bind b) u1) (CHead c3 (Bind b) v1))))) (ex3_2_intro C T 
(\lambda (_: C).(\lambda (v1: T).(subst0 i v0 v1 v2))) (\lambda (c3: 
C).(\lambda (_: T).(csubst0 i v0 c3 c2))) (\lambda (c3: C).(\lambda (v1: 
T).(eq C (CHead c1 (Bind b) u1) (CHead c3 (Bind b) v1)))) c1 u1 H19 H18 
(refl_equal C (CHead c1 (Bind b) u1)))))))) k H10)))))))) H8)) 
H7)))))))))))))) y0 v x y H1))) H0))) H))))))).
(* COMMENTS
Initial nodes: 3878
END *)

