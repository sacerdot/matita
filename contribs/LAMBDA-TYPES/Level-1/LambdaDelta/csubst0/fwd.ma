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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/csubst0/fwd".

include "csubst0/defs.ma".

theorem csubst0_gen_sort:
 \forall (x: C).(\forall (v: T).(\forall (i: nat).(\forall (n: nat).((csubst0 
i v (CSort n) x) \to (\forall (P: Prop).P)))))
\def
 \lambda (x: C).(\lambda (v: T).(\lambda (i: nat).(\lambda (n: nat).(\lambda 
(H: (csubst0 i v (CSort n) x)).(\lambda (P: Prop).(let H0 \def (match H in 
csubst0 return (\lambda (n0: nat).(\lambda (t: T).(\lambda (c: C).(\lambda 
(c0: C).(\lambda (_: (csubst0 n0 t c c0)).((eq nat n0 i) \to ((eq T t v) \to 
((eq C c (CSort n)) \to ((eq C c0 x) \to P))))))))) with [(csubst0_snd k i0 
v0 u1 u2 H0 c) \Rightarrow (\lambda (H1: (eq nat (s k i0) i)).(\lambda (H2: 
(eq T v0 v)).(\lambda (H3: (eq C (CHead c k u1) (CSort n))).(\lambda (H4: (eq 
C (CHead c k u2) x)).(eq_ind nat (s k i0) (\lambda (_: nat).((eq T v0 v) \to 
((eq C (CHead c k u1) (CSort n)) \to ((eq C (CHead c k u2) x) \to ((subst0 i0 
v0 u1 u2) \to P))))) (\lambda (H5: (eq T v0 v)).(eq_ind T v (\lambda (t: 
T).((eq C (CHead c k u1) (CSort n)) \to ((eq C (CHead c k u2) x) \to ((subst0 
i0 t u1 u2) \to P)))) (\lambda (H6: (eq C (CHead c k u1) (CSort n))).(let H7 
\def (eq_ind C (CHead c k u1) (\lambda (e: C).(match e in C return (\lambda 
(_: C).Prop) with [(CSort _) \Rightarrow False | (CHead _ _ _) \Rightarrow 
True])) I (CSort n) H6) in (False_ind ((eq C (CHead c k u2) x) \to ((subst0 
i0 v u1 u2) \to P)) H7))) v0 (sym_eq T v0 v H5))) i H1 H2 H3 H4 H0))))) | 
(csubst0_fst k i0 c1 c2 v0 H0 u) \Rightarrow (\lambda (H1: (eq nat (s k i0) 
i)).(\lambda (H2: (eq T v0 v)).(\lambda (H3: (eq C (CHead c1 k u) (CSort 
n))).(\lambda (H4: (eq C (CHead c2 k u) x)).(eq_ind nat (s k i0) (\lambda (_: 
nat).((eq T v0 v) \to ((eq C (CHead c1 k u) (CSort n)) \to ((eq C (CHead c2 k 
u) x) \to ((csubst0 i0 v0 c1 c2) \to P))))) (\lambda (H5: (eq T v0 
v)).(eq_ind T v (\lambda (t: T).((eq C (CHead c1 k u) (CSort n)) \to ((eq C 
(CHead c2 k u) x) \to ((csubst0 i0 t c1 c2) \to P)))) (\lambda (H6: (eq C 
(CHead c1 k u) (CSort n))).(let H7 \def (eq_ind C (CHead c1 k u) (\lambda (e: 
C).(match e in C return (\lambda (_: C).Prop) with [(CSort _) \Rightarrow 
False | (CHead _ _ _) \Rightarrow True])) I (CSort n) H6) in (False_ind ((eq 
C (CHead c2 k u) x) \to ((csubst0 i0 v c1 c2) \to P)) H7))) v0 (sym_eq T v0 v 
H5))) i H1 H2 H3 H4 H0))))) | (csubst0_both k i0 v0 u1 u2 H0 c1 c2 H1) 
\Rightarrow (\lambda (H2: (eq nat (s k i0) i)).(\lambda (H3: (eq T v0 
v)).(\lambda (H4: (eq C (CHead c1 k u1) (CSort n))).(\lambda (H5: (eq C 
(CHead c2 k u2) x)).(eq_ind nat (s k i0) (\lambda (_: nat).((eq T v0 v) \to 
((eq C (CHead c1 k u1) (CSort n)) \to ((eq C (CHead c2 k u2) x) \to ((subst0 
i0 v0 u1 u2) \to ((csubst0 i0 v0 c1 c2) \to P)))))) (\lambda (H6: (eq T v0 
v)).(eq_ind T v (\lambda (t: T).((eq C (CHead c1 k u1) (CSort n)) \to ((eq C 
(CHead c2 k u2) x) \to ((subst0 i0 t u1 u2) \to ((csubst0 i0 t c1 c2) \to 
P))))) (\lambda (H7: (eq C (CHead c1 k u1) (CSort n))).(let H8 \def (eq_ind C 
(CHead c1 k u1) (\lambda (e: C).(match e in C return (\lambda (_: C).Prop) 
with [(CSort _) \Rightarrow False | (CHead _ _ _) \Rightarrow True])) I 
(CSort n) H7) in (False_ind ((eq C (CHead c2 k u2) x) \to ((subst0 i0 v u1 
u2) \to ((csubst0 i0 v c1 c2) \to P))) H8))) v0 (sym_eq T v0 v H6))) i H2 H3 
H4 H5 H0 H1)))))]) in (H0 (refl_equal nat i) (refl_equal T v) (refl_equal C 
(CSort n)) (refl_equal C x)))))))).

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
(v: T).(\lambda (i: nat).(\lambda (H: (csubst0 i v (CHead c1 k u1) x)).(let 
H0 \def (match H in csubst0 return (\lambda (n: nat).(\lambda (t: T).(\lambda 
(c: C).(\lambda (c0: C).(\lambda (_: (csubst0 n t c c0)).((eq nat n i) \to 
((eq T t v) \to ((eq C c (CHead c1 k u1)) \to ((eq C c0 x) \to (or3 (ex3_2 T 
nat (\lambda (_: T).(\lambda (j: nat).(eq nat i (s k j)))) (\lambda (u2: 
T).(\lambda (_: nat).(eq C x (CHead c1 k u2)))) (\lambda (u2: T).(\lambda (j: 
nat).(subst0 j v u1 u2)))) (ex3_2 C nat (\lambda (_: C).(\lambda (j: nat).(eq 
nat i (s k j)))) (\lambda (c2: C).(\lambda (_: nat).(eq C x (CHead c2 k 
u1)))) (\lambda (c2: C).(\lambda (j: nat).(csubst0 j v c1 c2)))) (ex4_3 T C 
nat (\lambda (_: T).(\lambda (_: C).(\lambda (j: nat).(eq nat i (s k j))))) 
(\lambda (u2: T).(\lambda (c2: C).(\lambda (_: nat).(eq C x (CHead c2 k 
u2))))) (\lambda (u2: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v u1 
u2)))) (\lambda (_: T).(\lambda (c2: C).(\lambda (j: nat).(csubst0 j v c1 
c2))))))))))))))) with [(csubst0_snd k0 i0 v0 u0 u2 H0 c) \Rightarrow 
(\lambda (H1: (eq nat (s k0 i0) i)).(\lambda (H2: (eq T v0 v)).(\lambda (H3: 
(eq C (CHead c k0 u0) (CHead c1 k u1))).(\lambda (H4: (eq C (CHead c k0 u2) 
x)).(eq_ind nat (s k0 i0) (\lambda (n: nat).((eq T v0 v) \to ((eq C (CHead c 
k0 u0) (CHead c1 k u1)) \to ((eq C (CHead c k0 u2) x) \to ((subst0 i0 v0 u0 
u2) \to (or3 (ex3_2 T nat (\lambda (_: T).(\lambda (j: nat).(eq nat n (s k 
j)))) (\lambda (u3: T).(\lambda (_: nat).(eq C x (CHead c1 k u3)))) (\lambda 
(u3: T).(\lambda (j: nat).(subst0 j v u1 u3)))) (ex3_2 C nat (\lambda (_: 
C).(\lambda (j: nat).(eq nat n (s k j)))) (\lambda (c2: C).(\lambda (_: 
nat).(eq C x (CHead c2 k u1)))) (\lambda (c2: C).(\lambda (j: nat).(csubst0 j 
v c1 c2)))) (ex4_3 T C nat (\lambda (_: T).(\lambda (_: C).(\lambda (j: 
nat).(eq nat n (s k j))))) (\lambda (u3: T).(\lambda (c2: C).(\lambda (_: 
nat).(eq C x (CHead c2 k u3))))) (\lambda (u3: T).(\lambda (_: C).(\lambda 
(j: nat).(subst0 j v u1 u3)))) (\lambda (_: T).(\lambda (c2: C).(\lambda (j: 
nat).(csubst0 j v c1 c2))))))))))) (\lambda (H5: (eq T v0 v)).(eq_ind T v 
(\lambda (t: T).((eq C (CHead c k0 u0) (CHead c1 k u1)) \to ((eq C (CHead c 
k0 u2) x) \to ((subst0 i0 t u0 u2) \to (or3 (ex3_2 T nat (\lambda (_: 
T).(\lambda (j: nat).(eq nat (s k0 i0) (s k j)))) (\lambda (u3: T).(\lambda 
(_: nat).(eq C x (CHead c1 k u3)))) (\lambda (u3: T).(\lambda (j: 
nat).(subst0 j v u1 u3)))) (ex3_2 C nat (\lambda (_: C).(\lambda (j: nat).(eq 
nat (s k0 i0) (s k j)))) (\lambda (c2: C).(\lambda (_: nat).(eq C x (CHead c2 
k u1)))) (\lambda (c2: C).(\lambda (j: nat).(csubst0 j v c1 c2)))) (ex4_3 T C 
nat (\lambda (_: T).(\lambda (_: C).(\lambda (j: nat).(eq nat (s k0 i0) (s k 
j))))) (\lambda (u3: T).(\lambda (c2: C).(\lambda (_: nat).(eq C x (CHead c2 
k u3))))) (\lambda (u3: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v u1 
u3)))) (\lambda (_: T).(\lambda (c2: C).(\lambda (j: nat).(csubst0 j v c1 
c2)))))))))) (\lambda (H6: (eq C (CHead c k0 u0) (CHead c1 k u1))).(let H7 
\def (f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: C).T) 
with [(CSort _) \Rightarrow u0 | (CHead _ _ t) \Rightarrow t])) (CHead c k0 
u0) (CHead c1 k u1) H6) in ((let H8 \def (f_equal C K (\lambda (e: C).(match 
e in C return (\lambda (_: C).K) with [(CSort _) \Rightarrow k0 | (CHead _ k 
_) \Rightarrow k])) (CHead c k0 u0) (CHead c1 k u1) H6) in ((let H9 \def 
(f_equal C C (\lambda (e: C).(match e in C return (\lambda (_: C).C) with 
[(CSort _) \Rightarrow c | (CHead c _ _) \Rightarrow c])) (CHead c k0 u0) 
(CHead c1 k u1) H6) in (eq_ind C c1 (\lambda (c0: C).((eq K k0 k) \to ((eq T 
u0 u1) \to ((eq C (CHead c0 k0 u2) x) \to ((subst0 i0 v u0 u2) \to (or3 
(ex3_2 T nat (\lambda (_: T).(\lambda (j: nat).(eq nat (s k0 i0) (s k j)))) 
(\lambda (u3: T).(\lambda (_: nat).(eq C x (CHead c1 k u3)))) (\lambda (u3: 
T).(\lambda (j: nat).(subst0 j v u1 u3)))) (ex3_2 C nat (\lambda (_: 
C).(\lambda (j: nat).(eq nat (s k0 i0) (s k j)))) (\lambda (c2: C).(\lambda 
(_: nat).(eq C x (CHead c2 k u1)))) (\lambda (c2: C).(\lambda (j: 
nat).(csubst0 j v c1 c2)))) (ex4_3 T C nat (\lambda (_: T).(\lambda (_: 
C).(\lambda (j: nat).(eq nat (s k0 i0) (s k j))))) (\lambda (u3: T).(\lambda 
(c2: C).(\lambda (_: nat).(eq C x (CHead c2 k u3))))) (\lambda (u3: 
T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v u1 u3)))) (\lambda (_: 
T).(\lambda (c2: C).(\lambda (j: nat).(csubst0 j v c1 c2))))))))))) (\lambda 
(H10: (eq K k0 k)).(eq_ind K k (\lambda (k1: K).((eq T u0 u1) \to ((eq C 
(CHead c1 k1 u2) x) \to ((subst0 i0 v u0 u2) \to (or3 (ex3_2 T nat (\lambda 
(_: T).(\lambda (j: nat).(eq nat (s k1 i0) (s k j)))) (\lambda (u3: 
T).(\lambda (_: nat).(eq C x (CHead c1 k u3)))) (\lambda (u3: T).(\lambda (j: 
nat).(subst0 j v u1 u3)))) (ex3_2 C nat (\lambda (_: C).(\lambda (j: nat).(eq 
nat (s k1 i0) (s k j)))) (\lambda (c2: C).(\lambda (_: nat).(eq C x (CHead c2 
k u1)))) (\lambda (c2: C).(\lambda (j: nat).(csubst0 j v c1 c2)))) (ex4_3 T C 
nat (\lambda (_: T).(\lambda (_: C).(\lambda (j: nat).(eq nat (s k1 i0) (s k 
j))))) (\lambda (u3: T).(\lambda (c2: C).(\lambda (_: nat).(eq C x (CHead c2 
k u3))))) (\lambda (u3: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v u1 
u3)))) (\lambda (_: T).(\lambda (c2: C).(\lambda (j: nat).(csubst0 j v c1 
c2)))))))))) (\lambda (H11: (eq T u0 u1)).(eq_ind T u1 (\lambda (t: T).((eq C 
(CHead c1 k u2) x) \to ((subst0 i0 v t u2) \to (or3 (ex3_2 T nat (\lambda (_: 
T).(\lambda (j: nat).(eq nat (s k i0) (s k j)))) (\lambda (u3: T).(\lambda 
(_: nat).(eq C x (CHead c1 k u3)))) (\lambda (u3: T).(\lambda (j: 
nat).(subst0 j v u1 u3)))) (ex3_2 C nat (\lambda (_: C).(\lambda (j: nat).(eq 
nat (s k i0) (s k j)))) (\lambda (c2: C).(\lambda (_: nat).(eq C x (CHead c2 
k u1)))) (\lambda (c2: C).(\lambda (j: nat).(csubst0 j v c1 c2)))) (ex4_3 T C 
nat (\lambda (_: T).(\lambda (_: C).(\lambda (j: nat).(eq nat (s k i0) (s k 
j))))) (\lambda (u3: T).(\lambda (c2: C).(\lambda (_: nat).(eq C x (CHead c2 
k u3))))) (\lambda (u3: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v u1 
u3)))) (\lambda (_: T).(\lambda (c2: C).(\lambda (j: nat).(csubst0 j v c1 
c2))))))))) (\lambda (H12: (eq C (CHead c1 k u2) x)).(eq_ind C (CHead c1 k 
u2) (\lambda (c0: C).((subst0 i0 v u1 u2) \to (or3 (ex3_2 T nat (\lambda (_: 
T).(\lambda (j: nat).(eq nat (s k i0) (s k j)))) (\lambda (u3: T).(\lambda 
(_: nat).(eq C c0 (CHead c1 k u3)))) (\lambda (u3: T).(\lambda (j: 
nat).(subst0 j v u1 u3)))) (ex3_2 C nat (\lambda (_: C).(\lambda (j: nat).(eq 
nat (s k i0) (s k j)))) (\lambda (c2: C).(\lambda (_: nat).(eq C c0 (CHead c2 
k u1)))) (\lambda (c2: C).(\lambda (j: nat).(csubst0 j v c1 c2)))) (ex4_3 T C 
nat (\lambda (_: T).(\lambda (_: C).(\lambda (j: nat).(eq nat (s k i0) (s k 
j))))) (\lambda (u3: T).(\lambda (c2: C).(\lambda (_: nat).(eq C c0 (CHead c2 
k u3))))) (\lambda (u3: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v u1 
u3)))) (\lambda (_: T).(\lambda (c2: C).(\lambda (j: nat).(csubst0 j v c1 
c2)))))))) (\lambda (H13: (subst0 i0 v u1 u2)).(let H \def (eq_ind K k0 
(\lambda (k: K).(eq nat (s k i0) i)) H1 k H10) in (or3_intro0 (ex3_2 T nat 
(\lambda (_: T).(\lambda (j: nat).(eq nat (s k i0) (s k j)))) (\lambda (u3: 
T).(\lambda (_: nat).(eq C (CHead c1 k u2) (CHead c1 k u3)))) (\lambda (u3: 
T).(\lambda (j: nat).(subst0 j v u1 u3)))) (ex3_2 C nat (\lambda (_: 
C).(\lambda (j: nat).(eq nat (s k i0) (s k j)))) (\lambda (c2: C).(\lambda 
(_: nat).(eq C (CHead c1 k u2) (CHead c2 k u1)))) (\lambda (c2: C).(\lambda 
(j: nat).(csubst0 j v c1 c2)))) (ex4_3 T C nat (\lambda (_: T).(\lambda (_: 
C).(\lambda (j: nat).(eq nat (s k i0) (s k j))))) (\lambda (u3: T).(\lambda 
(c2: C).(\lambda (_: nat).(eq C (CHead c1 k u2) (CHead c2 k u3))))) (\lambda 
(u3: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v u1 u3)))) (\lambda (_: 
T).(\lambda (c2: C).(\lambda (j: nat).(csubst0 j v c1 c2))))) (ex3_2_intro T 
nat (\lambda (_: T).(\lambda (j: nat).(eq nat (s k i0) (s k j)))) (\lambda 
(u3: T).(\lambda (_: nat).(eq C (CHead c1 k u2) (CHead c1 k u3)))) (\lambda 
(u3: T).(\lambda (j: nat).(subst0 j v u1 u3))) u2 i0 (refl_equal nat (s k 
i0)) (refl_equal C (CHead c1 k u2)) H13)))) x H12)) u0 (sym_eq T u0 u1 H11))) 
k0 (sym_eq K k0 k H10))) c (sym_eq C c c1 H9))) H8)) H7))) v0 (sym_eq T v0 v 
H5))) i H1 H2 H3 H4 H0))))) | (csubst0_fst k0 i0 c0 c2 v0 H0 u) \Rightarrow 
(\lambda (H1: (eq nat (s k0 i0) i)).(\lambda (H2: (eq T v0 v)).(\lambda (H3: 
(eq C (CHead c0 k0 u) (CHead c1 k u1))).(\lambda (H4: (eq C (CHead c2 k0 u) 
x)).(eq_ind nat (s k0 i0) (\lambda (n: nat).((eq T v0 v) \to ((eq C (CHead c0 
k0 u) (CHead c1 k u1)) \to ((eq C (CHead c2 k0 u) x) \to ((csubst0 i0 v0 c0 
c2) \to (or3 (ex3_2 T nat (\lambda (_: T).(\lambda (j: nat).(eq nat n (s k 
j)))) (\lambda (u2: T).(\lambda (_: nat).(eq C x (CHead c1 k u2)))) (\lambda 
(u2: T).(\lambda (j: nat).(subst0 j v u1 u2)))) (ex3_2 C nat (\lambda (_: 
C).(\lambda (j: nat).(eq nat n (s k j)))) (\lambda (c3: C).(\lambda (_: 
nat).(eq C x (CHead c3 k u1)))) (\lambda (c3: C).(\lambda (j: nat).(csubst0 j 
v c1 c3)))) (ex4_3 T C nat (\lambda (_: T).(\lambda (_: C).(\lambda (j: 
nat).(eq nat n (s k j))))) (\lambda (u2: T).(\lambda (c3: C).(\lambda (_: 
nat).(eq C x (CHead c3 k u2))))) (\lambda (u2: T).(\lambda (_: C).(\lambda 
(j: nat).(subst0 j v u1 u2)))) (\lambda (_: T).(\lambda (c3: C).(\lambda (j: 
nat).(csubst0 j v c1 c3))))))))))) (\lambda (H5: (eq T v0 v)).(eq_ind T v 
(\lambda (t: T).((eq C (CHead c0 k0 u) (CHead c1 k u1)) \to ((eq C (CHead c2 
k0 u) x) \to ((csubst0 i0 t c0 c2) \to (or3 (ex3_2 T nat (\lambda (_: 
T).(\lambda (j: nat).(eq nat (s k0 i0) (s k j)))) (\lambda (u2: T).(\lambda 
(_: nat).(eq C x (CHead c1 k u2)))) (\lambda (u2: T).(\lambda (j: 
nat).(subst0 j v u1 u2)))) (ex3_2 C nat (\lambda (_: C).(\lambda (j: nat).(eq 
nat (s k0 i0) (s k j)))) (\lambda (c3: C).(\lambda (_: nat).(eq C x (CHead c3 
k u1)))) (\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c1 c3)))) (ex4_3 T C 
nat (\lambda (_: T).(\lambda (_: C).(\lambda (j: nat).(eq nat (s k0 i0) (s k 
j))))) (\lambda (u2: T).(\lambda (c3: C).(\lambda (_: nat).(eq C x (CHead c3 
k u2))))) (\lambda (u2: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v u1 
u2)))) (\lambda (_: T).(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c1 
c3)))))))))) (\lambda (H6: (eq C (CHead c0 k0 u) (CHead c1 k u1))).(let H7 
\def (f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: C).T) 
with [(CSort _) \Rightarrow u | (CHead _ _ t) \Rightarrow t])) (CHead c0 k0 
u) (CHead c1 k u1) H6) in ((let H8 \def (f_equal C K (\lambda (e: C).(match e 
in C return (\lambda (_: C).K) with [(CSort _) \Rightarrow k0 | (CHead _ k _) 
\Rightarrow k])) (CHead c0 k0 u) (CHead c1 k u1) H6) in ((let H9 \def 
(f_equal C C (\lambda (e: C).(match e in C return (\lambda (_: C).C) with 
[(CSort _) \Rightarrow c0 | (CHead c _ _) \Rightarrow c])) (CHead c0 k0 u) 
(CHead c1 k u1) H6) in (eq_ind C c1 (\lambda (c: C).((eq K k0 k) \to ((eq T u 
u1) \to ((eq C (CHead c2 k0 u) x) \to ((csubst0 i0 v c c2) \to (or3 (ex3_2 T 
nat (\lambda (_: T).(\lambda (j: nat).(eq nat (s k0 i0) (s k j)))) (\lambda 
(u2: T).(\lambda (_: nat).(eq C x (CHead c1 k u2)))) (\lambda (u2: 
T).(\lambda (j: nat).(subst0 j v u1 u2)))) (ex3_2 C nat (\lambda (_: 
C).(\lambda (j: nat).(eq nat (s k0 i0) (s k j)))) (\lambda (c3: C).(\lambda 
(_: nat).(eq C x (CHead c3 k u1)))) (\lambda (c3: C).(\lambda (j: 
nat).(csubst0 j v c1 c3)))) (ex4_3 T C nat (\lambda (_: T).(\lambda (_: 
C).(\lambda (j: nat).(eq nat (s k0 i0) (s k j))))) (\lambda (u2: T).(\lambda 
(c3: C).(\lambda (_: nat).(eq C x (CHead c3 k u2))))) (\lambda (u2: 
T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v u1 u2)))) (\lambda (_: 
T).(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c1 c3))))))))))) (\lambda 
(H10: (eq K k0 k)).(eq_ind K k (\lambda (k1: K).((eq T u u1) \to ((eq C 
(CHead c2 k1 u) x) \to ((csubst0 i0 v c1 c2) \to (or3 (ex3_2 T nat (\lambda 
(_: T).(\lambda (j: nat).(eq nat (s k1 i0) (s k j)))) (\lambda (u2: 
T).(\lambda (_: nat).(eq C x (CHead c1 k u2)))) (\lambda (u2: T).(\lambda (j: 
nat).(subst0 j v u1 u2)))) (ex3_2 C nat (\lambda (_: C).(\lambda (j: nat).(eq 
nat (s k1 i0) (s k j)))) (\lambda (c3: C).(\lambda (_: nat).(eq C x (CHead c3 
k u1)))) (\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c1 c3)))) (ex4_3 T C 
nat (\lambda (_: T).(\lambda (_: C).(\lambda (j: nat).(eq nat (s k1 i0) (s k 
j))))) (\lambda (u2: T).(\lambda (c3: C).(\lambda (_: nat).(eq C x (CHead c3 
k u2))))) (\lambda (u2: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v u1 
u2)))) (\lambda (_: T).(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c1 
c3)))))))))) (\lambda (H11: (eq T u u1)).(eq_ind T u1 (\lambda (t: T).((eq C 
(CHead c2 k t) x) \to ((csubst0 i0 v c1 c2) \to (or3 (ex3_2 T nat (\lambda 
(_: T).(\lambda (j: nat).(eq nat (s k i0) (s k j)))) (\lambda (u2: 
T).(\lambda (_: nat).(eq C x (CHead c1 k u2)))) (\lambda (u2: T).(\lambda (j: 
nat).(subst0 j v u1 u2)))) (ex3_2 C nat (\lambda (_: C).(\lambda (j: nat).(eq 
nat (s k i0) (s k j)))) (\lambda (c3: C).(\lambda (_: nat).(eq C x (CHead c3 
k u1)))) (\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c1 c3)))) (ex4_3 T C 
nat (\lambda (_: T).(\lambda (_: C).(\lambda (j: nat).(eq nat (s k i0) (s k 
j))))) (\lambda (u2: T).(\lambda (c3: C).(\lambda (_: nat).(eq C x (CHead c3 
k u2))))) (\lambda (u2: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v u1 
u2)))) (\lambda (_: T).(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c1 
c3))))))))) (\lambda (H12: (eq C (CHead c2 k u1) x)).(eq_ind C (CHead c2 k 
u1) (\lambda (c: C).((csubst0 i0 v c1 c2) \to (or3 (ex3_2 T nat (\lambda (_: 
T).(\lambda (j: nat).(eq nat (s k i0) (s k j)))) (\lambda (u2: T).(\lambda 
(_: nat).(eq C c (CHead c1 k u2)))) (\lambda (u2: T).(\lambda (j: 
nat).(subst0 j v u1 u2)))) (ex3_2 C nat (\lambda (_: C).(\lambda (j: nat).(eq 
nat (s k i0) (s k j)))) (\lambda (c3: C).(\lambda (_: nat).(eq C c (CHead c3 
k u1)))) (\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c1 c3)))) (ex4_3 T C 
nat (\lambda (_: T).(\lambda (_: C).(\lambda (j: nat).(eq nat (s k i0) (s k 
j))))) (\lambda (u2: T).(\lambda (c3: C).(\lambda (_: nat).(eq C c (CHead c3 
k u2))))) (\lambda (u2: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v u1 
u2)))) (\lambda (_: T).(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c1 
c3)))))))) (\lambda (H13: (csubst0 i0 v c1 c2)).(let H \def (eq_ind K k0 
(\lambda (k: K).(eq nat (s k i0) i)) H1 k H10) in (or3_intro1 (ex3_2 T nat 
(\lambda (_: T).(\lambda (j: nat).(eq nat (s k i0) (s k j)))) (\lambda (u2: 
T).(\lambda (_: nat).(eq C (CHead c2 k u1) (CHead c1 k u2)))) (\lambda (u2: 
T).(\lambda (j: nat).(subst0 j v u1 u2)))) (ex3_2 C nat (\lambda (_: 
C).(\lambda (j: nat).(eq nat (s k i0) (s k j)))) (\lambda (c3: C).(\lambda 
(_: nat).(eq C (CHead c2 k u1) (CHead c3 k u1)))) (\lambda (c3: C).(\lambda 
(j: nat).(csubst0 j v c1 c3)))) (ex4_3 T C nat (\lambda (_: T).(\lambda (_: 
C).(\lambda (j: nat).(eq nat (s k i0) (s k j))))) (\lambda (u2: T).(\lambda 
(c3: C).(\lambda (_: nat).(eq C (CHead c2 k u1) (CHead c3 k u2))))) (\lambda 
(u2: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v u1 u2)))) (\lambda (_: 
T).(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c1 c3))))) (ex3_2_intro C 
nat (\lambda (_: C).(\lambda (j: nat).(eq nat (s k i0) (s k j)))) (\lambda 
(c3: C).(\lambda (_: nat).(eq C (CHead c2 k u1) (CHead c3 k u1)))) (\lambda 
(c3: C).(\lambda (j: nat).(csubst0 j v c1 c3))) c2 i0 (refl_equal nat (s k 
i0)) (refl_equal C (CHead c2 k u1)) H13)))) x H12)) u (sym_eq T u u1 H11))) 
k0 (sym_eq K k0 k H10))) c0 (sym_eq C c0 c1 H9))) H8)) H7))) v0 (sym_eq T v0 
v H5))) i H1 H2 H3 H4 H0))))) | (csubst0_both k0 i0 v0 u0 u2 H0 c0 c2 H1) 
\Rightarrow (\lambda (H2: (eq nat (s k0 i0) i)).(\lambda (H3: (eq T v0 
v)).(\lambda (H4: (eq C (CHead c0 k0 u0) (CHead c1 k u1))).(\lambda (H5: (eq 
C (CHead c2 k0 u2) x)).(eq_ind nat (s k0 i0) (\lambda (n: nat).((eq T v0 v) 
\to ((eq C (CHead c0 k0 u0) (CHead c1 k u1)) \to ((eq C (CHead c2 k0 u2) x) 
\to ((subst0 i0 v0 u0 u2) \to ((csubst0 i0 v0 c0 c2) \to (or3 (ex3_2 T nat 
(\lambda (_: T).(\lambda (j: nat).(eq nat n (s k j)))) (\lambda (u3: 
T).(\lambda (_: nat).(eq C x (CHead c1 k u3)))) (\lambda (u3: T).(\lambda (j: 
nat).(subst0 j v u1 u3)))) (ex3_2 C nat (\lambda (_: C).(\lambda (j: nat).(eq 
nat n (s k j)))) (\lambda (c3: C).(\lambda (_: nat).(eq C x (CHead c3 k 
u1)))) (\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c1 c3)))) (ex4_3 T C 
nat (\lambda (_: T).(\lambda (_: C).(\lambda (j: nat).(eq nat n (s k j))))) 
(\lambda (u3: T).(\lambda (c3: C).(\lambda (_: nat).(eq C x (CHead c3 k 
u3))))) (\lambda (u3: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v u1 
u3)))) (\lambda (_: T).(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c1 
c3)))))))))))) (\lambda (H6: (eq T v0 v)).(eq_ind T v (\lambda (t: T).((eq C 
(CHead c0 k0 u0) (CHead c1 k u1)) \to ((eq C (CHead c2 k0 u2) x) \to ((subst0 
i0 t u0 u2) \to ((csubst0 i0 t c0 c2) \to (or3 (ex3_2 T nat (\lambda (_: 
T).(\lambda (j: nat).(eq nat (s k0 i0) (s k j)))) (\lambda (u3: T).(\lambda 
(_: nat).(eq C x (CHead c1 k u3)))) (\lambda (u3: T).(\lambda (j: 
nat).(subst0 j v u1 u3)))) (ex3_2 C nat (\lambda (_: C).(\lambda (j: nat).(eq 
nat (s k0 i0) (s k j)))) (\lambda (c3: C).(\lambda (_: nat).(eq C x (CHead c3 
k u1)))) (\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c1 c3)))) (ex4_3 T C 
nat (\lambda (_: T).(\lambda (_: C).(\lambda (j: nat).(eq nat (s k0 i0) (s k 
j))))) (\lambda (u3: T).(\lambda (c3: C).(\lambda (_: nat).(eq C x (CHead c3 
k u3))))) (\lambda (u3: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v u1 
u3)))) (\lambda (_: T).(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c1 
c3))))))))))) (\lambda (H7: (eq C (CHead c0 k0 u0) (CHead c1 k u1))).(let H8 
\def (f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: C).T) 
with [(CSort _) \Rightarrow u0 | (CHead _ _ t) \Rightarrow t])) (CHead c0 k0 
u0) (CHead c1 k u1) H7) in ((let H9 \def (f_equal C K (\lambda (e: C).(match 
e in C return (\lambda (_: C).K) with [(CSort _) \Rightarrow k0 | (CHead _ k 
_) \Rightarrow k])) (CHead c0 k0 u0) (CHead c1 k u1) H7) in ((let H10 \def 
(f_equal C C (\lambda (e: C).(match e in C return (\lambda (_: C).C) with 
[(CSort _) \Rightarrow c0 | (CHead c _ _) \Rightarrow c])) (CHead c0 k0 u0) 
(CHead c1 k u1) H7) in (eq_ind C c1 (\lambda (c: C).((eq K k0 k) \to ((eq T 
u0 u1) \to ((eq C (CHead c2 k0 u2) x) \to ((subst0 i0 v u0 u2) \to ((csubst0 
i0 v c c2) \to (or3 (ex3_2 T nat (\lambda (_: T).(\lambda (j: nat).(eq nat (s 
k0 i0) (s k j)))) (\lambda (u3: T).(\lambda (_: nat).(eq C x (CHead c1 k 
u3)))) (\lambda (u3: T).(\lambda (j: nat).(subst0 j v u1 u3)))) (ex3_2 C nat 
(\lambda (_: C).(\lambda (j: nat).(eq nat (s k0 i0) (s k j)))) (\lambda (c3: 
C).(\lambda (_: nat).(eq C x (CHead c3 k u1)))) (\lambda (c3: C).(\lambda (j: 
nat).(csubst0 j v c1 c3)))) (ex4_3 T C nat (\lambda (_: T).(\lambda (_: 
C).(\lambda (j: nat).(eq nat (s k0 i0) (s k j))))) (\lambda (u3: T).(\lambda 
(c3: C).(\lambda (_: nat).(eq C x (CHead c3 k u3))))) (\lambda (u3: 
T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v u1 u3)))) (\lambda (_: 
T).(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c1 c3)))))))))))) (\lambda 
(H11: (eq K k0 k)).(eq_ind K k (\lambda (k1: K).((eq T u0 u1) \to ((eq C 
(CHead c2 k1 u2) x) \to ((subst0 i0 v u0 u2) \to ((csubst0 i0 v c1 c2) \to 
(or3 (ex3_2 T nat (\lambda (_: T).(\lambda (j: nat).(eq nat (s k1 i0) (s k 
j)))) (\lambda (u3: T).(\lambda (_: nat).(eq C x (CHead c1 k u3)))) (\lambda 
(u3: T).(\lambda (j: nat).(subst0 j v u1 u3)))) (ex3_2 C nat (\lambda (_: 
C).(\lambda (j: nat).(eq nat (s k1 i0) (s k j)))) (\lambda (c3: C).(\lambda 
(_: nat).(eq C x (CHead c3 k u1)))) (\lambda (c3: C).(\lambda (j: 
nat).(csubst0 j v c1 c3)))) (ex4_3 T C nat (\lambda (_: T).(\lambda (_: 
C).(\lambda (j: nat).(eq nat (s k1 i0) (s k j))))) (\lambda (u3: T).(\lambda 
(c3: C).(\lambda (_: nat).(eq C x (CHead c3 k u3))))) (\lambda (u3: 
T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v u1 u3)))) (\lambda (_: 
T).(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c1 c3))))))))))) (\lambda 
(H12: (eq T u0 u1)).(eq_ind T u1 (\lambda (t: T).((eq C (CHead c2 k u2) x) 
\to ((subst0 i0 v t u2) \to ((csubst0 i0 v c1 c2) \to (or3 (ex3_2 T nat 
(\lambda (_: T).(\lambda (j: nat).(eq nat (s k i0) (s k j)))) (\lambda (u3: 
T).(\lambda (_: nat).(eq C x (CHead c1 k u3)))) (\lambda (u3: T).(\lambda (j: 
nat).(subst0 j v u1 u3)))) (ex3_2 C nat (\lambda (_: C).(\lambda (j: nat).(eq 
nat (s k i0) (s k j)))) (\lambda (c3: C).(\lambda (_: nat).(eq C x (CHead c3 
k u1)))) (\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c1 c3)))) (ex4_3 T C 
nat (\lambda (_: T).(\lambda (_: C).(\lambda (j: nat).(eq nat (s k i0) (s k 
j))))) (\lambda (u3: T).(\lambda (c3: C).(\lambda (_: nat).(eq C x (CHead c3 
k u3))))) (\lambda (u3: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v u1 
u3)))) (\lambda (_: T).(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c1 
c3)))))))))) (\lambda (H13: (eq C (CHead c2 k u2) x)).(eq_ind C (CHead c2 k 
u2) (\lambda (c: C).((subst0 i0 v u1 u2) \to ((csubst0 i0 v c1 c2) \to (or3 
(ex3_2 T nat (\lambda (_: T).(\lambda (j: nat).(eq nat (s k i0) (s k j)))) 
(\lambda (u3: T).(\lambda (_: nat).(eq C c (CHead c1 k u3)))) (\lambda (u3: 
T).(\lambda (j: nat).(subst0 j v u1 u3)))) (ex3_2 C nat (\lambda (_: 
C).(\lambda (j: nat).(eq nat (s k i0) (s k j)))) (\lambda (c3: C).(\lambda 
(_: nat).(eq C c (CHead c3 k u1)))) (\lambda (c3: C).(\lambda (j: 
nat).(csubst0 j v c1 c3)))) (ex4_3 T C nat (\lambda (_: T).(\lambda (_: 
C).(\lambda (j: nat).(eq nat (s k i0) (s k j))))) (\lambda (u3: T).(\lambda 
(c3: C).(\lambda (_: nat).(eq C c (CHead c3 k u3))))) (\lambda (u3: 
T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v u1 u3)))) (\lambda (_: 
T).(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c1 c3))))))))) (\lambda 
(H14: (subst0 i0 v u1 u2)).(\lambda (H15: (csubst0 i0 v c1 c2)).(let H \def 
(eq_ind K k0 (\lambda (k: K).(eq nat (s k i0) i)) H2 k H11) in (or3_intro2 
(ex3_2 T nat (\lambda (_: T).(\lambda (j: nat).(eq nat (s k i0) (s k j)))) 
(\lambda (u3: T).(\lambda (_: nat).(eq C (CHead c2 k u2) (CHead c1 k u3)))) 
(\lambda (u3: T).(\lambda (j: nat).(subst0 j v u1 u3)))) (ex3_2 C nat 
(\lambda (_: C).(\lambda (j: nat).(eq nat (s k i0) (s k j)))) (\lambda (c3: 
C).(\lambda (_: nat).(eq C (CHead c2 k u2) (CHead c3 k u1)))) (\lambda (c3: 
C).(\lambda (j: nat).(csubst0 j v c1 c3)))) (ex4_3 T C nat (\lambda (_: 
T).(\lambda (_: C).(\lambda (j: nat).(eq nat (s k i0) (s k j))))) (\lambda 
(u3: T).(\lambda (c3: C).(\lambda (_: nat).(eq C (CHead c2 k u2) (CHead c3 k 
u3))))) (\lambda (u3: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v u1 
u3)))) (\lambda (_: T).(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c1 
c3))))) (ex4_3_intro T C nat (\lambda (_: T).(\lambda (_: C).(\lambda (j: 
nat).(eq nat (s k i0) (s k j))))) (\lambda (u3: T).(\lambda (c3: C).(\lambda 
(_: nat).(eq C (CHead c2 k u2) (CHead c3 k u3))))) (\lambda (u3: T).(\lambda 
(_: C).(\lambda (j: nat).(subst0 j v u1 u3)))) (\lambda (_: T).(\lambda (c3: 
C).(\lambda (j: nat).(csubst0 j v c1 c3)))) u2 c2 i0 (refl_equal nat (s k 
i0)) (refl_equal C (CHead c2 k u2)) H14 H15))))) x H13)) u0 (sym_eq T u0 u1 
H12))) k0 (sym_eq K k0 k H11))) c0 (sym_eq C c0 c1 H10))) H9)) H8))) v0 
(sym_eq T v0 v H6))) i H2 H3 H4 H5 H0 H1)))))]) in (H0 (refl_equal nat i) 
(refl_equal T v) (refl_equal C (CHead c1 k u1)) (refl_equal C x))))))))).

