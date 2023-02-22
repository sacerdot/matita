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

include "basic_1A/csubst0/defs.ma".

include "basic_1A/C/fwd.ma".

implied rec lemma csubst0_ind (P: (nat \to (T \to (C \to (C \to Prop))))) (f: 
(\forall (k: K).(\forall (i: nat).(\forall (v: T).(\forall (u1: T).(\forall 
(u2: T).((subst0 i v u1 u2) \to (\forall (c: C).(P (s k i) v (CHead c k u1) 
(CHead c k u2)))))))))) (f0: (\forall (k: K).(\forall (i: nat).(\forall (c1: 
C).(\forall (c2: C).(\forall (v: T).((csubst0 i v c1 c2) \to ((P i v c1 c2) 
\to (\forall (u: T).(P (s k i) v (CHead c1 k u) (CHead c2 k u))))))))))) (f1: 
(\forall (k: K).(\forall (i: nat).(\forall (v: T).(\forall (u1: T).(\forall 
(u2: T).((subst0 i v u1 u2) \to (\forall (c1: C).(\forall (c2: C).((csubst0 i 
v c1 c2) \to ((P i v c1 c2) \to (P (s k i) v (CHead c1 k u1) (CHead c2 k 
u2))))))))))))) (n: nat) (t: T) (c: C) (c0: C) (c1: csubst0 n t c c0) on c1: 
P n t c c0 \def match c1 with [(csubst0_snd k i v u1 u2 s0 c2) \Rightarrow (f 
k i v u1 u2 s0 c2) | (csubst0_fst k i c2 c3 v c4 u) \Rightarrow (f0 k i c2 c3 
v c4 ((csubst0_ind P f f0 f1) i v c2 c3 c4) u) | (csubst0_both k i v u1 u2 s0 
c2 c3 c4) \Rightarrow (f1 k i v u1 u2 s0 c2 c3 c4 ((csubst0_ind P f f0 f1) i 
v c2 c3 c4))].

lemma csubst0_gen_sort:
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
(ee: C).(match ee with [(CSort _) \Rightarrow False | (CHead _ _ _) 
\Rightarrow True])) I (CSort n) H2) in (False_ind P H3)))))))))) (\lambda (k: 
K).(\lambda (i0: nat).(\lambda (c1: C).(\lambda (c2: C).(\lambda (v0: 
T).(\lambda (_: (csubst0 i0 v0 c1 c2)).(\lambda (_: (((eq C c1 (CSort n)) \to 
P))).(\lambda (u: T).(\lambda (H3: (eq C (CHead c1 k u) (CSort n))).(let H4 
\def (eq_ind C (CHead c1 k u) (\lambda (ee: C).(match ee with [(CSort _) 
\Rightarrow False | (CHead _ _ _) \Rightarrow True])) I (CSort n) H3) in 
(False_ind P H4))))))))))) (\lambda (k: K).(\lambda (i0: nat).(\lambda (v0: 
T).(\lambda (u1: T).(\lambda (u2: T).(\lambda (_: (subst0 i0 v0 u1 
u2)).(\lambda (c1: C).(\lambda (c2: C).(\lambda (_: (csubst0 i0 v0 c1 
c2)).(\lambda (_: (((eq C c1 (CSort n)) \to P))).(\lambda (H4: (eq C (CHead 
c1 k u1) (CSort n))).(let H5 \def (eq_ind C (CHead c1 k u1) (\lambda (ee: 
C).(match ee with [(CSort _) \Rightarrow False | (CHead _ _ _) \Rightarrow 
True])) I (CSort n) H4) in (False_ind P H5))))))))))))) i v y x H0))) H)))))).

lemma csubst0_gen_head:
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
C).(match e with [(CSort _) \Rightarrow c | (CHead c0 _ _) \Rightarrow c0])) 
(CHead c k0 u0) (CHead c1 k u1) H2) in ((let H4 \def (f_equal C K (\lambda 
(e: C).(match e with [(CSort _) \Rightarrow k0 | (CHead _ k1 _) \Rightarrow 
k1])) (CHead c k0 u0) (CHead c1 k u1) H2) in ((let H5 \def (f_equal C T 
(\lambda (e: C).(match e with [(CSort _) \Rightarrow u0 | (CHead _ _ t) 
\Rightarrow t])) (CHead c k0 u0) (CHead c1 k u1) H2) in (\lambda (H6: (eq K 
k0 k)).(\lambda (H7: (eq C c c1)).(eq_ind_r C c1 (\lambda (c0: C).(or3 (ex3_2 
T nat (\lambda (_: T).(\lambda (j: nat).(eq nat (s k0 i0) (s k j)))) (\lambda 
(u3: T).(\lambda (_: nat).(eq C (CHead c0 k0 u2) (CHead c1 k u3)))) (\lambda 
(u3: T).(\lambda (j: nat).(subst0 j v0 u1 u3)))) (ex3_2 C nat (\lambda (_: 
C).(\lambda (j: nat).(eq nat (s k0 i0) (s k j)))) (\lambda (c2: C).(\lambda 
(_: nat).(eq C (CHead c0 k0 u2) (CHead c2 k u1)))) (\lambda (c2: C).(\lambda 
(j: nat).(csubst0 j v0 c1 c2)))) (ex4_3 T C nat (\lambda (_: T).(\lambda (_: 
C).(\lambda (j: nat).(eq nat (s k0 i0) (s k j))))) (\lambda (u3: T).(\lambda 
(c2: C).(\lambda (_: nat).(eq C (CHead c0 k0 u2) (CHead c2 k u3))))) (\lambda 
(u3: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v0 u1 u3)))) (\lambda (_: 
T).(\lambda (c2: C).(\lambda (j: nat).(csubst0 j v0 c1 c2))))))) (let H8 \def 
(eq_ind T u0 (\lambda (t: T).(subst0 i0 v0 t u2)) H1 u1 H5) in (eq_ind_r K k 
(\lambda (k1: K).(or3 (ex3_2 T nat (\lambda (_: T).(\lambda (j: nat).(eq nat 
(s k1 i0) (s k j)))) (\lambda (u3: T).(\lambda (_: nat).(eq C (CHead c1 k1 
u2) (CHead c1 k u3)))) (\lambda (u3: T).(\lambda (j: nat).(subst0 j v0 u1 
u3)))) (ex3_2 C nat (\lambda (_: C).(\lambda (j: nat).(eq nat (s k1 i0) (s k 
j)))) (\lambda (c2: C).(\lambda (_: nat).(eq C (CHead c1 k1 u2) (CHead c2 k 
u1)))) (\lambda (c2: C).(\lambda (j: nat).(csubst0 j v0 c1 c2)))) (ex4_3 T C 
nat (\lambda (_: T).(\lambda (_: C).(\lambda (j: nat).(eq nat (s k1 i0) (s k 
j))))) (\lambda (u3: T).(\lambda (c2: C).(\lambda (_: nat).(eq C (CHead c1 k1 
u2) (CHead c2 k u3))))) (\lambda (u3: T).(\lambda (_: C).(\lambda (j: 
nat).(subst0 j v0 u1 u3)))) (\lambda (_: T).(\lambda (c2: C).(\lambda (j: 
nat).(csubst0 j v0 c1 c2))))))) (or3_intro0 (ex3_2 T nat (\lambda (_: 
T).(\lambda (j: nat).(eq nat (s k i0) (s k j)))) (\lambda (u3: T).(\lambda 
(_: nat).(eq C (CHead c1 k u2) (CHead c1 k u3)))) (\lambda (u3: T).(\lambda 
(j: nat).(subst0 j v0 u1 u3)))) (ex3_2 C nat (\lambda (_: C).(\lambda (j: 
nat).(eq nat (s k i0) (s k j)))) (\lambda (c2: C).(\lambda (_: nat).(eq C 
(CHead c1 k u2) (CHead c2 k u1)))) (\lambda (c2: C).(\lambda (j: 
nat).(csubst0 j v0 c1 c2)))) (ex4_3 T C nat (\lambda (_: T).(\lambda (_: 
C).(\lambda (j: nat).(eq nat (s k i0) (s k j))))) (\lambda (u3: T).(\lambda 
(c2: C).(\lambda (_: nat).(eq C (CHead c1 k u2) (CHead c2 k u3))))) (\lambda 
(u3: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v0 u1 u3)))) (\lambda (_: 
T).(\lambda (c2: C).(\lambda (j: nat).(csubst0 j v0 c1 c2))))) (ex3_2_intro T 
nat (\lambda (_: T).(\lambda (j: nat).(eq nat (s k i0) (s k j)))) (\lambda 
(u3: T).(\lambda (_: nat).(eq C (CHead c1 k u2) (CHead c1 k u3)))) (\lambda 
(u3: T).(\lambda (j: nat).(subst0 j v0 u1 u3))) u2 i0 (refl_equal nat (s k 
i0)) (refl_equal C (CHead c1 k u2)) H8)) k0 H6)) c H7)))) H4)) H3)))))))))) 
(\lambda (k0: K).(\lambda (i0: nat).(\lambda (c0: C).(\lambda (c2: 
C).(\lambda (v0: T).(\lambda (H1: (csubst0 i0 v0 c0 c2)).(\lambda (H2: (((eq 
C c0 (CHead c1 k u1)) \to (or3 (ex3_2 T nat (\lambda (_: T).(\lambda (j: 
nat).(eq nat i0 (s k j)))) (\lambda (u2: T).(\lambda (_: nat).(eq C c2 (CHead 
c1 k u2)))) (\lambda (u2: T).(\lambda (j: nat).(subst0 j v0 u1 u2)))) (ex3_2 
C nat (\lambda (_: C).(\lambda (j: nat).(eq nat i0 (s k j)))) (\lambda (c3: 
C).(\lambda (_: nat).(eq C c2 (CHead c3 k u1)))) (\lambda (c3: C).(\lambda 
(j: nat).(csubst0 j v0 c1 c3)))) (ex4_3 T C nat (\lambda (_: T).(\lambda (_: 
C).(\lambda (j: nat).(eq nat i0 (s k j))))) (\lambda (u2: T).(\lambda (c3: 
C).(\lambda (_: nat).(eq C c2 (CHead c3 k u2))))) (\lambda (u2: T).(\lambda 
(_: C).(\lambda (j: nat).(subst0 j v0 u1 u2)))) (\lambda (_: T).(\lambda (c3: 
C).(\lambda (j: nat).(csubst0 j v0 c1 c3))))))))).(\lambda (u: T).(\lambda 
(H3: (eq C (CHead c0 k0 u) (CHead c1 k u1))).(let H4 \def (f_equal C C 
(\lambda (e: C).(match e with [(CSort _) \Rightarrow c0 | (CHead c _ _) 
\Rightarrow c])) (CHead c0 k0 u) (CHead c1 k u1) H3) in ((let H5 \def 
(f_equal C K (\lambda (e: C).(match e with [(CSort _) \Rightarrow k0 | (CHead 
_ k1 _) \Rightarrow k1])) (CHead c0 k0 u) (CHead c1 k u1) H3) in ((let H6 
\def (f_equal C T (\lambda (e: C).(match e with [(CSort _) \Rightarrow u | 
(CHead _ _ t) \Rightarrow t])) (CHead c0 k0 u) (CHead c1 k u1) H3) in 
(\lambda (H7: (eq K k0 k)).(\lambda (H8: (eq C c0 c1)).(eq_ind_r T u1 
(\lambda (t: T).(or3 (ex3_2 T nat (\lambda (_: T).(\lambda (j: nat).(eq nat 
(s k0 i0) (s k j)))) (\lambda (u2: T).(\lambda (_: nat).(eq C (CHead c2 k0 t) 
(CHead c1 k u2)))) (\lambda (u2: T).(\lambda (j: nat).(subst0 j v0 u1 u2)))) 
(ex3_2 C nat (\lambda (_: C).(\lambda (j: nat).(eq nat (s k0 i0) (s k j)))) 
(\lambda (c3: C).(\lambda (_: nat).(eq C (CHead c2 k0 t) (CHead c3 k u1)))) 
(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v0 c1 c3)))) (ex4_3 T C nat 
(\lambda (_: T).(\lambda (_: C).(\lambda (j: nat).(eq nat (s k0 i0) (s k 
j))))) (\lambda (u2: T).(\lambda (c3: C).(\lambda (_: nat).(eq C (CHead c2 k0 
t) (CHead c3 k u2))))) (\lambda (u2: T).(\lambda (_: C).(\lambda (j: 
nat).(subst0 j v0 u1 u2)))) (\lambda (_: T).(\lambda (c3: C).(\lambda (j: 
nat).(csubst0 j v0 c1 c3))))))) (let H9 \def (eq_ind C c0 (\lambda (c: 
C).((eq C c (CHead c1 k u1)) \to (or3 (ex3_2 T nat (\lambda (_: T).(\lambda 
(j: nat).(eq nat i0 (s k j)))) (\lambda (u2: T).(\lambda (_: nat).(eq C c2 
(CHead c1 k u2)))) (\lambda (u2: T).(\lambda (j: nat).(subst0 j v0 u1 u2)))) 
(ex3_2 C nat (\lambda (_: C).(\lambda (j: nat).(eq nat i0 (s k j)))) (\lambda 
(c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k u1)))) (\lambda (c3: 
C).(\lambda (j: nat).(csubst0 j v0 c1 c3)))) (ex4_3 T C nat (\lambda (_: 
T).(\lambda (_: C).(\lambda (j: nat).(eq nat i0 (s k j))))) (\lambda (u2: 
T).(\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k u2))))) (\lambda 
(u2: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v0 u1 u2)))) (\lambda (_: 
T).(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v0 c1 c3)))))))) H2 c1 H8) 
in (let H10 \def (eq_ind C c0 (\lambda (c: C).(csubst0 i0 v0 c c2)) H1 c1 H8) 
in (eq_ind_r K k (\lambda (k1: K).(or3 (ex3_2 T nat (\lambda (_: T).(\lambda 
(j: nat).(eq nat (s k1 i0) (s k j)))) (\lambda (u2: T).(\lambda (_: nat).(eq 
C (CHead c2 k1 u1) (CHead c1 k u2)))) (\lambda (u2: T).(\lambda (j: 
nat).(subst0 j v0 u1 u2)))) (ex3_2 C nat (\lambda (_: C).(\lambda (j: 
nat).(eq nat (s k1 i0) (s k j)))) (\lambda (c3: C).(\lambda (_: nat).(eq C 
(CHead c2 k1 u1) (CHead c3 k u1)))) (\lambda (c3: C).(\lambda (j: 
nat).(csubst0 j v0 c1 c3)))) (ex4_3 T C nat (\lambda (_: T).(\lambda (_: 
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
(\lambda (e: C).(match e with [(CSort _) \Rightarrow c0 | (CHead c _ _) 
\Rightarrow c])) (CHead c0 k0 u0) (CHead c1 k u1) H4) in ((let H6 \def 
(f_equal C K (\lambda (e: C).(match e with [(CSort _) \Rightarrow k0 | (CHead 
_ k1 _) \Rightarrow k1])) (CHead c0 k0 u0) (CHead c1 k u1) H4) in ((let H7 
\def (f_equal C T (\lambda (e: C).(match e with [(CSort _) \Rightarrow u0 | 
(CHead _ _ t) \Rightarrow t])) (CHead c0 k0 u0) (CHead c1 k u1) H4) in 
(\lambda (H8: (eq K k0 k)).(\lambda (H9: (eq C c0 c1)).(let H10 \def (eq_ind 
C c0 (\lambda (c: C).((eq C c (CHead c1 k u1)) \to (or3 (ex3_2 T nat (\lambda 
(_: T).(\lambda (j: nat).(eq nat i0 (s k j)))) (\lambda (u3: T).(\lambda (_: 
nat).(eq C c2 (CHead c1 k u3)))) (\lambda (u3: T).(\lambda (j: nat).(subst0 j 
v0 u1 u3)))) (ex3_2 C nat (\lambda (_: C).(\lambda (j: nat).(eq nat i0 (s k 
j)))) (\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k u1)))) (\lambda 
(c3: C).(\lambda (j: nat).(csubst0 j v0 c1 c3)))) (ex4_3 T C nat (\lambda (_: 
T).(\lambda (_: C).(\lambda (j: nat).(eq nat i0 (s k j))))) (\lambda (u3: 
T).(\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k u3))))) (\lambda 
(u3: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v0 u1 u3)))) (\lambda (_: 
T).(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v0 c1 c3)))))))) H3 c1 H9) 
in (let H11 \def (eq_ind C c0 (\lambda (c: C).(csubst0 i0 v0 c c2)) H2 c1 H9) 
in (let H12 \def (eq_ind T u0 (\lambda (t: T).(subst0 i0 v0 t u2)) H1 u1 H7) 
in (eq_ind_r K k (\lambda (k1: K).(or3 (ex3_2 T nat (\lambda (_: T).(\lambda 
(j: nat).(eq nat (s k1 i0) (s k j)))) (\lambda (u3: T).(\lambda (_: nat).(eq 
C (CHead c2 k1 u2) (CHead c1 k u3)))) (\lambda (u3: T).(\lambda (j: 
nat).(subst0 j v0 u1 u3)))) (ex3_2 C nat (\lambda (_: C).(\lambda (j: 
nat).(eq nat (s k1 i0) (s k j)))) (\lambda (c3: C).(\lambda (_: nat).(eq C 
(CHead c2 k1 u2) (CHead c3 k u1)))) (\lambda (c3: C).(\lambda (j: 
nat).(csubst0 j v0 c1 c3)))) (ex4_3 T C nat (\lambda (_: T).(\lambda (_: 
C).(\lambda (j: nat).(eq nat (s k1 i0) (s k j))))) (\lambda (u3: T).(\lambda 
(c3: C).(\lambda (_: nat).(eq C (CHead c2 k1 u2) (CHead c3 k u3))))) (\lambda 
(u3: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v0 u1 u3)))) (\lambda (_: 
T).(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v0 c1 c3))))))) (or3_intro2 
(ex3_2 T nat (\lambda (_: T).(\lambda (j: nat).(eq nat (s k i0) (s k j)))) 
(\lambda (u3: T).(\lambda (_: nat).(eq C (CHead c2 k u2) (CHead c1 k u3)))) 
(\lambda (u3: T).(\lambda (j: nat).(subst0 j v0 u1 u3)))) (ex3_2 C nat 
(\lambda (_: C).(\lambda (j: nat).(eq nat (s k i0) (s k j)))) (\lambda (c3: 
C).(\lambda (_: nat).(eq C (CHead c2 k u2) (CHead c3 k u1)))) (\lambda (c3: 
C).(\lambda (j: nat).(csubst0 j v0 c1 c3)))) (ex4_3 T C nat (\lambda (_: 
T).(\lambda (_: C).(\lambda (j: nat).(eq nat (s k i0) (s k j))))) (\lambda 
(u3: T).(\lambda (c3: C).(\lambda (_: nat).(eq C (CHead c2 k u2) (CHead c3 k 
u3))))) (\lambda (u3: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v0 u1 
u3)))) (\lambda (_: T).(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v0 c1 
c3))))) (ex4_3_intro T C nat (\lambda (_: T).(\lambda (_: C).(\lambda (j: 
nat).(eq nat (s k i0) (s k j))))) (\lambda (u3: T).(\lambda (c3: C).(\lambda 
(_: nat).(eq C (CHead c2 k u2) (CHead c3 k u3))))) (\lambda (u3: T).(\lambda 
(_: C).(\lambda (j: nat).(subst0 j v0 u1 u3)))) (\lambda (_: T).(\lambda (c3: 
C).(\lambda (j: nat).(csubst0 j v0 c1 c3)))) u2 c2 i0 (refl_equal nat (s k 
i0)) (refl_equal C (CHead c2 k u2)) H12 H11)) k0 H8))))))) H6)) 
H5))))))))))))) i v y x H0))) H))))))).

lemma csubst0_gen_S_bind_2:
 \forall (b: B).(\forall (x: C).(\forall (c2: C).(\forall (v: T).(\forall 
(v2: T).(\forall (i: nat).((csubst0 (S i) v x (CHead c2 (Bind b) v2)) \to 
(or3 (ex2 T (\lambda (v1: T).(subst0 i v v1 v2)) (\lambda (v1: T).(eq C x 
(CHead c2 (Bind b) v1)))) (ex2 C (\lambda (c1: C).(csubst0 i v c1 c2)) 
(\lambda (c1: C).(eq C x (CHead c1 (Bind b) v2)))) (ex3_2 C T (\lambda (_: 
C).(\lambda (v1: T).(subst0 i v v1 v2))) (\lambda (c1: C).(\lambda (_: 
T).(csubst0 i v c1 c2))) (\lambda (c1: C).(\lambda (v1: T).(eq C x (CHead c1 
(Bind b) v1))))))))))))
\def
 \lambda (b: B).(\lambda (x: C).(C_ind (\lambda (c: C).(\forall (c2: 
C).(\forall (v: T).(\forall (v2: T).(\forall (i: nat).((csubst0 (S i) v c 
(CHead c2 (Bind b) v2)) \to (or3 (ex2 T (\lambda (v1: T).(subst0 i v v1 v2)) 
(\lambda (v1: T).(eq C c (CHead c2 (Bind b) v1)))) (ex2 C (\lambda (c1: 
C).(csubst0 i v c1 c2)) (\lambda (c1: C).(eq C c (CHead c1 (Bind b) v2)))) 
(ex3_2 C T (\lambda (_: C).(\lambda (v1: T).(subst0 i v v1 v2))) (\lambda 
(c1: C).(\lambda (_: T).(csubst0 i v c1 c2))) (\lambda (c1: C).(\lambda (v1: 
T).(eq C c (CHead c1 (Bind b) v1)))))))))))) (\lambda (n: nat).(\lambda (c2: 
C).(\lambda (v: T).(\lambda (v2: T).(\lambda (i: nat).(\lambda (H: (csubst0 
(S i) v (CSort n) (CHead c2 (Bind b) v2))).(csubst0_gen_sort (CHead c2 (Bind 
b) v2) v (S i) n H (or3 (ex2 T (\lambda (v1: T).(subst0 i v v1 v2)) (\lambda 
(v1: T).(eq C (CSort n) (CHead c2 (Bind b) v1)))) (ex2 C (\lambda (c1: 
C).(csubst0 i v c1 c2)) (\lambda (c1: C).(eq C (CSort n) (CHead c1 (Bind b) 
v2)))) (ex3_2 C T (\lambda (_: C).(\lambda (v1: T).(subst0 i v v1 v2))) 
(\lambda (c1: C).(\lambda (_: T).(csubst0 i v c1 c2))) (\lambda (c1: 
C).(\lambda (v1: T).(eq C (CSort n) (CHead c1 (Bind b) v1))))))))))))) 
(\lambda (c: C).(\lambda (_: ((\forall (c2: C).(\forall (v: T).(\forall (v2: 
T).(\forall (i: nat).((csubst0 (S i) v c (CHead c2 (Bind b) v2)) \to (or3 
(ex2 T (\lambda (v1: T).(subst0 i v v1 v2)) (\lambda (v1: T).(eq C c (CHead 
c2 (Bind b) v1)))) (ex2 C (\lambda (c1: C).(csubst0 i v c1 c2)) (\lambda (c1: 
C).(eq C c (CHead c1 (Bind b) v2)))) (ex3_2 C T (\lambda (_: C).(\lambda (v1: 
T).(subst0 i v v1 v2))) (\lambda (c1: C).(\lambda (_: T).(csubst0 i v c1 
c2))) (\lambda (c1: C).(\lambda (v1: T).(eq C c (CHead c1 (Bind b) 
v1))))))))))))).(\lambda (k: K).(\lambda (t: T).(\lambda (c2: C).(\lambda (v: 
T).(\lambda (v2: T).(\lambda (i: nat).(\lambda (H0: (csubst0 (S i) v (CHead c 
k t) (CHead c2 (Bind b) v2))).(let H1 \def (csubst0_gen_head k c (CHead c2 
(Bind b) v2) t v (S i) H0) in (or3_ind (ex3_2 T nat (\lambda (_: T).(\lambda 
(j: nat).(eq nat (S i) (s k j)))) (\lambda (u2: T).(\lambda (_: nat).(eq C 
(CHead c2 (Bind b) v2) (CHead c k u2)))) (\lambda (u2: T).(\lambda (j: 
nat).(subst0 j v t u2)))) (ex3_2 C nat (\lambda (_: C).(\lambda (j: nat).(eq 
nat (S i) (s k j)))) (\lambda (c3: C).(\lambda (_: nat).(eq C (CHead c2 (Bind 
b) v2) (CHead c3 k t)))) (\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c 
c3)))) (ex4_3 T C nat (\lambda (_: T).(\lambda (_: C).(\lambda (j: nat).(eq 
nat (S i) (s k j))))) (\lambda (u2: T).(\lambda (c3: C).(\lambda (_: nat).(eq 
C (CHead c2 (Bind b) v2) (CHead c3 k u2))))) (\lambda (u2: T).(\lambda (_: 
C).(\lambda (j: nat).(subst0 j v t u2)))) (\lambda (_: T).(\lambda (c3: 
C).(\lambda (j: nat).(csubst0 j v c c3))))) (or3 (ex2 T (\lambda (v1: 
T).(subst0 i v v1 v2)) (\lambda (v1: T).(eq C (CHead c k t) (CHead c2 (Bind 
b) v1)))) (ex2 C (\lambda (c1: C).(csubst0 i v c1 c2)) (\lambda (c1: C).(eq C 
(CHead c k t) (CHead c1 (Bind b) v2)))) (ex3_2 C T (\lambda (_: C).(\lambda 
(v1: T).(subst0 i v v1 v2))) (\lambda (c1: C).(\lambda (_: T).(csubst0 i v c1 
c2))) (\lambda (c1: C).(\lambda (v1: T).(eq C (CHead c k t) (CHead c1 (Bind 
b) v1)))))) (\lambda (H2: (ex3_2 T nat (\lambda (_: T).(\lambda (j: nat).(eq 
nat (S i) (s k j)))) (\lambda (u2: T).(\lambda (_: nat).(eq C (CHead c2 (Bind 
b) v2) (CHead c k u2)))) (\lambda (u2: T).(\lambda (j: nat).(subst0 j v t 
u2))))).(ex3_2_ind T nat (\lambda (_: T).(\lambda (j: nat).(eq nat (S i) (s k 
j)))) (\lambda (u2: T).(\lambda (_: nat).(eq C (CHead c2 (Bind b) v2) (CHead 
c k u2)))) (\lambda (u2: T).(\lambda (j: nat).(subst0 j v t u2))) (or3 (ex2 T 
(\lambda (v1: T).(subst0 i v v1 v2)) (\lambda (v1: T).(eq C (CHead c k t) 
(CHead c2 (Bind b) v1)))) (ex2 C (\lambda (c1: C).(csubst0 i v c1 c2)) 
(\lambda (c1: C).(eq C (CHead c k t) (CHead c1 (Bind b) v2)))) (ex3_2 C T 
(\lambda (_: C).(\lambda (v1: T).(subst0 i v v1 v2))) (\lambda (c1: 
C).(\lambda (_: T).(csubst0 i v c1 c2))) (\lambda (c1: C).(\lambda (v1: 
T).(eq C (CHead c k t) (CHead c1 (Bind b) v1)))))) (\lambda (x0: T).(\lambda 
(x1: nat).(\lambda (H3: (eq nat (S i) (s k x1))).(\lambda (H4: (eq C (CHead 
c2 (Bind b) v2) (CHead c k x0))).(\lambda (H5: (subst0 x1 v t x0)).(let H6 
\def (f_equal C C (\lambda (e: C).(match e with [(CSort _) \Rightarrow c2 | 
(CHead c0 _ _) \Rightarrow c0])) (CHead c2 (Bind b) v2) (CHead c k x0) H4) in 
((let H7 \def (f_equal C K (\lambda (e: C).(match e with [(CSort _) 
\Rightarrow (Bind b) | (CHead _ k0 _) \Rightarrow k0])) (CHead c2 (Bind b) 
v2) (CHead c k x0) H4) in ((let H8 \def (f_equal C T (\lambda (e: C).(match e 
with [(CSort _) \Rightarrow v2 | (CHead _ _ t0) \Rightarrow t0])) (CHead c2 
(Bind b) v2) (CHead c k x0) H4) in (\lambda (H9: (eq K (Bind b) k)).(\lambda 
(H10: (eq C c2 c)).(let H11 \def (eq_ind_r T x0 (\lambda (t0: T).(subst0 x1 v 
t t0)) H5 v2 H8) in (eq_ind_r C c (\lambda (c0: C).(or3 (ex2 T (\lambda (v1: 
T).(subst0 i v v1 v2)) (\lambda (v1: T).(eq C (CHead c k t) (CHead c0 (Bind 
b) v1)))) (ex2 C (\lambda (c1: C).(csubst0 i v c1 c0)) (\lambda (c1: C).(eq C 
(CHead c k t) (CHead c1 (Bind b) v2)))) (ex3_2 C T (\lambda (_: C).(\lambda 
(v1: T).(subst0 i v v1 v2))) (\lambda (c1: C).(\lambda (_: T).(csubst0 i v c1 
c0))) (\lambda (c1: C).(\lambda (v1: T).(eq C (CHead c k t) (CHead c1 (Bind 
b) v1))))))) (let H12 \def (eq_ind_r K k (\lambda (k0: K).(eq nat (S i) (s k0 
x1))) H3 (Bind b) H9) in (eq_ind K (Bind b) (\lambda (k0: K).(or3 (ex2 T 
(\lambda (v1: T).(subst0 i v v1 v2)) (\lambda (v1: T).(eq C (CHead c k0 t) 
(CHead c (Bind b) v1)))) (ex2 C (\lambda (c1: C).(csubst0 i v c1 c)) (\lambda 
(c1: C).(eq C (CHead c k0 t) (CHead c1 (Bind b) v2)))) (ex3_2 C T (\lambda 
(_: C).(\lambda (v1: T).(subst0 i v v1 v2))) (\lambda (c1: C).(\lambda (_: 
T).(csubst0 i v c1 c))) (\lambda (c1: C).(\lambda (v1: T).(eq C (CHead c k0 
t) (CHead c1 (Bind b) v1))))))) (let H13 \def (f_equal nat nat (\lambda (e: 
nat).(match e with [O \Rightarrow i | (S n) \Rightarrow n])) (S i) (S x1) 
H12) in (let H14 \def (eq_ind_r nat x1 (\lambda (n: nat).(subst0 n v t v2)) 
H11 i H13) in (or3_intro0 (ex2 T (\lambda (v1: T).(subst0 i v v1 v2)) 
(\lambda (v1: T).(eq C (CHead c (Bind b) t) (CHead c (Bind b) v1)))) (ex2 C 
(\lambda (c1: C).(csubst0 i v c1 c)) (\lambda (c1: C).(eq C (CHead c (Bind b) 
t) (CHead c1 (Bind b) v2)))) (ex3_2 C T (\lambda (_: C).(\lambda (v1: 
T).(subst0 i v v1 v2))) (\lambda (c1: C).(\lambda (_: T).(csubst0 i v c1 c))) 
(\lambda (c1: C).(\lambda (v1: T).(eq C (CHead c (Bind b) t) (CHead c1 (Bind 
b) v1))))) (ex_intro2 T (\lambda (v1: T).(subst0 i v v1 v2)) (\lambda (v1: 
T).(eq C (CHead c (Bind b) t) (CHead c (Bind b) v1))) t H14 (refl_equal C 
(CHead c (Bind b) t)))))) k H9)) c2 H10))))) H7)) H6))))))) H2)) (\lambda 
(H2: (ex3_2 C nat (\lambda (_: C).(\lambda (j: nat).(eq nat (S i) (s k j)))) 
(\lambda (c3: C).(\lambda (_: nat).(eq C (CHead c2 (Bind b) v2) (CHead c3 k 
t)))) (\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c c3))))).(ex3_2_ind C 
nat (\lambda (_: C).(\lambda (j: nat).(eq nat (S i) (s k j)))) (\lambda (c3: 
C).(\lambda (_: nat).(eq C (CHead c2 (Bind b) v2) (CHead c3 k t)))) (\lambda 
(c3: C).(\lambda (j: nat).(csubst0 j v c c3))) (or3 (ex2 T (\lambda (v1: 
T).(subst0 i v v1 v2)) (\lambda (v1: T).(eq C (CHead c k t) (CHead c2 (Bind 
b) v1)))) (ex2 C (\lambda (c1: C).(csubst0 i v c1 c2)) (\lambda (c1: C).(eq C 
(CHead c k t) (CHead c1 (Bind b) v2)))) (ex3_2 C T (\lambda (_: C).(\lambda 
(v1: T).(subst0 i v v1 v2))) (\lambda (c1: C).(\lambda (_: T).(csubst0 i v c1 
c2))) (\lambda (c1: C).(\lambda (v1: T).(eq C (CHead c k t) (CHead c1 (Bind 
b) v1)))))) (\lambda (x0: C).(\lambda (x1: nat).(\lambda (H3: (eq nat (S i) 
(s k x1))).(\lambda (H4: (eq C (CHead c2 (Bind b) v2) (CHead x0 k 
t))).(\lambda (H5: (csubst0 x1 v c x0)).(let H6 \def (f_equal C C (\lambda 
(e: C).(match e with [(CSort _) \Rightarrow c2 | (CHead c0 _ _) \Rightarrow 
c0])) (CHead c2 (Bind b) v2) (CHead x0 k t) H4) in ((let H7 \def (f_equal C K 
(\lambda (e: C).(match e with [(CSort _) \Rightarrow (Bind b) | (CHead _ k0 
_) \Rightarrow k0])) (CHead c2 (Bind b) v2) (CHead x0 k t) H4) in ((let H8 
\def (f_equal C T (\lambda (e: C).(match e with [(CSort _) \Rightarrow v2 | 
(CHead _ _ t0) \Rightarrow t0])) (CHead c2 (Bind b) v2) (CHead x0 k t) H4) in 
(\lambda (H9: (eq K (Bind b) k)).(\lambda (H10: (eq C c2 x0)).(let H11 \def 
(eq_ind_r C x0 (\lambda (c0: C).(csubst0 x1 v c c0)) H5 c2 H10) in (eq_ind_r 
T t (\lambda (t0: T).(or3 (ex2 T (\lambda (v1: T).(subst0 i v v1 t0)) 
(\lambda (v1: T).(eq C (CHead c k t) (CHead c2 (Bind b) v1)))) (ex2 C 
(\lambda (c1: C).(csubst0 i v c1 c2)) (\lambda (c1: C).(eq C (CHead c k t) 
(CHead c1 (Bind b) t0)))) (ex3_2 C T (\lambda (_: C).(\lambda (v1: T).(subst0 
i v v1 t0))) (\lambda (c1: C).(\lambda (_: T).(csubst0 i v c1 c2))) (\lambda 
(c1: C).(\lambda (v1: T).(eq C (CHead c k t) (CHead c1 (Bind b) v1))))))) 
(let H12 \def (eq_ind_r K k (\lambda (k0: K).(eq nat (S i) (s k0 x1))) H3 
(Bind b) H9) in (eq_ind K (Bind b) (\lambda (k0: K).(or3 (ex2 T (\lambda (v1: 
T).(subst0 i v v1 t)) (\lambda (v1: T).(eq C (CHead c k0 t) (CHead c2 (Bind 
b) v1)))) (ex2 C (\lambda (c1: C).(csubst0 i v c1 c2)) (\lambda (c1: C).(eq C 
(CHead c k0 t) (CHead c1 (Bind b) t)))) (ex3_2 C T (\lambda (_: C).(\lambda 
(v1: T).(subst0 i v v1 t))) (\lambda (c1: C).(\lambda (_: T).(csubst0 i v c1 
c2))) (\lambda (c1: C).(\lambda (v1: T).(eq C (CHead c k0 t) (CHead c1 (Bind 
b) v1))))))) (let H13 \def (f_equal nat nat (\lambda (e: nat).(match e with 
[O \Rightarrow i | (S n) \Rightarrow n])) (S i) (S x1) H12) in (let H14 \def 
(eq_ind_r nat x1 (\lambda (n: nat).(csubst0 n v c c2)) H11 i H13) in 
(or3_intro1 (ex2 T (\lambda (v1: T).(subst0 i v v1 t)) (\lambda (v1: T).(eq C 
(CHead c (Bind b) t) (CHead c2 (Bind b) v1)))) (ex2 C (\lambda (c1: 
C).(csubst0 i v c1 c2)) (\lambda (c1: C).(eq C (CHead c (Bind b) t) (CHead c1 
(Bind b) t)))) (ex3_2 C T (\lambda (_: C).(\lambda (v1: T).(subst0 i v v1 
t))) (\lambda (c1: C).(\lambda (_: T).(csubst0 i v c1 c2))) (\lambda (c1: 
C).(\lambda (v1: T).(eq C (CHead c (Bind b) t) (CHead c1 (Bind b) v1))))) 
(ex_intro2 C (\lambda (c1: C).(csubst0 i v c1 c2)) (\lambda (c1: C).(eq C 
(CHead c (Bind b) t) (CHead c1 (Bind b) t))) c H14 (refl_equal C (CHead c 
(Bind b) t)))))) k H9)) v2 H8))))) H7)) H6))))))) H2)) (\lambda (H2: (ex4_3 T 
C nat (\lambda (_: T).(\lambda (_: C).(\lambda (j: nat).(eq nat (S i) (s k 
j))))) (\lambda (u2: T).(\lambda (c3: C).(\lambda (_: nat).(eq C (CHead c2 
(Bind b) v2) (CHead c3 k u2))))) (\lambda (u2: T).(\lambda (_: C).(\lambda 
(j: nat).(subst0 j v t u2)))) (\lambda (_: T).(\lambda (c3: C).(\lambda (j: 
nat).(csubst0 j v c c3)))))).(ex4_3_ind T C nat (\lambda (_: T).(\lambda (_: 
C).(\lambda (j: nat).(eq nat (S i) (s k j))))) (\lambda (u2: T).(\lambda (c3: 
C).(\lambda (_: nat).(eq C (CHead c2 (Bind b) v2) (CHead c3 k u2))))) 
(\lambda (u2: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v t u2)))) 
(\lambda (_: T).(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c c3)))) (or3 
(ex2 T (\lambda (v1: T).(subst0 i v v1 v2)) (\lambda (v1: T).(eq C (CHead c k 
t) (CHead c2 (Bind b) v1)))) (ex2 C (\lambda (c1: C).(csubst0 i v c1 c2)) 
(\lambda (c1: C).(eq C (CHead c k t) (CHead c1 (Bind b) v2)))) (ex3_2 C T 
(\lambda (_: C).(\lambda (v1: T).(subst0 i v v1 v2))) (\lambda (c1: 
C).(\lambda (_: T).(csubst0 i v c1 c2))) (\lambda (c1: C).(\lambda (v1: 
T).(eq C (CHead c k t) (CHead c1 (Bind b) v1)))))) (\lambda (x0: T).(\lambda 
(x1: C).(\lambda (x2: nat).(\lambda (H3: (eq nat (S i) (s k x2))).(\lambda 
(H4: (eq C (CHead c2 (Bind b) v2) (CHead x1 k x0))).(\lambda (H5: (subst0 x2 
v t x0)).(\lambda (H6: (csubst0 x2 v c x1)).(let H7 \def (f_equal C C 
(\lambda (e: C).(match e with [(CSort _) \Rightarrow c2 | (CHead c0 _ _) 
\Rightarrow c0])) (CHead c2 (Bind b) v2) (CHead x1 k x0) H4) in ((let H8 \def 
(f_equal C K (\lambda (e: C).(match e with [(CSort _) \Rightarrow (Bind b) | 
(CHead _ k0 _) \Rightarrow k0])) (CHead c2 (Bind b) v2) (CHead x1 k x0) H4) 
in ((let H9 \def (f_equal C T (\lambda (e: C).(match e with [(CSort _) 
\Rightarrow v2 | (CHead _ _ t0) \Rightarrow t0])) (CHead c2 (Bind b) v2) 
(CHead x1 k x0) H4) in (\lambda (H10: (eq K (Bind b) k)).(\lambda (H11: (eq C 
c2 x1)).(let H12 \def (eq_ind_r C x1 (\lambda (c0: C).(csubst0 x2 v c c0)) H6 
c2 H11) in (let H13 \def (eq_ind_r T x0 (\lambda (t0: T).(subst0 x2 v t t0)) 
H5 v2 H9) in (let H14 \def (eq_ind_r K k (\lambda (k0: K).(eq nat (S i) (s k0 
x2))) H3 (Bind b) H10) in (eq_ind K (Bind b) (\lambda (k0: K).(or3 (ex2 T 
(\lambda (v1: T).(subst0 i v v1 v2)) (\lambda (v1: T).(eq C (CHead c k0 t) 
(CHead c2 (Bind b) v1)))) (ex2 C (\lambda (c1: C).(csubst0 i v c1 c2)) 
(\lambda (c1: C).(eq C (CHead c k0 t) (CHead c1 (Bind b) v2)))) (ex3_2 C T 
(\lambda (_: C).(\lambda (v1: T).(subst0 i v v1 v2))) (\lambda (c1: 
C).(\lambda (_: T).(csubst0 i v c1 c2))) (\lambda (c1: C).(\lambda (v1: 
T).(eq C (CHead c k0 t) (CHead c1 (Bind b) v1))))))) (let H15 \def (f_equal 
nat nat (\lambda (e: nat).(match e with [O \Rightarrow i | (S n) \Rightarrow 
n])) (S i) (S x2) H14) in (let H16 \def (eq_ind_r nat x2 (\lambda (n: 
nat).(csubst0 n v c c2)) H12 i H15) in (let H17 \def (eq_ind_r nat x2 
(\lambda (n: nat).(subst0 n v t v2)) H13 i H15) in (or3_intro2 (ex2 T 
(\lambda (v1: T).(subst0 i v v1 v2)) (\lambda (v1: T).(eq C (CHead c (Bind b) 
t) (CHead c2 (Bind b) v1)))) (ex2 C (\lambda (c1: C).(csubst0 i v c1 c2)) 
(\lambda (c1: C).(eq C (CHead c (Bind b) t) (CHead c1 (Bind b) v2)))) (ex3_2 
C T (\lambda (_: C).(\lambda (v1: T).(subst0 i v v1 v2))) (\lambda (c1: 
C).(\lambda (_: T).(csubst0 i v c1 c2))) (\lambda (c1: C).(\lambda (v1: 
T).(eq C (CHead c (Bind b) t) (CHead c1 (Bind b) v1))))) (ex3_2_intro C T 
(\lambda (_: C).(\lambda (v1: T).(subst0 i v v1 v2))) (\lambda (c1: 
C).(\lambda (_: T).(csubst0 i v c1 c2))) (\lambda (c1: C).(\lambda (v1: 
T).(eq C (CHead c (Bind b) t) (CHead c1 (Bind b) v1)))) c t H17 H16 
(refl_equal C (CHead c (Bind b) t))))))) k H10))))))) H8)) H7))))))))) H2)) 
H1))))))))))) x)).

