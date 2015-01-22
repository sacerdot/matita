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

include "Basic-1/csubst0/props.ma".

include "Basic-1/csubst0/fwd.ma".

include "Basic-1/clear/fwd.ma".

theorem csubst0_clear_O:
 \forall (c1: C).(\forall (c2: C).(\forall (v: T).((csubst0 O v c1 c2) \to 
(\forall (c: C).((clear c1 c) \to (clear c2 c))))))
\def
 \lambda (c1: C).(C_ind (\lambda (c: C).(\forall (c2: C).(\forall (v: 
T).((csubst0 O v c c2) \to (\forall (c0: C).((clear c c0) \to (clear c2 
c0))))))) (\lambda (n: nat).(\lambda (c2: C).(\lambda (v: T).(\lambda (H: 
(csubst0 O v (CSort n) c2)).(\lambda (c: C).(\lambda (_: (clear (CSort n) 
c)).(csubst0_gen_sort c2 v O n H (clear c2 c)))))))) (\lambda (c: C).(\lambda 
(H: ((\forall (c2: C).(\forall (v: T).((csubst0 O v c c2) \to (\forall (c0: 
C).((clear c c0) \to (clear c2 c0)))))))).(\lambda (k: K).(\lambda (t: 
T).(\lambda (c2: C).(\lambda (v: T).(\lambda (H0: (csubst0 O v (CHead c k t) 
c2)).(\lambda (c0: C).(\lambda (H1: (clear (CHead c k t) c0)).(or3_ind (ex3_2 
T nat (\lambda (_: T).(\lambda (j: nat).(eq nat O (s k j)))) (\lambda (u2: 
T).(\lambda (_: nat).(eq C c2 (CHead c k u2)))) (\lambda (u2: T).(\lambda (j: 
nat).(subst0 j v t u2)))) (ex3_2 C nat (\lambda (_: C).(\lambda (j: nat).(eq 
nat O (s k j)))) (\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k 
t)))) (\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c c3)))) (ex4_3 T C nat 
(\lambda (_: T).(\lambda (_: C).(\lambda (j: nat).(eq nat O (s k j))))) 
(\lambda (u2: T).(\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k 
u2))))) (\lambda (u2: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v t 
u2)))) (\lambda (_: T).(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c 
c3))))) (clear c2 c0) (\lambda (H2: (ex3_2 T nat (\lambda (_: T).(\lambda (j: 
nat).(eq nat O (s k j)))) (\lambda (u2: T).(\lambda (_: nat).(eq C c2 (CHead 
c k u2)))) (\lambda (u2: T).(\lambda (j: nat).(subst0 j v t 
u2))))).(ex3_2_ind T nat (\lambda (_: T).(\lambda (j: nat).(eq nat O (s k 
j)))) (\lambda (u2: T).(\lambda (_: nat).(eq C c2 (CHead c k u2)))) (\lambda 
(u2: T).(\lambda (j: nat).(subst0 j v t u2))) (clear c2 c0) (\lambda (x0: 
T).(\lambda (x1: nat).(\lambda (H3: (eq nat O (s k x1))).(\lambda (H4: (eq C 
c2 (CHead c k x0))).(\lambda (H5: (subst0 x1 v t x0)).(eq_ind_r C (CHead c k 
x0) (\lambda (c3: C).(clear c3 c0)) (K_ind (\lambda (k0: K).((clear (CHead c 
k0 t) c0) \to ((eq nat O (s k0 x1)) \to (clear (CHead c k0 x0) c0)))) 
(\lambda (b: B).(\lambda (_: (clear (CHead c (Bind b) t) c0)).(\lambda (H7: 
(eq nat O (s (Bind b) x1))).(let H8 \def (eq_ind nat O (\lambda (ee: 
nat).(match ee in nat return (\lambda (_: nat).Prop) with [O \Rightarrow True 
| (S _) \Rightarrow False])) I (S x1) H7) in (False_ind (clear (CHead c (Bind 
b) x0) c0) H8))))) (\lambda (f: F).(\lambda (H6: (clear (CHead c (Flat f) t) 
c0)).(\lambda (H7: (eq nat O (s (Flat f) x1))).(let H8 \def (eq_ind_r nat x1 
(\lambda (n: nat).(subst0 n v t x0)) H5 O H7) in (clear_flat c c0 
(clear_gen_flat f c c0 t H6) f x0))))) k H1 H3) c2 H4)))))) H2)) (\lambda 
(H2: (ex3_2 C nat (\lambda (_: C).(\lambda (j: nat).(eq nat O (s k j)))) 
(\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k t)))) (\lambda (c3: 
C).(\lambda (j: nat).(csubst0 j v c c3))))).(ex3_2_ind C nat (\lambda (_: 
C).(\lambda (j: nat).(eq nat O (s k j)))) (\lambda (c3: C).(\lambda (_: 
nat).(eq C c2 (CHead c3 k t)))) (\lambda (c3: C).(\lambda (j: nat).(csubst0 j 
v c c3))) (clear c2 c0) (\lambda (x0: C).(\lambda (x1: nat).(\lambda (H3: (eq 
nat O (s k x1))).(\lambda (H4: (eq C c2 (CHead x0 k t))).(\lambda (H5: 
(csubst0 x1 v c x0)).(eq_ind_r C (CHead x0 k t) (\lambda (c3: C).(clear c3 
c0)) (K_ind (\lambda (k0: K).((clear (CHead c k0 t) c0) \to ((eq nat O (s k0 
x1)) \to (clear (CHead x0 k0 t) c0)))) (\lambda (b: B).(\lambda (_: (clear 
(CHead c (Bind b) t) c0)).(\lambda (H7: (eq nat O (s (Bind b) x1))).(let H8 
\def (eq_ind nat O (\lambda (ee: nat).(match ee in nat return (\lambda (_: 
nat).Prop) with [O \Rightarrow True | (S _) \Rightarrow False])) I (S x1) H7) 
in (False_ind (clear (CHead x0 (Bind b) t) c0) H8))))) (\lambda (f: 
F).(\lambda (H6: (clear (CHead c (Flat f) t) c0)).(\lambda (H7: (eq nat O (s 
(Flat f) x1))).(let H8 \def (eq_ind_r nat x1 (\lambda (n: nat).(csubst0 n v c 
x0)) H5 O H7) in (clear_flat x0 c0 (H x0 v H8 c0 (clear_gen_flat f c c0 t 
H6)) f t))))) k H1 H3) c2 H4)))))) H2)) (\lambda (H2: (ex4_3 T C nat (\lambda 
(_: T).(\lambda (_: C).(\lambda (j: nat).(eq nat O (s k j))))) (\lambda (u2: 
T).(\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k u2))))) (\lambda 
(u2: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v t u2)))) (\lambda (_: 
T).(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c c3)))))).(ex4_3_ind T C 
nat (\lambda (_: T).(\lambda (_: C).(\lambda (j: nat).(eq nat O (s k j))))) 
(\lambda (u2: T).(\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k 
u2))))) (\lambda (u2: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v t 
u2)))) (\lambda (_: T).(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c 
c3)))) (clear c2 c0) (\lambda (x0: T).(\lambda (x1: C).(\lambda (x2: 
nat).(\lambda (H3: (eq nat O (s k x2))).(\lambda (H4: (eq C c2 (CHead x1 k 
x0))).(\lambda (H5: (subst0 x2 v t x0)).(\lambda (H6: (csubst0 x2 v c 
x1)).(eq_ind_r C (CHead x1 k x0) (\lambda (c3: C).(clear c3 c0)) (K_ind 
(\lambda (k0: K).((clear (CHead c k0 t) c0) \to ((eq nat O (s k0 x2)) \to 
(clear (CHead x1 k0 x0) c0)))) (\lambda (b: B).(\lambda (_: (clear (CHead c 
(Bind b) t) c0)).(\lambda (H8: (eq nat O (s (Bind b) x2))).(let H9 \def 
(eq_ind nat O (\lambda (ee: nat).(match ee in nat return (\lambda (_: 
nat).Prop) with [O \Rightarrow True | (S _) \Rightarrow False])) I (S x2) H8) 
in (False_ind (clear (CHead x1 (Bind b) x0) c0) H9))))) (\lambda (f: 
F).(\lambda (H7: (clear (CHead c (Flat f) t) c0)).(\lambda (H8: (eq nat O (s 
(Flat f) x2))).(let H9 \def (eq_ind_r nat x2 (\lambda (n: nat).(csubst0 n v c 
x1)) H6 O H8) in (let H10 \def (eq_ind_r nat x2 (\lambda (n: nat).(subst0 n v 
t x0)) H5 O H8) in (clear_flat x1 c0 (H x1 v H9 c0 (clear_gen_flat f c c0 t 
H7)) f x0)))))) k H1 H3) c2 H4)))))))) H2)) (csubst0_gen_head k c c2 t v O 
H0))))))))))) c1).
(* COMMENTS
Initial nodes: 1582
END *)

theorem csubst0_clear_O_back:
 \forall (c1: C).(\forall (c2: C).(\forall (v: T).((csubst0 O v c1 c2) \to 
(\forall (c: C).((clear c2 c) \to (clear c1 c))))))
\def
 \lambda (c1: C).(C_ind (\lambda (c: C).(\forall (c2: C).(\forall (v: 
T).((csubst0 O v c c2) \to (\forall (c0: C).((clear c2 c0) \to (clear c 
c0))))))) (\lambda (n: nat).(\lambda (c2: C).(\lambda (v: T).(\lambda (H: 
(csubst0 O v (CSort n) c2)).(\lambda (c: C).(\lambda (_: (clear c2 
c)).(csubst0_gen_sort c2 v O n H (clear (CSort n) c)))))))) (\lambda (c: 
C).(\lambda (H: ((\forall (c2: C).(\forall (v: T).((csubst0 O v c c2) \to 
(\forall (c0: C).((clear c2 c0) \to (clear c c0)))))))).(\lambda (k: 
K).(\lambda (t: T).(\lambda (c2: C).(\lambda (v: T).(\lambda (H0: (csubst0 O 
v (CHead c k t) c2)).(\lambda (c0: C).(\lambda (H1: (clear c2 c0)).(or3_ind 
(ex3_2 T nat (\lambda (_: T).(\lambda (j: nat).(eq nat O (s k j)))) (\lambda 
(u2: T).(\lambda (_: nat).(eq C c2 (CHead c k u2)))) (\lambda (u2: 
T).(\lambda (j: nat).(subst0 j v t u2)))) (ex3_2 C nat (\lambda (_: 
C).(\lambda (j: nat).(eq nat O (s k j)))) (\lambda (c3: C).(\lambda (_: 
nat).(eq C c2 (CHead c3 k t)))) (\lambda (c3: C).(\lambda (j: nat).(csubst0 j 
v c c3)))) (ex4_3 T C nat (\lambda (_: T).(\lambda (_: C).(\lambda (j: 
nat).(eq nat O (s k j))))) (\lambda (u2: T).(\lambda (c3: C).(\lambda (_: 
nat).(eq C c2 (CHead c3 k u2))))) (\lambda (u2: T).(\lambda (_: C).(\lambda 
(j: nat).(subst0 j v t u2)))) (\lambda (_: T).(\lambda (c3: C).(\lambda (j: 
nat).(csubst0 j v c c3))))) (clear (CHead c k t) c0) (\lambda (H2: (ex3_2 T 
nat (\lambda (_: T).(\lambda (j: nat).(eq nat O (s k j)))) (\lambda (u2: 
T).(\lambda (_: nat).(eq C c2 (CHead c k u2)))) (\lambda (u2: T).(\lambda (j: 
nat).(subst0 j v t u2))))).(ex3_2_ind T nat (\lambda (_: T).(\lambda (j: 
nat).(eq nat O (s k j)))) (\lambda (u2: T).(\lambda (_: nat).(eq C c2 (CHead 
c k u2)))) (\lambda (u2: T).(\lambda (j: nat).(subst0 j v t u2))) (clear 
(CHead c k t) c0) (\lambda (x0: T).(\lambda (x1: nat).(\lambda (H3: (eq nat O 
(s k x1))).(\lambda (H4: (eq C c2 (CHead c k x0))).(\lambda (H5: (subst0 x1 v 
t x0)).(let H6 \def (eq_ind C c2 (\lambda (c3: C).(clear c3 c0)) H1 (CHead c 
k x0) H4) in (K_ind (\lambda (k0: K).((eq nat O (s k0 x1)) \to ((clear (CHead 
c k0 x0) c0) \to (clear (CHead c k0 t) c0)))) (\lambda (b: B).(\lambda (H7: 
(eq nat O (s (Bind b) x1))).(\lambda (_: (clear (CHead c (Bind b) x0) 
c0)).(let H9 \def (eq_ind nat O (\lambda (ee: nat).(match ee in nat return 
(\lambda (_: nat).Prop) with [O \Rightarrow True | (S _) \Rightarrow False])) 
I (S x1) H7) in (False_ind (clear (CHead c (Bind b) t) c0) H9))))) (\lambda 
(f: F).(\lambda (H7: (eq nat O (s (Flat f) x1))).(\lambda (H8: (clear (CHead 
c (Flat f) x0) c0)).(let H9 \def (eq_ind_r nat x1 (\lambda (n: nat).(subst0 n 
v t x0)) H5 O H7) in (clear_flat c c0 (clear_gen_flat f c c0 x0 H8) f t))))) 
k H3 H6))))))) H2)) (\lambda (H2: (ex3_2 C nat (\lambda (_: C).(\lambda (j: 
nat).(eq nat O (s k j)))) (\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead 
c3 k t)))) (\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c 
c3))))).(ex3_2_ind C nat (\lambda (_: C).(\lambda (j: nat).(eq nat O (s k 
j)))) (\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k t)))) (\lambda 
(c3: C).(\lambda (j: nat).(csubst0 j v c c3))) (clear (CHead c k t) c0) 
(\lambda (x0: C).(\lambda (x1: nat).(\lambda (H3: (eq nat O (s k 
x1))).(\lambda (H4: (eq C c2 (CHead x0 k t))).(\lambda (H5: (csubst0 x1 v c 
x0)).(let H6 \def (eq_ind C c2 (\lambda (c3: C).(clear c3 c0)) H1 (CHead x0 k 
t) H4) in (K_ind (\lambda (k0: K).((eq nat O (s k0 x1)) \to ((clear (CHead x0 
k0 t) c0) \to (clear (CHead c k0 t) c0)))) (\lambda (b: B).(\lambda (H7: (eq 
nat O (s (Bind b) x1))).(\lambda (_: (clear (CHead x0 (Bind b) t) c0)).(let 
H9 \def (eq_ind nat O (\lambda (ee: nat).(match ee in nat return (\lambda (_: 
nat).Prop) with [O \Rightarrow True | (S _) \Rightarrow False])) I (S x1) H7) 
in (False_ind (clear (CHead c (Bind b) t) c0) H9))))) (\lambda (f: 
F).(\lambda (H7: (eq nat O (s (Flat f) x1))).(\lambda (H8: (clear (CHead x0 
(Flat f) t) c0)).(let H9 \def (eq_ind_r nat x1 (\lambda (n: nat).(csubst0 n v 
c x0)) H5 O H7) in (clear_flat c c0 (H x0 v H9 c0 (clear_gen_flat f x0 c0 t 
H8)) f t))))) k H3 H6))))))) H2)) (\lambda (H2: (ex4_3 T C nat (\lambda (_: 
T).(\lambda (_: C).(\lambda (j: nat).(eq nat O (s k j))))) (\lambda (u2: 
T).(\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k u2))))) (\lambda 
(u2: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v t u2)))) (\lambda (_: 
T).(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c c3)))))).(ex4_3_ind T C 
nat (\lambda (_: T).(\lambda (_: C).(\lambda (j: nat).(eq nat O (s k j))))) 
(\lambda (u2: T).(\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k 
u2))))) (\lambda (u2: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v t 
u2)))) (\lambda (_: T).(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c 
c3)))) (clear (CHead c k t) c0) (\lambda (x0: T).(\lambda (x1: C).(\lambda 
(x2: nat).(\lambda (H3: (eq nat O (s k x2))).(\lambda (H4: (eq C c2 (CHead x1 
k x0))).(\lambda (H5: (subst0 x2 v t x0)).(\lambda (H6: (csubst0 x2 v c 
x1)).(let H7 \def (eq_ind C c2 (\lambda (c3: C).(clear c3 c0)) H1 (CHead x1 k 
x0) H4) in (K_ind (\lambda (k0: K).((eq nat O (s k0 x2)) \to ((clear (CHead 
x1 k0 x0) c0) \to (clear (CHead c k0 t) c0)))) (\lambda (b: B).(\lambda (H8: 
(eq nat O (s (Bind b) x2))).(\lambda (_: (clear (CHead x1 (Bind b) x0) 
c0)).(let H10 \def (eq_ind nat O (\lambda (ee: nat).(match ee in nat return 
(\lambda (_: nat).Prop) with [O \Rightarrow True | (S _) \Rightarrow False])) 
I (S x2) H8) in (False_ind (clear (CHead c (Bind b) t) c0) H10))))) (\lambda 
(f: F).(\lambda (H8: (eq nat O (s (Flat f) x2))).(\lambda (H9: (clear (CHead 
x1 (Flat f) x0) c0)).(let H10 \def (eq_ind_r nat x2 (\lambda (n: 
nat).(csubst0 n v c x1)) H6 O H8) in (let H11 \def (eq_ind_r nat x2 (\lambda 
(n: nat).(subst0 n v t x0)) H5 O H8) in (clear_flat c c0 (H x1 v H10 c0 
(clear_gen_flat f x1 c0 x0 H9)) f t)))))) k H3 H7))))))))) H2)) 
(csubst0_gen_head k c c2 t v O H0))))))))))) c1).
(* COMMENTS
Initial nodes: 1606
END *)

theorem csubst0_clear_S:
 \forall (c1: C).(\forall (c2: C).(\forall (v: T).(\forall (i: nat).((csubst0 
(S i) v c1 c2) \to (\forall (c: C).((clear c1 c) \to (or4 (clear c2 c) (ex3_4 
B C T T (\lambda (b: B).(\lambda (e: C).(\lambda (u1: T).(\lambda (_: T).(eq 
C c (CHead e (Bind b) u1)))))) (\lambda (b: B).(\lambda (e: C).(\lambda (_: 
T).(\lambda (u2: T).(clear c2 (CHead e (Bind b) u2)))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) 
(ex3_4 B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C c (CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(clear c2 (CHead e2 (Bind b) u)))))) 
(\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i 
v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C c (CHead e1 (Bind b) u1))))))) 
(\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(u2: T).(clear c2 (CHead e2 (Bind b) u2))))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) 
(\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 i v e1 e2))))))))))))))
\def
 \lambda (c1: C).(C_ind (\lambda (c: C).(\forall (c2: C).(\forall (v: 
T).(\forall (i: nat).((csubst0 (S i) v c c2) \to (\forall (c0: C).((clear c 
c0) \to (or4 (clear c2 c0) (ex3_4 B C T T (\lambda (b: B).(\lambda (e: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e (Bind b) u1)))))) 
(\lambda (b: B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: T).(clear c2 
(CHead e (Bind b) u2)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (ex3_4 B C C T (\lambda (b: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c0 (CHead e1 (Bind 
b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(clear c2 (CHead e2 (Bind b) u)))))) (\lambda (_: B).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i v e1 e2)))))) (ex4_5 B C C T T 
(\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(_: T).(eq C c0 (CHead e1 (Bind b) u1))))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(clear c2 (CHead e2 
(Bind b) u2))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 
e2))))))))))))))) (\lambda (n: nat).(\lambda (c2: C).(\lambda (v: T).(\lambda 
(i: nat).(\lambda (H: (csubst0 (S i) v (CSort n) c2)).(\lambda (c: 
C).(\lambda (_: (clear (CSort n) c)).(csubst0_gen_sort c2 v (S i) n H (or4 
(clear c2 c) (ex3_4 B C T T (\lambda (b: B).(\lambda (e: C).(\lambda (u1: 
T).(\lambda (_: T).(eq C c (CHead e (Bind b) u1)))))) (\lambda (b: 
B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: T).(clear c2 (CHead e (Bind 
b) u2)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: 
T).(subst0 i v u1 u2)))))) (ex3_4 B C C T (\lambda (b: B).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C c (CHead e1 (Bind b) u)))))) 
(\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(clear c2 
(CHead e2 (Bind b) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 i v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(eq C c 
(CHead e1 (Bind b) u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(clear c2 (CHead e2 (Bind b) u2))))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(u2: T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 e2)))))))))))))))) 
(\lambda (c: C).(\lambda (H: ((\forall (c2: C).(\forall (v: T).(\forall (i: 
nat).((csubst0 (S i) v c c2) \to (\forall (c0: C).((clear c c0) \to (or4 
(clear c2 c0) (ex3_4 B C T T (\lambda (b: B).(\lambda (e: C).(\lambda (u1: 
T).(\lambda (_: T).(eq C c0 (CHead e (Bind b) u1)))))) (\lambda (b: 
B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: T).(clear c2 (CHead e (Bind 
b) u2)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: 
T).(subst0 i v u1 u2)))))) (ex3_4 B C C T (\lambda (b: B).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C c0 (CHead e1 (Bind b) u)))))) 
(\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(clear c2 
(CHead e2 (Bind b) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 i v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 
(CHead e1 (Bind b) u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(clear c2 (CHead e2 (Bind b) u2))))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(u2: T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 
e2)))))))))))))))).(\lambda (k: K).(\lambda (t: T).(\lambda (c2: C).(\lambda 
(v: T).(\lambda (i: nat).(\lambda (H0: (csubst0 (S i) v (CHead c k t) 
c2)).(\lambda (c0: C).(\lambda (H1: (clear (CHead c k t) c0)).(or3_ind (ex3_2 
T nat (\lambda (_: T).(\lambda (j: nat).(eq nat (S i) (s k j)))) (\lambda 
(u2: T).(\lambda (_: nat).(eq C c2 (CHead c k u2)))) (\lambda (u2: 
T).(\lambda (j: nat).(subst0 j v t u2)))) (ex3_2 C nat (\lambda (_: 
C).(\lambda (j: nat).(eq nat (S i) (s k j)))) (\lambda (c3: C).(\lambda (_: 
nat).(eq C c2 (CHead c3 k t)))) (\lambda (c3: C).(\lambda (j: nat).(csubst0 j 
v c c3)))) (ex4_3 T C nat (\lambda (_: T).(\lambda (_: C).(\lambda (j: 
nat).(eq nat (S i) (s k j))))) (\lambda (u2: T).(\lambda (c3: C).(\lambda (_: 
nat).(eq C c2 (CHead c3 k u2))))) (\lambda (u2: T).(\lambda (_: C).(\lambda 
(j: nat).(subst0 j v t u2)))) (\lambda (_: T).(\lambda (c3: C).(\lambda (j: 
nat).(csubst0 j v c c3))))) (or4 (clear c2 c0) (ex3_4 B C T T (\lambda (b: 
B).(\lambda (e: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e (Bind 
b) u1)))))) (\lambda (b: B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: 
T).(clear c2 (CHead e (Bind b) u2)))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (ex3_4 B C C T 
(\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c0 
(CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(clear c2 (CHead e2 (Bind b) u)))))) (\lambda (_: 
B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i v e1 e2)))))) 
(ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (_: T).(eq C c0 (CHead e1 (Bind b) u1))))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(clear 
c2 (CHead e2 (Bind b) u2))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (\lambda (_: 
B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
i v e1 e2)))))))) (\lambda (H2: (ex3_2 T nat (\lambda (_: T).(\lambda (j: 
nat).(eq nat (S i) (s k j)))) (\lambda (u2: T).(\lambda (_: nat).(eq C c2 
(CHead c k u2)))) (\lambda (u2: T).(\lambda (j: nat).(subst0 j v t 
u2))))).(ex3_2_ind T nat (\lambda (_: T).(\lambda (j: nat).(eq nat (S i) (s k 
j)))) (\lambda (u2: T).(\lambda (_: nat).(eq C c2 (CHead c k u2)))) (\lambda 
(u2: T).(\lambda (j: nat).(subst0 j v t u2))) (or4 (clear c2 c0) (ex3_4 B C T 
T (\lambda (b: B).(\lambda (e: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 
(CHead e (Bind b) u1)))))) (\lambda (b: B).(\lambda (e: C).(\lambda (_: 
T).(\lambda (u2: T).(clear c2 (CHead e (Bind b) u2)))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) 
(ex3_4 B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C c0 (CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(clear c2 (CHead e2 (Bind b) u)))))) 
(\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i 
v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e1 (Bind b) u1))))))) 
(\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(u2: T).(clear c2 (CHead e2 (Bind b) u2))))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) 
(\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 i v e1 e2)))))))) (\lambda (x0: T).(\lambda (x1: 
nat).(\lambda (H3: (eq nat (S i) (s k x1))).(\lambda (H4: (eq C c2 (CHead c k 
x0))).(\lambda (H5: (subst0 x1 v t x0)).(eq_ind_r C (CHead c k x0) (\lambda 
(c3: C).(or4 (clear c3 c0) (ex3_4 B C T T (\lambda (b: B).(\lambda (e: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e (Bind b) u1)))))) 
(\lambda (b: B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: T).(clear c3 
(CHead e (Bind b) u2)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (ex3_4 B C C T (\lambda (b: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c0 (CHead e1 (Bind 
b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(clear c3 (CHead e2 (Bind b) u)))))) (\lambda (_: B).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i v e1 e2)))))) (ex4_5 B C C T T 
(\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(_: T).(eq C c0 (CHead e1 (Bind b) u1))))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(clear c3 (CHead e2 
(Bind b) u2))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 
e2))))))))) (K_ind (\lambda (k0: K).((clear (CHead c k0 t) c0) \to ((eq nat 
(S i) (s k0 x1)) \to (or4 (clear (CHead c k0 x0) c0) (ex3_4 B C T T (\lambda 
(b: B).(\lambda (e: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e 
(Bind b) u1)))))) (\lambda (b: B).(\lambda (e: C).(\lambda (_: T).(\lambda 
(u2: T).(clear (CHead c k0 x0) (CHead e (Bind b) u2)))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) 
(ex3_4 B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C c0 (CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(clear (CHead c k0 x0) (CHead e2 (Bind b) 
u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 i v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e1 (Bind 
b) u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (u2: T).(clear (CHead c k0 x0) (CHead e2 (Bind b) u2))))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(u2: T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 e2))))))))))) 
(\lambda (b: B).(\lambda (H6: (clear (CHead c (Bind b) t) c0)).(\lambda (H7: 
(eq nat (S i) (s (Bind b) x1))).(let H8 \def (f_equal nat nat (\lambda (e: 
nat).(match e in nat return (\lambda (_: nat).nat) with [O \Rightarrow i | (S 
n) \Rightarrow n])) (S i) (S x1) H7) in (let H9 \def (eq_ind_r nat x1 
(\lambda (n: nat).(subst0 n v t x0)) H5 i H8) in (eq_ind_r C (CHead c (Bind 
b) t) (\lambda (c3: C).(or4 (clear (CHead c (Bind b) x0) c3) (ex3_4 B C T T 
(\lambda (b0: B).(\lambda (e: C).(\lambda (u1: T).(\lambda (_: T).(eq C c3 
(CHead e (Bind b0) u1)))))) (\lambda (b0: B).(\lambda (e: C).(\lambda (_: 
T).(\lambda (u2: T).(clear (CHead c (Bind b) x0) (CHead e (Bind b0) u2)))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v 
u1 u2)))))) (ex3_4 B C C T (\lambda (b0: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C c3 (CHead e1 (Bind b0) u)))))) (\lambda (b0: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(clear (CHead c (Bind b) 
x0) (CHead e2 (Bind b0) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 i v e1 e2)))))) (ex4_5 B C C T T (\lambda 
(b0: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(eq 
C c3 (CHead e1 (Bind b0) u1))))))) (\lambda (b0: B).(\lambda (_: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (u2: T).(clear (CHead c (Bind b) x0) (CHead 
e2 (Bind b0) u2))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (\lambda (_: 
B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
i v e1 e2))))))))) (or4_intro1 (clear (CHead c (Bind b) x0) (CHead c (Bind b) 
t)) (ex3_4 B C T T (\lambda (b0: B).(\lambda (e: C).(\lambda (u1: T).(\lambda 
(_: T).(eq C (CHead c (Bind b) t) (CHead e (Bind b0) u1)))))) (\lambda (b0: 
B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: T).(clear (CHead c (Bind b) 
x0) (CHead e (Bind b0) u2)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (ex3_4 B C C T (\lambda (b0: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C (CHead c (Bind b) 
t) (CHead e1 (Bind b0) u)))))) (\lambda (b0: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(clear (CHead c (Bind b) x0) (CHead e2 (Bind b0) u)))))) 
(\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i 
v e1 e2)))))) (ex4_5 B C C T T (\lambda (b0: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C (CHead c (Bind b) t) (CHead e1 
(Bind b0) u1))))))) (\lambda (b0: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(clear (CHead c (Bind b) x0) (CHead e2 
(Bind b0) u2))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 
e2))))))) (ex3_4_intro B C T T (\lambda (b0: B).(\lambda (e: C).(\lambda (u1: 
T).(\lambda (_: T).(eq C (CHead c (Bind b) t) (CHead e (Bind b0) u1)))))) 
(\lambda (b0: B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: T).(clear 
(CHead c (Bind b) x0) (CHead e (Bind b0) u2)))))) (\lambda (_: B).(\lambda 
(_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 u2))))) b c t x0 
(refl_equal C (CHead c (Bind b) t)) (clear_bind b c x0) H9)) c0 
(clear_gen_bind b c c0 t H6))))))) (\lambda (f: F).(\lambda (H6: (clear 
(CHead c (Flat f) t) c0)).(\lambda (H7: (eq nat (S i) (s (Flat f) x1))).(let 
H8 \def (f_equal nat nat (\lambda (e: nat).e) (S i) (s (Flat f) x1) H7) in 
(let H9 \def (eq_ind_r nat x1 (\lambda (n: nat).(subst0 n v t x0)) H5 (S i) 
H8) in (or4_intro0 (clear (CHead c (Flat f) x0) c0) (ex3_4 B C T T (\lambda 
(b: B).(\lambda (e: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e 
(Bind b) u1)))))) (\lambda (b: B).(\lambda (e: C).(\lambda (_: T).(\lambda 
(u2: T).(clear (CHead c (Flat f) x0) (CHead e (Bind b) u2)))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) 
(ex3_4 B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C c0 (CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(clear (CHead c (Flat f) x0) (CHead e2 
(Bind b) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(csubst0 i v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: B).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e1 
(Bind b) u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (u2: T).(clear (CHead c (Flat f) x0) (CHead e2 (Bind b) 
u2))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 e2))))))) 
(clear_flat c c0 (clear_gen_flat f c c0 t H6) f x0))))))) k H1 H3) c2 
H4)))))) H2)) (\lambda (H2: (ex3_2 C nat (\lambda (_: C).(\lambda (j: 
nat).(eq nat (S i) (s k j)))) (\lambda (c3: C).(\lambda (_: nat).(eq C c2 
(CHead c3 k t)))) (\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c 
c3))))).(ex3_2_ind C nat (\lambda (_: C).(\lambda (j: nat).(eq nat (S i) (s k 
j)))) (\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k t)))) (\lambda 
(c3: C).(\lambda (j: nat).(csubst0 j v c c3))) (or4 (clear c2 c0) (ex3_4 B C 
T T (\lambda (b: B).(\lambda (e: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 
(CHead e (Bind b) u1)))))) (\lambda (b: B).(\lambda (e: C).(\lambda (_: 
T).(\lambda (u2: T).(clear c2 (CHead e (Bind b) u2)))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) 
(ex3_4 B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C c0 (CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(clear c2 (CHead e2 (Bind b) u)))))) 
(\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i 
v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e1 (Bind b) u1))))))) 
(\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(u2: T).(clear c2 (CHead e2 (Bind b) u2))))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) 
(\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 i v e1 e2)))))))) (\lambda (x0: C).(\lambda (x1: 
nat).(\lambda (H3: (eq nat (S i) (s k x1))).(\lambda (H4: (eq C c2 (CHead x0 
k t))).(\lambda (H5: (csubst0 x1 v c x0)).(eq_ind_r C (CHead x0 k t) (\lambda 
(c3: C).(or4 (clear c3 c0) (ex3_4 B C T T (\lambda (b: B).(\lambda (e: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e (Bind b) u1)))))) 
(\lambda (b: B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: T).(clear c3 
(CHead e (Bind b) u2)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (ex3_4 B C C T (\lambda (b: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c0 (CHead e1 (Bind 
b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(clear c3 (CHead e2 (Bind b) u)))))) (\lambda (_: B).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i v e1 e2)))))) (ex4_5 B C C T T 
(\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(_: T).(eq C c0 (CHead e1 (Bind b) u1))))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(clear c3 (CHead e2 
(Bind b) u2))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 
e2))))))))) (K_ind (\lambda (k0: K).((clear (CHead c k0 t) c0) \to ((eq nat 
(S i) (s k0 x1)) \to (or4 (clear (CHead x0 k0 t) c0) (ex3_4 B C T T (\lambda 
(b: B).(\lambda (e: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e 
(Bind b) u1)))))) (\lambda (b: B).(\lambda (e: C).(\lambda (_: T).(\lambda 
(u2: T).(clear (CHead x0 k0 t) (CHead e (Bind b) u2)))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) 
(ex3_4 B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C c0 (CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(clear (CHead x0 k0 t) (CHead e2 (Bind b) 
u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 i v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e1 (Bind 
b) u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (u2: T).(clear (CHead x0 k0 t) (CHead e2 (Bind b) u2))))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(u2: T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 e2))))))))))) 
(\lambda (b: B).(\lambda (H6: (clear (CHead c (Bind b) t) c0)).(\lambda (H7: 
(eq nat (S i) (s (Bind b) x1))).(let H8 \def (f_equal nat nat (\lambda (e: 
nat).(match e in nat return (\lambda (_: nat).nat) with [O \Rightarrow i | (S 
n) \Rightarrow n])) (S i) (S x1) H7) in (let H9 \def (eq_ind_r nat x1 
(\lambda (n: nat).(csubst0 n v c x0)) H5 i H8) in (eq_ind_r C (CHead c (Bind 
b) t) (\lambda (c3: C).(or4 (clear (CHead x0 (Bind b) t) c3) (ex3_4 B C T T 
(\lambda (b0: B).(\lambda (e: C).(\lambda (u1: T).(\lambda (_: T).(eq C c3 
(CHead e (Bind b0) u1)))))) (\lambda (b0: B).(\lambda (e: C).(\lambda (_: 
T).(\lambda (u2: T).(clear (CHead x0 (Bind b) t) (CHead e (Bind b0) u2)))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v 
u1 u2)))))) (ex3_4 B C C T (\lambda (b0: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C c3 (CHead e1 (Bind b0) u)))))) (\lambda (b0: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(clear (CHead x0 (Bind b) 
t) (CHead e2 (Bind b0) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 i v e1 e2)))))) (ex4_5 B C C T T (\lambda (b0: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(eq C c3 
(CHead e1 (Bind b0) u1))))))) (\lambda (b0: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(clear (CHead x0 (Bind b) t) (CHead e2 
(Bind b0) u2))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 
e2))))))))) (or4_intro2 (clear (CHead x0 (Bind b) t) (CHead c (Bind b) t)) 
(ex3_4 B C T T (\lambda (b0: B).(\lambda (e: C).(\lambda (u1: T).(\lambda (_: 
T).(eq C (CHead c (Bind b) t) (CHead e (Bind b0) u1)))))) (\lambda (b0: 
B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: T).(clear (CHead x0 (Bind b) 
t) (CHead e (Bind b0) u2)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (ex3_4 B C C T (\lambda (b0: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C (CHead c (Bind b) 
t) (CHead e1 (Bind b0) u)))))) (\lambda (b0: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(clear (CHead x0 (Bind b) t) (CHead e2 (Bind b0) u)))))) 
(\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i 
v e1 e2)))))) (ex4_5 B C C T T (\lambda (b0: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C (CHead c (Bind b) t) (CHead e1 
(Bind b0) u1))))))) (\lambda (b0: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(clear (CHead x0 (Bind b) t) (CHead e2 
(Bind b0) u2))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 
e2))))))) (ex3_4_intro B C C T (\lambda (b0: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C (CHead c (Bind b) t) (CHead e1 (Bind b0) u)))))) 
(\lambda (b0: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(clear 
(CHead x0 (Bind b) t) (CHead e2 (Bind b0) u)))))) (\lambda (_: B).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i v e1 e2))))) b c x0 t 
(refl_equal C (CHead c (Bind b) t)) (clear_bind b x0 t) H9)) c0 
(clear_gen_bind b c c0 t H6))))))) (\lambda (f: F).(\lambda (H6: (clear 
(CHead c (Flat f) t) c0)).(\lambda (H7: (eq nat (S i) (s (Flat f) x1))).(let 
H8 \def (f_equal nat nat (\lambda (e: nat).e) (S i) (s (Flat f) x1) H7) in 
(let H9 \def (eq_ind_r nat x1 (\lambda (n: nat).(csubst0 n v c x0)) H5 (S i) 
H8) in (let H10 \def (H x0 v i H9 c0 (clear_gen_flat f c c0 t H6)) in 
(or4_ind (clear x0 c0) (ex3_4 B C T T (\lambda (b: B).(\lambda (e: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e (Bind b) u1)))))) 
(\lambda (b: B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: T).(clear x0 
(CHead e (Bind b) u2)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (ex3_4 B C C T (\lambda (b: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c0 (CHead e1 (Bind 
b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(clear x0 (CHead e2 (Bind b) u)))))) (\lambda (_: B).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i v e1 e2)))))) (ex4_5 B C C T T 
(\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(_: T).(eq C c0 (CHead e1 (Bind b) u1))))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(clear x0 (CHead e2 
(Bind b) u2))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 
e2))))))) (or4 (clear (CHead x0 (Flat f) t) c0) (ex3_4 B C T T (\lambda (b: 
B).(\lambda (e: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e (Bind 
b) u1)))))) (\lambda (b: B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: 
T).(clear (CHead x0 (Flat f) t) (CHead e (Bind b) u2)))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) 
(ex3_4 B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C c0 (CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(clear (CHead x0 (Flat f) t) (CHead e2 
(Bind b) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(csubst0 i v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: B).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e1 
(Bind b) u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (u2: T).(clear (CHead x0 (Flat f) t) (CHead e2 (Bind b) 
u2))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 
e2)))))))) (\lambda (H11: (clear x0 c0)).(or4_intro0 (clear (CHead x0 (Flat 
f) t) c0) (ex3_4 B C T T (\lambda (b: B).(\lambda (e: C).(\lambda (u1: 
T).(\lambda (_: T).(eq C c0 (CHead e (Bind b) u1)))))) (\lambda (b: 
B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: T).(clear (CHead x0 (Flat f) 
t) (CHead e (Bind b) u2)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (ex3_4 B C C T (\lambda (b: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c0 (CHead e1 (Bind 
b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(clear (CHead x0 (Flat f) t) (CHead e2 (Bind b) u)))))) (\lambda (_: 
B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i v e1 e2)))))) 
(ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (_: T).(eq C c0 (CHead e1 (Bind b) u1))))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(clear 
(CHead x0 (Flat f) t) (CHead e2 (Bind b) u2))))))) (\lambda (_: B).(\lambda 
(_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 
u2)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 i v e1 e2))))))) (clear_flat x0 c0 H11 f t))) 
(\lambda (H11: (ex3_4 B C T T (\lambda (b: B).(\lambda (e: C).(\lambda (u1: 
T).(\lambda (_: T).(eq C c0 (CHead e (Bind b) u1)))))) (\lambda (b: 
B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: T).(clear x0 (CHead e (Bind 
b) u2)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: 
T).(subst0 i v u1 u2))))))).(ex3_4_ind B C T T (\lambda (b: B).(\lambda (e: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e (Bind b) u1)))))) 
(\lambda (b: B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: T).(clear x0 
(CHead e (Bind b) u2)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 i v u1 u2))))) (or4 (clear (CHead x0 (Flat f) t) 
c0) (ex3_4 B C T T (\lambda (b: B).(\lambda (e: C).(\lambda (u1: T).(\lambda 
(_: T).(eq C c0 (CHead e (Bind b) u1)))))) (\lambda (b: B).(\lambda (e: 
C).(\lambda (_: T).(\lambda (u2: T).(clear (CHead x0 (Flat f) t) (CHead e 
(Bind b) u2)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(u2: T).(subst0 i v u1 u2)))))) (ex3_4 B C C T (\lambda (b: B).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C c0 (CHead e1 (Bind b) u)))))) 
(\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(clear 
(CHead x0 (Flat f) t) (CHead e2 (Bind b) u)))))) (\lambda (_: B).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i v e1 e2)))))) (ex4_5 B C 
C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (_: T).(eq C c0 (CHead e1 (Bind b) u1))))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(clear 
(CHead x0 (Flat f) t) (CHead e2 (Bind b) u2))))))) (\lambda (_: B).(\lambda 
(_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 
u2)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 i v e1 e2)))))))) (\lambda (x2: B).(\lambda (x3: 
C).(\lambda (x4: T).(\lambda (x5: T).(\lambda (H12: (eq C c0 (CHead x3 (Bind 
x2) x4))).(\lambda (H13: (clear x0 (CHead x3 (Bind x2) x5))).(\lambda (H14: 
(subst0 i v x4 x5)).(or4_intro1 (clear (CHead x0 (Flat f) t) c0) (ex3_4 B C T 
T (\lambda (b: B).(\lambda (e: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 
(CHead e (Bind b) u1)))))) (\lambda (b: B).(\lambda (e: C).(\lambda (_: 
T).(\lambda (u2: T).(clear (CHead x0 (Flat f) t) (CHead e (Bind b) u2)))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v 
u1 u2)))))) (ex3_4 B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C c0 (CHead e1 (Bind b) u)))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(clear (CHead x0 (Flat f) 
t) (CHead e2 (Bind b) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 i v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 
(CHead e1 (Bind b) u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(clear (CHead x0 (Flat f) t) (CHead e2 
(Bind b) u2))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 
e2))))))) (ex3_4_intro B C T T (\lambda (b: B).(\lambda (e: C).(\lambda (u1: 
T).(\lambda (_: T).(eq C c0 (CHead e (Bind b) u1)))))) (\lambda (b: 
B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: T).(clear (CHead x0 (Flat f) 
t) (CHead e (Bind b) u2)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 i v u1 u2))))) x2 x3 x4 x5 H12 (clear_flat x0 
(CHead x3 (Bind x2) x5) H13 f t) H14))))))))) H11)) (\lambda (H11: (ex3_4 B C 
C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c0 
(CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(clear x0 (CHead e2 (Bind b) u)))))) (\lambda (_: 
B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i v e1 
e2))))))).(ex3_4_ind B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C c0 (CHead e1 (Bind b) u)))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(clear x0 (CHead e2 (Bind 
b) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 i v e1 e2))))) (or4 (clear (CHead x0 (Flat f) t) c0) (ex3_4 B C T 
T (\lambda (b: B).(\lambda (e: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 
(CHead e (Bind b) u1)))))) (\lambda (b: B).(\lambda (e: C).(\lambda (_: 
T).(\lambda (u2: T).(clear (CHead x0 (Flat f) t) (CHead e (Bind b) u2)))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v 
u1 u2)))))) (ex3_4 B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C c0 (CHead e1 (Bind b) u)))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(clear (CHead x0 (Flat f) 
t) (CHead e2 (Bind b) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 i v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 
(CHead e1 (Bind b) u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(clear (CHead x0 (Flat f) t) (CHead e2 
(Bind b) u2))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 
e2)))))))) (\lambda (x2: B).(\lambda (x3: C).(\lambda (x4: C).(\lambda (x5: 
T).(\lambda (H12: (eq C c0 (CHead x3 (Bind x2) x5))).(\lambda (H13: (clear x0 
(CHead x4 (Bind x2) x5))).(\lambda (H14: (csubst0 i v x3 x4)).(or4_intro2 
(clear (CHead x0 (Flat f) t) c0) (ex3_4 B C T T (\lambda (b: B).(\lambda (e: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e (Bind b) u1)))))) 
(\lambda (b: B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: T).(clear 
(CHead x0 (Flat f) t) (CHead e (Bind b) u2)))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (ex3_4 B C C T 
(\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c0 
(CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(clear (CHead x0 (Flat f) t) (CHead e2 (Bind b) u)))))) 
(\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i 
v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e1 (Bind b) u1))))))) 
(\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(u2: T).(clear (CHead x0 (Flat f) t) (CHead e2 (Bind b) u2))))))) (\lambda 
(_: B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: 
T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 e2))))))) (ex3_4_intro B C 
C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c0 
(CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(clear (CHead x0 (Flat f) t) (CHead e2 (Bind b) u)))))) 
(\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i 
v e1 e2))))) x2 x3 x4 x5 H12 (clear_flat x0 (CHead x4 (Bind x2) x5) H13 f t) 
H14))))))))) H11)) (\lambda (H11: (ex4_5 B C C T T (\lambda (b: B).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e1 
(Bind b) u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (u2: T).(clear x0 (CHead e2 (Bind b) u2))))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 
i v u1 u2)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (_: T).(csubst0 i v e1 e2)))))))).(ex4_5_ind B C C T T 
(\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(_: T).(eq C c0 (CHead e1 (Bind b) u1))))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(clear x0 (CHead e2 
(Bind b) u2))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 
e2)))))) (or4 (clear (CHead x0 (Flat f) t) c0) (ex3_4 B C T T (\lambda (b: 
B).(\lambda (e: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e (Bind 
b) u1)))))) (\lambda (b: B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: 
T).(clear (CHead x0 (Flat f) t) (CHead e (Bind b) u2)))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) 
(ex3_4 B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C c0 (CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(clear (CHead x0 (Flat f) t) (CHead e2 
(Bind b) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(csubst0 i v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: B).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e1 
(Bind b) u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (u2: T).(clear (CHead x0 (Flat f) t) (CHead e2 (Bind b) 
u2))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 
e2)))))))) (\lambda (x2: B).(\lambda (x3: C).(\lambda (x4: C).(\lambda (x5: 
T).(\lambda (x6: T).(\lambda (H12: (eq C c0 (CHead x3 (Bind x2) 
x5))).(\lambda (H13: (clear x0 (CHead x4 (Bind x2) x6))).(\lambda (H14: 
(subst0 i v x5 x6)).(\lambda (H15: (csubst0 i v x3 x4)).(or4_intro3 (clear 
(CHead x0 (Flat f) t) c0) (ex3_4 B C T T (\lambda (b: B).(\lambda (e: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e (Bind b) u1)))))) 
(\lambda (b: B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: T).(clear 
(CHead x0 (Flat f) t) (CHead e (Bind b) u2)))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (ex3_4 B C C T 
(\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c0 
(CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(clear (CHead x0 (Flat f) t) (CHead e2 (Bind b) u)))))) 
(\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i 
v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e1 (Bind b) u1))))))) 
(\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(u2: T).(clear (CHead x0 (Flat f) t) (CHead e2 (Bind b) u2))))))) (\lambda 
(_: B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: 
T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 e2))))))) (ex4_5_intro B C 
C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (_: T).(eq C c0 (CHead e1 (Bind b) u1))))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(clear 
(CHead x0 (Flat f) t) (CHead e2 (Bind b) u2))))))) (\lambda (_: B).(\lambda 
(_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 
u2)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 i v e1 e2)))))) x2 x3 x4 x5 x6 H12 (clear_flat x0 
(CHead x4 (Bind x2) x6) H13 f t) H14 H15))))))))))) H11)) H10))))))) k H1 H3) 
c2 H4)))))) H2)) (\lambda (H2: (ex4_3 T C nat (\lambda (_: T).(\lambda (_: 
C).(\lambda (j: nat).(eq nat (S i) (s k j))))) (\lambda (u2: T).(\lambda (c3: 
C).(\lambda (_: nat).(eq C c2 (CHead c3 k u2))))) (\lambda (u2: T).(\lambda 
(_: C).(\lambda (j: nat).(subst0 j v t u2)))) (\lambda (_: T).(\lambda (c3: 
C).(\lambda (j: nat).(csubst0 j v c c3)))))).(ex4_3_ind T C nat (\lambda (_: 
T).(\lambda (_: C).(\lambda (j: nat).(eq nat (S i) (s k j))))) (\lambda (u2: 
T).(\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k u2))))) (\lambda 
(u2: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v t u2)))) (\lambda (_: 
T).(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c c3)))) (or4 (clear c2 
c0) (ex3_4 B C T T (\lambda (b: B).(\lambda (e: C).(\lambda (u1: T).(\lambda 
(_: T).(eq C c0 (CHead e (Bind b) u1)))))) (\lambda (b: B).(\lambda (e: 
C).(\lambda (_: T).(\lambda (u2: T).(clear c2 (CHead e (Bind b) u2)))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v 
u1 u2)))))) (ex3_4 B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C c0 (CHead e1 (Bind b) u)))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(clear c2 (CHead e2 (Bind 
b) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 i v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e1 (Bind 
b) u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (u2: T).(clear c2 (CHead e2 (Bind b) u2))))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 
i v u1 u2)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (_: T).(csubst0 i v e1 e2)))))))) (\lambda (x0: T).(\lambda 
(x1: C).(\lambda (x2: nat).(\lambda (H3: (eq nat (S i) (s k x2))).(\lambda 
(H4: (eq C c2 (CHead x1 k x0))).(\lambda (H5: (subst0 x2 v t x0)).(\lambda 
(H6: (csubst0 x2 v c x1)).(eq_ind_r C (CHead x1 k x0) (\lambda (c3: C).(or4 
(clear c3 c0) (ex3_4 B C T T (\lambda (b: B).(\lambda (e: C).(\lambda (u1: 
T).(\lambda (_: T).(eq C c0 (CHead e (Bind b) u1)))))) (\lambda (b: 
B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: T).(clear c3 (CHead e (Bind 
b) u2)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: 
T).(subst0 i v u1 u2)))))) (ex3_4 B C C T (\lambda (b: B).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C c0 (CHead e1 (Bind b) u)))))) 
(\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(clear c3 
(CHead e2 (Bind b) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 i v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 
(CHead e1 (Bind b) u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(clear c3 (CHead e2 (Bind b) u2))))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(u2: T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 e2))))))))) (K_ind 
(\lambda (k0: K).((clear (CHead c k0 t) c0) \to ((eq nat (S i) (s k0 x2)) \to 
(or4 (clear (CHead x1 k0 x0) c0) (ex3_4 B C T T (\lambda (b: B).(\lambda (e: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e (Bind b) u1)))))) 
(\lambda (b: B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: T).(clear 
(CHead x1 k0 x0) (CHead e (Bind b) u2)))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (ex3_4 B C C T 
(\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c0 
(CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(clear (CHead x1 k0 x0) (CHead e2 (Bind b) u)))))) 
(\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i 
v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e1 (Bind b) u1))))))) 
(\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(u2: T).(clear (CHead x1 k0 x0) (CHead e2 (Bind b) u2))))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 
i v u1 u2)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (_: T).(csubst0 i v e1 e2))))))))))) (\lambda (b: B).(\lambda 
(H7: (clear (CHead c (Bind b) t) c0)).(\lambda (H8: (eq nat (S i) (s (Bind b) 
x2))).(let H9 \def (f_equal nat nat (\lambda (e: nat).(match e in nat return 
(\lambda (_: nat).nat) with [O \Rightarrow i | (S n) \Rightarrow n])) (S i) 
(S x2) H8) in (let H10 \def (eq_ind_r nat x2 (\lambda (n: nat).(csubst0 n v c 
x1)) H6 i H9) in (let H11 \def (eq_ind_r nat x2 (\lambda (n: nat).(subst0 n v 
t x0)) H5 i H9) in (eq_ind_r C (CHead c (Bind b) t) (\lambda (c3: C).(or4 
(clear (CHead x1 (Bind b) x0) c3) (ex3_4 B C T T (\lambda (b0: B).(\lambda 
(e: C).(\lambda (u1: T).(\lambda (_: T).(eq C c3 (CHead e (Bind b0) u1)))))) 
(\lambda (b0: B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: T).(clear 
(CHead x1 (Bind b) x0) (CHead e (Bind b0) u2)))))) (\lambda (_: B).(\lambda 
(_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (ex3_4 B C C 
T (\lambda (b0: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c3 
(CHead e1 (Bind b0) u)))))) (\lambda (b0: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(clear (CHead x1 (Bind b) x0) (CHead e2 (Bind b0) u)))))) 
(\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i 
v e1 e2)))))) (ex4_5 B C C T T (\lambda (b0: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C c3 (CHead e1 (Bind b0) u1))))))) 
(\lambda (b0: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(u2: T).(clear (CHead x1 (Bind b) x0) (CHead e2 (Bind b0) u2))))))) (\lambda 
(_: B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: 
T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 e2))))))))) (or4_intro3 
(clear (CHead x1 (Bind b) x0) (CHead c (Bind b) t)) (ex3_4 B C T T (\lambda 
(b0: B).(\lambda (e: C).(\lambda (u1: T).(\lambda (_: T).(eq C (CHead c (Bind 
b) t) (CHead e (Bind b0) u1)))))) (\lambda (b0: B).(\lambda (e: C).(\lambda 
(_: T).(\lambda (u2: T).(clear (CHead x1 (Bind b) x0) (CHead e (Bind b0) 
u2)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: 
T).(subst0 i v u1 u2)))))) (ex3_4 B C C T (\lambda (b0: B).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C (CHead c (Bind b) t) (CHead e1 (Bind 
b0) u)))))) (\lambda (b0: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(clear (CHead x1 (Bind b) x0) (CHead e2 (Bind b0) u)))))) (\lambda (_: 
B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i v e1 e2)))))) 
(ex4_5 B C C T T (\lambda (b0: B).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (_: T).(eq C (CHead c (Bind b) t) (CHead e1 (Bind b0) 
u1))))))) (\lambda (b0: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (u2: T).(clear (CHead x1 (Bind b) x0) (CHead e2 (Bind b0) 
u2))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 e2))))))) 
(ex4_5_intro B C C T T (\lambda (b0: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C (CHead c (Bind b) t) (CHead e1 
(Bind b0) u1))))))) (\lambda (b0: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(clear (CHead x1 (Bind b) x0) (CHead e2 
(Bind b0) u2))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 
e2)))))) b c x1 t x0 (refl_equal C (CHead c (Bind b) t)) (clear_bind b x1 x0) 
H11 H10)) c0 (clear_gen_bind b c c0 t H7)))))))) (\lambda (f: F).(\lambda 
(H7: (clear (CHead c (Flat f) t) c0)).(\lambda (H8: (eq nat (S i) (s (Flat f) 
x2))).(let H9 \def (f_equal nat nat (\lambda (e: nat).e) (S i) (s (Flat f) 
x2) H8) in (let H10 \def (eq_ind_r nat x2 (\lambda (n: nat).(csubst0 n v c 
x1)) H6 (S i) H9) in (let H11 \def (eq_ind_r nat x2 (\lambda (n: nat).(subst0 
n v t x0)) H5 (S i) H9) in (let H12 \def (H x1 v i H10 c0 (clear_gen_flat f c 
c0 t H7)) in (or4_ind (clear x1 c0) (ex3_4 B C T T (\lambda (b: B).(\lambda 
(e: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e (Bind b) u1)))))) 
(\lambda (b: B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: T).(clear x1 
(CHead e (Bind b) u2)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (ex3_4 B C C T (\lambda (b: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c0 (CHead e1 (Bind 
b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(clear x1 (CHead e2 (Bind b) u)))))) (\lambda (_: B).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i v e1 e2)))))) (ex4_5 B C C T T 
(\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(_: T).(eq C c0 (CHead e1 (Bind b) u1))))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(clear x1 (CHead e2 
(Bind b) u2))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 
e2))))))) (or4 (clear (CHead x1 (Flat f) x0) c0) (ex3_4 B C T T (\lambda (b: 
B).(\lambda (e: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e (Bind 
b) u1)))))) (\lambda (b: B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: 
T).(clear (CHead x1 (Flat f) x0) (CHead e (Bind b) u2)))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) 
(ex3_4 B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C c0 (CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(clear (CHead x1 (Flat f) x0) (CHead e2 
(Bind b) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(csubst0 i v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: B).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e1 
(Bind b) u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (u2: T).(clear (CHead x1 (Flat f) x0) (CHead e2 (Bind b) 
u2))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 
e2)))))))) (\lambda (H13: (clear x1 c0)).(or4_intro0 (clear (CHead x1 (Flat 
f) x0) c0) (ex3_4 B C T T (\lambda (b: B).(\lambda (e: C).(\lambda (u1: 
T).(\lambda (_: T).(eq C c0 (CHead e (Bind b) u1)))))) (\lambda (b: 
B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: T).(clear (CHead x1 (Flat f) 
x0) (CHead e (Bind b) u2)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (ex3_4 B C C T (\lambda (b: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c0 (CHead e1 (Bind 
b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(clear (CHead x1 (Flat f) x0) (CHead e2 (Bind b) u)))))) (\lambda (_: 
B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i v e1 e2)))))) 
(ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (_: T).(eq C c0 (CHead e1 (Bind b) u1))))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(clear 
(CHead x1 (Flat f) x0) (CHead e2 (Bind b) u2))))))) (\lambda (_: B).(\lambda 
(_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 
u2)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 i v e1 e2))))))) (clear_flat x1 c0 H13 f x0))) 
(\lambda (H13: (ex3_4 B C T T (\lambda (b: B).(\lambda (e: C).(\lambda (u1: 
T).(\lambda (_: T).(eq C c0 (CHead e (Bind b) u1)))))) (\lambda (b: 
B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: T).(clear x1 (CHead e (Bind 
b) u2)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: 
T).(subst0 i v u1 u2))))))).(ex3_4_ind B C T T (\lambda (b: B).(\lambda (e: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e (Bind b) u1)))))) 
(\lambda (b: B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: T).(clear x1 
(CHead e (Bind b) u2)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 i v u1 u2))))) (or4 (clear (CHead x1 (Flat f) x0) 
c0) (ex3_4 B C T T (\lambda (b: B).(\lambda (e: C).(\lambda (u1: T).(\lambda 
(_: T).(eq C c0 (CHead e (Bind b) u1)))))) (\lambda (b: B).(\lambda (e: 
C).(\lambda (_: T).(\lambda (u2: T).(clear (CHead x1 (Flat f) x0) (CHead e 
(Bind b) u2)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(u2: T).(subst0 i v u1 u2)))))) (ex3_4 B C C T (\lambda (b: B).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C c0 (CHead e1 (Bind b) u)))))) 
(\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(clear 
(CHead x1 (Flat f) x0) (CHead e2 (Bind b) u)))))) (\lambda (_: B).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i v e1 e2)))))) (ex4_5 B C 
C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (_: T).(eq C c0 (CHead e1 (Bind b) u1))))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(clear 
(CHead x1 (Flat f) x0) (CHead e2 (Bind b) u2))))))) (\lambda (_: B).(\lambda 
(_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 
u2)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 i v e1 e2)))))))) (\lambda (x3: B).(\lambda (x4: 
C).(\lambda (x5: T).(\lambda (x6: T).(\lambda (H14: (eq C c0 (CHead x4 (Bind 
x3) x5))).(\lambda (H15: (clear x1 (CHead x4 (Bind x3) x6))).(\lambda (H16: 
(subst0 i v x5 x6)).(or4_intro1 (clear (CHead x1 (Flat f) x0) c0) (ex3_4 B C 
T T (\lambda (b: B).(\lambda (e: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 
(CHead e (Bind b) u1)))))) (\lambda (b: B).(\lambda (e: C).(\lambda (_: 
T).(\lambda (u2: T).(clear (CHead x1 (Flat f) x0) (CHead e (Bind b) u2)))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v 
u1 u2)))))) (ex3_4 B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C c0 (CHead e1 (Bind b) u)))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(clear (CHead x1 (Flat f) 
x0) (CHead e2 (Bind b) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 i v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 
(CHead e1 (Bind b) u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(clear (CHead x1 (Flat f) x0) (CHead e2 
(Bind b) u2))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 
e2))))))) (ex3_4_intro B C T T (\lambda (b: B).(\lambda (e: C).(\lambda (u1: 
T).(\lambda (_: T).(eq C c0 (CHead e (Bind b) u1)))))) (\lambda (b: 
B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: T).(clear (CHead x1 (Flat f) 
x0) (CHead e (Bind b) u2)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 i v u1 u2))))) x3 x4 x5 x6 H14 (clear_flat x1 
(CHead x4 (Bind x3) x6) H15 f x0) H16))))))))) H13)) (\lambda (H13: (ex3_4 B 
C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C 
c0 (CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(clear x1 (CHead e2 (Bind b) u)))))) (\lambda (_: 
B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i v e1 
e2))))))).(ex3_4_ind B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C c0 (CHead e1 (Bind b) u)))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(clear x1 (CHead e2 (Bind 
b) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 i v e1 e2))))) (or4 (clear (CHead x1 (Flat f) x0) c0) (ex3_4 B C 
T T (\lambda (b: B).(\lambda (e: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 
(CHead e (Bind b) u1)))))) (\lambda (b: B).(\lambda (e: C).(\lambda (_: 
T).(\lambda (u2: T).(clear (CHead x1 (Flat f) x0) (CHead e (Bind b) u2)))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v 
u1 u2)))))) (ex3_4 B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C c0 (CHead e1 (Bind b) u)))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(clear (CHead x1 (Flat f) 
x0) (CHead e2 (Bind b) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 i v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 
(CHead e1 (Bind b) u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(clear (CHead x1 (Flat f) x0) (CHead e2 
(Bind b) u2))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 
e2)))))))) (\lambda (x3: B).(\lambda (x4: C).(\lambda (x5: C).(\lambda (x6: 
T).(\lambda (H14: (eq C c0 (CHead x4 (Bind x3) x6))).(\lambda (H15: (clear x1 
(CHead x5 (Bind x3) x6))).(\lambda (H16: (csubst0 i v x4 x5)).(or4_intro2 
(clear (CHead x1 (Flat f) x0) c0) (ex3_4 B C T T (\lambda (b: B).(\lambda (e: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e (Bind b) u1)))))) 
(\lambda (b: B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: T).(clear 
(CHead x1 (Flat f) x0) (CHead e (Bind b) u2)))))) (\lambda (_: B).(\lambda 
(_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (ex3_4 B C C 
T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c0 
(CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(clear (CHead x1 (Flat f) x0) (CHead e2 (Bind b) u)))))) 
(\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i 
v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e1 (Bind b) u1))))))) 
(\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(u2: T).(clear (CHead x1 (Flat f) x0) (CHead e2 (Bind b) u2))))))) (\lambda 
(_: B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: 
T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 e2))))))) (ex3_4_intro B C 
C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c0 
(CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(clear (CHead x1 (Flat f) x0) (CHead e2 (Bind b) u)))))) 
(\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i 
v e1 e2))))) x3 x4 x5 x6 H14 (clear_flat x1 (CHead x5 (Bind x3) x6) H15 f x0) 
H16))))))))) H13)) (\lambda (H13: (ex4_5 B C C T T (\lambda (b: B).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e1 
(Bind b) u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (u2: T).(clear x1 (CHead e2 (Bind b) u2))))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 
i v u1 u2)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (_: T).(csubst0 i v e1 e2)))))))).(ex4_5_ind B C C T T 
(\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(_: T).(eq C c0 (CHead e1 (Bind b) u1))))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(clear x1 (CHead e2 
(Bind b) u2))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 
e2)))))) (or4 (clear (CHead x1 (Flat f) x0) c0) (ex3_4 B C T T (\lambda (b: 
B).(\lambda (e: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e (Bind 
b) u1)))))) (\lambda (b: B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: 
T).(clear (CHead x1 (Flat f) x0) (CHead e (Bind b) u2)))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) 
(ex3_4 B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C c0 (CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(clear (CHead x1 (Flat f) x0) (CHead e2 
(Bind b) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(csubst0 i v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: B).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e1 
(Bind b) u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (u2: T).(clear (CHead x1 (Flat f) x0) (CHead e2 (Bind b) 
u2))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 
e2)))))))) (\lambda (x3: B).(\lambda (x4: C).(\lambda (x5: C).(\lambda (x6: 
T).(\lambda (x7: T).(\lambda (H14: (eq C c0 (CHead x4 (Bind x3) 
x6))).(\lambda (H15: (clear x1 (CHead x5 (Bind x3) x7))).(\lambda (H16: 
(subst0 i v x6 x7)).(\lambda (H17: (csubst0 i v x4 x5)).(or4_intro3 (clear 
(CHead x1 (Flat f) x0) c0) (ex3_4 B C T T (\lambda (b: B).(\lambda (e: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e (Bind b) u1)))))) 
(\lambda (b: B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: T).(clear 
(CHead x1 (Flat f) x0) (CHead e (Bind b) u2)))))) (\lambda (_: B).(\lambda 
(_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (ex3_4 B C C 
T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c0 
(CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(clear (CHead x1 (Flat f) x0) (CHead e2 (Bind b) u)))))) 
(\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i 
v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e1 (Bind b) u1))))))) 
(\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(u2: T).(clear (CHead x1 (Flat f) x0) (CHead e2 (Bind b) u2))))))) (\lambda 
(_: B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: 
T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 e2))))))) (ex4_5_intro B C 
C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (_: T).(eq C c0 (CHead e1 (Bind b) u1))))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(clear 
(CHead x1 (Flat f) x0) (CHead e2 (Bind b) u2))))))) (\lambda (_: B).(\lambda 
(_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 
u2)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 i v e1 e2)))))) x3 x4 x5 x6 x7 H14 (clear_flat x1 
(CHead x5 (Bind x3) x7) H15 f x0) H16 H17))))))))))) H13)) H12)))))))) k H1 
H3) c2 H4)))))))) H2)) (csubst0_gen_head k c c2 t v (S i) H0)))))))))))) c1).
(* COMMENTS
Initial nodes: 14968
END *)

theorem csubst0_clear_trans:
 \forall (c1: C).(\forall (c2: C).(\forall (v: T).(\forall (i: nat).((csubst0 
i v c1 c2) \to (\forall (e2: C).((clear c2 e2) \to (or (clear c1 e2) (ex2 C 
(\lambda (e1: C).(csubst0 i v e1 e2)) (\lambda (e1: C).(clear c1 e1))))))))))
\def
 \lambda (c1: C).(\lambda (c2: C).(\lambda (v: T).(\lambda (i: nat).(\lambda 
(H: (csubst0 i v c1 c2)).(csubst0_ind (\lambda (n: nat).(\lambda (t: 
T).(\lambda (c: C).(\lambda (c0: C).(\forall (e2: C).((clear c0 e2) \to (or 
(clear c e2) (ex2 C (\lambda (e1: C).(csubst0 n t e1 e2)) (\lambda (e1: 
C).(clear c e1)))))))))) (\lambda (k: K).(\lambda (i0: nat).(\lambda (v0: 
T).(\lambda (u1: T).(\lambda (u2: T).(\lambda (H0: (subst0 i0 v0 u1 
u2)).(\lambda (c: C).(\lambda (e2: C).(\lambda (H1: (clear (CHead c k u2) 
e2)).(K_ind (\lambda (k0: K).((clear (CHead c k0 u2) e2) \to (or (clear 
(CHead c k0 u1) e2) (ex2 C (\lambda (e1: C).(csubst0 (s k0 i0) v0 e1 e2)) 
(\lambda (e1: C).(clear (CHead c k0 u1) e1)))))) (\lambda (b: B).(\lambda 
(H2: (clear (CHead c (Bind b) u2) e2)).(eq_ind_r C (CHead c (Bind b) u2) 
(\lambda (c0: C).(or (clear (CHead c (Bind b) u1) c0) (ex2 C (\lambda (e1: 
C).(csubst0 (s (Bind b) i0) v0 e1 c0)) (\lambda (e1: C).(clear (CHead c (Bind 
b) u1) e1))))) (or_intror (clear (CHead c (Bind b) u1) (CHead c (Bind b) u2)) 
(ex2 C (\lambda (e1: C).(csubst0 (S i0) v0 e1 (CHead c (Bind b) u2))) 
(\lambda (e1: C).(clear (CHead c (Bind b) u1) e1))) (ex_intro2 C (\lambda 
(e1: C).(csubst0 (S i0) v0 e1 (CHead c (Bind b) u2))) (\lambda (e1: C).(clear 
(CHead c (Bind b) u1) e1)) (CHead c (Bind b) u1) (csubst0_snd_bind b i0 v0 u1 
u2 H0 c) (clear_bind b c u1))) e2 (clear_gen_bind b c e2 u2 H2)))) (\lambda 
(f: F).(\lambda (H2: (clear (CHead c (Flat f) u2) e2)).(or_introl (clear 
(CHead c (Flat f) u1) e2) (ex2 C (\lambda (e1: C).(csubst0 i0 v0 e1 e2)) 
(\lambda (e1: C).(clear (CHead c (Flat f) u1) e1))) (clear_flat c e2 
(clear_gen_flat f c e2 u2 H2) f u1)))) k H1)))))))))) (\lambda (k: 
K).(\lambda (i0: nat).(\lambda (c3: C).(\lambda (c4: C).(\lambda (v0: 
T).(\lambda (H0: (csubst0 i0 v0 c3 c4)).(\lambda (H1: ((\forall (e2: 
C).((clear c4 e2) \to (or (clear c3 e2) (ex2 C (\lambda (e1: C).(csubst0 i0 
v0 e1 e2)) (\lambda (e1: C).(clear c3 e1)))))))).(\lambda (u: T).(\lambda 
(e2: C).(\lambda (H2: (clear (CHead c4 k u) e2)).(K_ind (\lambda (k0: 
K).((clear (CHead c4 k0 u) e2) \to (or (clear (CHead c3 k0 u) e2) (ex2 C 
(\lambda (e1: C).(csubst0 (s k0 i0) v0 e1 e2)) (\lambda (e1: C).(clear (CHead 
c3 k0 u) e1)))))) (\lambda (b: B).(\lambda (H3: (clear (CHead c4 (Bind b) u) 
e2)).(eq_ind_r C (CHead c4 (Bind b) u) (\lambda (c: C).(or (clear (CHead c3 
(Bind b) u) c) (ex2 C (\lambda (e1: C).(csubst0 (s (Bind b) i0) v0 e1 c)) 
(\lambda (e1: C).(clear (CHead c3 (Bind b) u) e1))))) (or_intror (clear 
(CHead c3 (Bind b) u) (CHead c4 (Bind b) u)) (ex2 C (\lambda (e1: C).(csubst0 
(S i0) v0 e1 (CHead c4 (Bind b) u))) (\lambda (e1: C).(clear (CHead c3 (Bind 
b) u) e1))) (ex_intro2 C (\lambda (e1: C).(csubst0 (S i0) v0 e1 (CHead c4 
(Bind b) u))) (\lambda (e1: C).(clear (CHead c3 (Bind b) u) e1)) (CHead c3 
(Bind b) u) (csubst0_fst_bind b i0 c3 c4 v0 H0 u) (clear_bind b c3 u))) e2 
(clear_gen_bind b c4 e2 u H3)))) (\lambda (f: F).(\lambda (H3: (clear (CHead 
c4 (Flat f) u) e2)).(let H_x \def (H1 e2 (clear_gen_flat f c4 e2 u H3)) in 
(let H4 \def H_x in (or_ind (clear c3 e2) (ex2 C (\lambda (e1: C).(csubst0 i0 
v0 e1 e2)) (\lambda (e1: C).(clear c3 e1))) (or (clear (CHead c3 (Flat f) u) 
e2) (ex2 C (\lambda (e1: C).(csubst0 i0 v0 e1 e2)) (\lambda (e1: C).(clear 
(CHead c3 (Flat f) u) e1)))) (\lambda (H5: (clear c3 e2)).(or_introl (clear 
(CHead c3 (Flat f) u) e2) (ex2 C (\lambda (e1: C).(csubst0 i0 v0 e1 e2)) 
(\lambda (e1: C).(clear (CHead c3 (Flat f) u) e1))) (clear_flat c3 e2 H5 f 
u))) (\lambda (H5: (ex2 C (\lambda (e1: C).(csubst0 i0 v0 e1 e2)) (\lambda 
(e1: C).(clear c3 e1)))).(ex2_ind C (\lambda (e1: C).(csubst0 i0 v0 e1 e2)) 
(\lambda (e1: C).(clear c3 e1)) (or (clear (CHead c3 (Flat f) u) e2) (ex2 C 
(\lambda (e1: C).(csubst0 i0 v0 e1 e2)) (\lambda (e1: C).(clear (CHead c3 
(Flat f) u) e1)))) (\lambda (x: C).(\lambda (H6: (csubst0 i0 v0 x 
e2)).(\lambda (H7: (clear c3 x)).(or_intror (clear (CHead c3 (Flat f) u) e2) 
(ex2 C (\lambda (e1: C).(csubst0 i0 v0 e1 e2)) (\lambda (e1: C).(clear (CHead 
c3 (Flat f) u) e1))) (ex_intro2 C (\lambda (e1: C).(csubst0 i0 v0 e1 e2)) 
(\lambda (e1: C).(clear (CHead c3 (Flat f) u) e1)) x H6 (clear_flat c3 x H7 f 
u)))))) H5)) H4))))) k H2))))))))))) (\lambda (k: K).(\lambda (i0: 
nat).(\lambda (v0: T).(\lambda (u1: T).(\lambda (u2: T).(\lambda (H0: (subst0 
i0 v0 u1 u2)).(\lambda (c3: C).(\lambda (c4: C).(\lambda (H1: (csubst0 i0 v0 
c3 c4)).(\lambda (H2: ((\forall (e2: C).((clear c4 e2) \to (or (clear c3 e2) 
(ex2 C (\lambda (e1: C).(csubst0 i0 v0 e1 e2)) (\lambda (e1: C).(clear c3 
e1)))))))).(\lambda (e2: C).(\lambda (H3: (clear (CHead c4 k u2) e2)).(K_ind 
(\lambda (k0: K).((clear (CHead c4 k0 u2) e2) \to (or (clear (CHead c3 k0 u1) 
e2) (ex2 C (\lambda (e1: C).(csubst0 (s k0 i0) v0 e1 e2)) (\lambda (e1: 
C).(clear (CHead c3 k0 u1) e1)))))) (\lambda (b: B).(\lambda (H4: (clear 
(CHead c4 (Bind b) u2) e2)).(eq_ind_r C (CHead c4 (Bind b) u2) (\lambda (c: 
C).(or (clear (CHead c3 (Bind b) u1) c) (ex2 C (\lambda (e1: C).(csubst0 (s 
(Bind b) i0) v0 e1 c)) (\lambda (e1: C).(clear (CHead c3 (Bind b) u1) e1))))) 
(or_intror (clear (CHead c3 (Bind b) u1) (CHead c4 (Bind b) u2)) (ex2 C 
(\lambda (e1: C).(csubst0 (S i0) v0 e1 (CHead c4 (Bind b) u2))) (\lambda (e1: 
C).(clear (CHead c3 (Bind b) u1) e1))) (ex_intro2 C (\lambda (e1: C).(csubst0 
(S i0) v0 e1 (CHead c4 (Bind b) u2))) (\lambda (e1: C).(clear (CHead c3 (Bind 
b) u1) e1)) (CHead c3 (Bind b) u1) (csubst0_both_bind b i0 v0 u1 u2 H0 c3 c4 
H1) (clear_bind b c3 u1))) e2 (clear_gen_bind b c4 e2 u2 H4)))) (\lambda (f: 
F).(\lambda (H4: (clear (CHead c4 (Flat f) u2) e2)).(let H_x \def (H2 e2 
(clear_gen_flat f c4 e2 u2 H4)) in (let H5 \def H_x in (or_ind (clear c3 e2) 
(ex2 C (\lambda (e1: C).(csubst0 i0 v0 e1 e2)) (\lambda (e1: C).(clear c3 
e1))) (or (clear (CHead c3 (Flat f) u1) e2) (ex2 C (\lambda (e1: C).(csubst0 
i0 v0 e1 e2)) (\lambda (e1: C).(clear (CHead c3 (Flat f) u1) e1)))) (\lambda 
(H6: (clear c3 e2)).(or_introl (clear (CHead c3 (Flat f) u1) e2) (ex2 C 
(\lambda (e1: C).(csubst0 i0 v0 e1 e2)) (\lambda (e1: C).(clear (CHead c3 
(Flat f) u1) e1))) (clear_flat c3 e2 H6 f u1))) (\lambda (H6: (ex2 C (\lambda 
(e1: C).(csubst0 i0 v0 e1 e2)) (\lambda (e1: C).(clear c3 e1)))).(ex2_ind C 
(\lambda (e1: C).(csubst0 i0 v0 e1 e2)) (\lambda (e1: C).(clear c3 e1)) (or 
(clear (CHead c3 (Flat f) u1) e2) (ex2 C (\lambda (e1: C).(csubst0 i0 v0 e1 
e2)) (\lambda (e1: C).(clear (CHead c3 (Flat f) u1) e1)))) (\lambda (x: 
C).(\lambda (H7: (csubst0 i0 v0 x e2)).(\lambda (H8: (clear c3 x)).(or_intror 
(clear (CHead c3 (Flat f) u1) e2) (ex2 C (\lambda (e1: C).(csubst0 i0 v0 e1 
e2)) (\lambda (e1: C).(clear (CHead c3 (Flat f) u1) e1))) (ex_intro2 C 
(\lambda (e1: C).(csubst0 i0 v0 e1 e2)) (\lambda (e1: C).(clear (CHead c3 
(Flat f) u1) e1)) x H7 (clear_flat c3 x H8 f u1)))))) H6)) H5))))) k 
H3))))))))))))) i v c1 c2 H))))).
(* COMMENTS
Initial nodes: 2085
END *)

